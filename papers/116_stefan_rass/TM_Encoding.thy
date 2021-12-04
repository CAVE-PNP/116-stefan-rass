theory TM_Encoding
  imports Goedel_Numbering TM SQ
    "Supplementary/Misc" "HOL-Library.Sublist"
begin


section\<open>Encoding TMs\<close>

text\<open>As defined in the paper (ch 4.2, p. 11f, outlined in ch. 3.1, p. 8)
  the decoding of a TM \<open>M\<close> from a binary word \<open>w\<close> includes:

  1. Exponential padding. "all but the most significant \<open>\<lceil>log(len(w))\<rceil>\<close> bits are ignored"
  2. Arbitrary-length \<open>1\<^sup>+0\<close> prefix. "from [the result] we drop all preceding 1-bits and the first 0-bit"
  3. Code description. "let \<open>\<rho>(M) \<in> \<Sigma>\<^sup>*\<close> denote a complete description of a TM M in string form".

  Recall the definition of \<^typ>\<open>bin\<close> (see \<^file>\<open>Binary.thy\<close>),
  which causes the MSB to be the \<^const>\<open>last\<close> element of the list,
  which is the \<^emph>\<open>rightmost\<close> one when explicitly referring to lists in Isabelle.\<close>


subsection\<open>Code Description\<close>

type_synonym bin_symbol = "bool option"

type_synonym binTM = "(nat, bin_symbol) wf_TM"

consts bin_TM_enc :: "binTM \<Rightarrow> bin"

specification (bin_TM_enc)
  bin_TM_enc_inj: "inj bin_TM_enc" sorry

definition bin_TM_dec :: "bin \<Rightarrow> binTM" where
  "bin_TM_dec \<equiv> inv bin_TM_enc"

lemma bin_TM_enc_inv: "bin_TM_dec (bin_TM_enc M) = M"
  unfolding bin_TM_dec_def using bin_TM_enc_inj by simp


text\<open>Instantiate the \<^const>\<open>Rej_TM.Rejecting_TM\<close> for \<^typ>\<open>binTM\<close> for the requirement of
 "every string over \<open>{0, 1}\<^sup>*\<close> represents some TM (easy to assure by executing
  an invalid code as a canonic TM that instantly halts and rejects its input)".\<close>

interpretation bin_Rej_TM: Rej_TM "{}::bin_symbol set" "0::nat"
  by (rule Rej_TM.intro) (fact finite.emptyI)

abbreviation "bin_rejM \<equiv> bin_Rej_TM.Rejecting_TM"

lemma bin_rejM_simps: "bin_rejM = \<lparr>
    tape_count = 1,
    states = {0},
    start_state = 0,
    final_states = {0},
    accepting_states = {},
    symbols = {blank_class.Bk},
    next_state = \<lambda>q w. 0,
    next_action = \<lambda>q w. [TM.action.Nop]
  \<rparr>" by simp

text\<open>The function that assigns a word to every TM, represented as \<open>\<rho>(M)\<close> in the paper.\<close>

abbreviation "TM_encode \<equiv> bin_TM_enc"

definition is_encoded_TM :: "word \<Rightarrow> bool"
  where "is_encoded_TM w = (\<exists>M. w = TM_encode M)"

definition TM_decode :: "word \<Rightarrow> binTM"
  where "TM_decode w = (if is_encoded_TM w then bin_TM_dec w else bin_rejM)"


lemma codec_TM: "TM M \<Longrightarrow> TM_decode (TM_encode M) = M"
proof -
  assume "TM M"
  have "is_encoded_TM (TM_encode M)" unfolding is_encoded_TM_def by fast
  then have "TM_decode (TM_encode M) = filter_wf_TMs M"
    unfolding TM_decode_def bin_TM_enc_inv[OF \<open>TM M\<close>] by (fact if_P)
  also have "... = M" unfolding filter_wf_TMs_def using \<open>TM M\<close> by (fact if_P)
  finally show ?thesis .
qed

lemma decode_TM_wf: "TM (TM_decode w)" unfolding TM_decode_def filter_wf_TMs_def
  using bin_Rej_TM.TM_axioms by presburger


subsubsection\<open>Exponential Padding\<close>

definition add_exp_pad :: "word \<Rightarrow> word"
  where [simp]: "add_exp_pad w = (let l = length w in False \<up> (2^l - l) @ w)"

definition strip_exp_pad :: "word \<Rightarrow> word"
  where [simp]: "strip_exp_pad w = (let l = length w in drop (l - clog l) w)"


lemma exp_pad_Nil: "strip_exp_pad [] = []" by force

lemma exp_pad_correct[simp]: "w \<noteq> [] \<Longrightarrow> strip_exp_pad (add_exp_pad w) = w"
proof -
  let ?l = "length w"
  let ?pad = "False \<up> (2 ^ ?l - ?l)"
  let ?wp = "?pad @ w"

  assume "w \<noteq> []"
  then have "?l > 0" ..
  then have l_clog: "clog (2 ^ ?l) = ?l" by (intro clog_exp)

  have len_pad: "length ?pad = 2 ^ ?l - ?l" by simp
  have len_wp: "length ?wp = 2^?l" unfolding length_append len_pad by simp

  have *: "length ?wp - clog (length ?wp) = length ?pad" unfolding len_wp l_clog len_pad ..
  show "strip_exp_pad (add_exp_pad w) = w"
    unfolding add_exp_pad_def strip_exp_pad_def Let_def * by force
qed

lemma exp_pad_suffix: "suffix w (add_exp_pad w)"
  unfolding add_exp_pad_def Let_def by (intro suffixI, unfold append_same_eq, rule)

lemma add_exp_pad_len: "length (add_exp_pad w) = 2 ^ length w" by (simp add: Let_def)

lemma drop_diff_length: "n \<le> length xs \<Longrightarrow> length (drop (length xs - n) xs) = n" by simp

lemma strip_exp_pad_len:
  assumes "w \<noteq> []"
  defines "l \<equiv> length w"
  shows "length (strip_exp_pad w) = clog l"
proof -
  from \<open>w \<noteq> []\<close> have "l > 0" unfolding l_def ..
  with clog_le have "clog l \<le> l" .

  have "length (strip_exp_pad w) = l - (l - clog l)"
    unfolding strip_exp_pad_def l_def[symmetric] Let_def length_drop ..
  also have "... = clog l" using \<open>clog l \<le> l\<close> by (rule diff_diff_cancel)
  finally show ?thesis .
qed


subsubsection\<open>Arbitrary-length \<open>1\<^sup>+0\<close> prefix\<close>

definition add_al_prefix :: "word \<Rightarrow> word" where
  "add_al_prefix w = w @ [False, True]"

definition has_al_prefix :: "word \<Rightarrow> bool"
  where "has_al_prefix w = (\<exists>n>0. \<exists>w'. w = w' @ [False] @ True \<up> n)"

definition strip_al_prefix :: "word \<Rightarrow> word"
  where "strip_al_prefix w = rev (drop 1 (dropWhile (\<lambda>b. b = True) (rev w)))"

lemmas alp_simps[simp] = add_al_prefix_def has_al_prefix_def strip_al_prefix_def

lemma add_alp_min: "add_al_prefix w \<noteq> []"
  and add_alp_correct: "has_al_prefix (add_al_prefix w)"
  and alp_correct: "strip_al_prefix (add_al_prefix w) = w"
  and alp_Nil: "strip_al_prefix [] = []" by force+

lemma replicate_takeWhile: "takeWhile (\<lambda>x. x = a) xs = a \<up> length (takeWhile (\<lambda>x. x = a) xs)"
proof (intro replicate_eqI)
  fix y
  assume "y \<in> set (takeWhile (\<lambda>x. x = a) xs)"
  thus "y = a" by (blast dest: set_takeWhileD conjunct2)
qed rule

lemma replicate_While: "(a \<up> length (takeWhile (\<lambda>x. x = a) xs)) @ dropWhile (\<lambda>x. x = a) xs = xs"
  by (fold replicate_takeWhile) (rule takeWhile_dropWhile_id)

lemma strip_alp_correct1:
  assumes "has_al_prefix w"
  obtains n where "n > 0"
    and "w = strip_al_prefix w @ [False] @ True \<up> n"
proof
  let ?dw = "dropWhile (\<lambda>b. b = True) (rev w)"
  define n where "n \<equiv> length (takeWhile (\<lambda>b. b = True) (rev w))"

  obtain nO wO where "nO > 0" and "w = wO @ [False] @ True \<up> nO"
    using \<open>has_al_prefix w\<close> unfolding has_al_prefix_def by blast
  then have r0: "rev w = True \<up> nO @ False # rev wO" by simp
  moreover from r0 have r1: "rev w = True \<up> nO @ ?dw" by (simp add: dropWhile_append3)
  ultimately have dw_split: "?dw = False # drop 1 ?dw" by simp

  have r2: "rev w = True \<up> n @ ?dw" unfolding n_def replicate_While ..
  also have "... = True \<up> n @ False # drop 1 ?dw" by (fold dw_split) rule
  finally have "w = rev (True \<up> n @ False # drop 1 ?dw)" by (unfold rev_swap)

  also have "... = strip_al_prefix w @ [False] @ True \<up> n" by force
  finally show "w = strip_al_prefix w @ [False] @ True \<up> n" .

  from r1 r2 have "True \<up> nO @ ?dw = True \<up> n @ ?dw" by (rule subst)
  then have "n = nO" unfolding append_same_eq by simp
  then show "n > 0" using \<open>nO > 0\<close> by blast
qed

lemma strip_alp_correct2:
  "prefix (strip_al_prefix w) w" (is "prefix ?w' w")
proof -
  \<comment> \<open>The following definitions are constructed to fit in the following proof;
    their values are not important.\<close>
  define n where "n \<equiv> Suc (length (takeWhile (\<lambda>b. b) (rev w)))"
  define m where "m \<equiv> length (rev w) - n"

  have "?w' = rev (drop n (rev w))" unfolding n_def strip_al_prefix_def dropWhile_eq_drop by force
  also have "... = take m w" unfolding m_def rev_drop rev_rev_ident ..
  finally have "?w' = take m w" . \<comment> \<open>for some \<open>m\<close>\<close>
  show "prefix ?w' w" unfolding \<open>?w' = take m w\<close> by (rule take_is_prefix)
qed

lemma strip_alp_altdef: "strip_al_prefix (w @ False # True \<up> n) = w"
proof -
  let ?T = "(\<lambda>b. b = True)" and ?Tn = "True \<up> n"
  let ?d = "dropWhile ?T (rev (w @ False # ?Tn))"
  have h0: "x \<in> set ?Tn \<Longrightarrow> ?T x" for x by simp

  have "?d = dropWhile ?T (?Tn @ False # rev w)" by simp
  also have "... = dropWhile ?T (False # rev w)" using h0 by (rule dropWhile_append2)
  also have "... = False # rev w" by simp
  finally have h1: "drop 1 ?d = rev w" by (rule forw_subst) force
  show "strip_al_prefix (w @ False # True \<up> n) = w"
    unfolding strip_al_prefix_def h1 by (rule rev_rev_ident)
qed


subsubsection\<open>Assembling components\<close>

definition TM_encode_pad :: "binTM \<Rightarrow> word"
  where "TM_encode_pad M = add_exp_pad (add_al_prefix (TM_encode M))"

definition TM_decode_pad :: "word \<Rightarrow> binTM"
  where "TM_decode_pad w = TM_decode (strip_al_prefix (strip_exp_pad w))"

lemma TM_codec: "TM M \<Longrightarrow> TM_decode_pad (TM_encode_pad M) = M"
  unfolding TM_decode_pad_def TM_encode_pad_def using add_alp_min
  by (subst exp_pad_correct, unfold alp_correct codec_TM, blast+)

lemma wf_TM_has_enc: "TM M \<Longrightarrow> \<exists>w. TM_decode_pad w = M"
  using TM_codec by blast


subsubsection\<open>Proving required properties\<close>

text\<open>from ch. 3.1:
  "The encoding that we will use [...] will have the following properties:

  1. every string over \<open>{0, 1}\<^sup>*\<close> represents some TM [...],\<close>

theorem TM_decode_pad_wf: "TM (TM_decode_pad w)"
  unfolding TM_decode_pad_def by (rule decode_TM_wf)


text\<open>2. every TM is represented by infinitely many strings. [...]"\<close>

theorem TM_inf_encs: "TM M \<Longrightarrow> infinite {w. TM_decode_pad w = M}"
proof (intro infinite_lists allI bexI CollectI)
  \<comment> \<open>Proof follows the structure of @{thm infinite_lists}:
    For every \<open>l \<in> \<nat>\<close> there exists a word \<open>w\<close> with \<open>length w \<ge> l\<close> that is also in the set.\<close>
  assume "TM M"
  fix l
  define w' where w': "w' = (TM_encode M) @ False # True \<up> l"
  define w where w: "w = add_exp_pad w'"

  show "l \<le> length w" unfolding w w' by force

  have "TM_decode_pad w = TM_decode (strip_al_prefix w')" unfolding w w' TM_decode_pad_def
    by (subst exp_pad_correct) blast+
  also have "... = TM_decode (TM_encode M)" unfolding w' strip_alp_altdef ..
  also have "... = M" using \<open>TM M\<close> by (rule codec_TM)
  finally show "TM_decode_pad w = M" .
qed


text\<open>from ch. 4.2:
  "[The encoding] assures several properties [...]:

  1. [...] an arbitrary word \<open>w'\<close> encoding a TM has at least
             \<open>2^(ℓ - \<lceil>log ℓ\<rceil>) \<ge> 2^(ℓ - (log ℓ) - 1)\<close>      (7)
     equivalents \<open>w\<close> in the set \<open>{0, 1}\<^sup>ℓ\<close> that map to \<open>w'\<close>.
     Thus, if a TM \<open>M\<close> is encoded within \<open>ℓ\<close> bits, then (7) counts
     how many equivalent codes for \<open>M\<close> are found at least in \<open>{0, 1}\<^sup>ℓ\<close>.\<close>

theorem num_equivalent_encodings:
  fixes M w
  defines "l \<equiv> length w"
  assumes "l > 0"
    and "TM_decode_pad w = M"
  shows "2^(l - clog l) \<le> card {w. length w = l \<and> TM_decode_pad w = M}" (is "?lhs \<le> card ?A")
proof -
  from \<open>l > 0\<close> have "w \<noteq> []" unfolding l_def ..
  from \<open>l > 0\<close> have "clog l \<le> l" by (rule clog_le)

  define w' where "w' \<equiv> strip_exp_pad w"
  have lw': "length w' = clog l" unfolding w'_def l_def using \<open>w \<noteq> []\<close> by (rule strip_exp_pad_len)

  have "?lhs = card {pad::bin. length pad = l - clog l}" using card_bin_len_eq ..
  also have "... = card ((\<lambda>pad. pad @ w') ` {pad. length pad = l - clog l})"
    using card_image[symmetric] inj_imp_inj_on inj_append_L .
  also have "... = card {pad @ w' | pad. length pad = l - clog l}"
    by (intro arg_cong[where f=card]) (rule image_Collect)
  also have "... \<le> card {w. length w = l \<and> TM_decode_pad w = M}"
  proof (intro card_mono)
    show "finite {w. length w = l \<and> TM_decode_pad w = M}" using finite_bin_len_eq by simp
    show "{pad @ w' | pad. length pad = l - clog l} \<subseteq> {w. length w = l \<and> TM_decode_pad w = M}"
    proof safe
      fix pad::bin
      assume lp: "length pad = l - clog l"
      show lpw': "length (pad @ w') = l" unfolding length_append lp lw'
        using \<open>clog l \<le> l\<close> by (rule le_add_diff_inverse2)

      have h1: "drop (l - clog l) pad = []" using lp by (intro drop_all) (rule eq_imp_le)
      have h2: "l - clog l - length pad = 0" unfolding lp by simp
      have h3: "drop (l - clog l) (pad @ w') = w'" unfolding drop_append h1 h2 by simp
      show "TM_decode_pad (pad @ w') = M" unfolding TM_decode_pad_def strip_exp_pad_def
        unfolding lpw' Let_def h3 unfolding w'_def
        using \<open>TM_decode_pad w = M\<close> by (fold TM_decode_pad_def)
    qed
  qed
  finally show ?thesis .
qed


text\<open>2. The retraction of preceding 1-bits creates the needed infinitude of
        equivalent encodings of every possible TM \<open>M\<close>, as \<^emph>\<open>we can embed any code \<open>\<rho>(M)\<close>
        in a word of length \<open>ℓ\<close> for which \<open>log(ℓ) > len (\<rho>(M))\<close>.\<close>
        We will need this to prove the hierarchy theorem in Section 4.3.\<close>

theorem embed_TM_in_len:
  fixes M l
  assumes "TM M"
    and min_word_len: "clog l \<ge> length (TM_encode M) + 2"
    \<comment> \<open>The \<open>+2\<close> bits are required for the \<open>1\<^sup>+0\<close>-prefix.
        Note: this theorem technically also holds when the assumption @{thm min_word_len} reads
        \<^term>\<open>clog l > length (TM_encode M) \<longleftrightarrow> clog l \<ge> length (TM_encode M) + 1\<close>,
        but only due to \<^const>\<open>strip_al_prefix\<close> allowing the absence of preceding ones.
        If it were to enforce the constraint of a correct \<open>1\<^sup>+0\<close>-prefix,
        this would no longer be the case.
        Additionally, in the stronger version allows the case of \<^term>\<open>l = 0\<close>,
        so \<^term>\<open>l > 0\<close> would have to be added to the assumption.\<close>
  obtains w
  where "length w = l"
    and "TM_decode_pad w = M"
proof
  have "l > 0" by (rule ccontr) (use min_word_len in force)
  hence "clog l \<le> l" by (rule clog_le)

  let ?\<rho>M = "TM_encode M" let ?l\<rho> = "length ?\<rho>M"
  define al_prefix where "al_prefix \<equiv> False # True \<up> (clog l - ?l\<rho> - 1)"
  define w' where "w' \<equiv> ?\<rho>M @ al_prefix"
  have w'_correct: "strip_al_prefix w' = ?\<rho>M" unfolding w'_def al_prefix_def strip_alp_altdef ..
  have "length w' = ?l\<rho> + length al_prefix" unfolding w'_def by simp
  also have "... = ?l\<rho> + (clog l - ?l\<rho> - 1) + 1" unfolding add_left_cancel al_prefix_def
    unfolding length_Cons length_replicate by presburger
  also have "... = clog l - 1 + 1" unfolding add_right_cancel using min_word_len
    by (subst diff_commute, intro le_add_diff_inverse) fastforce
  also have "... = clog l" by (intro le_add_diff_inverse2) simp
  finally have w'_len: "length w' = clog l" .

  define exp_pad where "exp_pad \<equiv> False \<up> (l - clog l)"
  define w where "w \<equiv> exp_pad @ w'"
  have exp_len: "length exp_pad = l - clog l" unfolding exp_pad_def by (rule length_replicate)
  have dexp: "drop (l - clog l) exp_pad = []" unfolding exp_pad_def by force

  have "length w = l - clog l + clog l" unfolding w_def length_append
    unfolding exp_pad_def w'_len length_replicate ..
  also have "... = l" using \<open>clog l \<le> l\<close> by (fact le_add_diff_inverse2)
  finally show "length w = l" .

  have w_correct: "strip_exp_pad w = w'" unfolding strip_exp_pad_def \<open>length w = l\<close> Let_def
    unfolding w_def drop_append dexp exp_len by simp

  show "TM_decode_pad w = M" unfolding TM_decode_pad_def w_correct w'_correct
    using \<open>TM M\<close> by (rule codec_TM)
qed


end
