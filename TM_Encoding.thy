section \<open>Encoding TMs as (Binary) Strings\<close>

theory TM_Encoding
  imports Goedel_Numbering "Supplementary/Misc" "Supplementary/UF_Code"
    "Universal_Turing_Machine.UTM" "HOL-Library.Sublist"
begin


text\<open>A Turing Machine (TM) as defined by @{cite xuIsabelleTM2013} is a list of states.
  Each state is a pair of instructions (\<^typ>\<open>instr\<close>),
  the first one executed when a blank cell (\<^term>\<open>Bk\<close>) is read,
  the second one in case of an occupied cell (\<^term>\<open>Oc\<close>).
  A TM is thus a list of instructions, as the pairs are flattened out
  into a list with an even number of elements (see @{cite \<open>ch.~2 and eqn.~1\<close> xuIsabelleTM2013}).
  An instruction is an \<^typ>\<open>action\<close>
  (write symbol (\<^term>\<open>WB\<close>, \<^term>\<open>WO\<close>), move head (\<^term>\<open>L\<close>, \<^term>\<open>R\<close>) or stall (\<^term>\<open>Nop\<close>))
  and a reference to the \<^emph>\<open>next state\<close> (a natural number indicated the position in the list).
  The state with number \<open>0\<close> is reserved as the halting state
  (the first state in the list has the number \<open>1\<close>).\<close>

type_synonym TM = "tprog0"


text\<open>As defined in @{cite \<open>ch.~4.2\<close> rassOwf2017} (outlined in @{cite \<open>ch.~3.1\<close> rassOwf2017})
  the decoding of a TM \<open>M\<close> from a binary word \<open>w\<close> includes:

    \<^item> Exponential padding. ``all but the most significant \<open>\<lceil>log(len(w))\<rceil>\<close> bits are ignored''
    \<^item> Arbitrary-length \<open>1\<^sup>+0\<close> prefix. ``from [the result] we drop all preceding 1-bits and the first 0-bit''
    \<^item> Code description. ``let \<open>\<rho>(M) \<in> \<Sigma>\<^sup>*\<close> denote a complete description of a TM M in string form''.

  Recall the definition of \<^typ>\<open>bin\<close> (see \<^file>\<open>Binary.thy\<close>),
  which causes the MSB to be the \<^const>\<open>last\<close> element of the list,
  which is the \<^emph>\<open>rightmost\<close> one when explicitly referring to lists in Isabelle.\<close>


subsection\<open>Exponential Padding\<close>

definition add_exp_pad :: "word \<Rightarrow> word"
  where "add_exp_pad w = (let l = length w in False \<up> (2^l - l) @ w)"

definition strip_exp_pad :: "word \<Rightarrow> word"
  where "strip_exp_pad w = (let l = length w in drop (l - clog l) w)"

lemmas exp_pad_simps[simp] = add_exp_pad_def strip_exp_pad_def


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
  show "strip_exp_pad (add_exp_pad w) = w" unfolding exp_pad_simps Let_def * by simp
qed

lemma exp_pad_suffix: "suffix w (add_exp_pad w)"
  unfolding add_exp_pad_def Let_def by (intro suffixI, unfold append_same_eq, rule)

lemma add_exp_pad_len: "length (add_exp_pad w) = 2 ^ length w" by simp

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


subsection\<open>Arbitrary-length \<open>1\<^sup>+0\<close> prefix\<close>

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
  "prefix (strip_al_prefix w) w" (is "prefix ?bsw w")
proof -
  \<comment> \<open>The following definitions are constructed to fit in the following proof;
    their values are not important.\<close>
  define n where "n \<equiv> Suc (length (takeWhile (\<lambda>b. b) (rev w)))"
  define m where "m \<equiv> length (rev w) - n"

  have "?bsw = rev (drop n (rev w))" unfolding n_def strip_al_prefix_def dropWhile_eq_drop by force
  also have "... = take m w" unfolding m_def rev_drop rev_rev_ident ..
  finally have "?bsw = take m w" . \<comment> \<open>for some \<open>m\<close>\<close>
  show "prefix ?bsw w" unfolding \<open>?bsw = take m w\<close> by (rule take_is_prefix)
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


subsection\<open>Code Description\<close>

text\<open>For this part, only a short description is given in @{cite \<open>ch.~3.1\<close> rassOwf2017}.
  The somewhat obvious choice is to utilize \<^const>\<open>code\<close>, since it is already defined
  and used as encoding by the universal TM \<^const>\<open>utm\<close> (see @{thm utm_halt_lemma2}).

  This step is also used to implement the following requirement:
  ``every string over \<open>{0, 1}\<^sup>*\<close> represents some TM (easy to assure by executing
  an invalid code as a canonic TM that instantly halts and rejects its input)''\<close>

definition Rejecting_TM :: TM
  where "Rejecting_TM = [(WB, 0), (WB, 0)]"

\<comment> \<open>The proof of correctness for the \<^const>\<open>Rejecting_TM\<close> is found in \<^file>\<open>Complexity.thy\<close>.\<close>

lemma rej_TM_wf: "composable_tm0 Rejecting_TM" unfolding Rejecting_TM_def composable_tm.simps by force



text\<open>An issue of the following definitions is that the existing definition \<^term>\<open>code\<close>
  uses a naive Gödel numbering scheme that includes encoding list items as prime powers,
  where each \<^emph>\<open>next prime\<close> (\<^term>\<open>Np n\<close>) is searched naively starting from \<^term>\<open>Pi n\<close>
  (see \<^const>\<open>godel_code'\<close>, \<^const>\<open>Pi\<close>, and \<^const>\<open>Np\<close>).\<close>

text\<open>The function that assigns a word to every TM, represented as \<open>\<rho>(M)\<close> in the paper.\<close>

definition encode_TM :: "TM \<Rightarrow> word"
  where "encode_TM M = gn_inv (code M)" (* is gn_inv correct here or should it be replaced? *)

\<comment> \<open>The following definitions are placeholders,
  since apparently there is no defined inverse of \<^const>\<open>code\<close>.\<close>

definition is_encoded_TM :: "word \<Rightarrow> bool"
  where "is_encoded_TM w = (\<exists>M. w = encode_TM M)"

definition filter_wf_TMs :: "TM \<Rightarrow> TM" \<comment> \<open>only allow well-formed TMs\<close>
  where "filter_wf_TMs M = (if composable_tm0 M then M else Rejecting_TM)"

definition decode_TM :: "word \<Rightarrow> TM"
  where "decode_TM w =
    (if is_encoded_TM w then filter_wf_TMs (THE M. w = encode_TM M) else Rejecting_TM)"


lemma encode_TM_inj: "inj encode_TM" unfolding encode_TM_def
proof (intro injI)
  fix x y
  assume "gn_inv (code x) = gn_inv (code y)"
  then have "code x = code y" using gn_inv_inj code_gt_0
    by (subst (asm) inj_on_eq_iff[where f=gn_inv]) fast+
  with code_inj show "x = y" by (rule injD)
qed

lemma codec_TM: "composable_tm0 M \<Longrightarrow> decode_TM (encode_TM M) = M" (is "composable_tm0 M \<Longrightarrow> ?lhs = M")
proof -
  assume wf: "composable_tm0 M"
  let ?e = "\<lambda>M. gn_inv (code M)"
  have c: "\<exists>M'. ?e M = ?e M'" by blast
  have "inj ?e" using encode_TM_inj unfolding encode_TM_def .
  with injD have i: "gn_inv (code M) = gn_inv (code M') \<Longrightarrow> M = M'" for M M' .

  have "?lhs = (if \<exists>M'. ?e M = ?e M' then filter_wf_TMs (THE M''. ?e M = ?e M'') else Rejecting_TM)"
    unfolding decode_TM_def encode_TM_def is_encoded_TM_def ..
  also have "... = filter_wf_TMs (THE M''. ?e M = ?e M'')" using c by (rule if_P)
  also have "... = filter_wf_TMs M" by (rule arg_cong[where f=filter_wf_TMs], blast dest: i)
  also have "... = M" unfolding filter_wf_TMs_def using wf by (rule if_P)
  finally show ?thesis .
qed

lemma decode_TM_wf: "composable_tm0 (decode_TM w)" unfolding decode_TM_def filter_wf_TMs_def
  using rej_TM_wf by (cases "is_encoded_TM w", presburger+)


text\<open>There is (exactly) one TM whose encoding is the empty word (\<open>[]::bin\<close>);
  and that is the machine without instructions (\<open>[]::TM\<close>).
  However, since this machine is not well-formed (see \<^const>\<open>composable_tm0\<close>), the following lemma holds.\<close>

lemma decode_TM_Nil: "decode_TM [] = Rejecting_TM"
proof -
  (* this should probably be known to simp *)
  have le1_split: "n \<le> 1 \<Longrightarrow> n = 0 \<or> n = 1" for n::nat by auto

  have gn_inv_iff: "[] = gn_inv n \<longleftrightarrow> n \<le> 1" for n
  proof
    assume "[] = gn_inv n"
    then have "length (gn_inv n) = 0" by force
    then have "bit_length n \<le> 1" unfolding gn_inv_def length_butlast by force

    show "n \<le> 1"
    proof (rule ccontr)
      assume "\<not> n \<le> 1" hence "n \<ge> 2" by force
      have bl2: "2 = bit_length 2" unfolding numerals(2) by simp
      also have "... \<le> bit_length n" using bit_length_mono \<open>n \<ge> 2\<close> ..
      finally show "False" using \<open>bit_length n \<le> 1\<close> by force
    qed
  next
    assume "n \<le> 1"
    with le1_split have "n = 0 \<or> n = 1" .
    then show "[] = gn_inv n" by (elim disjE) simp_all
  qed

  have code_ge_1_iff: "code M \<le> 1 \<longleftrightarrow> code M = 1" for M
    using code_gt_0[of M] by (intro iffI) simp_all

  have "(THE M. [] = encode_TM M) = (THE M. code M = 1)"
    unfolding encode_TM_def gn_inv_iff code_ge_1_iff ..
  also have "(THE M. code M = 1) = (THE M. M = [])" unfolding code_1_iff ..
  finally have The_Nil: "(THE M. [] = encode_TM M) = []" unfolding the_eq_trivial .

  have "is_encoded_TM []" unfolding is_encoded_TM_def encode_TM_def
    using code_Nil by (intro exI[where x="[]"]) simp
  then have "decode_TM [] = filter_wf_TMs []" unfolding decode_TM_def The_Nil by (rule if_P)
  also have "... = Rejecting_TM" unfolding filter_wf_TMs_def composable_tm.simps by simp
  finally show ?thesis .
qed


subsection\<open>Assembling Components\<close>

(* TODO These names are already confusing. Find less ambiguous ones *)

definition TM_encode_pad :: "TM \<Rightarrow> word"
  where "TM_encode_pad M = add_exp_pad (add_al_prefix (encode_TM M))"

definition TM_decode_pad :: "word \<Rightarrow> TM"
  where "TM_decode_pad w = decode_TM (strip_al_prefix (strip_exp_pad w))"

lemma TM_codec: "composable_tm0 M \<Longrightarrow> TM_decode_pad (TM_encode_pad M) = M"
  unfolding TM_decode_pad_def TM_encode_pad_def using add_alp_min
  by (subst exp_pad_correct, unfold alp_correct codec_TM, blast+)

lemma wf_TM_has_enc: "composable_tm0 M \<Longrightarrow> \<exists>w. TM_decode_pad w = M"
  using TM_codec by blast

lemma TM_decode_Nil: "TM_decode_pad [] = Rejecting_TM"
  unfolding TM_decode_pad_def exp_pad_Nil alp_Nil decode_TM_Nil ..


subsection\<open>Properties of the Encoding\<close>

text\<open>From @{cite \<open>ch.~3.1\<close> rassOwf2017}:

  ``The encoding that we will use [...] will have the following properties:

  1. every string over \<open>{0, 1}\<^sup>*\<close> represents some TM [...],''\<close>

theorem TM_decode_pad_wf: "composable_tm0 (TM_decode_pad w)"
  unfolding TM_decode_pad_def by (rule decode_TM_wf)


text\<open>``2. every TM is represented by infinitely many strings. [...]''\<close>

theorem TM_inf_encs: "composable_tm0 M \<Longrightarrow> infinite {w. TM_decode_pad w = M}"
proof (intro infinite_lists allI bexI CollectI)
  assume wf: "composable_tm0 M"
  fix l
  define w' where w': "w' = (encode_TM M) @ False # True \<up> l"
  define w where w: "w = add_exp_pad w'"

  show "l \<le> length w" unfolding w w' by simp

  have "TM_decode_pad w = decode_TM (strip_al_prefix w')" unfolding w w' TM_decode_pad_def
    by (subst exp_pad_correct) blast+
  also have "... = decode_TM (encode_TM M)" unfolding w' strip_alp_altdef ..
  also have "... = M" using \<open>composable_tm0 M\<close> by (rule codec_TM)
  finally show "TM_decode_pad w = M" .
qed


text\<open>From @{cite \<open>ch.~4.2\<close> rassOwf2017}:

  ``[The encoding] assures several properties [...]:

  1. [...] an arbitrary word \<open>w'\<close> encoding a TM has at least
             \<open>2\<^bsup>ℓ - \<lceil>log ℓ\<rceil>\<^esup> \<ge> 2\<^bsup>ℓ - log ℓ - 1\<^esup>\<close>
     equivalents \<open>w\<close> in the set \<open>{0, 1}\<^sup>ℓ\<close> that map to \<open>w'\<close>.
     Thus, if a TM \<open>M\<close> is encoded within \<open>ℓ\<close> bits, then [the above equation] counts
     how many equivalent codes for \<open>M\<close> are found at least in \<open>{0, 1}\<^sup>ℓ\<close>.''\<close>

theorem num_equivalent_encodings:
  fixes M w
  assumes "TM_decode_pad w = M"
  defines "l \<equiv> length w"
  shows "2^(l - clog l) \<le> card {w. length w = l \<and> TM_decode_pad w = M}" (is "?lhs \<le> card ?A")
proof (cases "l > 0")
  case True
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
next
  case False
  then have "l = 0" by blast
  then have "w = []" unfolding l_def ..
  have "M = Rejecting_TM" using \<open>TM_decode_pad w = M\<close> unfolding \<open>w = []\<close> TM_decode_Nil ..

  have "2 ^ (l - clog l) = 1" unfolding \<open>l = 0\<close> by simp
  also have "1 = card {[]::bin}" by simp
  also have "... \<le> card {w. length w = l \<and> TM_decode_pad w = M}" unfolding \<open>l = 0\<close> \<open>M = Rejecting_TM\<close>
  proof (intro card_mono)
    show "finite {w. length w = 0 \<and> TM_decode_pad w = Rejecting_TM}" using finite_bin_len_eq by simp
    show "{[]} \<subseteq> {w. length w = 0 \<and> TM_decode_pad w = Rejecting_TM}" using TM_decode_Nil by simp
  qed
  finally show ?thesis .
qed


text\<open>``2. The retraction of preceding 1-bits creates the needed infinitude of
        equivalent encodings of every possible TM \<open>M\<close>, as \<^emph>\<open>we can embed any code \<open>\<rho>(M)\<close>
        in a word of length \<open>ℓ\<close> for which \<open>log ℓ > len (\<rho>(M))\<close>.\<close>
        We will need this to prove the hierarchy theorem in Section 4.3.''\<close>

theorem embed_TM_in_len:
  fixes M l
  assumes "composable_tm0 M"
    and min_word_len: "clog l \<ge> length (encode_TM M) + 2" \<comment> \<open>The \<open>+2\<close> bits are required for the \<open>1\<^sup>+0\<close>-prefix.

        Note: this theorem technically also holds when the assumption @{thm min_word_len} reads
        \<^term>\<open>clog l > length (encode_TM M) \<longleftrightarrow> clog l \<ge> length (encode_TM M) + 1\<close>,
        but only due to \<^const>\<open>strip_al_prefix\<close> allowing the absence of preceding ones.
        If it were to enforce the constraint of a correct \<open>1\<^sup>+0\<close>-prefix,
        this would no longer be the case.
        Additionally, the weaker version allows the case of \<^term>\<open>l = 0\<close>,
        which requires special treatment (it follows that \<^term>\<open>M = Rejecting_TM\<close>).\<close>
  obtains w
  where "length w = l"
    and "TM_decode_pad w = M"
proof
  have "l > 0"
  proof (rule ccontr)
    assume "\<not> l > 0" hence "l = 0" ..
    from min_word_len show False unfolding \<open>l = 0\<close> by force
  qed
  hence "clog l \<le> l" by (rule clog_le)

  let ?\<rho>M = "encode_TM M" let ?l\<rho> = "length ?\<rho>M"
  define al_prefix where "al_prefix \<equiv> False # True \<up> (clog l - ?l\<rho> - 1)"
  define w' where "w' \<equiv> ?\<rho>M @ al_prefix"
  have w'_correct: "strip_al_prefix w' = ?\<rho>M" unfolding w'_def al_prefix_def strip_alp_altdef ..
  have "length w' = ?l\<rho> + length al_prefix" unfolding w'_def by simp
  also have "... = ?l\<rho> + (clog l - ?l\<rho> - 1) + 1" unfolding add_left_cancel al_prefix_def
    unfolding length_Cons length_replicate by presburger
  also have "... = clog l - 1 + 1" unfolding add_right_cancel using min_word_len
    by (subst diff_commute, intro le_add_diff_inverse) simp
  also have "... = clog l" by (intro le_add_diff_inverse2) simp
  finally have w'_len: "length w' = clog l" .

  define exp_pad where "exp_pad \<equiv> False \<up> (l - clog l)"
  define w where "w \<equiv> exp_pad @ w'"
  have exp_len: "length exp_pad = l - clog l" unfolding exp_pad_def by (rule length_replicate)
  have dexp: "drop (l - clog l) exp_pad = []" unfolding exp_pad_def by force

  have "length w = l - clog l + clog l" unfolding w_def length_append
    unfolding exp_pad_def w'_len length_replicate ..
  also have "... = l" using \<open>clog l \<le> l\<close> by (rule le_add_diff_inverse2)
  finally show "length w = l" .

  have w_correct: "strip_exp_pad w = w'" unfolding strip_exp_pad_def \<open>length w = l\<close> Let_def
    unfolding w_def drop_append dexp exp_len by simp

  show "TM_decode_pad w = M" unfolding TM_decode_pad_def w_correct w'_correct
    using \<open>composable_tm0 M\<close> by (rule codec_TM)
qed


end
