theory TM_Encoding
  imports gn UF_Code
    "Universal_Turing_Machine.UTM" "HOL-Library.Sublist" "HOL-Library.Discrete"
begin


text\<open>A Turing Machine (TM) as defined by Xu et al. [2013] is a list of states.
  Each state is a pair of instructions (\<^typ>\<open>instr\<close>),
  the first one executed when a blank cell (\<^term>\<open>Bk\<close>) is read,
  the second one in case of an occupied cell (\<^term>\<open>Oc\<close>).
  A TM is thus a list of instructions, as the pairs are flattened out
  into a list with an even number of elements (see ibid. ch. 2 and eqn. (1)).
  An instruction is an \<^typ>\<open>action\<close>
  (write symbol (\<^term>\<open>W0\<close>, \<^term>\<open>W1\<close>), move head (\<^term>\<open>L\<close>, \<^term>\<open>R\<close>) or stall (\<^term>\<open>Nop\<close>))
  and a reference to the "next state" (a natural number indicated the position in the list).
  The state with number \<open>0\<close> is reserved as the halting state
  (the first state in the list has the number \<open>1\<close>).\<close>
type_synonym TM = "tprog0"


subsection\<open>Encoding TMs\<close>

\<comment> \<open>An issue of the following definitions is that the existing definition \<^term>\<open>code\<close>
  uses a naive Gödel numbering scheme that includes encoding list items as prime powers,
  where each "next prime" \<^term>\<open>Np n\<close> is searched naively starting from \<^term>\<open>Pi n\<close>
  (see \<^term>\<open>godel_code'\<close>, \<^term>\<open>Pi\<close>, and \<^term>\<open>Np\<close>).\<close>

\<comment> \<open>Reminder: For binary numbers, as stated in the paper (ch. 1, p. 2),
  the "least significant bit is located at the right end".
  The recursive definitions for words result in somewhat unintuitive definitions here:
  The number 6 is 110 in binary, but as \<^typ>\<open>word\<close> it is \<^term>\<open>num.Bit0 (num.Bit1 num.One)\<close>.
  Similarly, as \<^typ>\<open>bin\<close> (synonym for \<^typ>\<open>bool list\<close>), 6 is \<^term>\<open>[False, True]\<close>.\<close>

value "nat_of_num (num.Bit0 (num.Bit1 num.One))"
value "nat_of_num (word_of_bin ([False, True]))"

text\<open>As defined in the paper (ch 4.2, p. 11f, outlined in ch. 3.1, p. 8)
  the decoding of a TM \<open>M\<close> from a binary word \<open>w\<close> includes:

  1. Exponential padding. "all but the most significant \<open>\<lceil>log(len(w))\<rceil>\<close> bits are ignored"
  2. Arbitrary-length \<open>1\<^sup>+0\<close> prefix. "from [the result] we drop all preceding 1-bits and the first 0-bit"
  3. Code description. "let \<open>\<rho>(M) \<in> \<Sigma>\<^sup>*\<close> denote a complete description of a TM M in string form".\<close>

subsubsection\<open>Discrete ceiling log\<close>
abbreviation clog :: "nat \<Rightarrow> nat"
  where "clog n \<equiv> Discrete.log (n-1) + 1"

lemma clog_exp: "0 < n \<Longrightarrow> clog (2^n) = n"
proof (induction n rule: nat_induct_non_zero)
  case (Suc n)
  then show ?case using Discrete.log.simps by fastforce
qed simp

lemma dlog_altdef: "1 \<le> n \<Longrightarrow> Discrete.log n = nat \<lfloor>log 2 n\<rfloor>"
  using log_altdef by simp

lemma nat_strict_mono_greatest:
  fixes f::"nat \<Rightarrow> nat" and N::nat
  assumes "strict_mono f" "f 0 \<le> N"
  obtains n where "f n \<le> N" and "\<forall>m. f m \<le> N \<longrightarrow> m \<le> n"
proof -
  define M where "M \<equiv> {m. f m \<le> N}"
  define n where "n = Max M"

  from \<open>strict_mono f\<close> have "\<And>n. n \<le> f n" by (rule strict_mono_imp_increasing)
  hence "finite M" using M_def finite_less_ub by simp
  moreover from M_def \<open>f 0 \<le> N\<close> have "M \<noteq> {}" by auto
  ultimately have "n \<in> M" unfolding n_def using Max_in[of M] by simp

  then have "f n \<le> N" using n_def M_def by simp
  moreover have "\<forall>m. f m \<le> N \<longrightarrow> m \<le> n"
    using Max_ge \<open>finite M\<close> n_def M_def by blast
  ultimately show thesis using that by simp
qed

lemma power_two_decompose:
  fixes n::nat
  assumes "1 \<le> n"
  obtains k m::nat
  where "n = 2^k + m" and "m < 2^k"
proof -
  have "strict_mono (\<lambda>k. (2::nat)^k)" by (intro strict_monoI) simp
  then obtain k where "2^k \<le> n" and *:"\<forall>k'. 2^k' \<le> n \<longrightarrow> k' \<le> k"
    using assms nat_strict_mono_greatest[of "\<lambda>k. 2^k" n] by auto

  define m where "m \<equiv> n - 2^k"

  have "n = 2^k + m" using m_def \<open>2^k \<le> n\<close> by simp

  moreover have "m < 2^k" proof (rule ccontr)
    assume "\<not> m < 2^k"
    hence "2^(k+1) \<le> n" using m_def by simp
    thus False using * by fastforce
  qed

  ultimately show thesis using that by simp
qed

lemma log_eq1:
  fixes k m::nat
  assumes "0 \<le> m" "m < 2^k"
  shows "Discrete.log (2^k + m) = k"
  using assms log_eqI by force

lemma log_eq2:
  fixes k m::nat
  assumes "1 \<le> m" "m < 2^k"
  shows "nat \<lceil>log 2 (2^k + m)\<rceil> = k + 1"
proof -
  let ?n = "2^k+m"
  have "k < log 2 ?n"
    using assms less_log2_of_power[of k ?n] by simp
  moreover have "log 2 ?n \<le> k+1"
    using assms log2_of_power_le[of ?n "k+1"] by simp
  ultimately show ?thesis by linarith
qed

lemma log_altdef_ceil:
  assumes "2 \<le> (n::nat)"
  shows "clog n = nat \<lceil>log 2 n\<rceil>"
proof -
  from assms have "1 \<le> n" by simp
  with power_two_decompose obtain k m where km_def: "n = 2^k + m" "m < 2^k" .
  have "1 + nat \<lfloor>log 2 (n-1)\<rfloor> = nat \<lceil>log 2 n\<rceil>" proof (cases "m = 0")
    case True
    then have k_def: "n = 2^k" using \<open>n = 2^k + m\<close> by simp
    then have "nat \<lfloor>log 2 (n-1)\<rfloor> = k - 1"
      using dlog_altdef[of "n-1"] clog_exp[of k] assms by fastforce
    moreover have "nat \<lceil>log 2 n\<rceil> = k" using k_def by simp
    moreover have \<open>1 \<le> k\<close> using assms k_def
      by (smt (z3) One_nat_def int_zle_neg not_le not_less_eq numerals(2) of_nat_0_less_iff power_0)
    ultimately show ?thesis by simp
  next
    case False
    then have \<open>1\<le>m\<close> by simp
    have "nat \<lfloor>log 2 (n-1)\<rfloor> = k"
      using km_def \<open>1\<le>m\<close> log_eq1[of "m-1" k] dlog_altdef[of "n-1"] assms by simp
    moreover have "nat \<lceil>log 2 n\<rceil> = 1 + k"
      using km_def \<open>1\<le>m\<close> log_eq2 by simp
    ultimately show ?thesis by simp
  qed
  then show ?thesis using assms dlog_altdef by simp
qed

subsubsection\<open>Exponential Padding\<close>

definition add_exp_pad :: "word \<Rightarrow> word"
  where "add_exp_pad w = (let b = bin_of_word w; l = length b in word_of_bin (
      False \<up> (2^l - l) @ b
    ))"

definition strip_exp_pad :: "word \<Rightarrow> word"
  where "strip_exp_pad w = (let b = bin_of_word w; l = length b in word_of_bin (
      drop (l - clog l) b
  ))"

lemma exp_pad_Nil: "strip_exp_pad num.One = num.One"
  unfolding strip_exp_pad_def bin_of_word.simps Let_def by simp

lemmas exp_pad_simps = add_exp_pad_def strip_exp_pad_def

lemma exp_pad_correct[simp]: "w \<noteq> num.One \<Longrightarrow> strip_exp_pad (add_exp_pad w) = w"
proof -
  let ?w = "bin_of_word w"
  let ?l = "length ?w"
  let ?pad = "False \<up> (2 ^ ?l - ?l)"
  let ?wp = "?pad @ ?w"

  assume "w \<noteq> num.One"
  with len_gt_0 have "?l > 0" unfolding word_len_eq_bin_len .
  then have l_clog: "clog (2^?l) = ?l" by (intro clog_exp)

  have len_pad: "length ?pad = 2 ^ ?l - ?l" by simp
  have len_wp: "length ?wp = 2^?l" unfolding length_append len_pad by simp

  have *: "length ?wp - clog (length ?wp) = length ?pad" unfolding len_wp l_clog len_pad ..
  show "strip_exp_pad (add_exp_pad w) = w"
    unfolding exp_pad_simps Let_def bin_word_bin_id * by simp
qed

lemma exp_pad_suffix:
  fixes w
  defines "b \<equiv> bin_of_word w"
    and "b_pad \<equiv> bin_of_word (add_exp_pad w)"
  shows "suffix b b_pad"
  unfolding assms add_exp_pad_def Let_def bin_word_bin_id
  by (intro suffixI, unfold append_same_eq, rule)

lemma add_exp_pad_len: "len (add_exp_pad w) = 2 ^ len w"
  unfolding word_len_eq_bin_len add_exp_pad_def Let_def by simp

lemma drop_diff_length: "n \<le> length xs \<Longrightarrow> length (drop (length xs - n) xs) = n" by simp

lemma log_less: "n > 0 \<Longrightarrow> Discrete.log n < n" (* complements "HOL-Library.Discrete" *)
proof -
  assume "n > 0"
  have "Discrete.log n < 2 ^ Discrete.log n" by (rule less_exp)
  also have "... \<le> n" using \<open>n > 0\<close> by (rule log_exp2_le)
  finally show ?thesis .
qed

lemma log_le: "Discrete.log n \<le> n" (* complements "HOL-Library.Discrete" *)
proof (cases "n > 0")
  assume "n > 0"
  with log_less show ?thesis by (intro less_imp_le)
qed (* case "n = 0" by *) simp

lemma strip_exp_pad_altdef: "strip_exp_pad w = (let l = len w in
      word_of_bin (drop (l - clog l) (bin_of_word w)))"
  unfolding strip_exp_pad_def Let_def word_len_eq_bin_len ..

lemma strip_exp_pad_len:
  assumes "w \<noteq> num.One"
  defines "l \<equiv> len w"
  shows "len (strip_exp_pad w) = clog (len w)"
  unfolding word_len_eq_bin_len strip_exp_pad_def Let_def bin_word_bin_id
proof (intro drop_diff_length, fold word_len_eq_bin_len l_def)
  have "l > 0" unfolding l_def using \<open>w \<noteq> num.One\<close> by (rule len_gt_0)
  have "Discrete.log (l-1) \<le> l-1" by (rule log_le)
  then have "clog l \<le> l-1 + 1" by (unfold add_le_cancel_right)
  also have "... = l" using \<open>l > 0\<close> by simp
  finally show "clog l \<le> l" . (* this is clog_le... *)
qed

subsubsection\<open>Arbitrary-length \<open>1\<^sup>+0\<close> prefix\<close>

fun add_al_prefix :: "word \<Rightarrow> word" where
  "add_al_prefix num.One = num.Bit0 (num.Bit1 num.One)"
| "add_al_prefix (num.Bit0 w) = num.Bit0 (add_al_prefix w)"
| "add_al_prefix (num.Bit1 w) = num.Bit1 (add_al_prefix w)"

definition has_al_prefix :: "word \<Rightarrow> bool"
  where "has_al_prefix w = (\<exists>n>0. \<exists>w'. bin_of_word w = w' @ [False] @ True \<up> n)"

definition strip_al_prefix :: "word \<Rightarrow> word" where
  "strip_al_prefix w = word_of_bin (rev (drop 1 (dropWhile (\<lambda>b. b = True) (rev (bin_of_word w)))))"

lemmas al_prefix_simps = add_al_prefix.simps has_al_prefix_def strip_al_prefix_def

lemma add_alp_min: "add_al_prefix w \<noteq> num.One" by (induction w) simp_all

lemma add_alp_altdef: "add_al_prefix w = word_of_bin (bin_of_word w @ [False, True])"
  by (induction w) simp_all

lemma add_alp_correct: "has_al_prefix (add_al_prefix w)" unfolding has_al_prefix_def
proof (intro exI conjI)
  show "0 < Suc 0" ..
  show "bin_of_word (add_al_prefix w) = (bin_of_word w) @ [False] @ True \<up> (Suc 0)"
    unfolding add_alp_altdef by simp
qed

lemma alp_correct: "strip_al_prefix (add_al_prefix w) = w"
  unfolding strip_al_prefix_def add_alp_altdef by simp

lemma alp_Nil: "strip_al_prefix num.One = num.One" unfolding strip_al_prefix_def by simp

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
    and "bin_of_word w = bin_of_word (strip_al_prefix w) @ [False] @ True \<up> n"
proof
  let ?w = "bin_of_word w"
  let ?dw = "dropWhile (\<lambda>b. b = True) (rev ?w)"
  define n where "n \<equiv> length (takeWhile (\<lambda>b. b = True) (rev ?w))"

  have *: "bin_of_word (strip_al_prefix w) = rev (drop 1 ?dw)"
    unfolding strip_al_prefix_def rev_rev_ident bin_word_bin_id ..

  obtain nO wO where "nO > 0" and "?w = wO @ [False] @ True \<up> nO"
    using \<open>has_al_prefix w\<close> unfolding has_al_prefix_def by blast
  then have r0: "rev ?w = True \<up> nO @ False # rev wO" by simp
  moreover from r0 have r1: "rev ?w = True \<up> nO @ ?dw" by (simp add: dropWhile_append3)
  ultimately have dw_split: "?dw = False # drop 1 ?dw" by simp

  have r2: "rev ?w = True \<up> n @ ?dw" unfolding n_def replicate_While ..
  also have "... = True \<up> n @ False # drop 1 ?dw" by (fold dw_split) rule
  finally have "?w = rev (True \<up> n @ False # drop 1 ?dw)" by (unfold rev_swap)

  also have "... = rev (drop 1 ?dw) @ [False] @ True \<up> n" by simp
  finally show "?w = bin_of_word (strip_al_prefix w) @ [False] @ True \<up> n" unfolding * .

  from r1 r2 have "True \<up> nO @ ?dw = True \<up> n @ ?dw" by (rule subst)
  then have "n = nO" unfolding append_same_eq by simp
  then show "n > 0" using \<open>nO > 0\<close> by blast
qed

lemma strip_alp_correct2:
  "prefix (bin_of_word (strip_al_prefix w)) (bin_of_word w)" (is "prefix ?bsw ?w")
proof -
  \<comment> \<open>The following definitions are constructed to fit in the following proof;
    their values are not important.\<close>
  define n where "n \<equiv> Suc (length (takeWhile (\<lambda>b. b) (rev ?w)))"
  define m where "m \<equiv> length (rev ?w) - n"

  have "bin_of_word (strip_al_prefix w) = rev (drop n (rev ?w))"
    unfolding n_def strip_al_prefix_def bin_word_bin_id dropWhile_eq_drop by simp
  also have "... = take m ?w" unfolding m_def rev_drop rev_rev_ident ..
  finally have "?bsw = take m ?w" . \<comment> \<open>for some \<open>m\<close>\<close>
  show "prefix ?bsw ?w" unfolding \<open>?bsw = take m ?w\<close> by (rule take_is_prefix)
qed

lemma strip_alp_altdef: "strip_al_prefix (word_of_bin (bin_of_word w @ False # True \<up> n)) = w"
proof -
  let ?b = bin_of_word and ?w = word_of_bin and ?T = "(\<lambda>b. b = True)" and ?Tn = "True \<up> n"
  let ?a1 = "rev (?b w)" and ?a = "False # rev (?b w)"
    and ?d = "dropWhile ?T (rev (?b w @ False # ?Tn))"

  thm dropWhile_append2
  have h0: "x \<in> set ?Tn \<Longrightarrow> ?T x" for x by simp

  have "?d = dropWhile ?T (?Tn @ ?a)" by simp
  also from h0 have "dropWhile ?T (?Tn @ ?a) = dropWhile ?T ?a" by (rule dropWhile_append2)
  also have "dropWhile ?T ?a = ?a" by simp
  finally have h1: "drop 1 ?d = ?a1" by simp
  then have h2: "rev (drop 1 ?d) = ?b w" unfolding h1 by simp

  show "strip_al_prefix (?w (?b w @ False # True \<up> n)) = w"
    unfolding strip_al_prefix_def bin_word_bin_id word_bin_word_id h2 ..
qed

subsubsection\<open>Code Description\<close>

text\<open>For this part, only a short description is given in ch. 3.1.
  The somewhat obvious choice is to utilize \<^term>\<open>code\<close>, since it is already defined
  and used as encoding by the universal TM \<^term>\<open>UTM\<close> (see @{thm UTM_halt_lemma2}).

  This step is also used to implement the following requirement:
  "every string over \<open>{0, 1}\<^sup>*\<close> represents some TM (easy to assure by executing
  an invalid code as a canonic TM that instantly halts and rejects its input)"\<close>

definition Rejecting_TM :: TM
  where "Rejecting_TM = [(W0, 0), (W0, 0)]"

\<comment> \<open>The proof of correctness for the \<^const>\<open>Rejecting_TM\<close> is found in \<^file>\<open>complexity.thy\<close>.\<close>

lemma rej_TM_wf: "tm_wf0 Rejecting_TM" unfolding Rejecting_TM_def tm_wf.simps by force


text\<open>The function that assigns a word to every TM, represented as \<open>\<rho>(M)\<close> in the paper.\<close>
definition encode_TM :: "TM \<Rightarrow> word"
  where "encode_TM M = gn_inv (code M)"

\<comment> \<open>The following definitions are placeholders,
  since apparently there is no defined inverse of \<^term>\<open>code\<close>.\<close>

definition is_encoded_TM :: "word \<Rightarrow> bool"
  where "is_encoded_TM w = (\<exists>M. w = encode_TM M)"

definition filter_wf_TMs :: "TM \<Rightarrow> TM" \<comment> \<open>only allow well-formed TMs\<close>
  where "filter_wf_TMs M = (if tm_wf0 M then M else Rejecting_TM)"

definition decode_TM :: "word \<Rightarrow> TM"
  where "decode_TM w =
    (if is_encoded_TM w then filter_wf_TMs (THE M. w = encode_TM M) else Rejecting_TM)"

lemma encode_TM_inj: "inj encode_TM"
  unfolding encode_TM_def using gn_inv_inj code_inj godel_code_great
  by (metis (mono_tags, lifting) code.elims injD injI inv_gn_id is_gn_def)

lemma codec_TM: "tm_wf0 M \<Longrightarrow> decode_TM (encode_TM M) = M" (is "tm_wf0 M \<Longrightarrow> ?lhs = M")
proof -
  assume wf: "tm_wf0 M"
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

lemma decode_TM_wf: "tm_wf0 (decode_TM w)" unfolding decode_TM_def filter_wf_TMs_def
  using rej_TM_wf by (cases "is_encoded_TM w", presburger+)

lemma decode_TM_Nil: "decode_TM num.One = Rejecting_TM"
proof -
  \<comment> \<open>There is (exactly) one TM whose encoding is \<^term>\<open>num.One\<close>,
    which is \<^term>\<open>[]::TM\<close>, the machine without instructions.
    Since this machine is not well-formed (see \<^term>\<open>tm_wf0\<close>), however, this lemma holds.\<close>

  (* this should probably be known to simp *)
  have le1_split: "n \<le> 1 \<Longrightarrow> n = 0 \<or> n = 1" for n::nat by auto

  have gn_inv_iff: "num.One = gn_inv n \<longleftrightarrow> n \<le> 1" for n
  proof
    assume "num.One = gn_inv n"
    then show "n \<le> 1" proof (induction n)
      case (Suc n)
      have if_reverse1: "a = (if c then b else d) \<Longrightarrow> a \<noteq> b \<Longrightarrow> \<not> c"
        for a b d :: 'a and c :: bool by argo

      have "num.One \<noteq> Num.inc n" for n by (cases n) simp_all
      with \<open>num.One = gn_inv (Suc n)\<close> have "\<not> 0 < n" unfolding gn_inv_def num_of_nat.simps by (rule if_reverse1)
      then show "Suc n \<le> 1" by simp
    qed (*case "n = 0" by *) simp
  next
    assume "n \<le> 1"
    with le1_split have "n = 0 \<or> n = 1" .
    then show "num.One = gn_inv n" by (elim disjE) simp_all
  qed

  have code_ge_1_iff: "code M \<le> 1 \<longleftrightarrow> code M = 1" for M
    using code_gt_0[of M] by (intro iffI) simp_all

  have "(THE M. num.One = encode_TM M) = (THE M. code M = 1)"
    unfolding encode_TM_def gn_inv_iff code_ge_1_iff ..
  also have "(THE M. code M = 1) = (THE M. M = [])" unfolding code_1_iff ..
  finally have The_Nil: "(THE M. num.One = encode_TM M) = []" unfolding the_eq_trivial .

  have "is_encoded_TM num.One" unfolding is_encoded_TM_def encode_TM_def
    using code_Nil by (intro exI[where x="[]"]) simp
  then have "decode_TM num.One = filter_wf_TMs []" unfolding decode_TM_def The_Nil by (rule if_P)
  also have "... = Rejecting_TM" unfolding filter_wf_TMs_def tm_wf.simps by simp
  finally show ?thesis .
qed


subsubsection\<open>Assembling components\<close>

(* TODO These names are already confusing. Find less ambiguous ones *)

definition TM_encode_pad :: "TM \<Rightarrow> word"
  where "TM_encode_pad M = add_exp_pad (add_al_prefix (encode_TM M))"

definition TM_decode_pad :: "word \<Rightarrow> TM"
  where "TM_decode_pad w = decode_TM (strip_al_prefix (strip_exp_pad w))"

lemma TM_codec: "tm_wf0 M \<Longrightarrow> TM_decode_pad (TM_encode_pad M) = M"
  unfolding TM_decode_pad_def TM_encode_pad_def using add_alp_min
  by (subst exp_pad_correct, unfold alp_correct codec_TM, blast+)

lemma wf_TM_has_enc: "tm_wf0 M \<Longrightarrow> \<exists>w. TM_decode_pad w = M"
  using TM_codec by blast

lemma TM_decode_Nil: "TM_decode_pad num.One = Rejecting_TM"
  unfolding TM_decode_pad_def exp_pad_Nil alp_Nil decode_TM_Nil ..


subsubsection\<open>Proving required properties\<close>

text\<open>from ch. 3.1:
  "The encoding that we will use [...] will have the following properties:

  1. every string over \<open>{0, 1}\<^sup>*\<close> represents some TM [...],\<close>

theorem TM_decode_pad_wf: "tm_wf0 (TM_decode_pad w)"
  unfolding TM_decode_pad_def by (rule decode_TM_wf)


text\<open>2. every TM is represented by infinitely many strings. [...]"\<close>

theorem TM_inf_encs: "tm_wf0 M \<Longrightarrow> infinite {w. TM_decode_pad w = M}"
proof (intro infinite_growing bexI CollectI)
  \<comment> \<open>Proof sketch (see @{thm infinite_growing}}):
    a set over a type with a linorder is infinite if is (a) non-empty
    and (b) for each member x there is a (c) member y for which (d) \<open>x < y\<close>.
    The linorder over \<^typ>\<open>word\<close> (=\<^typ>\<open>num\<close>) is defined
    in terms of \<^typ>\<open>nat\<close> (see @{thm less_num_def}}).\<close>
  assume wf: "tm_wf0 M"
  with wf_TM_has_enc show (*a*) "{w. TM_decode_pad w = M} \<noteq> {}" by blast

  fix x
  assume (*b*) "x \<in> {w. TM_decode_pad w = M}"
  then have "TM_decode_pad x = M" ..

  \<comment> \<open>Constructing the larger word.\<close>
  let ?e = encode_TM and ?b = bin_of_word and ?w = word_of_bin
  define y where "y = add_exp_pad (?w (?b (?e M) @ False # True \<up> len x))"

  \<comment> \<open>The following definitions enable handling large expressions in the next section.\<close>
  define b where "b = ?b (?e M)"
  let ?h = "length (b @ False # True \<up> len x)"
  define a where "a = False \<up> (2 ^ ?h - ?h)"

  have "len x < Suc (len x)" ..
  also have "... = len (num.Bit0 x)" by simp
  also have "... = len (word_of_bin (False # (bin_of_word x)))" by simp
  also have "... = length (False # (bin_of_word x))" unfolding word_len_eq_bin_len by simp
  also have "... = length (False # True \<up> len x)" unfolding word_len_eq_bin_len by simp
  also have "... \<le> length (a @ b @ False # True \<up> len x)" by simp
  also have "... = len y" unfolding y_def add_exp_pad_def bin_word_bin_id Let_def word_len_eq_bin_len'
    unfolding a_def b_def ..
  finally have "len x < len y" .
  then have "nat_of_num x < nat_of_num y" by (rule num_of_nat_lengths)
  then show (*d*) "x < y" unfolding less_num_def .

  have "strip_al_prefix (?w (?b (?e M) @ False # True \<up> len x)) = ?w (?b (?e M))"
    unfolding strip_alp_altdef by simp

  have "TM_decode_pad y = decode_TM (strip_al_prefix (?w (?b (?e M) @ False # True \<up> len x)))"
    unfolding y_def TM_decode_pad_def
  proof (subst exp_pad_correct)
    have "length (?b (?e M) @ False # True \<up> len x) > 0" by simp
    then have "len (?w (?b (?e M) @ False # True \<up> len x)) > 0" by (unfold word_len_eq_bin_len')
    then show "?w (?b (?e M) @ False # True \<up> len x) \<noteq> num.One" by fastforce
  qed rule
  also have "... = decode_TM (encode_TM M)" unfolding strip_alp_altdef ..
  also have "... = M" using wf by (rule codec_TM)
  finally show (*c*) "TM_decode_pad y = M" .
qed


text\<open>from ch. 4.2:
  "[The encoding] assures several properties [...]:

  1. [...] an arbitrary word \<open>w'\<close> encoding a TM has at least
             \<open>2^(ℓ - \<lceil>log ℓ\<rceil>) \<ge> 2^(ℓ - (log ℓ) - 1)\<close>      (7)
     equivalents \<open>w\<close> in the set \<open>{0, 1}\<^sup>ℓ\<close> that map to \<open>w'\<close>.
     Thus, if a TM \<open>M\<close> is encoded within \<open>ℓ\<close> bits, then (7) counts
     how many equivalent codes for \<open>M\<close> are found at least in \<open>{0, 1}\<^sup>ℓ\<close>.\<close>

lemma inj_imp_inj_on: "inj f \<Longrightarrow> inj_on f A" by (simp add: inj_on_def)

lemma card_bin_len_eq: "card {w::bin. length w = l} = 2 ^ l"
proof -
  let ?bools = "UNIV :: bool set"
  have "card {w::bin. length w = l} = card {w. set w \<subseteq> ?bools \<and> length w = l}" by simp
  also have "... = card ?bools ^ l" by (intro card_lists_length_eq) (rule finite)
  also have "... = 2 ^ l" unfolding card_UNIV_bool ..
  finally show ?thesis .
qed

lemma card_words_len_eq: "card {w. len w = l} = 2 ^ l"
proof -
  have "inj_on bin_of_word {w. len w = l}" using inj_imp_inj_on bij_is_inj bin_of_word_bij .
  then have "card {w. len w = l} = card (bin_of_word ` {w. len w = l})" by (rule card_image[symmetric])
  also have "... = card {w::bin. length w = l}" unfolding word_len_eq_bin_len
  proof (intro arg_cong[where f=card] subset_antisym subsetI image_eqI)
    (* direction "\<longleftarrow>" *)
    fix x :: bin
    assume "x \<in> {w. length w = l}"
    thus "word_of_bin x \<in> {w. length (bin_of_word w) = l}" by simp
    show "x = bin_of_word (word_of_bin x)" by simp
  qed (* direction "\<longrightarrow>" by *) blast
  also have "... = 2 ^ l" by (rule card_bin_len_eq)
  finally show ?thesis .
qed

lemma image_Collect_compose: "f ` {g x | x. P x} = {f (g x) | x. P x}" by blast

corollary card_words_len_eq_prefix:
  fixes p :: word
  shows "card {p @@ w | w. len w = l} = 2^l" (is "card ?A = 2^l")
proof -
  let ?B = "{w. len w  = l}"
  define f :: "word \<Rightarrow> word" where "f \<equiv> drp (len p)"
  have "bij_betw f ?A ?B" unfolding bij_betw_def inj_on_def proof safe
    fix x y assume "f (p @@ x) = f (p @@ y)"
    thus "p@@x = p@@y"
      unfolding f_def using drp_prefix by simp
  next
    fix x
    show "len (f (p @@ x)) = len x"
      unfolding f_def using drp_prefix by simp
  next
    have *: "f ` ?A = ?B"
      using drp_prefix[of p] image_Collect_compose[of f "\<lambda>w. p @@ w"]
      unfolding f_def by simp
    fix x assume "l = len x"
    with * show "x \<in> f ` {p @@ w |w. len w = len x}" by blast
  qed
  with card_words_len_eq show ?thesis
    using bij_betw_same_card by fastforce
qed

lemma finite_words_len_eq: "finite {w. len w = n}" (is "finite ?A")
proof -
  define B where "B \<equiv> {xs::bin. length xs = n}"

  have "\<And>xs::bin. set xs \<subseteq> {True, False}" by fast
  moreover have "finite {True, False}" by fast
  ultimately have "finite B"
    unfolding B_def using finite_lists_length_eq[of "{True, False}"]
    by presburger 

  moreover have "bin_of_word ` ?A = B"
    unfolding B_def using word_bin_iso
    by (smt (verit, best) Collect_cong Collect_mem_eq image_iff mem_Collect_eq)

  ultimately show ?thesis
    using finite_imageD[of bin_of_word ?A]
    using inj_imp_inj_on bin_of_word_bij bij_def by blast
qed

lemma clog_le: "0 < n \<Longrightarrow> clog n \<le> n"
  by (metis Nat.le_diff_conv2 diff_is_0_eq' discrete le_add_diff_inverse2 le_numeral_extra(4) log_le)

lemma inj_append:
  fixes xs ys :: "'a list"
  shows inj_append_L: "inj (\<lambda>xs. xs @ ys)" 
    and inj_append_R: "inj (\<lambda>ys. xs @ ys)" 
  using append_same_eq by (intro injI, simp)+

lemma inj_app_L: "inj (\<lambda>a. a @@ b)"
proof -
  have *: "(\<lambda>a. a @@ b) = word_of_bin \<circ> (\<lambda>x. x @ bin_of_word b) \<circ> bin_of_word"
    unfolding app.simps by force
  show "inj (\<lambda>a. a @@ b)" unfolding * using inj_append_L[of "bin_of_word b"] word_bin_bij
    by (intro inj_compose) (simp_all only: bij_is_inj)
qed

lemma inj_app_R: "inj (\<lambda>b. a @@ b)"
proof -
  have *: "(\<lambda>b. a @@ b) = word_of_bin \<circ> (\<lambda>x. bin_of_word a @ x) \<circ> bin_of_word"
    unfolding app.simps by force
  show "inj (\<lambda>b. a @@ b)" unfolding * using inj_append_R[of "bin_of_word a"] word_bin_bij
    by (intro inj_compose) (simp_all only: bij_is_inj)
qed
  

theorem num_equivalent_encodings:
  fixes M w
  assumes "TM_decode_pad w = M"
  defines "l \<equiv> len w"
  shows "2^(l - clog l) \<le> card {w. len w = l \<and> TM_decode_pad w = M}" (is "?lhs \<le> card ?A")
proof (cases "l > 0")
  case True
  from \<open>l > 0\<close> have "w \<noteq> num.One" unfolding l_def unfolding len_eq_0_iff ..
  from \<open>l > 0\<close> have "clog l \<le> l" by (rule clog_le)

  define w' where "w' \<equiv> strip_exp_pad w"
  have lw': "len w' = clog l" unfolding w'_def l_def using \<open>w \<noteq> num.One\<close> by (rule strip_exp_pad_len)
  
  have "?lhs = card {pad. len pad = l - clog l}" using card_words_len_eq ..
  also have "... = card ((\<lambda>pad. pad @@ w') ` {pad. len pad = l - clog l})"
    using card_image[symmetric] inj_imp_inj_on inj_app_L .
  also have "... = card {pad @@ w' | pad. len pad = l - clog l}"
    by (intro arg_cong[where f=card]) (rule image_Collect)
  also have "... \<le> card {w. len w = l \<and> TM_decode_pad w = M}"
  proof (intro card_mono)
    show "finite {w. len w = l \<and> TM_decode_pad w = M}" using finite_words_len_eq by simp
    show "{pad @@ w' | pad. len pad = l - clog l} \<subseteq> {w. len w = l \<and> TM_decode_pad w = M}"
    proof safe
      fix pad
      assume lp: "len pad = l - clog l"
      show lpw': "len (pad @@ w') = l" unfolding app_len lp lw'
        using \<open>clog l \<le> l\<close> by (rule le_add_diff_inverse2)

      have h1: "drop (l - clog l) (bin_of_word pad) = []" using lp
        unfolding word_len_eq_bin_len by (intro drop_all) (rule eq_imp_le)
      have h2: "l - clog l - length (bin_of_word pad) = 0"
        unfolding word_len_eq_bin_len[symmetric] lp by simp
      have h3: "drop (l - clog l) (bin_of_word (pad @@ w')) = bin_of_word w'"
        unfolding app.simps word_bin_iso drop_append h1 h2 by simp
      show "TM_decode_pad (pad @@ w') = M" unfolding TM_decode_pad_def strip_exp_pad_altdef
        unfolding lpw' Let_def h3 word_bin_word_id unfolding w'_def
        using \<open>TM_decode_pad w = M\<close> by (fold TM_decode_pad_def)
    qed
  qed
  finally show ?thesis .
next
  case False
  then have "l = 0" by blast
  then have "w = num.One" unfolding l_def by (fold len_eq_0_iff)
  have "M = Rejecting_TM" using \<open>TM_decode_pad w = M\<close> unfolding \<open>w = num.One\<close> TM_decode_Nil ..

  have "2 ^ (l - clog l) = 1" unfolding \<open>l = 0\<close> by simp
  also have "1 = card {num.One}" by simp
  also have "... \<le> card {w. len w = l \<and> TM_decode_pad w = M}" unfolding \<open>l = 0\<close> \<open>M = Rejecting_TM\<close>
  proof (intro card_mono)
    show "finite {w. len w = 0 \<and> TM_decode_pad w = Rejecting_TM}" using finite_words_len_eq by simp
    show "{num.One} \<subseteq> {w. len w = 0 \<and> TM_decode_pad w = Rejecting_TM}" using TM_decode_Nil by simp
  qed
  finally show ?thesis .
qed


text\<open>2. The retraction of preceding 1-bits creates the needed infinitude of
        equivalent encodings of every possible TM \<open>M\<close>, as \<^emph>\<open>we can embed any code \<open>\<rho>(M)\<close>
        in a word of length \<open>ℓ\<close> for which \<open>log(ℓ) > len (\<rho>(M))\<close>.\<close> [...]\<close>

theorem embed_TM_in_len:
  fixes M l
  assumes "tm_wf0 M"
    and min_word_len: "clog l \<ge> len (encode_TM M) + 2"
    \<comment> \<open>The \<open>+2\<close> bits are required for the \<open>1\<^sup>+0\<close>-prefix.
        Note: this theorem technically also holds when the assumption @{thm min_word_len} reads
        \<^term>\<open>clog l > len (encode_TM M) \<longleftrightarrow> clog l \<ge> len (encode_TM M) + 1\<close>,
        but only due to \<^const>\<open>strip_al_prefix\<close> allowing the absence of preceding ones.
        If it were to enforce the constraint of a correct \<open>1\<^sup>+0\<close>-prefix, this would no longer be the case.
        Additionally, the weaker version allows the case of \<^term>\<open>l = 0\<close>,
        which requires special treatment (it follows that \<^term>\<open>M = Rejecting_TM\<close>).\<close>
  obtains w
  where "len w = l"
    and "TM_decode_pad w = M"
proof
  have "l > 0"
  proof (rule ccontr)
    assume "\<not> l > 0" hence "l = 0" ..
    from min_word_len show False unfolding \<open>l = 0\<close> by force
  qed
  hence "clog l \<le> l" by (rule clog_le)

  let ?\<rho>M = "encode_TM M" let ?l\<rho> = "len ?\<rho>M" let ?w = word_of_bin and ?b = bin_of_word
  define al_prefix where "al_prefix \<equiv> False # True \<up> (clog l - ?l\<rho> - 1)"
  define w' where "w' \<equiv> ?w (?b ?\<rho>M @ al_prefix)"
  have w'_correct: "strip_al_prefix w' = ?\<rho>M" unfolding w'_def al_prefix_def strip_alp_altdef ..
  have "len w' = ?l\<rho> + length al_prefix" unfolding w'_def word_len_eq_bin_len by simp
  also have "... = ?l\<rho> + (clog l - ?l\<rho> - 1) + 1" unfolding add_left_cancel al_prefix_def
      unfolding length_Cons length_replicate by presburger
  also have "... = clog l" using min_word_len by force
  finally have w'_len: "length (?b w') = clog l" unfolding word_len_eq_bin_len .

  define exp_pad where "exp_pad \<equiv> False \<up> (l - clog l)"
  define w where "w \<equiv> ?w (exp_pad @ ?b w')"
  have exp_len: "length exp_pad = l - clog l" unfolding exp_pad_def by (rule length_replicate)
  have dexp: "drop (l - clog l) exp_pad = []" unfolding exp_pad_def by force

  have "len w = l - clog l + clog l" unfolding w_def word_len_eq_bin_len bin_word_bin_id length_append
    unfolding exp_pad_def w'_len length_replicate ..
  also have "... = l" using \<open>clog l \<le> l\<close> by (rule le_add_diff_inverse2)
  finally show "len w = l" .

  have w_correct: "strip_exp_pad w = w'" unfolding strip_exp_pad_altdef \<open>len w = l\<close> Let_def
    unfolding w_def bin_word_bin_id drop_append dexp exp_len by simp 

  show "TM_decode_pad w = M" unfolding TM_decode_pad_def w_correct w'_correct
    using \<open>tm_wf0 M\<close> by (rule codec_TM)
qed


end
