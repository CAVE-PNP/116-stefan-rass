theory complexity
  imports Main gn "Universal_Turing_Machine.UTM" "HOL-Library.Sublist" "HOL-Library.Discrete"
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


subsection\<open>Basic Measures\<close>

text\<open>The tape size can not use the universal function \<^term>\<open>size\<close>, since for any pair \<^term>\<open>p = (a, b)\<close>, \<^term>\<open>size p = 1\<close>.\<close>
fun tape_size :: "tape \<Rightarrow> nat" \<comment> \<open>using \<open>fun\<close> since \<open>definition\<close> does not recognize patterns like \<^term>\<open>(l, r)\<close>\<close>
  where "tape_size (l, r) = length l + length r"


subsubsection\<open>Time\<close>

text\<open>The time restriction predicate is similar to \<^term>\<open>Hoare_halt\<close>, but includes a maximum number of steps.\<close>
definition time_restricted :: "(nat \<Rightarrow> nat) \<Rightarrow> tprog0 \<Rightarrow> bool"
  where "time_restricted T p \<equiv> \<forall>tp. \<exists>n.
            n \<le> T (tape_size tp)
          \<and> is_final (steps0 (1, tp) p n)"

(* TODO (?) notation: \<open>p terminates_in_time T\<close> *)

(* size of tape after M does n steps on input x *)
abbreviation space0 where "space0 M x n \<equiv> let (_,tp) = steps0 (1, x) M n in tape_size tp"

text\<open>\<open>time\<^sub>M(x)\<close> is the number of steps until the computation of \<open>M\<close> halts on input \<open>x\<close>
     or \<open>None\<close> if \<open>M\<close> does not halt on input \<open>x\<close>\<close>
definition time :: "tprog0 \<Rightarrow> tape \<Rightarrow> nat option"
  where "time p tp = (
    if \<exists>n. is_final (steps0 (1, tp) p n)
      then Some (LEAST n. is_final (steps0 (1, tp) p n))
      else None
    )"


lemma time_restricted_altdef:
  "time_restricted T p \<longleftrightarrow> (\<forall>tp. \<exists>n. time p tp = Some n \<and> n \<le> T (tape_size tp))"
  unfolding time_restricted_def (* in order for the intros to work in direction "\<Longleftarrow>" *)
proof (intro iffI allI exI conjI)
  fix tp
  let ?f = "\<lambda>n. is_final (steps0 (1, tp) p n)" let ?lf = "LEAST n. ?f n"

  assume (* time_restricted T p *) "\<forall>tp. \<exists>n \<le> T (tape_size tp). is_final (steps0 (1, tp) p n)"
  then have n_ex: "\<exists>n. n \<le> T (tape_size tp) \<and> ?f n" ..
  then obtain n where "n \<le> T (tape_size tp)" and "?f n" by blast

  from n_ex have "\<exists>n. ?f n" by blast
  then show "time p tp = Some ?lf" unfolding time_def by (rule if_P)
  have "?lf \<le> n" using Least_le \<open>?f n\<close> .
  also note \<open>n \<le> T (tape_size tp)\<close>
  finally show "?lf \<le> T (tape_size tp)" .
next
  fix tp
  let ?f = "\<lambda>n. is_final (steps0 (1, tp) p n)" let ?lf = "LEAST n. ?f n"

  assume "\<forall>tp. \<exists>n. time p tp = Some n \<and> n \<le> T (tape_size tp)"
  then obtain n where n_some: "time p tp = Some n" and n_le: "n \<le> T (tape_size tp)" by blast

  have n_ex: "\<exists>n. ?f n" by (metis n_some option.discI time_def)
  with n_some have "?lf = n" unfolding time_def by simp

  show "?f ?lf" using LeastI_ex n_ex .
  show "?lf \<le> T (tape_size tp)" unfolding \<open>?lf = n\<close> using n_le .
qed

corollary "time_restricted T p \<Longrightarrow> (\<forall>tp. \<exists>n. the (time p tp) \<le> T (tape_size tp))"
  unfolding time_restricted_altdef
  by (metis option.sel)


subsubsection\<open>Space\<close>

definition space_restricted :: "(nat \<Rightarrow> nat) \<Rightarrow> tprog0 \<Rightarrow> bool"
  where "space_restricted T M \<equiv> \<forall>x. \<forall>n. space0 M x n \<le> T(tape_size x)"

definition space :: "tprog0 \<Rightarrow> tape \<Rightarrow> nat"
  where "space M x = Max {space0 M x n | n. n\<in>\<nat>}"


lemma update_space_one: "tape_size (update a (l,r)) \<le> 1 + tape_size (l,r)"
  by (induction a) simp_all
lemma update_space_le: "tape_size (l,r) \<le> tape_size(update a (l,r))"
  by (induction a) simp_all

lemma step_space_mono: "space0 M x n \<le> space0 M x (Suc n)"
  oops

lemma tape_size_mono: "n \<le> m \<Longrightarrow> space0 M x n \<le> space0 M x m"
  oops


subsection\<open>Encoding Words\<close>

text\<open>Encoding binary words as TM tape cells: \<^term>\<open>num.Bit1\<close> is encoded as \<^term>\<open>[Oc, Oc]\<close> and \<^term>\<open>num.Bit1\<close> as term>\<open>[Oc, Bk]\<close>.
  Thus, the ends of an encoded term can be marked with the pattern \<^term>\<open>[Bk, Bk]\<close>.\<close>
fun encode_word :: "word \<Rightarrow> cell list" where
  "encode_word num.One = []"
| "encode_word (num.Bit0 w) = Oc # Bk # encode_word w"
| "encode_word (num.Bit1 w) = Oc # Oc # encode_word w"

fun is_encoded_word :: "cell list \<Rightarrow> bool" where
  "is_encoded_word [] = True"
| "is_encoded_word (Oc # _ # cs) = is_encoded_word cs"
| "is_encoded_word _ = False"

fun decode_word :: "cell list \<Rightarrow> word" where
  "decode_word (Oc # Bk # cs) = num.Bit0 (decode_word cs)"
| "decode_word (Oc # Oc # cs) = num.Bit1 (decode_word cs)"
| "decode_word _ = num.One"


lemma encode_decode_word: "decode_word (encode_word w) = w"
  by (induction w) simp_all

lemma decode_encode_word:
  "is_encoded_word cs \<Longrightarrow> encode_word (decode_word cs) = cs"
  (is "?ie cs \<Longrightarrow> ?de cs = cs")
proof (induction cs rule: is_encoded_word.induct)
  case (2 c cs) (* cs = Oc # c # cs *)
  from \<open>?ie (Oc # c # cs)\<close> have "?ie cs" by simp
  with "2.IH" have IH: "?de cs = cs" .
  then show ?case by (cases c) simp_all
qed (* cases "cs = []", "cs = Bk # _", "cs = [_]" by *) simp_all


subsection\<open>Deciding Languages\<close>

\<comment> \<open>Since \<open>L\<close> is a typical name for unspecified languages in the literature,
    the synonymous constructor \<^term>\<open>L\<close> of type \<^typ>\<open>action\<close> ("move head left") is hidden.\<close>
hide_const (open) L

abbreviation head where "head tp \<equiv> read (snd tp)"

text\<open>A TM \<^term>\<open>p\<close> is considered to decide a language \<^term>\<open>L\<close>, iff for every possible word \<^term>\<open>w\<close>
  it correctly calculates language membership.
  That is, for \<^term>\<open>w \<in> L\<close> the computation results in \<^term>\<open>Oc\<close> under the TM head,
  and for \<^term>\<open>w \<notin> L\<close> in \<^term>\<open>Bk\<close>.
  The head is over the first cell of the right tape.
  That is, for \<^term>\<open>tp = (l, x # r)\<close>, the symbol under the head is \<open>x\<close>, or \<^term>\<open>read (snd tp)\<close>.
  Additionally (through \<^term>\<open>read\<close>), the edge of the tape is interpreted as \<^term>\<open>Bk\<close>.\<close>

abbreviation input where "input w \<equiv> (\<lambda>tp. tp = (([]::cell list), encode_word w))"

definition halts :: "tprog0 \<Rightarrow> word \<Rightarrow> bool"
  where "halts M w \<equiv> Hoare_halt (input w) M (\<lambda>_. True)"

definition accepts :: "tprog0 \<Rightarrow> word \<Rightarrow> bool"
  where "accepts M w \<equiv> Hoare_halt (input w) M (\<lambda>tp. head tp = Oc)"

definition rejects :: "tprog0 \<Rightarrow> word \<Rightarrow> bool"
  where "rejects M w \<equiv> Hoare_halt (input w) M (\<lambda>tp. head tp = Bk)"

definition decides :: "tprog0 \<Rightarrow> lang  \<Rightarrow> bool"
  where "decides M L \<equiv> \<forall>w. (w \<in> L \<longleftrightarrow> accepts M w) \<and> (w \<notin> L \<longleftrightarrow> rejects M w)"


lemma Hoare_haltE[elim]:
  fixes P M tp
  assumes "Hoare_halt P M Q"
    and "P tp"
  obtains n
  where "is_final (steps0 (1, tp) M n)"
    and "Q holds_for steps0 (1, tp) M n"
  using assms unfolding Hoare_halt_def by blast

\<comment> \<open>to avoid conflicts in terms like \<open>P \<mapsto> Q\<close>\<close>
no_notation Abacus_Hoare.assert_imp ("_ \<mapsto> _" [0, 0] 100)

lemma hoare_true: "Hoare_halt P M Q \<Longrightarrow> Hoare_halt P M (\<lambda>_. True)"
proof (subst Hoare_consequence)
  show "Q \<mapsto> (\<lambda>_. True)" unfolding Turing_Hoare.assert_imp_def by blast
qed simp_all

lemma accepts_halts: "accepts M w \<Longrightarrow> halts M w"
  unfolding accepts_def halts_def by (rule hoare_true)
lemma rejects_halts: "rejects M w \<Longrightarrow> halts M w"
  unfolding rejects_def halts_def by (rule hoare_true)

lemma holds_for_le:
  assumes f: "is_final (steps0 (1, l, r) M n)"
    and Qn: "Q holds_for steps0 (1, l, r) M n"
    and "n \<le> m"
  shows "Q holds_for steps0 (1, l, r) M m" (is "?Qh m")
proof -
  from \<open>n \<le> m\<close> obtain n' where "m = n + n'" by (rule less_eqE)
  then have "?Qh m = Q holds_for steps0 (steps0 (1, l, r) M n) M n'" by simp
  also have "... = ?Qh n" using f by (rule is_final_holds)
  finally show ?thesis using Qn ..
qed

lemma max_cases:
  assumes "P a"
    and "P b"
  shows "P (max a b)"
  using assms unfolding max_def by simp

lemma holds_for_and[intro]:
  assumes P: "P holds_for c"
    and Q: "Q holds_for c"
  shows "(\<lambda>tp. P tp \<and> Q tp) holds_for c"
proof -
  obtain s l r where c_def: "c = (s, l, r)" by (rule prod_cases3)
  from c_def P have "P (l, r)" by simp
  moreover from c_def Q have "Q (l, r)" by simp
  ultimately show ?thesis unfolding c_def by simp
qed

lemma hoare_and[intro]:
  assumes h1: "Hoare_halt P M Q1"
    and h2: "Hoare_halt P M Q2"
  shows "Hoare_halt P M (\<lambda>tp. Q1 tp \<and> Q2 tp)"
proof (intro Hoare_haltI)
  fix l r
  assume p: "P (l, r)" (is "P ?tp")
  from p h1 obtain n1
    where f1: "is_final (steps0 (1, ?tp) M n1)"
      and q1: "Q1 holds_for steps0 (1, ?tp) M n1" by blast
  from p h2 obtain n2
    where f2: "is_final (steps0 (1, ?tp) M n2)"
      and q2: "Q2 holds_for steps0 (1, ?tp) M n2" by blast
  define n where "n = max n1 n2"

  have "is_final (steps0 (1, l, r) M n)" (is "?f n")
    unfolding n_def using f1 f2 by (rule max_cases)
  moreover have "(\<lambda>tp. Q1 tp \<and> Q2 tp) holds_for steps0 (1, l, r) M n" (is "?q n") unfolding n_def
  proof (intro holds_for_and)
    show "Q1 holds_for steps0 (1, l, r) M (max n1 n2)"
      using f1 q1 max.cobounded1 by (rule holds_for_le)
    show "Q2 holds_for steps0 (1, l, r) M (max n1 n2)"
      using f2 q2 max.cobounded2 by (rule holds_for_le)
  qed
  ultimately show "\<exists>n. ?f n \<and> ?q n" by blast
qed

lemma hoare_contr:
  fixes P M tp
  assumes "Hoare_halt P M (\<lambda>_. False)" and "P tp"
  shows "False"
proof - \<comment> \<open>This one is tricky since the automatic solvers do not pick apart pairs on their own.
  Since @{thm holds_for.simps} is defined in terms of pair items, it is not directly applicable.\<close>
  from assms obtain n where "(\<lambda>_. False) holds_for steps0 (1, tp) M n" ..
  moreover obtain s l r where "steps0 (1, tp) M n = (s, l, r)" using prod_cases3 .
  ultimately show "(\<lambda>_. False) (l, r)" (* \<equiv> False *) by simp
qed

lemma input_encoding: \<comment> \<open>Each word has an input encoding. Useful with @{thm hoare_contr}}\<close>
  fixes w
  shows "input w ([], encode_word (decode_word (encode_word w)))" unfolding encode_decode_word ..

lemma holds_for_neg: "\<not> Q holds_for c \<longleftrightarrow> (\<lambda>tp. \<not> Q tp) holds_for c"
proof -
  obtain s l r where c_def: "c = (s, l, r)" by (rule prod_cases3)
  show ?thesis unfolding c_def by simp
qed

lemma hoare_halt_neg:
  assumes "\<not> Hoare_halt (input w) M Q"
    and "halts M w"
  shows "Hoare_halt (input w) M (\<lambda>tp. \<not> Q tp)"
  using assms unfolding Hoare_halt_def holds_for_neg[symmetric] halts_def by fast

lemma head_halt_inj:
  assumes "Hoare_halt (input w) M (\<lambda>tp. head tp = x)"
      and "Hoare_halt (input w) M (\<lambda>tp. head tp = y)"
    shows "x = y"
proof (rule ccontr)
  assume "x \<noteq> y"
  then have *: "a = x \<and> a = y \<longleftrightarrow> False" for a by blast

  from hoare_and have "Hoare_halt (input w) M (\<lambda>tp. head tp = x \<and> head tp = y)"
    using assms .
  then have "Hoare_halt (input w) M (\<lambda>_. False)" unfolding * .
  thus False using input_encoding by (rule hoare_contr)
qed

lemma acc_not_rej:
  assumes "accepts M w"
  shows "\<not> rejects M w"
proof (intro notI)
  assume "rejects M w"

  have "Hoare_halt (input w) M (\<lambda>tp. head tp = Oc)"
    using \<open>accepts M w\<close> unfolding accepts_def .
  moreover have "Hoare_halt (input w) M (\<lambda>tp. head tp = Bk)"
    using \<open>rejects M w\<close> unfolding rejects_def .
  ultimately show False using head_halt_inj[of w M Oc Bk] by blast
qed


lemma rejects_altdef:
  "rejects M w = (halts M w \<and> \<not> accepts M w)"
proof (intro iffI conjI)
  assume "rejects M w"
  then show "halts M w" unfolding rejects_def halts_def using hoare_true by fast
  assume "rejects M w"
  then show "\<not> accepts M w" using acc_not_rej by auto
next
  have *: "c \<noteq> Oc \<longleftrightarrow> c = Bk" for c by (cases c) blast+

  assume "halts M w \<and> \<not> accepts M w"
  then have "Hoare_halt (input w) M (\<lambda>tp. head tp \<noteq> Oc)"
    unfolding accepts_def by (intro hoare_halt_neg) blast+
  then show "rejects M w" unfolding rejects_def * .
qed

lemma decides_halts:
  assumes "decides M L"
  shows "halts M w"
proof (cases "w \<in> L")
  case True
  hence "accepts M w" using assms unfolding decides_def by simp
  then show ?thesis by (rule accepts_halts)
next
  case False
  hence "rejects M w" using assms unfolding decides_def by auto
  then show ?thesis by (rule rejects_halts)
qed

lemma decides_altdef: "decides M L = (\<forall>w. halts M w \<and> (w \<in> L \<longleftrightarrow> accepts M w))"
proof (intro iffI allI)
  fix w
  assume "decides M L"
  hence "halts M w" by (rule decides_halts)
  moreover have "w \<in> L \<longleftrightarrow> accepts M w" using \<open>decides M L\<close>
    unfolding decides_def by simp
  ultimately show "halts M w \<and> (w \<in> L \<longleftrightarrow> accepts M w)" ..
next
  assume "\<forall>w. halts M w \<and> (w \<in> L \<longleftrightarrow> accepts M w)"
  then show "decides M L" unfolding decides_def
    by (simp add: rejects_altdef)
qed

lemma decides_altdef2:
  "decides M L \<longleftrightarrow> (\<forall>w.
    Hoare_halt (input w) M (\<lambda>tp. head tp = (if w \<in> L then Oc else Bk))
  )"
  (is "decides M L \<longleftrightarrow> ( \<forall>w. Hoare_halt (?pre w) M (?post w) )")
proof (intro iffI allI)
  assume "decides M L"
  fix w
  from \<open>decides M L\<close> show "Hoare_halt (?pre w) M (?post w)"
    unfolding decides_def accepts_def rejects_def
  proof (cases "w \<in> L")
    case False
    from \<open>decides M L\<close> \<open>w \<notin> L\<close> have "rejects M w" unfolding decides_def by blast
    thus ?thesis unfolding rejects_def using \<open>w \<notin> L\<close> by presburger
  qed (* case "w \<in> L" by *) presburger
next
  assume assm: "\<forall>w. Hoare_halt (?pre w) M (?post w)"
  show "decides M L" unfolding decides_def proof (intro allI conjI)
    fix w
    show "w \<in> L \<longleftrightarrow> accepts M w" proof
      assume "w \<in> L"
      thus "accepts M w" unfolding accepts_def using assm by presburger
    next
      assume "accepts M w"
      then have "Oc = (if w\<in>L then Oc else Bk)"
        unfolding accepts_def using assm head_halt_inj[of w M Oc] by presburger
      thus "w \<in> L" using cell.distinct(1) by presburger
    qed
  next
    fix w
    show "w \<notin> L \<longleftrightarrow> rejects M w" proof
      assume "w \<notin> L"
      thus "rejects M w" unfolding rejects_def using assm by presburger
    next
      assume "rejects M w"
      then have "Bk = (if w\<in>L then Oc else Bk)"
        unfolding rejects_def using assm head_halt_inj[of w M Bk] by presburger
      thus "w \<notin> L" by auto
    qed
  qed
qed


(* TODO (?) notation: \<open>p decides L\<close> *)


subsection\<open>DTIME\<close>

text\<open>\<open>DTIME(T)\<close> is the set of languages decided by TMs in time \<open>T\<close> or less.\<close>
definition DTIME :: "(nat \<Rightarrow> nat) \<Rightarrow> lang set"
  where "DTIME T \<equiv> {L. \<exists>M. decides M L \<and> time_restricted T M}"

lemma in_dtimeI[intro]:
  assumes "decides M L"
    and "time_restricted T M"
  shows "L \<in> DTIME T"
  unfolding DTIME_def using assms by blast

lemma in_dtimeE[elim]:
  assumes "L \<in> DTIME T"
  obtains M
  where "decides M L"
    and "time_restricted T M"
  using assms unfolding DTIME_def by blast

lemma in_dtimeE'[elim]:
  assumes "L \<in> DTIME T"
  shows "\<exists>M. decides M L \<and> time_restricted T M"
  using assms unfolding DTIME_def ..


subsection\<open>Encoding TMs\<close>

\<comment> \<open>An issue of the following definitions is that the existing definition \<^term>\<open>code\<close>
  uses a naive Gödel numbering scheme that includes encoding list items as prime powers,
  where each "next prime" \<^term>\<open>Np n\<close> is searched naively starting from \<^term>\<open>Pi n\<close>
  (see \<^term>\<open>godel_code'\<close>, \<^term>\<open>Pi\<close>, and \<^term>\<open>Np\<close>).\<close>

\<comment> \<open>Reminder: For binary numbers, as stated in the paper (ch. 1, p. 2),
  the "least significant bit is located at the right end".
  The recursive definitions for words result in somewhat unintuitive definitions here:
  The number 6 is 110 in binary, but as \<^typ>\<open>word\<close> it is \<^term>\<open>num.Bit0 (num.Bit1 num.One)\<close>.
  Similarly, as \<^typ>\<open>bit_string\<close> (synonym for \<^typ>\<open>bool list\<close>), 6 is \<^term>\<open>[False, True]\<close>.\<close>

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
  unfolding assms add_exp_pad_def by (intro suffixI) simp

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
  finally show "clog l \<le> l" .
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


subsubsection\<open>Properties of \<^term>\<open>code\<close>\<close>

lemma code_Nil: "code [] = 1" unfolding code.simps Let_def godel_code_eq_1 modify_tprog.simps ..
lemma code_gt_0: "code M > 0" unfolding code.simps Let_def using godel_code_great .

lemma godel_code'_mono2: "godel_code' ps n \<le> godel_code' ps (Suc n)"
proof (induction n rule: godel_code'.induct)
  case (1 n)
  thus ?case unfolding godel_code'.simps ..
next
  case (2 x xs n)
  from Pi_inc[of n] have "Pi n ^ x \<le> Pi (Suc n) ^ x" by (intro power_mono) simp_all
  find_theorems "_ ^ _ < _ ^ _"
  then show ?case unfolding godel_code'.simps using "2.IH" by (rule mult_le_mono)
qed

corollary Pi_pow_gr_1: "Pi n ^ p \<ge> 1"
  using one_le_power[of "Pi n"] less_imp_le Pi_gr_1 unfolding One_nat_def .

lemma godel_code'_mono1: "godel_code' ps n \<le> godel_code' (p#ps) n"
proof -
  have "(Suc 0) * godel_code' ps n \<le> Pi n ^ p * godel_code' ps (Suc n)"
    using Pi_pow_gr_1 godel_code'_mono2 unfolding One_nat_def by (rule mult_le_mono)
  then show ?thesis unfolding godel_code'.simps by simp
qed

lemma code_Cons: "code M < code (i # M)"
proof -
  obtain a n where i: "i = (a, n)" by (rule prod.exhaust)
  let ?g = godel_code' and ?M = "modify_tprog M" and ?M' = "modify_tprog ((a, n) # M)"
  have a: "2 ^ length ?M < (2::nat) ^ length ?M'" by (subst power_strict_increasing) simp_all

  have "?g ?M (Suc 0) \<le> ?g ?M (Suc (Suc (Suc 0)))" using godel_code'_mono2 le_trans by blast
  also have "... \<le> Pi (Suc 0) ^ action_map a * Pi (Suc (Suc 0)) ^ n * ..." using Pi_pow_gr_1 by simp
  finally have b: "?g ?M (Suc 0) \<le> ?g ?M' (Suc 0)"
    unfolding modify_tprog.simps godel_code'.simps mult.assoc .

  have "code M = 2 ^ length ?M * ?g ?M (Suc 0)" unfolding code.simps godel_code.simps Let_def ..
  also from a have "... < 2 ^ length ?M' * ?g ?M (Suc 0)" using godel_code'_nonzero by (rule mult_less_mono1)
  also from b have "... \<le> 2 ^ length ?M' * ?g ?M' (Suc 0)" by (rule mult_le_mono2)
  also have "... = code ((a, n) # M)" unfolding code.simps godel_code.simps Let_def ..
  finally show ?thesis by (unfold i)
qed

lemma code_gt_1: "M \<noteq> [] \<Longrightarrow> code M > 1"
proof (induction M rule: list_nonempty_induct)
  case (single x)
  have "1 = code []" using code_Nil ..
  also have "... < code [x]" by (rule code_Cons)
  finally show ?case .
next
  case (cons x xs)
  note \<open>1 < code xs\<close>
  also have "code xs < code (x # xs)" by (rule code_Cons)
  finally show ?case .
qed

lemma code_1_iff: "code M = 1 \<longleftrightarrow> M = []"
proof (intro iffI)
  assume "code M = 1"
  then show "M = []" using code_gt_1 by fastforce
next
  assume "M = []"
  then show "code M = 1" using code_Nil by blast
qed


subsubsection\<open>Code Description\<close>

text\<open>For this part, only a short description is given in ch. 3.1.
  The somewhat obvious choice is to utilize \<^term>\<open>code\<close>, since it is already defined
  and used as encoding by the universal TM \<^term>\<open>UTM\<close> (see @{thm UTM_halt_lemma2}).

  This step is also used to implement the following requirement:
  "every string over \<open>{0, 1}\<^sup>*\<close> represents some TM (easy to assure by executing
  an invalid code as a canonic TM that instantly halts and rejects its input)"\<close>

definition Rejecting_TM :: tprog0
  where "Rejecting_TM = [(W0, 0), (W0, 0)]"

lemma rej_TM_wf: "tm_wf0 Rejecting_TM" unfolding Rejecting_TM_def tm_wf.simps by force

lemma rej_TM: "rejects Rejecting_TM w" unfolding rejects_def
proof (intro Hoare_haltI exI conjI)
  fix l r
  have fetch: "fetch Rejecting_TM 1 b = (W0, 0)" for b unfolding Rejecting_TM_def
    by (cases b) (simp_all add: fetch.simps nth_of.simps)

  have step1: "steps0 (1, (l, r)) Rejecting_TM 1 = (0, l, Bk # tl r)"
  proof -
    have "steps0 (1, (l, r)) Rejecting_TM 1 = step0 (1, l, r) Rejecting_TM" unfolding One_nat_def steps.simps ..
    also have "... = (0, update W0 (l, r))" unfolding step.simps diff_zero fetch by simp
    also have "... = (0, l, Bk # tl r)" by simp
    finally show ?thesis .
  qed

  show "is_final (steps0 (1, l, r) Rejecting_TM 1)" unfolding step1 ..
  show "(\<lambda>tp. head tp = Bk) holds_for steps0 (1, l, r) Rejecting_TM 1"
    unfolding step1 holds_for.simps by simp
qed


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

lemma action_map_inj: "inj action_map"
proof (intro injI)
  fix x y
  assume "action_map x = action_map y"
  then show "x=y" by (cases x; cases y) simp_all
qed

fun unroll :: "('a \<Rightarrow> 'c) \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow> ('a\<times>'b) list \<Rightarrow> 'c list" where
  "unroll _ _ [] = []"
| "unroll f g ((a,b)#t) = f a#g b#unroll f g t"

corollary modify_tprog_unroll_def: "modify_tprog = unroll action_map (\<lambda>b. b)"
proof (* why is this so hard? *)
  fix xs
  note unroll_simps = unroll.simps[of action_map "\<lambda>b. b"]
  show "modify_tprog xs = unroll action_map (\<lambda>b. b) xs" proof (induction xs)
    case (Cons a xs)
    then show ?case using unroll_simps(2) modify_tprog.simps(2)
      by (smt (verit, best) list.discI list.sel(1) unroll.elims)
  qed simp
qed

lemma unroll_inj:
  fixes f::"'a \<Rightarrow> 'c" and g::"'b \<Rightarrow> 'c"
  assumes "inj f" "inj g"
  shows "inj (unroll f g)"
proof (intro injI)
  let ?F = "unroll f g"
  fix xs ys
  assume "?F xs = ?F ys"
  then show "xs = ys" proof (induction xs arbitrary: ys)
    case Nil
    then have "?F ys = []" by simp
    then show ?case
      using unroll.elims list.distinct(1) by blast
  next
    case (Cons ab xs)
    define a where "a \<equiv> fst ab"
    define b where "b \<equiv> snd ab"
    have ab_def: "ab = (a,b)" unfolding a_def b_def by simp
    with Cons.prems have "\<exists>ys' a' b'. ys = (a',b')#ys' \<and> (?F ys' = ?F xs) \<and> f a' = f a \<and>  g b' = g b"
        using list.discI list.sel unroll.elims case_prod_conv
        by (smt (verit, del_insts) unroll.simps(2))
    then obtain ys' a' b' where "ys = (a',b')#ys'" and "?F ys' = ?F xs" and "f a' = f a" and "g b' = g b"
      by blast
    note * = this
    with assms have "(a,b) = (a',b')" unfolding inj_def using assms by simp
    with Cons.IH * show ?case unfolding ab_def by force
  qed
qed

corollary modify_tprog_inj: "inj modify_tprog"
  unfolding modify_tprog_unroll_def
  using unroll_inj[of action_map "\<lambda>x. x"] action_map_inj by simp

lemma godel_inj: "inj godel_code" sorry

lemma code_inj: "inj code"
  using modify_tprog_inj godel_inj
  and code.simps inj_compose[of godel_code modify_tprog]
  by (metis comp_apply inj_on_cong)

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
    which is \<^term>\<open>[]::tprog0\<close>, the machine without instructions.
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

lemma TM_decode_pad_wf: "tm_wf0 (TM_decode_pad w)"
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

lemma num_equivalent_encodings:
  fixes M w
  assumes "TM_decode_pad w = M"
  defines "l \<equiv> len w"
  shows "card {w. len w = l \<and> TM_decode_pad w = M} \<ge> 2^(l - clog l)"
  using assms
  oops


end