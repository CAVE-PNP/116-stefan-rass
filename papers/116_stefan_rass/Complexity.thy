theory Complexity
  imports Goedel_Numbering TM_Encoding
    "Universal_Turing_Machine.UTM"
begin


subsection\<open>Basic Definitions\<close>

text\<open>The tape size can not use the universal function \<^const>\<open>size\<close>,
  since for any pair \<^term>\<open>p = (a, b)\<close>, \<^term>\<open>size p = 1\<close>.\<close>

fun tape_size :: "tape \<Rightarrow> nat" \<comment> \<open>using \<open>fun\<close> since \<open>definition\<close> does not recognize patterns like \<^term>\<open>(l, r)\<close>\<close>
  where "tape_size (l, r) = length l + length r"

text\<open>At the start of execution, the TM's head is over the first cell of the right tape.
  That is, for \<^term>\<open>tp = (l, x # r)\<close>, the symbol under the head is \<open>x\<close>, or \<^term>\<open>read (snd tp)\<close>.
  Additionally (through \<^const>\<open>read\<close>), the edge of the tape is interpreted as \<^const>\<open>Bk\<close>.\<close>

abbreviation head where "head tp \<equiv> read (snd tp)"


subsubsection\<open>Encoding Words\<close>

text\<open>Encoding binary words as TM tape cells: \<^term>\<open>True\<close> is encoded as \<^term>\<open>[Oc, Oc]\<close>
  and \<^term>\<open>False\<close> as \<^term>\<open>[Oc, Bk]\<close>.
  Thus, the ends of an encoded term can be marked with the pattern \<^term>\<open>[Bk, Bk]\<close>.\<close>

fun encode_word :: "word \<Rightarrow> cell list" where
  "encode_word [] = []"
| "encode_word (False # w) = Oc # Bk # encode_word w"
| "encode_word (True  # w) = Oc # Oc # encode_word w"

fun is_encoded_word :: "cell list \<Rightarrow> bool" where
  "is_encoded_word [] = True"
| "is_encoded_word (Oc # _ # cs) = is_encoded_word cs"
| "is_encoded_word _ = False"

fun decode_word :: "cell list \<Rightarrow> word" where
  "decode_word (Oc # Bk # cs) = False # (decode_word cs)"
| "decode_word (Oc # Oc # cs) = True  # (decode_word cs)"
| "decode_word _ = []"


lemma encode_decode_word: "decode_word (encode_word w) = w"
proof (induction w)
  case (Cons a w) thus ?case by (induction a) simp_all
qed (* case "w = []" by *) simp

lemma decode_encode_word:
  "is_encoded_word cs \<Longrightarrow> encode_word (decode_word cs) = cs"
  (is "?ie cs \<Longrightarrow> ?de cs = cs")
proof (induction cs rule: is_encoded_word.induct)
  case (2 c cs) (* cs = Oc # c # cs *)
  from \<open>?ie (Oc # c # cs)\<close> have "?ie cs" by simp
  with "2.IH" have IH: "?de cs = cs" .
  then show ?case by (cases c) simp_all
qed (* cases "cs = []", "cs = Bk # _", "cs = [_]" by *) simp_all


text\<open>TM execution begins with the \<^const>\<open>head\<close> at the start of the input word.\<close>

abbreviation input_tape ("<_>\<^sub>t\<^sub>p") where "<w>\<^sub>t\<^sub>p \<equiv> (([]::cell list), encode_word w)"

\<comment> \<open>The following predicate is useful for Hoare statements.\<close>

abbreviation input where "input w \<equiv> (\<lambda>tp. tp = <w>\<^sub>t\<^sub>p)"


subsubsection\<open>Time\<close>

text\<open>The time restriction predicate is similar to \<^term>\<open>Hoare_halt\<close>,
  but includes a maximum number of steps.
  From Hopcroft, p287f:
   "If for every input word of length n, M makes at most T(n) moves before
    halting, then M is said to be a T(n) time-bounded Turing machine, or of time
    complexity T(n). The language recognized by M is said to be of time complexity T(n)."

   "[...] it is reasonable to assume that any time complexity function \<open>T(n)\<close> is
    at least \<open>n + 1\<close>, for this is the time needed just to read the input and verify that the
    end has been reached by reading the first blank.\<dagger> We thus make the convention
    that "time complexity \<open>T(n)\<close>" means \<open>max (n + 1, \<lceil>T(n)\<rceil>])\<close>. For example, the value of
    time complexity \<open>n log\<^sub>2n\<close> at \<open>m = 1\<close> is \<open>2\<close>, not \<open>0\<close>, and at \<open>n = 2\<close>, its value is \<open>3\<close>.

    \<dagger> Note, however, that there are TM's that accept or reject without reading all their input.
      We choose to eliminate them from consideration."\<close>

abbreviation (input) tcomp :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat"
  where "tcomp T n \<equiv> max (n + 1) (T n)"

definition time_bounded :: "(nat \<Rightarrow> nat) \<Rightarrow> TM \<Rightarrow> bool"
  where "time_bounded T M \<equiv> \<forall>w. \<exists>n.
            n \<le> tcomp T (tape_size <w>\<^sub>t\<^sub>p)
          \<and> is_final (steps0 (1, <w>\<^sub>t\<^sub>p) M n)"

(* TODO (?) notation: \<open>p terminates_in_time T\<close> *)


lemma time_bounded_altdef:
  "time_bounded T M \<longleftrightarrow> (\<forall>w. is_final (steps0 (1, <w>\<^sub>t\<^sub>p) M (tcomp T (tape_size <w>\<^sub>t\<^sub>p))))"
  unfolding time_bounded_def using is_final by blast

lemma time_bounded_altdef':
  "time_bounded T M \<Longrightarrow> is_final (steps0 (1, <w>\<^sub>t\<^sub>p) M (tcomp T (tape_size <w>\<^sub>t\<^sub>p)))"
  using time_bounded_altdef by blast
  

text\<open>\<open>time\<^sub>M(x)\<close> is the number of steps until the computation of \<open>M\<close> halts on input \<open>x\<close>,
  or \<open>None\<close> if \<open>M\<close> does not halt on input \<open>x\<close>.\<close>

definition time :: "TM \<Rightarrow> tape \<Rightarrow> nat option"
  where "time M x \<equiv> (
    if \<exists>n. is_final (steps0 (1, x) M n)
      then Some (LEAST n. is_final (steps0 (1, x) M n))
      else None
    )"


text\<open>Notion of time-constructible from Hopcroft ch. 12.3, p. 299:
  "A function T(n) is said to be time constructible if there exists a T(n) time-
  bounded multitape Turing machine M such that for each n there exists some input
  on which M actually makes T(n) moves."\<close>

definition tconstr :: "(nat \<Rightarrow> nat) \<Rightarrow> bool"
  where "tconstr T \<equiv> \<exists>M. \<forall>n. \<exists>w. time M ([], w) = Some (T n)"

text\<open>Fully time-constructible, ibid.:
  "We say that T(n) is fully time-constructible if there is a TM
  that uses T(n) time on all inputs of length n."\<close>

definition fully_tconstr :: "(nat \<Rightarrow> nat) \<Rightarrow> bool"
  where "fully_tconstr T \<equiv> \<exists>M. \<forall>n w. length w = n \<longrightarrow> time M ([], w) = Some (T n)"

lemma ftc_altdef: "fully_tconstr T \<longleftrightarrow> (\<exists>M. \<forall>w. time M ([], w) = Some (T (length w)))"
  unfolding fully_tconstr_def by simp


lemma time_bounded_altdef2:
  "time_bounded T M \<longleftrightarrow> (\<forall>w. \<exists>n. time M <w>\<^sub>t\<^sub>p = Some n \<and> n \<le> tcomp T (tape_size <w>\<^sub>t\<^sub>p))"
  unfolding time_bounded_def (* in order for the intros to work in direction "\<Longleftarrow>" *) Let_def
proof (intro iffI allI exI conjI)
  fix w
  let ?f = "\<lambda>n. is_final (steps0 (1, <w>\<^sub>t\<^sub>p) M n)" let ?lf = "LEAST n. ?f n"
  let ?tcompT = "\<lambda>tp. tcomp T (tape_size tp)"

  assume (* time_bounded T p *) "\<forall>w. \<exists>n \<le> ?tcompT <w>\<^sub>t\<^sub>p. is_final (steps0 (1, <w>\<^sub>t\<^sub>p) M n)"
  then have n_ex: "\<exists>n. n \<le> ?tcompT <w>\<^sub>t\<^sub>p \<and> ?f n" ..
  then obtain n where "n \<le> ?tcompT <w>\<^sub>t\<^sub>p" and "?f n" by blast

  from n_ex have "\<exists>n. ?f n" by blast
  then show "time M <w>\<^sub>t\<^sub>p = Some ?lf" unfolding time_def by (rule if_P)
  have "?lf \<le> n" using Least_le \<open>?f n\<close> .
  also note \<open>n \<le> ?tcompT <w>\<^sub>t\<^sub>p\<close>
  finally show "?lf \<le> ?tcompT <w>\<^sub>t\<^sub>p" .
next
  fix w
  let ?f = "\<lambda>n. is_final (steps0 (1, <w>\<^sub>t\<^sub>p) M n)" let ?lf = "LEAST n. ?f n"
  let ?tcompT = "\<lambda>w. tcomp T (tape_size <w>\<^sub>t\<^sub>p)"

  assume "\<forall>w. \<exists>n. time M <w>\<^sub>t\<^sub>p = Some n \<and> n \<le> ?tcompT w"
  then obtain n where n_some: "time M <w>\<^sub>t\<^sub>p = Some n" and n_le: "n \<le> ?tcompT w" by blast

  from n_some have "time M <w>\<^sub>t\<^sub>p \<noteq> None" by (rule option.discI)
  then have n_ex: "\<exists>n. ?f n" unfolding time_def by argo
  with n_some have "?lf = n" unfolding time_def by simp

  show "?f ?lf" using LeastI_ex n_ex .
  show "?lf \<le> ?tcompT w" unfolding \<open>?lf = n\<close> using n_le .
qed

corollary "time_bounded T M \<Longrightarrow> the (time M <w>\<^sub>t\<^sub>p) \<le> tcomp T (tape_size <w>\<^sub>t\<^sub>p)"
  unfolding time_bounded_altdef2
proof (elim allE exE conjE)
  fix tp n
  assume some_n: "time M tp = Some n" and n_le: "n \<le> tcomp T (tape_size tp)"
  from n_le show "the (time M tp) \<le> tcomp T (tape_size tp)" unfolding some_n option.sel .
qed


subsubsection\<open>Space\<close>

(* implement adjustment similar to tcomp for space complexity. see Hopcroft p287 *)

(* size of tape after M does n steps on input x *)
abbreviation space0 where "space0 M x n \<equiv> let (_,tp) = steps0 (1, x) M n in tape_size tp"

definition space_restricted :: "(nat \<Rightarrow> nat) \<Rightarrow> TM \<Rightarrow> bool"
  where "space_restricted T M \<equiv> \<forall>x. \<forall>n. space0 M x n \<le> T(tape_size x)"

definition space :: "TM \<Rightarrow> tape \<Rightarrow> nat"
  where "space M x = Max {space0 M x n | n. n\<in>\<nat>}"


lemma update_space_one: "tape_size (update a (l,r)) \<le> 1 + tape_size (l,r)"
  by (induction a) simp_all
lemma update_space_le: "tape_size (l,r) \<le> tape_size(update a (l,r))"
  by (induction a) simp_all

lemma step_space_mono: "space0 M x n \<le> space0 M x (Suc n)"
  oops

lemma tape_size_mono: "n \<le> m \<Longrightarrow> space0 M x n \<le> space0 M x m"
  oops


subsection\<open>Deciding Languages\<close>

\<comment> \<open>Since \<open>L\<close> is a typical name for unspecified languages in the literature,
    the synonymous constructor \<^term>\<open>L\<close> of type \<^typ>\<open>action\<close> ("move head left") is hidden.\<close>
hide_const (open) L

text\<open>A TM \<^term>\<open>p\<close> is considered to decide a language \<^term>\<open>L\<close>, iff for every possible word \<^term>\<open>w\<close>
  it correctly calculates language membership.
  That is, for \<^term>\<open>w \<in> L\<close> the computation results in \<^term>\<open>Oc\<close> under the TM head,
  and for \<^term>\<open>w \<notin> L\<close> in \<^term>\<open>Bk\<close>.\<close>


definition halts :: "TM \<Rightarrow> word \<Rightarrow> bool"
  where "halts M w \<equiv> Hoare_halt (input w) M (\<lambda>_. True)"


lemma halts_time: "halts M w \<Longrightarrow> \<exists>n. time M <w>\<^sub>t\<^sub>p = Some n" unfolding halts_def Hoare_halt_def time_def by auto

lemma time_halts: "time M <w>\<^sub>t\<^sub>p = Some n \<Longrightarrow> halts M w" unfolding halts_def Hoare_halt_def
proof (intro allI impI exI conjI)
  fix tp
  assume "input w tp"
  then have "tp = <w>\<^sub>t\<^sub>p" .

  have if_h1: "(if P then a else b) = c \<Longrightarrow> b \<noteq> c \<Longrightarrow> P" for P and a b c :: 'a by argo
  assume assm: "time M <w>\<^sub>t\<^sub>p = Some n"
  then have ex_n: "\<exists>n. is_final (steps0 (1, <w>\<^sub>t\<^sub>p) M n)" unfolding time_def
    by (rule if_h1) (rule option.distinct(1))

  have if_h2: "(if P then a else b) = c \<Longrightarrow> b \<noteq> c \<Longrightarrow> a = c" for P and a b c :: 'a by argo
  from assm have "Some (LEAST n. is_final (steps0 (1, <w>\<^sub>t\<^sub>p) M n)) = Some n"
    unfolding time_def by (rule if_h2) (rule option.distinct(1))
  then have n: "n = (LEAST n. is_final (steps0 (1, <w>\<^sub>t\<^sub>p) M n))" by blast
  from ex_n show "is_final (steps0 (1, tp) M n)" unfolding n \<open>tp = <w>\<^sub>t\<^sub>p\<close> by (rule LeastI_ex)

  obtain s l r where split: "steps0 (1, tp) M n = (s, l, r)" by (rule prod_cases3)
  show "(\<lambda>_. True) holds_for steps0 (1, tp) M n" unfolding split holds_for.simps ..
qed

lemma halts_altdef: "halts M w \<longleftrightarrow> (\<exists>n. time M <w>\<^sub>t\<^sub>p = Some n)"
  using halts_time time_halts by blast


definition accepts :: "TM \<Rightarrow> word \<Rightarrow> bool"
  where "accepts M w \<equiv> Hoare_halt (input w) M (\<lambda>tp. head tp = Oc)"

definition rejects :: "TM \<Rightarrow> word \<Rightarrow> bool"
  where "rejects M w \<equiv> Hoare_halt (input w) M (\<lambda>tp. head tp = Bk)"

definition decides :: "TM \<Rightarrow> lang \<Rightarrow> bool"
  where "decides M L \<equiv> \<forall>w. (w \<in> L \<longleftrightarrow> accepts M w) \<and> (w \<notin> L \<longleftrightarrow> rejects M w)"


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

lemma decides_altdef2':
  "decides M L \<longleftrightarrow> (\<forall>w.
    Hoare_halt (input w) M (\<lambda>tp. head tp = Oc \<longleftrightarrow> w \<in> L)
  )"
proof -
  have *: "(a = Oc \<longleftrightarrow> c) \<longleftrightarrow> a = (if c then Oc else Bk)" for a c by (induction a) simp_all
  show ?thesis unfolding * by (rule decides_altdef2)
qed

(* TODO (?) notation: \<open>p decides L\<close> *)


subsection\<open>DTIME\<close>

text\<open>\<open>DTIME(T)\<close> is the set of languages decided by TMs in time \<open>T\<close> or less.\<close>
definition DTIME :: "(nat \<Rightarrow> nat) \<Rightarrow> lang set"
  where "DTIME T \<equiv> {L. \<exists>M. decides M L \<and> time_bounded T M}"

lemma in_dtimeI[intro]:
  assumes "decides M L"
    and "time_bounded T M"
  shows "L \<in> DTIME T"
  unfolding DTIME_def using assms by blast

lemma in_dtimeE[elim]:
  assumes "L \<in> DTIME T"
  obtains M
  where "decides M L"
    and "time_bounded T M"
  using assms unfolding DTIME_def by blast

lemma in_dtimeE'[elim]:
  assumes "L \<in> DTIME T"
  shows "\<exists>M. decides M L \<and> time_bounded T M"
  using assms unfolding DTIME_def ..


lemma tcomp_mono: "(\<And>n. T n \<ge> t n) \<Longrightarrow> tcomp T n \<ge> tcomp t n" by (intro max.mono) blast

lemma
  fixes T t
  assumes Tt: "\<And>n. T n \<ge> t n"
    and tr: "time_bounded t M"
  shows "time_bounded T M"
  unfolding time_bounded_def
proof (intro allI)
  fix w
  from tr obtain n where n_tcomp: "n \<le> tcomp t (tape_size <w>\<^sub>t\<^sub>p)"
                     and final_n: "is_final (steps0 (1, <w>\<^sub>t\<^sub>p) M n)"
    unfolding time_bounded_def by blast

  from le_trans n_tcomp tcomp_mono Tt have "n \<le> tcomp T (tape_size <w>\<^sub>t\<^sub>p)" .
  with final_n show "\<exists>n\<le>tcomp T (tape_size <w>\<^sub>t\<^sub>p). is_final (steps0 (1, <w>\<^sub>t\<^sub>p) M n)" by blast
qed


subsection\<open>Reductions\<close>

lemma simple_reduction:
  fixes A B :: lang 
    and f\<^sub>R :: "word \<Rightarrow> word" 
    and M\<^sub>R :: TM 
    and t\<^sub>R :: "nat \<Rightarrow> nat"
  assumes "\<And>w. w \<in> A \<longleftrightarrow> f\<^sub>R w \<in> B"
    and "\<And>w. length (f\<^sub>R w) \<le> length w"
    and "\<And>w. Hoare_halt (input w) M\<^sub>R (input (f\<^sub>R w))"
    and "tm_wf0 M\<^sub>R"
    and "time_bounded t\<^sub>R M\<^sub>R"
    and "B \<in> DTIME(t)"
  defines "T \<equiv> \<lambda>n. t n + t\<^sub>R n"
  shows "A \<in> DTIME(T)"
proof -
  from \<open>B \<in> DTIME t\<close> obtain M\<^sub>B
    where "decides M\<^sub>B B"
      and "time_bounded t M\<^sub>B" ..

  define M where "M \<equiv> M\<^sub>R |+| M\<^sub>B"

  {
    fix w
    note \<open>{input w} M\<^sub>R {input (f\<^sub>R w)}\<close>
    moreover from \<open>decides M\<^sub>B B\<close> have "{input (f\<^sub>R w)} M\<^sub>B {\<lambda>tp. (head tp = Oc) = (f\<^sub>R w \<in> B)}"
      unfolding decides_altdef2' ..
    moreover note \<open>tm_wf0 M\<^sub>R\<close>
    ultimately have "{input w} M\<^sub>R |+| M\<^sub>B {\<lambda>tp. (head tp = Oc) = (f\<^sub>R w \<in> B)}"
      by (rule Hoare_plus_halt)
    then have "{input w} M {\<lambda>tp. (head tp = Oc) = (w \<in> A)}" unfolding M_def \<open>w \<in> A \<longleftrightarrow> f\<^sub>R w \<in> B\<close> .
  }
  then have "decides M A" unfolding decides_altdef2' ..
  moreover have "time_bounded T M"
  proof -
    fix w
    define l where "l \<equiv> tape_size <w>\<^sub>t\<^sub>p"
      \<comment> \<open>Idea: Fix the input word \<^term>\<open>w\<close>.
        We already know that the first machine \<^term>\<open>M\<^sub>R\<close> is time bounded
        (@{thm \<open>time_bounded t\<^sub>R M\<^sub>R\<close>}),
        such that its run-time will be no longer than \<^term>\<open>t\<^sub>R l = t\<^sub>R (2 * length w)\<close>
        (times two due to the encoding \<^const>\<open>encode_word\<close>).

        We also know that it will result in the encoded corresponding input word
        with regards to \<open>B\<close> (@{thm \<open>\<And>w. {input w} M\<^sub>R {input (f\<^sub>R w)}\<close>}).
        Since the length of the corresponding input word is no longer
        than the length of the original input word \<^term>\<open>w\<close> (@{thm \<open>\<And>w. length (f\<^sub>R w) \<le> length w\<close>}),
        and the second machine \<^term>\<open>M\<^sub>B\<close> is time bounded (@{thm \<open>time_bounded t M\<^sub>B\<close>}),
        we may conclude that the run-time of \<^term>\<open>M \<equiv> M\<^sub>R |+| M\<^sub>B\<close> on the input \<^term>\<open><w>\<^sub>t\<^sub>p\<close>
        is no longer than \<^term>\<open>T l \<equiv> t l + t\<^sub>R l\<close>.

        \<^const>\<open>time_bounded\<close> is defined in terms of \<^const>\<open>tcomp\<close>, however,
        which means that the resulting total run time \<^term>\<open>T l\<close> may be as large as
        \<^term>\<open>tcomp t l + tcomp t\<^sub>R l \<equiv> max (l + 1) (t l) + max (l + 1) (t\<^sub>R l)\<close>.\<close>

    show ?thesis sorry
  qed
  ultimately show "A \<in> DTIME T" ..
qed


end