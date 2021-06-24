theory complexity
  imports Main gn "Universal_Turing_Machine.UTM"
begin

subsection\<open>Termination\<close>

text\<open>The tape size can not use the universal function \<^term>\<open>size\<close>, since for any pair \<^term>\<open>p = (a, b)\<close>, \<^term>\<open>size p = 1\<close>.\<close>
fun tape_size :: "tape \<Rightarrow> nat" \<comment> \<open>using \<open>fun\<close> since \<open>definition\<close> does not recognize patterns like \<^term>\<open>(l, r)\<close>\<close>
  where "tape_size (l, r) = length l + length r"

text\<open>The time restriction predicate is similar to \<^term>\<open>Hoare_halt\<close>, but includes a maximum number of steps.\<close>
definition time_restricted :: "(nat \<Rightarrow> nat) \<Rightarrow> tprog0 \<Rightarrow> bool"
  where "time_restricted T p \<equiv> \<forall>tp. \<exists>n.
            n \<le> T (tape_size tp)
          \<and> is_final (steps0 (1, tp) p n)"

(* TODO (?) notation: \<open>p terminates_in_time T\<close> *)

text\<open>\<open>time\<^sub>M(x)\<close> is the number of steps until the computation of \<open>M\<close> halts on input \<open>x\<close>\<close>
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


subsection\<open>Encoding Words\<close>

text\<open>Encoding binary words as TM tape cells: \<^term>\<open>Num.Bit1\<close> is encoded as \<^term>\<open>[Oc, Oc]\<close> and \<^term>\<open>Num.Bit1\<close> as term>\<open>[Oc, Bk]\<close>.
  Thus, the ends of an encoded term can be marked with the pattern \<^term>\<open>[Bk, Bk]\<close>.\<close>
fun encode_word :: "word \<Rightarrow> cell list"
  where "encode_word Num.One = []"
      | "encode_word (Num.Bit0 w) = Oc # Bk # encode_word w"
      | "encode_word (Num.Bit1 w) = Oc # Oc # encode_word w"

fun is_encoded_word :: "cell list \<Rightarrow> bool"
  where "is_encoded_word [] = True"
      | "is_encoded_word (Oc # _ # cs) = is_encoded_word cs"
      | "is_encoded_word _ = False"

fun decode_word :: "cell list \<Rightarrow> word"
  where "decode_word (Oc # Bk # cs) = Num.Bit0 (decode_word cs)"
      | "decode_word (Oc # Oc # cs) = Num.Bit1 (decode_word cs)"
      | "decode_word _ = Num.One"


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

definition halts_for :: "tprog0 \<Rightarrow> word \<Rightarrow> bool"
  where "halts_for M w \<equiv> Hoare_halt (\<lambda>tp. tp = ([], encode_word w)) M (\<lambda>_. True)"

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

definition accepts :: "tprog0 \<Rightarrow> word \<Rightarrow> bool"
  where "accepts M w \<equiv> Hoare_halt (input w) M (\<lambda>tp. head tp = Oc)"

definition rejects :: "tprog0 \<Rightarrow> word \<Rightarrow> bool"
  where "rejects M w \<equiv> Hoare_halt (input w) M (\<lambda>tp. head tp = Bk)"

definition decides :: "lang \<Rightarrow> tprog0 \<Rightarrow> bool"
  where "decides L M \<equiv> \<forall>w. (w \<in> L \<longleftrightarrow> accepts M w) \<and> (w \<notin> L \<longleftrightarrow> rejects M w)"


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
  obtain s l r where c: "c = (s, l, r)" by (rule prod_cases3)
  from c P have "P (l, r)" by simp
  moreover from c Q have "Q (l, r)" by simp
  ultimately show ?thesis unfolding c by simp
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

lemma hoare_and_neg: (*probably not useful but somewhat nice?*)
  assumes "Hoare_halt P M Q"
    and "\<not> Hoare_halt P M S"
  obtains tp where "Q tp \<and> \<not> S tp"
proof -
  from assms(2) obtain tp where "P tp"
    and 1: "(\<forall>n. \<not> is_final (steps0 (1, tp) M n) \<or> ~ (S holds_for steps0 (1, tp) M n))"
    unfolding Hoare_halt_def by auto
  from assms(1) obtain n 
    where 2: "is_final (steps0 (1, tp) M n)" 
      and 3: "Q holds_for steps0 (1, tp) M n"
    unfolding Hoare_halt_def using \<open>P tp\<close> by blast

  obtain s l r where split: "steps0 (1, tp) M n = (s, l, r)" by (rule prod_cases3)
  from 1 2 have "\<not> S holds_for steps0 (1, tp) M n" by blast
  with 3 show ?thesis unfolding split holds_for.simps by (intro that conjI)
qed

lemma holds_for_neg: "\<not> Q holds_for c \<longleftrightarrow> (\<lambda>tp. \<not> Q tp) holds_for c"
proof -
  obtain s l r where c: "c = (s, l, r)" by (rule prod_cases3)
  show ?thesis unfolding c by simp
qed

lemma hoare_halt_neg:
  assumes "\<not> Hoare_halt (input w) M Q"
    and "halts_for M w"
  shows "Hoare_halt (input w) M (\<lambda>tp. \<not> Q tp)"
  using assms unfolding Hoare_halt_def holds_for_neg[symmetric] halts_for_def by fast

lemma acc_not_rej:
  assumes "accepts M w"
  shows "\<not> rejects M w"
proof (intro notI)
  assume "rejects M w"
  have *: "a = Oc \<and> a = Bk \<longleftrightarrow> False" for a::cell by blast

  have "Hoare_halt (input w) M (\<lambda>tp. head tp = Oc)"
    using \<open>accepts M w\<close> unfolding accepts_def .
  moreover have "Hoare_halt (input w) M (\<lambda>tp. head tp = Bk)"
    using \<open>rejects M w\<close> unfolding rejects_def .
  ultimately have "Hoare_halt (input w) M (\<lambda>tp. head tp = Oc \<and> head tp = Bk)"
    by (rule hoare_and)

  then have "Hoare_halt (input w) M (\<lambda>_. False)" unfolding * .
  then show "False" by (intro hoare_contr) blast+
qed

lemma rejects_altdef:
  "rejects M w = (halts_for M w \<and> \<not> accepts M w)"
proof (intro iffI conjI)
  assume "rejects M w"
  then show "halts_for M w" unfolding rejects_def halts_for_def using hoare_true by simp
  assume "rejects M w"
  then show "\<not> accepts M w" using acc_not_rej by auto
next
  have *: "c \<noteq> Oc \<longleftrightarrow> c = Bk" for c by (cases c) blast+

  assume "halts_for M w \<and> \<not> accepts M w"
  then have "Hoare_halt (input w) M (\<lambda>tp. head tp \<noteq> Oc)"
    unfolding accepts_def by (intro hoare_halt_neg) blast+
  then show "rejects M w" unfolding rejects_def * .
qed

lemma decides_altdef:
  "decides L p \<longleftrightarrow> (\<forall>w. Hoare_halt
    (\<lambda>tp. tp = ([], encode_word w)) p (\<lambda>tp. read (snd tp) = (if w \<in> L then Oc else Bk)))"
  (is "decides L p \<longleftrightarrow> (\<forall>w. Hoare_halt (?l w) p (?r w))")
  oops

(* TODO (?) notation: \<open>p decides L\<close> *)


subsection\<open>DTIME\<close>

text\<open>\<open>DTIME(T)\<close> is the set of languages decided by TMs in time \<open>T\<close> or less.\<close>
definition DTIME :: "(nat \<Rightarrow> nat) \<Rightarrow> lang set"
  where "DTIME T \<equiv> {L. \<exists>p. decides L p \<and> time_restricted T p}"

lemma in_dtimeI[intro]:
  assumes "decides L p"
    and "time_restricted T p"
  shows "L \<in> DTIME T"
  unfolding DTIME_def using assms by blast

lemma in_dtimeE[elim]:
  assumes "L \<in> DTIME T"
  obtains p
  where "decides L p" 
    and "time_restricted T p"
  using assms unfolding DTIME_def by blast

lemma in_dtimeE'[elim]:
  assumes "L \<in> DTIME T"
  shows "\<exists>p. decides L p \<and> time_restricted T p"
  using assms unfolding DTIME_def ..


subsection\<open>Encoding TMs\<close>

\<comment> \<open>An issue of the following definitions is that the existing definition \<^term>\<open>code\<close>
  uses a naive Gödel numbering scheme that includes encoding list items as prime powers,
  where each "next prime" \<^term>\<open>Np p\<close> is defined as \<^term>\<open>p! + 1\<close>
  (see \<^term>\<open>godel_code'\<close>, \<^term>\<open>Pi\<close>, and \<^term>\<open>Np\<close>).\<close>

definition is_encoded_TM :: "word \<Rightarrow> bool"
  where "is_encoded_TM w = (\<exists>M. code M = gn w)"

definition decode_TM :: "word \<Rightarrow> tprog0"
  where "decode_TM w = (THE M. code M = gn w)"

definition Rejecting_TM :: tprog0
  where "Rejecting_TM = [(W0, 0), (W0, 0)]"

definition read_TM :: "word \<Rightarrow> tprog0"
  where "read_TM w = (if is_encoded_TM w then decode_TM w else Rejecting_TM)"

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


end