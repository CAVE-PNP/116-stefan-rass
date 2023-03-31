section\<open>Complexity\<close>

text\<open>Definitions and lemmas from computational complexity theory.\<close>

theory Complexity
  imports TM_Hoare Goedel_Numbering
    "Supplementary/Asymptotic"
begin

subsection\<open>Time\<close>

text\<open>The time restriction predicate is similar to \<^term>\<open>Hoare_halt\<close>,
  but includes a maximum number of steps.
  From @{cite \<open>ch.~12.1\<close> hopcroftAutomata1979}:
  ``If for every input word of length n, M makes at most T(n) moves before
    halting, then M is said to be a T(n) time-bounded Turing machine, or of time
    complexity T(n). The language recognized by M is said to be of time complexity T(n).''\<close>

context TM
begin

definition "config_time c \<equiv> LEAST n. is_final (steps n c)"

lemma steps_conf_time[intro, simp]:
  assumes "is_final (steps n c)"
  shows "steps (config_time c) c = steps n c"
proof -
  from assms have "is_final (steps (config_time c) c)" unfolding config_time_def by (rule LeastI)
  then show ?thesis using assms by (rule final_steps_rev)
qed

lemma conf_time_lessD[dest, elim]: "n < config_time c \<Longrightarrow> \<not> is_final (steps n c)"
  unfolding config_time_def by (rule not_less_Least)

lemma conf_time_geD[dest, elim]:
  assumes "n \<ge> config_time c"
    and "halts_config c"
  shows "is_final (steps n c)"
proof -
  from assms(2) have "is_final (steps (LEAST n. is_final (steps n c)) c)"
    unfolding halts_config_def by (rule LeastI_ex)
  with assms(1) show ?thesis unfolding config_time_def by blast
qed

lemma conf_time_leI[intro]: "is_final (steps n c) \<Longrightarrow> config_time c \<le> n"
  unfolding config_time_def run_def by (fact Least_le)

lemma conf_time_le_iff[intro]: "halts_config c \<Longrightarrow> is_final (steps n c) \<longleftrightarrow> config_time c \<le> n"
  by blast

lemma conf_time_gt_rev[intro]: "halts_config c \<Longrightarrow> \<not> is_final (steps n c) \<Longrightarrow> config_time c > n"
  by (subst (asm) conf_time_le_iff) auto

lemma conf_time_finalI[intro]: "halts_config c \<Longrightarrow> is_final (steps (config_time c) c)"
  using conf_time_le_iff by blast

lemma conf_time0[simp, intro]: "is_final c \<Longrightarrow> config_time c = 0" unfolding config_time_def by simp


lemma final_steps_config_time[dest]: "is_final (steps n c) \<Longrightarrow> steps n c = steps (config_time c) c" by simp

lemma conf_time_steps_finalI: "\<exists>n. is_final (steps n c) \<and> P (steps n c) \<Longrightarrow>
  is_final (steps (config_time c) c) \<and> P (steps (config_time c) c)" by force

lemma conf_time_steps_final_iff:
  "(\<exists>n. is_final (steps n c) \<and> P (steps n c)) \<longleftrightarrow>
  (is_final (steps (config_time c) c) \<and> P (steps (config_time c) c))"
  by (intro iffI conf_time_steps_finalI) blast+


definition "time w \<equiv> config_time (initial_config w)"
declare (in -) TM.time_def[simp]

lemma time_altdef: "time w = (LEAST n. is_final (run n w))"
  unfolding TM.run_def using config_time_def by simp

lemma compute_altdef[simp, intro]: "compute w = run (time w) w"
  unfolding compute_altdef2 time_altdef ..

lemma time_leI[intro]: "is_final (run n w) \<Longrightarrow> time w \<le> n"
  unfolding run_def time_def by (rule conf_time_leI)

lemma run_time_halts[dest]: "halts w \<Longrightarrow> is_final (run (time w) w)" unfolding halts_def by auto

lemma config_time_offset:
  fixes c0
  defines "n \<equiv> config_time c0"
  assumes "halts_config c0"
  shows "config_time (steps n1 c0) = n - n1"
proof (cases "is_final (steps n1 c0)")
  assume f: "is_final (steps n1 c0)"
  then have "n1 \<ge> n" unfolding n_def by blast
  with f show ?thesis unfolding n_def by simp
next
  assume nf: "\<not> is_final (steps n1 c0)"

  let ?N = "{n2. is_final (steps n2 (steps n1 c0))}"

  have "{n. is_final (steps n c0)} = {n. \<exists>n2. n = n1 + n2 \<and> is_final (steps n2 (steps n1 c0))}"
    (is "{n. ?lhs n} = {n. ?rhs n}")
  proof (rule sym, intro Collect_eqI iffI)
    fix n assume "?lhs n"
    with nf have "n > n1" by blast
    then have "\<exists>n2. n = n1 + n2" by (intro le_Suc_ex less_imp_le_nat)
    then obtain n2 where "n = n1 + n2" ..
    from \<open>?lhs n\<close> have "is_final (steps n2 (steps n1 c0))" unfolding \<open>n = n1 + n2\<close> by simp
    with \<open>n = n1 + n2\<close> show "?rhs n" by blast
  next
    fix n assume "?rhs n"
    then obtain n2 where "n = n1 + n2" and "is_final (steps n2 (steps n1 c0))" by blast
    then show "?lhs n" by simp
  qed
  then have *: "{n. is_final (steps n c0)} = (\<lambda>n2. n1 + n2) ` ?N" unfolding image_Collect .

  have "n = (LEAST n. is_final (steps n c0))" unfolding n_def config_time_def ..
  also have "... = (LEAST n. n \<in> {n. is_final (steps n c0)})" by simp
  also have "... = n1 + (LEAST n. is_final (steps n (steps n1 c0)))" unfolding *
  proof (subst Least_mono, unfold mem_Collect_eq)
    show "mono (\<lambda>n2. n1 + n2)" by (intro monoI add_left_mono)

    let ?n = "config_time c0" let ?n2 = "?n - n1"
    have *: "x \<in> ?N \<longleftrightarrow> x \<ge> ?n2" for x
      unfolding mem_Collect_eq steps_plus le_diff_conv add.commute[of x n1]
      using \<open>halts_config c0\<close> by (fact conf_time_le_iff)
    then show "\<exists>n\<in>?N. \<forall>n'\<in>?N. n \<le> n'" by blast
  qed blast
  also have "... = n1 + config_time (steps n1 c0)" unfolding config_time_def ..
  finally show ?thesis by presburger
qed


lemma config_time_eqI[intro]:
  assumes "TM.halts_config M1 c1"
    and "\<And>n. TM.is_final M1 (TM.steps M1 (n1 + n) c1) \<longleftrightarrow> TM.is_final M2 (TM.steps M2 n c2)"
  shows "TM.config_time M1 c1 - n1 = TM.config_time M2 c2"
proof -
  from \<open>TM.halts_config M1 c1\<close> have "TM.config_time M1 c1 - n1 = TM.config_time M1 (TM.steps M1 n1 c1)"
    by (subst TM.config_time_offset) auto
  also have "... = TM.config_time M2 c2" unfolding TM.config_time_def TM.steps_plus unfolding assms ..
  finally show ?thesis .
qed

lemma time_eqI[intro]:
  assumes "TM.halts M1 w1"
    and "\<And>n. TM.is_final M1 (TM.run M1 (n1 + n) w1) \<longleftrightarrow> TM.is_final M2 (TM.run M2 n w2)"
  shows "TM.time M1 w1 - n1 = TM.time M2 w2"
  using assms unfolding TM.time_def TM.run_def TM.halts_def by (fact config_time_eqI)


lemma (in Rej_TM) rej_tm_time: "time w = 0" by (simp add: is_final_def)

end \<comment> \<open>context \<^locale>\<open>TM\<close>\<close>


subsubsection\<open>Time Function Wrapper\<close>

text\<open>From @{cite \<open>ch.~12.1\<close> hopcroftAutomata1979}:
  ``[...] it is reasonable to assume that any time complexity function \<open>T(n)\<close> is
    at least \<open>n + 1\<close>, for this is the time needed just to read the input and verify that the
    end has been reached by reading the first blank.* We thus make the convention
    that `time complexity \<open>T(n)\<close>' means \<open>max (n + 1, \<lceil>T(n)\<rceil>])\<close>. For example, the value of
    time complexity \<open>n log\<^sub>2n\<close> at \<open>m = 1\<close> is \<open>2\<close>, not \<open>0\<close>, and at \<open>n = 2\<close>, its value is \<open>3\<close>.

    * Note, however, that there are TM's that accept or reject without reading all their input.
      We choose to eliminate them from consideration.''\<close>

definition tcomp :: "('c::semiring_1 \<Rightarrow> 'd::floor_ceiling) \<Rightarrow> nat \<Rightarrow> nat"
  where "tcomp T n \<equiv> max (n + 1) (nat \<lceil>T (of_nat n)\<rceil>)"

abbreviation (input) tcomp\<^sub>w :: "('c::semiring_1 \<Rightarrow> 'd::floor_ceiling) \<Rightarrow> 's list \<Rightarrow> nat"
  where "tcomp\<^sub>w T w \<equiv> tcomp T (length w)"


lemma tcomp_min: "tcomp f n \<ge> n + 1" by (simp add: tcomp_def)

lemma tcomp_of_nat:
  shows "tcomp (\<lambda>x. of_nat (f x)) = tcomp f"
    and "tcomp (\<lambda>n. f (of_nat n)) = tcomp f"
    and "tcomp (\<lambda>x. of_nat (f (of_nat x))) = tcomp f"
  unfolding tcomp_def of_nat_id by simp_all


lemma tcomp_nat_simps[simp]:
  fixes f :: "nat \<Rightarrow> nat"
  shows "tcomp f n = max (n + 1) (f n)"
    and "tcomp (\<lambda>n. of_nat (f n)) n = max (n + 1) (f n)"
  by (simp_all add: tcomp_def)

lemma tcomp_nat_id[simp]:
  fixes f :: "nat \<Rightarrow> nat"
  shows "(\<And>n. f n \<ge> n + 1) \<Longrightarrow> tcomp f = f"
  by (intro ext) (unfold tcomp_nat_simps, rule max_absorb2)

lemma tcomp_nat_mono[intro]:
  fixes T t :: "nat \<Rightarrow> 'd::floor_ceiling"
  shows "T n \<ge> t n \<Longrightarrow> tcomp T n \<ge> tcomp t n"
  unfolding Let_def of_nat_id tcomp_def
  by (intro nat_mono max.mono of_nat_mono add_right_mono ceiling_mono le_refl)

lemma tcomp_mono[intro]:
  fixes T t :: "'c::semiring_1 \<Rightarrow> 'd::floor_ceiling"
  assumes Tt: "T (of_nat n) \<ge> t (of_nat n)"
  shows "tcomp T n \<ge> tcomp t n"
proof -
  have "tcomp (\<lambda>n. T (of_nat n)) n \<ge> tcomp (\<lambda>n. t (of_nat n)) n"
    by (rule tcomp_nat_mono) (rule Tt)
  then show "tcomp T n \<ge> tcomp t n" unfolding tcomp_def of_nat_id .
qed

lemma tcomp_mono':
  fixes T t :: "'c::semiring_1 \<Rightarrow> 'd::floor_ceiling"
  assumes Tt: "\<And>x. T x \<ge> t x"
  shows "tcomp T n \<ge> tcomp t n"
proof -
  have "tcomp (\<lambda>n. T (of_nat n)) n \<ge> tcomp (\<lambda>n. t (of_nat n)) n"
    by (rule tcomp_nat_mono) (rule Tt)
  then show "tcomp T n \<ge> tcomp t n" unfolding tcomp_def of_nat_id .
qed

lemma
  fixes T :: "'c::semiring_1 \<Rightarrow> 'd::floor_ceiling"
  shows tcomp_altdef1: "nat (max (\<lceil>n\<rceil> + 1) \<lceil>T (of_nat n)\<rceil>) = tcomp T n" (is "?def1 = tcomp T n")
    and tcomp_altdef2: "nat (max \<lceil> n + 1 \<rceil> \<lceil>T (of_nat n)\<rceil>) = tcomp T n" (is "?def2 = tcomp T n")
proof -
  let ?n = "of_nat n"
  have h1: "\<lceil> n + 1 \<rceil> = \<lceil>n\<rceil> + 1" unfolding ceiling_of_nat by force
  have h2: "nat (\<lceil>n\<rceil> + 1) = n + 1" by (fold h1, unfold ceiling_of_nat) (fact nat_int)
  have h3: "nat (\<lceil>n\<rceil> + 1) \<le> nat \<lceil>T ?n\<rceil> \<longleftrightarrow> \<lceil>n\<rceil> + 1 \<le> \<lceil>T ?n\<rceil>" by (rule nat_le_eq_zle) simp

  have "tcomp T n = max (nat (\<lceil>n\<rceil> + 1)) (nat \<lceil>T ?n\<rceil>)" unfolding h2 of_nat_id tcomp_def ..
  also have "... = ?def1" unfolding max_def if_distrib[of nat] h3 ..
  finally show "?def1 = tcomp T n" ..
  then show "?def2 = tcomp T n" unfolding h1 .
qed

lemma tcomp_tcomp[simp]: "tcomp (tcomp f) = tcomp f" unfolding tcomp_def
  unfolding of_nat_id ceiling_of_nat nat_int max.left_idem ..


lemma less_max_self:
  fixes x :: "'a :: linorder"
  shows "x < max x y \<Longrightarrow> max x y = y"
  unfolding less_max_iff_disj by simp

lemma superlinear_tcomp_simp[dest?]:
  fixes f :: "'a :: semiring_1 \<Rightarrow> 'b :: floor_ceiling"
  assumes "superlinear (tcomp f)"
  shows "\<forall>\<^sub>\<infinity>n. tcomp f n = nat \<lceil>f (of_nat n)\<rceil>"
  using assms unfolding superlinear_altdef_nat
proof (elim allE, ae_nat_elim)
  fix n :: nat
  assume "2 \<le> n"
  then have "n + 1 < 2 * n" by simp
  also assume "2 * n \<le> tcomp f n"
  finally show "tcomp f n = nat \<lceil>f (of_nat n)\<rceil>"
    unfolding tcomp_def of_nat_id by (fact less_max_self)
qed

lemma ceil_m1_le_floor: "\<lceil>x\<rceil> - 1 \<le> \<lfloor>x\<rfloor>" using ceiling_diff_floor_le_1[of x] by simp

lemma superlinear_tcomp:
  fixes f :: "'a :: {linorder,semiring_1} \<Rightarrow> 'b :: floor_ceiling"
  assumes "superlinear (tcomp f)"
  shows "superlinear f"
proof -
  from assms have "\<forall>\<^sub>\<infinity>n. tcomp f n = nat \<lceil>f (of_nat n)\<rceil>" ..
  with assms show ?thesis unfolding superlinear_def of_nat_id
  proof (intro allI, elim allE, ae_nat_elim)
    fix C n :: nat
    assume "n \<ge> 1"
    then have "C * n + 1 \<le> (C + 1) * n" by simp
    also assume "(C + 1) * n \<le> tcomp f n"
    also assume "tcomp f n = nat \<lceil>f (of_nat n)\<rceil>"
    finally have "of_nat (C * n) + 1 \<le> \<lceil>f (of_nat n)\<rceil>" by linarith
    then have "of_nat (C * n) \<le> \<lceil>f (of_nat n)\<rceil> - 1" by (fact add_le_imp_le_diff)
    also have "... \<le> \<lfloor>f (of_nat n)\<rfloor>" by (fact ceil_m1_le_floor)
    finally show "of_nat (C * n) \<le> f (of_nat n)" unfolding le_floor_iff of_int_of_nat_eq .
  qed
qed

lemma superlinear_tcomp_iff[iff]: "superlinear (tcomp f) \<longleftrightarrow> superlinear f"
proof (intro iffI)
  show "superlinear f \<Longrightarrow> superlinear (tcomp f)" unfolding superlinear_def of_nat_id
  proof (intro allI, elim allE, ae_nat_elim)
    fix C n :: nat
    assume "of_nat (C * n) \<le> f (of_nat n)"
    also have "... \<le> of_int \<lceil>f (of_nat n)\<rceil>" by (fact le_of_int_ceiling)
    also have "... = of_nat (nat \<lceil>f (of_nat n)\<rceil>)"
    proof (intro of_nat_nat[symmetric])
      note of_nat_0_le_iff
      also note \<open>of_nat (C * n) \<le> f (of_nat n)\<close>
      also note \<open>f (of_nat n) \<le> of_int \<lceil>f (of_nat n)\<rceil>\<close>
      finally show "0 \<le> \<lceil>f (of_nat n)\<rceil>" by simp
    qed
    finally show "C * n \<le> tcomp f n" unfolding of_nat_le_iff tcomp_def by (fact max.coboundedI2)
  qed
qed \<comment> \<open>direction \<open>\<Longrightarrow>\<close> by\<close> (fact superlinear_tcomp)


subsubsection\<open>Time-Bounded Execution\<close>

text\<open>Predicates to verify that TMs halt within a given time-bound.\<close>

context TM begin

(* TODO extract general version \<open>halts_within n w \<equiv> is_final (run n w)\<close> (maybe abbrev?) *)
definition time_bounded_word :: "(nat \<Rightarrow> nat) \<Rightarrow> 's list \<Rightarrow> bool"
  where "time_bounded_word T w \<equiv> is_final (run (T (length w)) w)"

abbreviation time_bounded :: "(nat \<Rightarrow> nat) \<Rightarrow> bool"
  where "time_bounded T \<equiv> \<forall>w. time_bounded_word T w"

lemmas time_bounded_def = time_bounded_word_def


mk_ide time_bounded_word_def |intro time_bounded_wordI[intro]| |dest time_bounded_wordD[dest]|

lemma time_bounded_word_mono[dest]:
  "time_bounded_word t w \<Longrightarrow> t (length w) \<le> T (length w) \<Longrightarrow> time_bounded_word T w" by blast

lemma time_bounded_mono: "time_bounded t \<Longrightarrow> (\<And>x. t x \<le> T x) \<Longrightarrow> time_bounded T" by blast

lemma time_bounded_altdef2: "time_bounded T \<longleftrightarrow> (\<forall>w. halts w \<and> time w \<le> T (length w))" by blast

end \<comment> \<open>context \<^locale>\<open>TM\<close>\<close>


subsection\<open>Time-Constructibility\<close>

text\<open>Notion of time-constructible from @{cite \<open>ch.~12.3\<close> hopcroftAutomata1979}:
  ``A function T(n) is said to be time constructible if there exists a T(n) time-
  bounded multi-tape Turing machine M such that for each n there exists some input
  on which M actually makes T(n) moves.''\<close>

(* TODO this is getting ridiculous. find a more elegant solution *)
definition typed_time_constr :: "'q itself \<Rightarrow> 's itself \<Rightarrow> 'l itself \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> bool"
  where "typed_time_constr TYPE('q) TYPE('s) TYPE('l) T \<equiv> \<exists>M::('q, 's, 'l) TM. \<forall>n. \<exists>w. TM.time M w = T n"

abbreviation "time_constr \<equiv> typed_time_constr TYPE(nat) TYPE(nat) TYPE(unit)"


text\<open>Fully time-constructible, (@{cite \<open>ch.~12.3\<close> hopcroftAutomata1979}):
  ``We say that T(n) is fully time-constructible if there is a TM
  that uses T(n) time on all inputs of length n.''\<close>

definition typed_fully_time_constr :: "'q itself \<Rightarrow> 's itself \<Rightarrow> 'l itself \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> bool"
  where "typed_fully_time_constr TYPE('q) TYPE('s) TYPE('l) T \<equiv> \<exists>M::('q, 's, 'l) TM. \<forall>w. TM.time M w = T (length w)"

abbreviation "fully_time_constr \<equiv> typed_fully_time_constr TYPE(nat) TYPE(nat) TYPE(unit)"


corollary fully_imp_time_constr:
  assumes "typed_fully_time_constr TYPE('q) TYPE('s) TYPE('l) T"
  shows "typed_time_constr TYPE('q) TYPE('s) TYPE('l) T"
proof -
  from assms obtain M :: "('q, 's, 'l) TM" where *: "TM.time M w = T (length w)" for w
    unfolding typed_fully_time_constr_def by blast
  then show ?thesis unfolding typed_time_constr_def
  proof (intro exI allI)
    fix n
    let ?w = "undefined \<up> n" \<comment> \<open>@{thm Ex_list_of_length}\<close>
    show "TM.time M ?w = T n" unfolding * by simp
  qed
qed


definition typed_computable_in_time :: "'q itself \<Rightarrow> 'l itself \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> ('s list \<Rightarrow> 's list) \<Rightarrow> bool"
  where "typed_computable_in_time TYPE('q) TYPE('l) T f \<equiv> \<exists>M::('q, 's, 'l) TM. TM.computes M f \<and> TM.time_bounded M T"

abbreviation "computable_in_time \<equiv> typed_computable_in_time TYPE(nat) TYPE(unit)"

lemma computableE[elim]:
  assumes "typed_computable_in_time TYPE('q) TYPE('l) T f"
  obtains M::"('q, 's, 'l) TM" where "TM.computes M f" and "TM.time_bounded M T"
using assms that unfolding typed_computable_in_time_def by blast


subsection\<open>DTIME\<close>

text\<open>\<open>DTIME(T)\<close> is the set of languages decided by TMs in time \<open>T\<close> or less.\<close>
definition typed_DTIME :: "'q itself \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> 's lang set"
  where "typed_DTIME TYPE('q) T \<equiv> {L. \<exists>M::('q, 's) TM_decider. TM_decider.decides M L \<and> TM.time_bounded M T}"


abbreviation DTIME where
  "DTIME \<equiv> typed_DTIME TYPE(nat)"

lemma in_dtimeI[intro]:
  fixes M :: "('q, 's) TM_decider"
  assumes "alphabet L \<subseteq> TM.\<Sigma> M"
    and "TM_decider.decides M L"
    and "TM.time_bounded M T"
  shows "L \<in> typed_DTIME TYPE('q) T"
  unfolding typed_DTIME_def using assms by blast

lemma in_dtimeE[elim]:
  assumes "L \<in> typed_DTIME TYPE('q) T"
  obtains M :: "('q, 's) TM_decider"
  where "alphabet L \<subseteq> TM.symbols M"
    and "TM_decider.decides M L"
    and "TM.time_bounded M T"
  using assms unfolding typed_DTIME_def by blast


lemma in_dtimeD[dest]:
  fixes L :: "'s lang"
  assumes "L \<in> typed_DTIME TYPE('q) T"
  shows "\<exists>M::('q, 's) TM_decider. TM_decider.decides M L \<and> TM.time_bounded M T"
  using assms unfolding typed_DTIME_def ..

corollary in_dtime_mono[dest]:
  fixes T t
  assumes "L \<in> typed_DTIME TYPE('q) t"
    and "\<And>n. t n \<le> T n"
  shows "L \<in> typed_DTIME TYPE('q) T"
  using assms TM.time_bounded_mono by (elim in_dtimeE, intro in_dtimeI) blast+


subsection\<open>Classical Results\<close>

subsubsection\<open>Almost Everywhere\<close>

text\<open>@{cite \<open>ch.~12.2\<close> hopcroftAutomata1979} uses the finite control in Lemma 12.3
  to make the jump from almost everywhere to everywhere:

  ``We say that a statement with parameter \<open>n\<close> is true \<^emph>\<open>almost everywhere\<close> (a.e.) if it
  is true for all but a finite number of values of \<open>n\<close>. We say a statement is true infinitely
  often (i.o.) if it is true for an infinite number of \<open>n\<close>'s. Note that both a statement and
  its negation may be true i.o.''\<close>

text\<open>From @{cite \<open>ch.~12.2\<close> hopcroftAutomata1979}:

  ``\<^bold>\<open>Lemma 12.3\<close>  If \<open>L\<close> is accepted by a TM \<open>M\<close> that is \<open>S(n)\<close> space bounded a.e., then \<open>L\<close> is
  accepted by an \<open>S(n)\<close> space-bounded TM.
  Proof  Use the finite control to accept or reject strings of length \<open>n\<close> for the finite
  number of \<open>n\<close> where \<open>M\<close> is not \<open>S(n)\<close> bounded. Note that the construction is not
  effective, since in the absence of a time bound we cannot tell which of these words
  \<open>M\<close> accepts.''

  The lemma is only stated for space bounds,
  but it seems reasonable that a similar construction works on time bounds.\<close>

lemma DTIME_ae:
  assumes "\<exists>M::('q, 's) TM_decider. alphabet L \<subseteq> TM.symbols M \<and>
    (\<forall>\<^sub>\<infinity>w\<in>(alphabet L)*. TM_decider.decides_word M L w \<and> TM.time_bounded_word M T w)"
  shows "L \<in> typed_DTIME TYPE('q) T"
  sorry

lemma (in TM_decider) DTIME_aeI:
  assumes valid_alphabet: "alphabet L \<subseteq> \<Sigma>"
    and "\<forall>\<^sub>\<infinity>w\<in>(alphabet L)*. decides_word L w \<and> time_bounded_word T w"
  shows "L \<in> typed_DTIME TYPE('q) T"
proof (intro DTIME_ae exI[of _ M] conjI)
  from valid_alphabet show "alphabet L \<subseteq> \<Sigma>" .
  with symbol_axioms(1) have fin: "finite (alphabet L)" by (fact rev_finite_subset)
  with assms(2) show "\<forall>\<^sub>\<infinity>w\<in>(alphabet L)*. decides_word L w \<and> time_bounded_word T w"
    by (fastforce elim!: ae_word_rev_mpE intro!: ae_word_lengthI)
qed

lemma (in TM_decider) DTIME_aeI':
  assumes valid_alphabet: "alphabet L \<subseteq> \<Sigma>"
    and [intro]: "\<And>w. n \<le> length w \<Longrightarrow> w \<in> (alphabet L)* \<Longrightarrow> decides_word L w"
    and [intro]: "\<And>w. n \<le> length w \<Longrightarrow> w \<in> (alphabet L)* \<Longrightarrow> time_bounded_word T w"
  shows "L \<in> typed_DTIME TYPE('q) T"
proof -
  from valid_alphabet have "finite (alphabet L)" using finite_subset by blast
  with valid_alphabet show ?thesis by (intro DTIME_aeI ae_word_lengthI) blast+
qed

lemma DTIME_mono_ae:
  fixes L :: "'s lang"
  assumes "L \<in> typed_DTIME TYPE('q) t"
    and Tt: "\<forall>\<^sub>\<infinity>n. T n \<ge> t n"
  shows "L \<in> typed_DTIME TYPE('q) T"
proof -
  from \<open>L \<in> typed_DTIME TYPE('q) t\<close> obtain M :: "('q, 's) TM_decider"
    where symbols: "alphabet L \<subseteq> TM.symbols M"
      and decides: "TM_decider.decides M L"
      and tbounded: "TM.time_bounded M t" ..
  interpret TM_decider M .

  from symbols have fin: "finite (alphabet L)" using finite_subset by blast
  from Tt have "\<forall>\<^sub>\<infinity>w\<in>(alphabet L)*. decides_word L w \<and> time_bounded_word T w"
    unfolding ae_word_length_iff'[OF fin]
  proof (ae_nat_elim, intro ballI impI conjI)
    fix w n
    assume "w \<in> (alphabet L)*"
    with decides show "decides_word L w" by blast

    assume "length w = n" and "t n \<le> T n"
    with tbounded show "time_bounded_word T w" by blast
  qed
  with \<open>alphabet L \<subseteq> \<Sigma>\<close> show ?thesis by (fact DTIME_aeI)
qed


subsubsection\<open>Linear Speed-Up\<close>

text\<open>From @{cite \<open>ch.~12.2\<close> hopcroftAutomata1979}:

 ``\<^bold>\<open>Theorem 12.3\<close>  If \<open>L\<close> is accepted by a \<open>k\<close>-tape \<open>T(n)\<close> time-bounded Turing machine
  \<open>M\<^sub>1\<close>, then \<open>L\<close> is accepted by a \<open>k\<close>-tape \<open>cT(n)\<close> time-bounded TM \<open>M\<^sub>2\<close> for any \<open>c > 0\<close>,
  provided that \<open>k > 1\<close> and \<open>inf\<^sub>n\<^sub>\<rightarrow>\<^sub>\<infinity> T(n)/n = \<infinity>\<close>.''\<close>


(* TODO (!) check for consistency (fix types!) *)
lemma linear_time_speed_up:
  fixes T :: "nat \<Rightarrow> nat" and c :: real
  assumes "c > 0"
  \<comment> \<open>This assumption is stronger than the \<open>lim inf\<close> required by @{cite hopcroftAutomata1979}, but simpler to define in Isabelle.\<close>
    and "superlinear T"
    and "TM_decider.decides M1 L"
    and "TM.time_bounded M1 T"
  obtains M2 where "TM_decider.decides M2 L" and "TM.time_bounded M2 (tcomp (\<lambda>n. c * T n))"
  sorry


corollary DTIME_speed_up:
  fixes T :: "nat \<Rightarrow> nat" and c :: real
    and L::"'s lang"
  assumes "L \<in> typed_DTIME TYPE('q1) T"
    and "superlinear T"
    and "c > 0"
  shows "L \<in> typed_DTIME TYPE('q2) (tcomp (\<lambda>n. c * T n))"
proof -
  from \<open>L \<in> typed_DTIME TYPE('q1) T\<close> obtain M1 :: "('q1, 's) TM_decider"
    where "TM_decider.decides M1 L" and "TM.time_bounded M1 T" ..
  with assms(3, 2) obtain M2 :: "('q2, 's) TM_decider"
    where "TM_decider.decides M2 L" and "TM.time_bounded M2 (tcomp (\<lambda>n. c * T n))"
    by (rule linear_time_speed_up)
  then show ?thesis unfolding typed_DTIME_def by blast
qed


lemma speed_up_rev_helper:
  fixes n :: nat and c d :: real
  defines "d \<equiv> 1/(2*c)"
  assumes "c \<ge> 1" (* is this necessary? *)
  shows "nat \<lceil>d * \<lceil>c * n\<rceil>\<rceil> \<le> n"
proof (cases "n = 0")
  assume "n = 0"
  then show ?thesis by simp

next
  assume "n \<noteq> 0"
  then have "1 \<le> real n" by force

  from \<open>c \<ge> 1\<close> have *:"d > 0" unfolding d_def by simp
  then have "d * c = 1 / 2" unfolding d_def by simp

  from * have "d * \<lceil>c * n\<rceil> \<le> d * (c * n + 1)" using of_int_ceiling_le_add_one[of "c * n"] by force
  also have "... \<le> (d * c) * n + d" unfolding d_def by argo
  also have "... \<le> 1 / 2 * n + 1/(2 * c)" unfolding d_def by simp
  also have "... \<le> n/2 + 1/2" using \<open>c \<ge> 1\<close> by auto
  also have "... \<le> n/2 + n/2" using \<open>1 \<le> real n\<close> unfolding add_le_cancel_left by simp
  also have "... \<le> n" by simp
  finally show ?thesis by simp
qed

lemma speed_up_rev_helper':
  fixes n :: nat and c d :: real
  defines "d \<equiv> 1/(2*c)"
  assumes "c \<ge> 1"
  shows "nat \<lceil>d * nat \<lceil>c * n\<rceil>\<rceil> \<le> n"
proof -
  from \<open>c \<ge> 1\<close> have "c * n \<ge> 0" by simp
  then have *: "real (nat \<lceil>c * n\<rceil>) = real_of_int \<lceil>c * n\<rceil>" by simp
  from speed_up_rev_helper[OF \<open>c \<ge> 1\<close>] show ?thesis unfolding * d_def .
qed

lemma DTIME_speed_up_rev:
  fixes T :: "nat \<Rightarrow> nat" and c :: real
  defines "T' \<equiv> tcomp (\<lambda>n. c * T n)"
  assumes "L \<in> typed_DTIME TYPE('q1) T'"
    and "superlinear T"
    and "c > 0"
  shows "L \<in> typed_DTIME TYPE('q2) (tcomp T)"
proof (cases "c \<ge> 1")
  assume "\<not> c \<ge> 1"
  then have "c \<le> 1" by simp

  define T'' where "T'' \<equiv> tcomp (\<lambda>n. 1 * real (T' n))"
  have "T'' = T'" unfolding T''_def T'_def mult_1 tcomp_tcomp ..

  from \<open>superlinear T\<close> and \<open>c > 0\<close> have "superlinear T'" unfolding T'_def by simp
  with \<open>L \<in> typed_DTIME TYPE('q1) T'\<close>
  have "L \<in> typed_DTIME TYPE('q2) T''" unfolding T''_def by (rule DTIME_speed_up) simp
  then show "L \<in> typed_DTIME TYPE('q2) (tcomp T)" unfolding \<open>T'' = T'\<close> and T'_def
  proof (rule in_dtime_mono, intro tcomp_nat_mono)
    fix n
    have "real (T n) \<ge> 0" by simp
    with \<open>c \<le> 1\<close> show "c * T n \<le> T n" by (simp add: mult_le_cancel_right2)
  qed
next
  assume "c \<ge> 1"
  define d where "d \<equiv> 1 / (2*c)"
  from \<open>c > 0\<close> have "d > 0" unfolding d_def by simp

  define T'' where "T'' \<equiv> tcomp (\<lambda>n. d * T' n)"

  from \<open>superlinear T\<close> and \<open>c > 0\<close> have "superlinear T'" unfolding T'_def by simp

  from \<open>L \<in> typed_DTIME TYPE('q1) T'\<close> and \<open>superlinear T'\<close> and \<open>d > 0\<close>
  have "L \<in> typed_DTIME TYPE('q2) T''" unfolding T''_def by (rule DTIME_speed_up)
  then show "L \<in> typed_DTIME TYPE('q2) (tcomp T)"
  proof (rule in_dtime_mono)
    have nle_le': "\<not> a \<le> b \<Longrightarrow> a \<ge> b" for a b :: "'x :: linorder" by simp

    fix n
    show "T'' n \<le> tcomp T n "
    proof (cases "n + 1 \<ge> T n", cases "n + 1 \<ge> nat \<lceil>c * real (T n)\<rceil>")
      assume "\<not> n + 1 \<ge> T n"
      then have "n + 1 \<le> T n" by (fact nle_le')
      also have "... \<le> nat \<lceil>1 * real (T n)\<rceil>" by simp
      also have "... \<le> nat \<lceil>c * real (T n)\<rceil>" using \<open>c \<ge> 1\<close>
        by (intro nat_mono ceiling_mono mult_right_mono) auto
      finally have "n + 1 \<le> nat \<lceil>c * real (T n)\<rceil>" .

      then have h3: "T' n = nat \<lceil>c * real (T n)\<rceil>"
        unfolding T'_def tcomp_def unfolding of_nat_id nat_int ceiling_of_nat
        by (rule max.absorb2)

      have "T'' n = max (n + 1) (nat \<lceil>d * nat \<lceil>c * T n\<rceil>\<rceil>)" unfolding T''_def tcomp_def of_nat_id h3 ..
      also have "... \<le> tcomp T n" unfolding tcomp_def of_nat_id nat_int ceiling_of_nat
      proof (intro max.mono)
        from \<open>c \<ge> 1\<close> show "nat \<lceil>d * nat \<lceil>c * T n\<rceil>\<rceil> \<le> T n"
          unfolding d_def by (fact speed_up_rev_helper')
      qed blast
      finally show "T'' n \<le> tcomp T n" .
    next
      assume h1: "n + 1 \<ge> T n"
      assume "\<not> n + 1 \<ge> nat \<lceil>c * real (T n)\<rceil>"
      then have h1b: "n + 1 \<le> nat \<lceil>c * real (T n)\<rceil>" by (fact nle_le')
      then have h3: "T' n = nat \<lceil>c * real (T n)\<rceil>" unfolding T'_def tcomp_def
        unfolding of_nat_id nat_int ceiling_of_nat by (rule max.absorb2)

      have "T'' n = max (n + 1) (nat \<lceil>d * nat \<lceil>c * T n\<rceil>\<rceil>)" unfolding T''_def tcomp_def of_nat_id h3 ..
      also have "... \<le> tcomp T n" unfolding tcomp_def
      proof (rule max.mono)
        from \<open>c \<ge> 1\<close> have "nat \<lceil>d * nat \<lceil>c * T n\<rceil>\<rceil> \<le> T n" unfolding d_def by (fact speed_up_rev_helper')
        then show "nat \<lceil>d * nat \<lceil>c * T n\<rceil>\<rceil> \<le> nat \<lceil>T (of_nat n)\<rceil>" unfolding of_nat_id ceiling_of_nat nat_int .
      qed blast
      finally show "T'' n \<le> tcomp T n" .
    next
      assume h1: "n + 1 \<ge> T n"
      assume h1b: "n + 1 \<ge> nat \<lceil>c * real (T n)\<rceil>"
      then have h3: "T' n = n + 1"
        unfolding tcomp_def T'_def unfolding of_nat_id nat_int ceiling_of_nat by (rule max.absorb1)

      from \<open>c \<ge> 1\<close> have "d \<le> 1" unfolding d_def by simp
      then have "nat \<lceil>d * real (n + 1)\<rceil> \<le> n + 1" by simp

      then have "T'' n = n + 1" unfolding T''_def tcomp_def of_nat_id h3 by (rule max.absorb1)
      also have "... \<le> tcomp T n" unfolding tcomp_def by (rule max.cobounded1)
      finally show "T'' n \<le> tcomp T n" .
    qed
  qed
qed

(*
corollary DTIME_speed_up_eq:
  fixes T :: "nat \<Rightarrow> nat"
  assumes "c > 0"
    and "superlinear T"
  shows "typed_DTIME TYPE('q1) (\<lambda>n. c * T n) = typed_DTIME TYPE('q2) T"
  using assms apply (intro set_eqI iffI) apply (fact DTIME_speed_up_rev, fact DTIME_speed_up)

corollary DTIME_speed_up_div:
  fixes T :: "'c::semiring_1 \<Rightarrow> 'd::floor_ceiling" and d :: 'd
  assumes "d > 0"
    and "superlinear T"
    and "L \<in> typed_DTIME TYPE('q) T"
  shows "L \<in> typed_DTIME TYPE('q) (\<lambda>n. T n / d)"
proof -
  define c where "c \<equiv> 1 / d"
  have "a / d = c * a" for a unfolding c_def by simp

  from \<open>d > 0\<close> have "c > 0" unfolding c_def by simp
  then show "L \<in> typed_DTIME TYPE('q) (\<lambda>n. T n / d)" unfolding \<open>\<And>a. a / d = c * a\<close>
    using assms(2-3) by (rule DTIME_speed_up)
qed
*)

subsubsection\<open>Intersection of Languages\<close>

text\<open>A TM that decides the intersection of two languages \<open>L\<^sub>i\<close> could be constructed as follows:
  From the membership in \<open>DTIME(T\<^sub>i)\<close> obtain TMs \<open>M\<^sub>i\<close> (with \<open>k\<^sub>i\<close> tapes).
  Construct \<open>M\<close> as \<open>k\<^sub>1+k\<^sub>2\<close>-tape TM.
  Copy the input from tape \<open>1\<close> to tape \<open>k\<^sub>1+1\<close> (and reset the head on tape \<open>1\<close> to the start of the input).
  Assign tapes \<open>1..k\<^sub>1\<close> to \<open>M\<^sub>1\<close> and tapes \<open>k\<^sub>1+1..k\<^sub>1+k\<^sub>2\<close> to \<open>M\<^sub>2\<close> and run both TMs.
  When both TMs have terminated, accept the word if both TMs have accepted, and reject otherwise.\<close>

lemma DTIME_int:
  assumes "L\<^sub>1 \<in> DTIME(T\<^sub>1)"
    and "L\<^sub>2 \<in> DTIME(T\<^sub>2)"
  shows "L\<^sub>1 \<inter>\<^sub>L L\<^sub>2 \<in> DTIME(\<lambda>n. max (T\<^sub>1 n) (T\<^sub>2 n))" sorry


subsection\<open>Reductions\<close> (* currently broken *)

context TM_abbrevs
begin

(*
lemma reduce_decides:
  fixes A B :: "'s lang"
    and M\<^sub>R :: "('q1, 's) TM" and M\<^sub>B :: "('q2, 's) TM"
    and f\<^sub>R :: "'s list \<Rightarrow> 's list" and w :: "'s list"
  assumes "TM.decides_word M\<^sub>B B (f\<^sub>R w)"
    and f\<^sub>R: "f\<^sub>R w \<in> B \<longleftrightarrow> w \<in> A"
    and M\<^sub>R_f\<^sub>R: "TM.computes_word M\<^sub>R f\<^sub>R w"
    and "TM M\<^sub>R"
  defines "M \<equiv> M\<^sub>R |+| M\<^sub>B"
  shows "TM.decides_word M A w"
  sorry (* likely inconsistent: see hoare_comp *)

lemma reduce_time_bounded:
  fixes T\<^sub>B T\<^sub>R :: "'c::semiring_1 \<Rightarrow> 'd::floor_ceiling"
    and M\<^sub>R :: "('q1, 's) TM" and  M\<^sub>B :: "('q2, 's) TM"
    and f\<^sub>R :: "'s list \<Rightarrow> 's list" and w :: "'s list"
  assumes "TM.time_bounded_word M\<^sub>B T\<^sub>B (f\<^sub>R w)"
    and "TM.time_bounded_word M\<^sub>R T\<^sub>R w"
    and M\<^sub>R_f\<^sub>R: "TM.computes_word M\<^sub>R f\<^sub>R w"
    and f\<^sub>R_len: "length (f\<^sub>R w) \<le> length w"
  defines "M \<equiv> M\<^sub>R |+| M\<^sub>B"
  defines "T :: nat \<Rightarrow> 'd \<equiv> \<lambda>n. of_nat (tcomp T\<^sub>R n + tcomp T\<^sub>B n)"
  shows "TM.time_bounded_word M T w"
proof -
  define l :: nat where "l  \<equiv> length w"
  define l' :: 'c where "l' \<equiv> of_nat l"

  text\<open>Idea: We already know that the first machine \<^term>\<open>M\<^sub>R\<close> is time bounded
    (@{thm \<open>TM.time_bounded_word M\<^sub>R T\<^sub>R w\<close>}).

    We also know that its execution will result in the encoded corresponding input word \<open>f\<^sub>R w\<close>
    (@{thm \<open>TM.computes_word M\<^sub>R f\<^sub>R w\<close>}).
    Since the length of the corresponding input word is no longer
    than the length of the original input word \<^term>\<open>w\<close> (@{thm \<open>length (f\<^sub>R w) \<le> length w\<close>}),
    and the second machine \<^term>\<open>M\<^sub>B\<close> is time bounded (@{thm \<open>TM.time_bounded_word M\<^sub>B T\<^sub>B (f\<^sub>R w)\<close>}),
    we may conclude that the run-time of \<^term>\<open>M \<equiv> M\<^sub>R |+| M\<^sub>B\<close> on the input \<^term>\<open><w>\<^sub>t\<^sub>p\<close>
    is no longer than \<^term>\<open>T l = T\<^sub>R l' + T\<^sub>B l'\<close>.

    \<^const>\<open>TM.time_bounded\<close> is defined in terms of \<^const>\<open>tcomp\<close>, however,
    which means that the resulting total run time \<^term>\<open>T l\<close> may be as large as
    \<^term>\<open>tcomp T\<^sub>R l + tcomp T\<^sub>B l \<equiv> nat (max (l + 1) \<lceil>T\<^sub>R l'\<rceil>) + nat (max (l + 1) \<lceil>T\<^sub>B l'\<rceil>)\<close>.
    If \<^term>\<open>\<lceil>T\<^sub>R l'\<rceil> < l + 1\<close> or \<^term>\<open>\<lceil>T\<^sub>B l'\<rceil> < l + 1\<close>
    then \<^term>\<open>tcomp T l < tcomp T\<^sub>R l + tcomp T\<^sub>B l\<close>.\<close>

  show ?thesis sorry
qed
*)

lemma exists_ge:
  fixes P :: "'q :: linorder \<Rightarrow> bool"
  assumes "\<exists>n. \<forall>m\<ge>n. P m"
  shows "\<exists>n. \<forall>m\<ge>n. P m \<and> m \<ge> N"
proof -
  from assms obtain n where n': "P m" if "m \<ge> n" for m by blast
  then have "m \<ge> max n N \<Longrightarrow> P m \<and> m \<ge> N" for m by simp
  then show ?thesis by blast
qed

lemma exists_ge_eq:
  fixes P :: "nat \<Rightarrow> bool"
  shows "(\<exists>n. \<forall>m\<ge>n. P m) \<longleftrightarrow> (\<exists>n. \<forall>m\<ge>n. P m \<and> m \<ge> N)"
  by (intro iffI) (fact exists_ge, blast)

lemma ball_eq_simp: "(\<forall>n\<ge>x. \<forall>m. f m = n \<longrightarrow> P m) = (\<forall>m. f m \<ge> x \<longrightarrow> P m)" by blast

(*
lemma reduce_DTIME':
  fixes T :: "nat \<Rightarrow> real"
    and L\<^sub>1 L\<^sub>2 :: lang
    and f\<^sub>R :: "word \<Rightarrow> word" \<comment> \<open>the reduction\<close>
    and l\<^sub>R :: "nat \<Rightarrow> nat" \<comment> \<open>length bound of the reduction\<close>
  assumes "L\<^sub>1 \<in> DTIME(T)"
    and f\<^sub>R_MOST: "MOST w. (f\<^sub>R w \<in> L\<^sub>1 \<longleftrightarrow> w \<in> L\<^sub>2) \<and> (length (f\<^sub>R w) \<le> l\<^sub>R (length w))"
    and "computable_in_time T f\<^sub>R"
    and T_superlinear: "\<forall>N. \<exists>n\<^sub>0. \<forall>n\<ge>n\<^sub>0. T(n)/n \<ge> N"
    and T_l\<^sub>R_mono: "MOST n. T (l\<^sub>R n) \<ge> T(n)" \<comment> \<open>allows reasoning about \<^term>\<open>T\<close> and \<^term>\<open>l\<^sub>R\<close> as if both were \<^const>\<open>mono\<close>.\<close>
  shows "L\<^sub>2 \<in> DTIME(\<lambda>n. T(l\<^sub>R n))" \<comment> \<open>Reducing \<^term>\<open>L\<^sub>2\<close> to \<^term>\<open>L\<^sub>1\<close>\<close>
proof -
  from \<open>computable_in_time TYPE('q0) T f\<^sub>R\<close> obtain M\<^sub>R :: "('q0, 's) TM"
    where "TM.computes M\<^sub>R f\<^sub>R" "TM.time_bounded M\<^sub>R T" "TM M\<^sub>R"
    unfolding computable_in_time_def by auto
  from \<open>L1 \<in> typed_DTIME TYPE('q1) T\<close> obtain M1 :: "('q1, 's) TM"
    where "TM M1" "TM.decides M1 L1" "TM.time_bounded M1 T" ..

  define M where "M \<equiv> M\<^sub>R |+| M1"
  have "symbols M\<^sub>R = symbols M1" sorry
  with \<open>TM M\<^sub>R\<close> \<open>TM M1\<close> have "TM M" unfolding M_def by (fact wf_tm_comp)

  from f\<^sub>R_MOST obtain l\<^sub>0
    where f\<^sub>R_correct: "f\<^sub>R w \<in> L\<^sub>1 \<longleftrightarrow> w \<in> L\<^sub>2"
      and f\<^sub>R_len: "length (f\<^sub>R w) \<le> l\<^sub>R (length w)"
    if "length w \<ge> l\<^sub>0" for w by blast

  text\<open>Prove \<^term>\<open>M\<close> to be \<^term>\<open>T\<close>-time-bounded.
    Part 1: show a time-bound for \<^term>\<open>M\<close>.\<close>
  have "L\<^sub>2 \<in> DTIME(?T')"
  proof (rule DTIME_MOSTI)
    fix w :: word
    assume min_len: "length w \<ge> l\<^sub>0"

    fix w :: "'s list"
    assume min_len: "n \<le> length w"
       and "set w \<subseteq> symbols M"

    show "TM.decides_word M L2 w" unfolding M_def using \<open>TM M\<^sub>R\<close>
    proof (intro reduce_decides)
      have "pre_TM.wf_word M1 (f\<^sub>R w)" sorry (* missing assumption? *)
      with \<open>TM.decides M1 L1\<close> show "TM.decides_word M1 L1 (f\<^sub>R w)" by simp
      from f\<^sub>R_correct and min_len show "f\<^sub>R w \<in> L1 \<longleftrightarrow> w \<in> L2" .
      from \<open>TM.computes M\<^sub>R f\<^sub>R\<close> show "TM.computes_word M\<^sub>R f\<^sub>R w" ..
    qed

    show "TM.time_bounded_word M ?T' w" unfolding M_def
    proof (intro reduce_time_bounded)
      from \<open>TM.time_bounded M1 T\<close> show "TM.time_bounded_word M1 T (f\<^sub>R w)" ..
      from \<open>TM.time_bounded M\<^sub>R T\<close> show "TM.time_bounded_word M\<^sub>R T w" ..
      from \<open>TM.computes M\<^sub>R f\<^sub>R\<close> show "TM.computes_word M\<^sub>R f\<^sub>R w" ..
      from f\<^sub>R_len and min_len show "length (f\<^sub>R w) \<le> length w" .
    qed
  qed

  (* TODO (?) split proof here *)

  \<comment> \<open>Part 2: bound the run-time of M (\<open>?T'\<close>) by a multiple of the desired time-bound \<^term>\<open>T\<close>.\<close>
  from T_superlinear have "MOST n. T n \<ge> 2 * n"
    unfolding MOST_suff_large_iff of_nat_mult by (fact superlinearE')
  with T_l\<^sub>R_mono have "MOST n. ?T' n \<le> 4 * T (l\<^sub>R n)"
  proof (MOST_intro)
    fix n :: nat
    assume "n \<ge> 1" and "T n \<ge> 2*n" and "T (l\<^sub>R n) \<ge> T(n)"
    then have "n + 1 \<le> 2 * n" by simp
    also have "2 * n = nat \<lceil>2 * n\<rceil>" unfolding ceiling_of_nat nat_int ..

    also from \<open>\<lceil>?T n\<rceil> \<ge> 2*n\<close> have "nat \<lceil>2 * n\<rceil> \<le> nat \<lceil>\<lceil>?T n\<rceil>\<rceil>" by (intro nat_mono ceiling_mono) force
    also have "... = nat \<lceil>?T n\<rceil>" unfolding ceiling_of_int ..
    finally have *: "tcomp T n = nat \<lceil>?T n\<rceil>" unfolding tcomp_def max_def by (subst if_P) auto

    have "real (?T' n) \<le> real (2 * nat \<lceil>T (l\<^sub>R n)\<rceil>)" unfolding mult_2 h1 h2
      by (intro of_nat_mono add_left_mono) (fact \<open>nat \<lceil>T n\<rceil> \<le> nat \<lceil>T (l\<^sub>R n)\<rceil>\<close>)
    also have "... \<le> 2 * (2 * T (l\<^sub>R n))" unfolding of_nat_mult of_nat_numeral
    proof (intro mult_left_mono)
      from \<open>T n \<ge> 2*n\<close> \<open>n \<ge> 1\<close> \<open>T (l\<^sub>R n) \<ge> T(n)\<close> have "T (l\<^sub>R n) \<ge> 1" by simp
      have "nat \<lceil>T (l\<^sub>R n)\<rceil> = real_of_int \<lceil>T (l\<^sub>R n)\<rceil>" using \<open>T (l\<^sub>R n) \<ge> 1\<close> by (intro of_nat_nat) simp
      also have "\<lceil>T (l\<^sub>R n)\<rceil> \<le> T (l\<^sub>R n) + 1" by (fact of_int_ceiling_le_add_one)
      also have "... \<le> 2 * T (l\<^sub>R n)" unfolding mult_2 using \<open>T (l\<^sub>R n) \<ge> 1\<close> by (fact add_left_mono)
      finally show "nat \<lceil>T (l\<^sub>R n)\<rceil> \<le> 2 * T (l\<^sub>R n)" .
    qed simp
    also have "... = 4 * T (l\<^sub>R n)" by simp
    finally show "?T' n \<le> 4 * T (l\<^sub>R n)" .
  qed
  with \<open>L\<^sub>2 \<in> DTIME(?T')\<close> have "L\<^sub>2 \<in> DTIME(\<lambda>n. 4 * T (l\<^sub>R n))" by (rule DTIME_mono_MOST)

  then show "L\<^sub>2 \<in> DTIME(\<lambda>n. T(l\<^sub>R n))"
  proof (rule DTIME_speed_up_rev)
    {
      fix N
      from T_superlinear have "MOST n. T(n)/n \<ge> N" unfolding MOST_suff_large_iff ..
      with T_l\<^sub>R_mono have "MOST n. T(l\<^sub>R n)/n \<ge> N"
      proof (MOST_intro)
        fix n
        assume "T(l\<^sub>R n) \<ge> T(n)"
        assume "N \<le> T(n)/n"
        also from \<open>T(l\<^sub>R n) \<ge> T(n)\<close> have "... \<le> T(l\<^sub>R n)/n" by (rule divide_right_mono) simp
        finally show "N \<le> T(l\<^sub>R n)/n" .
      qed
    }
    then show "\<forall>N. \<exists>n\<^sub>0. \<forall>n\<ge>n\<^sub>0. T(l\<^sub>R n)/n \<ge> N" unfolding MOST_suff_large_iff ..
  qed \<comment> \<open>\<^term>\<open>0 < 4\<close> by\<close> simp
qed

lemma reduce_DTIME: \<comment> \<open>Version of \<open>reduce_DTIME'\<close> with constant length bound (\<^term>\<open>l\<^sub>R = Fun.id\<close>).\<close>
  assumes "L\<^sub>1 \<in> DTIME(T)"
    and f\<^sub>R_MOST: "MOST w. (f\<^sub>R w \<in> L\<^sub>1 \<longleftrightarrow> w \<in> L\<^sub>2) \<and> (length (f\<^sub>R w) \<le> length w)"
    and "computable_in_time T f\<^sub>R"
    and T_superlinear: "\<forall>N. \<exists>n\<^sub>0. \<forall>n\<ge>n\<^sub>0. T(n)/n \<ge> N"
  shows "L\<^sub>2 \<in> DTIME(T)" \<comment> \<open>Reducing \<^term>\<open>L\<^sub>2\<close> to \<^term>\<open>L\<^sub>1\<close>\<close>
  using assms by (rule reduce_DTIME') blast
*)

end \<comment> \<open>context \<^locale>\<open>TM_abbrevs\<close>\<close>

end