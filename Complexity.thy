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

lemma conf_time_geI[intro]: "is_final (steps n c) \<Longrightarrow> config_time c \<le> n"
  unfolding config_time_def run_def by (fact Least_le)

lemma conf_time_ge_iff[intro]: "halts_config c \<Longrightarrow> is_final (steps n c) \<longleftrightarrow> n \<ge> config_time c"
  by blast

lemma conf_time_less_rev[intro]: "halts_config c \<Longrightarrow> \<not> is_final (steps n c) \<Longrightarrow> n < config_time c"
  by (subst (asm) conf_time_ge_iff) auto

lemma conf_time_finalI[intro]: "halts_config c \<Longrightarrow> is_final (steps (config_time c) c)"
  using conf_time_ge_iff by blast

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

lemma time_leI[intro]:
  "is_final (run n w) \<Longrightarrow> time w \<le> n"
  unfolding run_def time_def by (rule conf_time_geI)

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
      using \<open>halts_config c0\<close> by (fact conf_time_ge_iff)
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


lemma (in Rej_TM) rej_tm_time: "time w = 0" by simp

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

(* TODO get rid of \<open>'c::semiring_1 \<Rightarrow> 'd::floor_ceiling\<close> from other definitions.
        replace by \<open>nat \<Rightarrow> nat\<close>, but retain some adapter like \<open>tcomp\<close> *)
definition tcomp :: "('c::semiring_1 \<Rightarrow> 'd::floor_ceiling) \<Rightarrow> nat \<Rightarrow> nat"
  where [simp]: "tcomp T n \<equiv> max (n + 1) (nat \<lceil>T (of_nat n)\<rceil>)"

abbreviation (input) tcomp\<^sub>w :: "('c::semiring_1 \<Rightarrow> 'd::floor_ceiling) \<Rightarrow> 's list \<Rightarrow> nat"
  where "tcomp\<^sub>w T w \<equiv> tcomp T (length w)"


lemma tcomp_min: "tcomp f n \<ge> n + 1" by simp

lemma tcomp_nat_simp[simp]:
  fixes f :: "nat \<Rightarrow> nat"
  shows "tcomp f n = max (n + 1) (f n)" by simp

lemma tcomp_nat_id:
  fixes f :: "nat \<Rightarrow> nat"
  shows "(\<And>n. f n \<ge> n + 1) \<Longrightarrow> tcomp f = f"
  by (intro ext) (unfold tcomp_nat_simp, rule max_absorb2)

lemma tcomp_nat_mono: "T n \<ge> t n \<Longrightarrow> tcomp T n \<ge> tcomp t n" unfolding Let_def of_nat_id tcomp_def
  by (intro nat_mono max.mono of_nat_mono add_right_mono ceiling_mono le_refl)

lemma tcomp_mono:
  assumes Tt: "T (of_nat n) \<ge> t (of_nat n)"
  shows "tcomp T n \<ge> tcomp t n"
proof -
  have "tcomp (\<lambda>n. T (of_nat n)) n \<ge> tcomp (\<lambda>n. t (of_nat n)) n"
    by (rule tcomp_nat_mono) (rule Tt)
  then show "tcomp T n \<ge> tcomp t n" unfolding tcomp_def of_nat_id .
qed

lemma tcomp_mono':
  assumes Tt: "\<And>x. T x \<ge> t x"
  shows "tcomp T n \<ge> tcomp t n"
proof -
  have "tcomp (\<lambda>n. T (of_nat n)) n \<ge> tcomp (\<lambda>n. t (of_nat n)) n"
    by (rule tcomp_nat_mono) (rule Tt)
  then show "tcomp T n \<ge> tcomp t n" unfolding tcomp_def of_nat_id .
qed

lemma
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


subsubsection\<open>Time-Bounded Execution\<close>

text\<open>Predicates to verify that TMs halt within a given time-bound.\<close>

context TM begin

definition time_bounded_word :: "('c::semiring_1 \<Rightarrow> 'd::floor_ceiling) \<Rightarrow> 's list \<Rightarrow> bool"
  where time_bounded_def[simp]: "time_bounded_word T w \<equiv> \<exists>n.
            n \<le> tcomp\<^sub>w T w \<and> is_final (run n w)"

abbreviation time_bounded :: "('c::semiring_1 \<Rightarrow> 'd::floor_ceiling) \<Rightarrow> bool"
  where "time_bounded T \<equiv> \<forall>w. time_bounded_word T w"

lemma time_boundedI: "is_final (run (tcomp\<^sub>w T w) w) \<Longrightarrow> time_bounded_word T w"
  unfolding time_bounded_def by blast

lemma time_bounded_altdef: "time_bounded_word T w \<longleftrightarrow> is_final (run (tcomp\<^sub>w T w) w)"
proof
  assume "time_bounded_word T w"
  then obtain n where "n \<le> tcomp\<^sub>w T w" and "is_final (run n w)" unfolding time_bounded_def by blast
  then show "is_final (run (tcomp\<^sub>w T w) w)" by blast
qed (* direction "\<Longleftarrow>" by *) (fact time_boundedI)

lemma time_boundedE: "time_bounded_word T w \<Longrightarrow> is_final (run (tcomp\<^sub>w T w) w)"
  using time_bounded_altdef by blast

lemma time_bounded_word_mono[dest]:
  fixes T t w
  assumes Tt: "tcomp\<^sub>w T w \<ge> tcomp\<^sub>w t w"
    and tr: "time_bounded_word t w"
  shows "time_bounded_word T w"
proof -
  from tr obtain n where n_tcomp: "n \<le> tcomp\<^sub>w t w" and final_n: "is_final (run n w)"
    unfolding time_bounded_def of_nat_id by blast
  from n_tcomp Tt have "n \<le> tcomp\<^sub>w T w" by (fact le_trans)
  with final_n show "time_bounded_word T w" unfolding time_bounded_def by blast
qed

lemma time_bounded_mono':
  fixes T t
  assumes "\<And>w::'s list. tcomp\<^sub>w T w \<ge> tcomp\<^sub>w t w"
    and "time_bounded t"
  shows "time_bounded T"
  using assms time_bounded_word_mono by blast

lemma time_bounded_mono:
  fixes T t :: "('c::semiring_1 \<Rightarrow> 'd::floor_ceiling)"
  assumes Tt: "\<And>x. T x \<ge> t x"
    and "time_bounded t"
  shows "time_bounded T"
  by (rule time_bounded_mono', rule tcomp_mono) fact+

lemma time_bounded_altdef2: "time_bounded T \<longleftrightarrow> (\<forall>w. halts w \<and> time w \<le> tcomp\<^sub>w T w)"
  unfolding time_bounded_def by blast

corollary time_bounded_time: "time_bounded T \<Longrightarrow> time w \<le> tcomp\<^sub>w T w"
  unfolding time_bounded_altdef2 by blast


end \<comment> \<open>context \<^locale>\<open>TM\<close>\<close>

text\<open>Notion of time-constructible from @{cite \<open>ch.~12.3\<close> hopcroftAutomata1979}:
  ``A function T(n) is said to be time constructible if there exists a T(n) time-
  bounded multitape Turing machine M such that for each n there exists some input
  on which M actually makes T(n) moves.''\<close>

definition tconstr :: "'s itself \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> bool"
  where "tconstr \<ss> T \<equiv> \<exists>M::(nat, 's) TM. \<forall>n. \<exists>w. TM.time M w = T n"

text\<open>Fully time-constructible, (@{cite \<open>ch.~12.3\<close> hopcroftAutomata1979}):
  ``We say that T(n) is fully time-constructible if there is a TM
  that uses T(n) time on all inputs of length n.''\<close>

definition fully_tconstr :: "'q itself \<Rightarrow> 's itself \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> bool"
  where "fully_tconstr \<qq> \<ss> T \<equiv> \<exists>M::('q, 's) TM. \<forall>w. TM.time M w = T (length w)"

definition computable_in_time :: "'q itself \<Rightarrow> ('c::semiring_1 \<Rightarrow> 'd::floor_ceiling) \<Rightarrow> ('s list \<Rightarrow> 's list) \<Rightarrow> bool"
  where "computable_in_time \<qq> T f \<equiv> \<exists>M::('q, 's) TM. TM.computes M f \<and> TM.time_bounded M T"

lemma computableE[elim]:
  assumes "computable_in_time TYPE('q) T f"
  obtains M::"('q, 's) TM" where "TM.computes M f" and "TM.time_bounded M T"
using assms that unfolding computable_in_time_def by blast


subsection\<open>DTIME\<close>

text\<open>\<open>DTIME(T)\<close> is the set of languages decided by TMs in time \<open>T\<close> or less.\<close>
definition typed_DTIME :: "'q itself \<Rightarrow> ('c::semiring_1 \<Rightarrow> 'd::floor_ceiling) \<Rightarrow> 's lang set"
  where "typed_DTIME \<tau> T \<equiv> {L. \<exists>M::('q, 's) TM. alphabet L \<subseteq> TM.symbols M \<and> TM.decides M L \<and> TM.time_bounded M T}"

abbreviation DTIME where
  "DTIME \<equiv> typed_DTIME TYPE(nat)"

lemma (in TM) in_dtimeI[intro]:
  assumes "alphabet L \<subseteq> \<Sigma>"
    and "decides L"
    and "time_bounded T"
  shows "L \<in> typed_DTIME TYPE('q) T"
  unfolding typed_DTIME_def using assms by blast

lemma in_dtimeE[elim]:
  assumes "L \<in> typed_DTIME TYPE('q) T"
  obtains M::"('q, 's) TM"
  where "alphabet L \<subseteq> TM.symbols M"
    and "TM.decides M L"
    and "TM.time_bounded M T"
  using assms unfolding typed_DTIME_def by blast

lemma in_dtimeD[dest]:
  assumes "L \<in> typed_DTIME TYPE('q) T"
  shows "\<exists>M::('q, 's) TM. alphabet L \<subseteq> TM.symbols M \<and> TM.decides M L \<and> TM.time_bounded M T"
  using assms unfolding typed_DTIME_def ..

corollary in_dtime_mono':
  fixes T t
  assumes "\<And>n. tcomp T n \<ge> tcomp t n"
    and "L \<in> typed_DTIME TYPE('q) t"
  shows "L \<in> typed_DTIME TYPE('q) T"
  using assms TM.time_bounded_mono' by (elim in_dtimeE, intro TM.in_dtimeI) blast+

corollary in_dtime_mono:
  fixes T t
  assumes "\<And>n. t n \<le> T n"
    and "L \<in> typed_DTIME TYPE('q) t"
  shows "L \<in> typed_DTIME TYPE('q) T"
  using assms by (intro in_dtime_mono'[of t T] tcomp_mono)

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
  assumes "\<exists>M::('q, 's) TM. alphabet L \<subseteq> TM.symbols M \<and>
    (\<forall>\<^sub>\<infinity>w\<in>(alphabet L)*. TM.decides_word M L w \<and> TM.time_bounded_word M T w)"
  shows "L \<in> typed_DTIME TYPE('q) T"
  sorry

lemma (in TM) DTIME_aeI:
  assumes valid_alphabet: "alphabet L \<subseteq> \<Sigma>"
    and [intro]: "\<And>w. n \<le> length w \<Longrightarrow> w \<in> (alphabet L)* \<Longrightarrow> decides_word L w"
    and [intro]: "\<And>w. n \<le> length w \<Longrightarrow> w \<in> (alphabet L)* \<Longrightarrow> time_bounded_word T w"
  shows "L \<in> typed_DTIME TYPE('q) T"
proof (intro DTIME_ae exI[of _ M] conjI)
  from valid_alphabet show "alphabet L \<subseteq> \<Sigma>" .

  from valid_alphabet and symbol_axioms(1) have "finite (alphabet L)" by (fact finite_subset)
  then show "\<forall>\<^sub>\<infinity>w\<in>(alphabet L)*. decides_word L w \<and> time_bounded_word T w"
    by (rule ae_word_lengthI) blast
qed

lemma DTIME_mono_ae':
  fixes L :: "'s lang"
  assumes Tt: "\<And>n. N \<le> n \<Longrightarrow> tcomp T n \<ge> tcomp t n"
    and "L \<in> typed_DTIME TYPE('q) t"
  shows "L \<in> typed_DTIME TYPE('q) T"
proof -
  from \<open>L \<in> typed_DTIME TYPE('q) t\<close> obtain M :: "('q, 's) TM"
    where symbols: "alphabet L \<subseteq> TM.symbols M"
      and decides: "TM.decides M L"
      and tbounded: "TM.time_bounded M t" ..

  interpret TM M .

  from symbols show ?thesis
  proof (rule DTIME_aeI)
    fix w
    assume "w \<in> (alphabet L)*"
    with decides show "decides_word L w" by blast

    assume "N \<le> length w"
    with Tt and tbounded show "time_bounded_word T w" by blast
  qed
qed

lemma DTIME_mono_ae:
  assumes Tt: "\<And>n. n \<ge> N \<Longrightarrow> T (of_nat n) \<ge> t (of_nat n)"
    and "L \<in> typed_DTIME TYPE('q) t"
  shows "L \<in> typed_DTIME TYPE('q) T"
proof (rule DTIME_mono_ae')
  fix n :: nat
  assume "n \<ge> N"
  then have "T (of_nat n) \<ge> t (of_nat n)" by (fact Tt)
  then show "tcomp t n \<le> tcomp T n" by (fact tcomp_mono)
qed (fact \<open>L \<in> typed_DTIME TYPE('q) t\<close>)


subsubsection\<open>Linear Speed-Up\<close>

text\<open>From @{cite \<open>ch.~12.2\<close> hopcroftAutomata1979}:

lemma decides_altdef4: "decides_word L w \<longleftrightarrow> (if w \<in> L then accepts w else rejects w)"
  unfolding decides_def using acc_not_rej by (cases "w \<in> L") auto

lemma decides_altdef3: "decides_word L w \<longleftrightarrow> wf_word w \<and> hoare_halt (init w) (\<lambda>c. state c \<in> accepting_states M \<longleftrightarrow> w\<in>L)"
  unfolding decides_altdef4 accepts_def rejects_def
  by (cases "w\<in>L") (simp add: hoare_halt_def del: initial_config_def)+
 ``\<^bold>\<open>Theorem 12.3\<close>  If \<open>L\<close> is accepted by a \<open>k\<close>-tape \<open>T(n)\<close> time-bounded Turing machine
  \<open>M\<^sub>1\<close>, then \<open>L\<close> is accepted by a \<open>k\<close>-tape \<open>cT(n)\<close> time-bounded TM \<open>M\<^sub>2\<close> for any \<open>c > 0\<close>,
  provided that \<open>k > 1\<close> and \<open>inf\<^sub>n\<^sub>\<rightarrow>\<^sub>\<infinity> T(n)/n = \<infinity>\<close>.''\<close>


lemma linear_time_speed_up:
  assumes "c > 0"
  \<comment> \<open>This assumption is stronger than the \<open>lim inf\<close> required by @{cite hopcroftAutomata1979}, but simpler to define in Isabelle.\<close>
    and "superlinear T"
    and "TM.decides M1 L"
    and "TM.time_bounded M1 T"
  obtains M2 where "TM.decides M2 L" and "TM.time_bounded M2 (\<lambda>n. c * T n)"
  sorry


corollary DTIME_speed_up:
  fixes T :: "'c::semiring_1 \<Rightarrow> 'd::floor_ceiling" and c :: 'd
    and L::"'s lang"
  assumes "c > 0"
    and "superlinear T"
    and "L \<in> typed_DTIME TYPE('q1) T"
  shows "L \<in> typed_DTIME TYPE('q2) (\<lambda>n. c * T n)"
proof -
  from \<open>L \<in> typed_DTIME TYPE('q1) T\<close> obtain M1::"('q1, 's) TM"
    where "TM.decides M1 L" and "TM.time_bounded M1 T" ..
  with assms(1-2) obtain M2::"('q2, 's) TM"
    where "TM.decides M2 L" and "TM.time_bounded M2 (\<lambda>n. c * T n)"
    by (rule linear_time_speed_up)
  then show ?thesis unfolding typed_DTIME_def by blast
qed

lemma DTIME_speed_up_rev:
  fixes T :: "'c::semiring_1 \<Rightarrow> 'd::floor_ceiling" and c :: 'd
  defines "T' \<equiv> \<lambda>n. c * T n"
  assumes "c > 0"
    and "superlinear T"
    and "L \<in> typed_DTIME TYPE('q1) T'"
  shows "L \<in> typed_DTIME TYPE('q2) T"
proof -
  define c' where "c' \<equiv> 1/c"
  have T: "T = (\<lambda>n. c' * T' n)" unfolding T'_def c'_def using \<open>c > 0\<close> by force

  from \<open>c > 0\<close> have "c' > 0" unfolding c'_def by simp
  moreover have "superlinear T'" unfolding T'_def unbounded_def
  proof (rule allI)
    fix N
    define N' where "N' \<equiv> N / c"
    {
      fix n :: nat
      let ?n = "of_nat n"
      have "T(?n)/?n \<ge> N/c \<longleftrightarrow> c*T(?n)/?n \<ge> N" unfolding pos_divide_le_eq[OF \<open>c > 0\<close>]
      proof -
        let ?lhs = "(T ?n) / ?n * c" and ?rhs = "(c * T ?n) / ?n"
        have "?lhs = ?rhs" by force
        then show "(N \<le> ?lhs) = (N \<le> ?rhs)" by (fact arg_cong)
      qed
    } note * = this
    from assms(3) have "\<exists>n'. \<forall>n\<ge>n'. T(of_nat n)/(of_nat n) \<ge> N'" unfolding unbounded_def ..
    then show "\<exists>n'. \<forall>n\<ge>n'. c * T(of_nat n)/(of_nat n) \<ge> N" unfolding N'_def * .
  qed
  from \<open>c' > 0\<close> this assms(4) show "L \<in> typed_DTIME TYPE('q2) T"
    unfolding T by (fact DTIME_speed_up)
qed

corollary DTIME_speed_up_eq:
  fixes T :: "'c::semiring_1 \<Rightarrow> 'd::floor_ceiling" and c :: 'd
  assumes "c > 0"
    and "superlinear T"
  shows "typed_DTIME TYPE('q1) (\<lambda>n. c * T n) = typed_DTIME TYPE('q2) T"
  using assms by (intro set_eqI iffI) (fact DTIME_speed_up_rev, fact DTIME_speed_up)

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


context TM_abbrevs
begin

subsection\<open>Reductions\<close> (* currently broken *)

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
lemma reduce_DTIME: (* TODO clean up and tidy assumptions *)
  fixes T\<^sub>B T\<^sub>R T :: "'c::semiring_1 \<Rightarrow> 'd::floor_ceiling"
    and f\<^sub>R :: "('s) list \<Rightarrow> 's list"
    and L1 L2 :: "'s list set"
  assumes f\<^sub>R_ae: "\<forall>\<^sub>\<infinity>n. \<forall>w. length w = n \<longrightarrow> (f\<^sub>R w \<in> L1) = (w \<in> L2) \<and> length (f\<^sub>R w) \<le> length w"
    and "computable_in_time TYPE('q0) T f\<^sub>R"
    and "superlinear T"
    and "L1 \<in> typed_DTIME TYPE('q1) T"
  shows "L2 \<in> typed_DTIME TYPE('q0 + 'q1) T"
proof -
  from \<open>computable_in_time TYPE('q0) T f\<^sub>R\<close> obtain M\<^sub>R :: "('q0, 's) TM"
    where "TM.computes M\<^sub>R f\<^sub>R" "TM.time_bounded M\<^sub>R T" "TM M\<^sub>R"
    unfolding computable_in_time_def by auto
  from \<open>L1 \<in> typed_DTIME TYPE('q1) T\<close> obtain M1 :: "('q1, 's) TM"
    where "TM M1" "TM.decides M1 L1" "TM.time_bounded M1 T" ..

  define M where "M \<equiv> M\<^sub>R |+| M1"
  have "symbols M\<^sub>R = symbols M1" sorry
  with \<open>TM M\<^sub>R\<close> \<open>TM M1\<close> have "TM M" unfolding M_def by (fact wf_tm_comp)

  let ?T  = "\<lambda>n. T (of_nat n)"
  let ?T' = "\<lambda>n. of_nat (tcomp T n + tcomp T n) :: 'd"

  from f\<^sub>R_ae obtain n
    where f\<^sub>R_correct: "f\<^sub>R w \<in> L1 \<longleftrightarrow> w \<in> L2"
      and f\<^sub>R_len: "length (f\<^sub>R w) \<le> length w"
    if "length w \<ge> n" for w
    unfolding MOST_nat_le ball_eq_simp by blast

  text\<open>Prove \<^term>\<open>M\<close> to be \<^term>\<open>T\<close>-time-bounded.
    Part 1: show a time-bound for \<^term>\<open>M\<close>.\<close>
  have "L2 \<in> typed_DTIME TYPE('q0+'q1) ?T'"
  proof (rule TM.DTIME_aeI)
    show "TM M" by fact

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

  text\<open>Part 2: bound the run-time of M (\<^term>\<open>?T'\<close>) by a multiple of the desired time-bound \<^term>\<open>T\<close>.\<close>
  have "\<exists>n0. \<forall>n\<ge>n0. \<lceil>?T n\<rceil> \<ge> (2 * n) \<and> n \<ge> 1"
  proof (rule exists_ge, rule ex_reg, intro allI impI)
    from \<open>superlinear T\<close> show "\<exists>n0. \<forall>n\<ge>n0. of_nat 2 * of_nat n \<le> ?T n"
      by (rule superlinearE')

    fix n0 n
    assume "n0 \<le> n" and "\<forall>n\<ge>n0. of_nat 2 * of_nat n \<le> ?T n"
    then have h1: "of_nat (2 * n) \<le> ?T n" unfolding of_nat_mult by blast

    have "int (2 * n) = \<lceil>of_nat (2 * n) :: 'd\<rceil>" unfolding ceiling_of_nat ..
    also from h1 have "... \<le> \<lceil>?T n\<rceil>" by (fact ceiling_mono)
    finally show "\<lceil>?T n\<rceil> \<ge> int (2 * n)" .
  qed
  then obtain n0 where n0: "\<lceil>?T n\<rceil> \<ge> 2*n" "n \<ge> 1" if "n \<ge> n0" for n by blast

  have "?T' n \<le> 4 * ?T n" if "n \<ge> n0" for n
  proof -
    from \<open>n \<ge> n0\<close> have "n \<ge> 1" and "\<lceil>?T n\<rceil> \<ge> 2*n" by (fact n0)+
    then have "n + 1 \<le> 2 * n" by simp
    also have "2 * n = nat \<lceil>2 * n\<rceil>" unfolding ceiling_of_nat nat_int ..

    also from \<open>\<lceil>?T n\<rceil> \<ge> 2*n\<close> have "nat \<lceil>2 * n\<rceil> \<le> nat \<lceil>\<lceil>?T n\<rceil>\<rceil>" by (intro nat_mono ceiling_mono) force
    also have "... = nat \<lceil>?T n\<rceil>" unfolding ceiling_of_int ..
    finally have *: "tcomp T n = nat \<lceil>?T n\<rceil>" unfolding tcomp_def max_def by (subst if_P) auto

    from \<open>\<lceil>?T n\<rceil> \<ge> 2*n\<close> \<open>n \<ge> 1\<close> have "\<lceil>?T n\<rceil> \<ge> 2" by linarith
    then have "\<lceil>?T n\<rceil> \<ge> 1" "?T n \<ge> 1" by simp+
    have "(of_nat (nat \<lceil>?T n\<rceil>) :: 'd) = of_int \<lceil>?T n\<rceil>" using \<open>\<lceil>?T n\<rceil> \<ge> 1\<close> by (intro of_nat_nat) simp
    also have "... \<le> ?T n + 1" by (fact of_int_ceiling_le_add_one)
    also have "... \<le> 2 * ?T n" unfolding mult_2 using \<open>?T n \<ge> 1\<close> by (fact add_left_mono)
    finally have "?T' n \<le> 2 * (2 * ?T n)" unfolding * of_nat_add mult_2 by (intro add_mono)
    also have "... = 4 * ?T n" by simp
    finally show ?thesis .
  qed
  then have "\<And>n. n \<ge> n0 \<Longrightarrow> ?T' (of_nat n) \<le> 4 * ?T n" unfolding of_nat_id .

  from this and \<open>L2 \<in> typed_DTIME TYPE('q0+'q1) ?T'\<close>
  have "L2 \<in> typed_DTIME TYPE('q0+'q1) (\<lambda>n. 4 * T n)" by (fact DTIME_mono_ae)
  with \<open>superlinear T\<close> show "L2 \<in> typed_DTIME TYPE('q0+'q1) T"
    by (intro DTIME_speed_up_rev[where T=T]) auto
qed
*)

end \<comment> \<open>context \<^locale>\<open>TM_abbrevs\<close>\<close>

end