section\<open>Complexity\<close>

text\<open>Definitions and lemmas from computational complexity theory.\<close>

theory Complexity
  imports TM_Hoare Goedel_Numbering
    "Supplementary/Asymptotic" "HOL-Eisbach.Eisbach" CoTM
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

abbreviation time_bounded_symbols :: "(nat \<Rightarrow> nat) \<Rightarrow> bool"
  where "time_bounded_symbols T \<equiv> \<forall>w. set w \<subseteq> TM.symbols M \<longrightarrow> time_bounded_word T w"

lemmas time_bounded_def = time_bounded_word_def


mk_ide time_bounded_word_def |intro time_bounded_wordI[intro]| |dest time_bounded_wordD[dest]|

lemma time_bounded_word_mono[dest]:
  "time_bounded_word t w \<Longrightarrow> t (length w) \<le> T (length w) \<Longrightarrow> time_bounded_word T w" by blast

lemma time_bounded_mono: "time_bounded t \<Longrightarrow> (\<And>x. t x \<le> T x) \<Longrightarrow> time_bounded T" by blast

lemma time_bounded_altdef2: "time_bounded T \<longleftrightarrow> (\<forall>w. halts w \<and> time w \<le> T (length w))" by blast

lemma time_bounded_then_symbols: "time_bounded T \<Longrightarrow> time_bounded_symbols T" by simp

lemma time_bounded_symbols_mono: "time_bounded_symbols t \<Longrightarrow> (\<And>x. t x \<le> T x) \<Longrightarrow>
                                  time_bounded_symbols T" by auto

lemma time_bounded_word_min:
  assumes "time_bounded_word T' w"
  obtains T :: "nat \<Rightarrow> nat" where
  "is_final (run (T (length w)) w)" and "\<And>n. n < T (length w) \<Longrightarrow> \<not>is_final (run n w)"
  by (metis (lifting) TM.time_bounded_wordD add_diff_cancel_left' assms compute_altdef
      final_run_compute not_less_iff_gr_or_eq order_le_less time_leI)

lemma time_bounded_min:
  assumes "time_bounded T'"
  obtains T :: "nat \<Rightarrow> nat" where
  "\<And>w. is_final (run (T (length w)) w)" and
  "\<exists>w. (\<forall>n. n < T (length w) \<longrightarrow> \<not>is_final (run n w))"
proof -
  have 1: "\<And>n. \<exists>k. \<forall>w. length w = n \<longrightarrow> is_final (run k w)" using assms(1)
    by (metis time_bounded_wordD)
  have 2: "\<And>n w. length w = n \<Longrightarrow>
           is_final (run (LEAST k. \<forall>w. length w = n \<longrightarrow> is_final (run k w)) w)"
    using 1 by (smt (verit, del_insts) LeastI_ex)
  show "(\<And>T. (\<And>w. is_final (run (T (length w)) w)) \<Longrightarrow>
        \<exists>w. \<forall>n<T (length w). is_not_final (run n w) \<Longrightarrow> thesis) \<Longrightarrow> thesis"
  proof
    fix w :: "'s list"
    define n :: nat where "n \<equiv> length w"
    define T :: "nat \<Rightarrow> nat" where
      "\<And>n. T n \<equiv> (LEAST k. \<forall>w. length w = n \<longrightarrow> is_final (run k w))"
    show "is_final (run (T n) w)" unfolding T_def using 2 [of w n] n_def by blast
    fix n :: nat
    show "\<exists>w. \<forall>n<T (length w). is_not_final (run n w)"
      unfolding T_def using 2 [of w n] n_def
      by (smt (verit, ccfv_threshold) length_0_conv not_less_Least)
  qed
qed

lemma time_bounded_word_final_state:
  assumes "time_bounded_word T w"
  obtains fs where "fs \<in> F"
  using assms by auto

lemma time_bounded_tcompI: "time_bounded T \<Longrightarrow> time_bounded (tcomp T)"
  by (rule time_bounded_mono) auto

lemma time_bounded_word_tcompI: "time_bounded_word T w \<Longrightarrow>
    time_bounded_word (tcomp T) w"
  by (rule time_bounded_word_mono) auto

lemma time_bounded_symbols_tcompI: "time_bounded_symbols T \<Longrightarrow>
    time_bounded_symbols (tcomp T)"
  by (simp add: TM.time_bounded_word_tcompI)

end \<comment> \<open>context \<^locale>\<open>TM\<close>\<close>

lemma final_only_after_inspection: "TM.is_final (valid_PTM M)
    (TM.run (valid_PTM M) n w) \<Longrightarrow> n \<ge> length w"
  unfolding TM.is_final_def TM.run_def using proper_TM.inspect_input_not_stop
  by (metis Rep_PTM dual_order.order_iff_strict is_finalI mem_Collect_eq
      not_less_iff_gr_or_eq o_apply valid_PTM_def)

lemma time_bounded_PTMD [dest]: "TM.time_bounded_word (valid_PTM M) T w \<Longrightarrow>
                         T (length w) \<ge> length w"
  using TM.time_bounded_wordD final_only_after_inspection by blast

lemma time_bounded_word_ext: "TM.time_bounded_word (Abs_TM (tm_to_ext_tm tm)) t (map (\<lambda>x. [x]) w) \<longleftrightarrow>
                                      TM.time_bounded_word tm t w"
proof -
  have "\<And>tm t w. state (TM.run (Abs_TM (tm_to_ext_tm tm)) (t (length w)) (map (\<lambda>x. [x]) w)) = state (TM.run tm (t (length w)) w)"
    by (metis tm_ext_state_run)
  moreover have "\<And>tm s. s \<in> TM.F (Abs_TM (tm_to_ext_tm tm)) \<longleftrightarrow> s \<in> TM.F tm"
    by (metis ext_final_states ext_tm_valid valid_tm_final_states)
  ultimately have "\<And>tm t w. TM.is_final tm (TM.run tm (t (length w)) w) \<longleftrightarrow>
        TM.is_final (Abs_TM (tm_to_ext_tm tm)) (TM.run (Abs_TM (tm_to_ext_tm tm)) (t (length w)) (map (\<lambda>x. [x]) w))"
    by (metis TM.is_final_def)
  thus ?thesis
    by (metis TM.time_bounded_wordD TM.time_bounded_wordI length_map)
qed

lemma time_bounded_symbols_ext: "TM.time_bounded_symbols (Abs_TM (tm_to_ext_tm tm)) t \<longleftrightarrow>
                                 TM.time_bounded_symbols tm t"
proof (rule ccontr)
  have "(\<forall>w. set w \<subseteq> TM.TM.symbols (Abs_TM (tm_to_ext_tm tm)) \<longrightarrow>
        TM.time_bounded_word (Abs_TM (tm_to_ext_tm tm)) t w)
        \<Longrightarrow> (\<exists>w. set w \<subseteq> TM.TM.symbols tm \<and> \<not>(TM.time_bounded_word tm t w)) \<Longrightarrow> False"
  proof -
    assume "\<forall>w. set w \<subseteq> TM.TM.symbols (Abs_TM (tm_to_ext_tm tm)) \<longrightarrow>
            TM.time_bounded_word (Abs_TM (tm_to_ext_tm tm)) t w"
    and "\<exists>w. set w \<subseteq> TM.TM.symbols tm \<and> \<not> TM.time_bounded_word tm t w"
    then obtain w :: "'a list" where "set w \<subseteq> TM.TM.symbols tm \<and> \<not> TM.time_bounded_word tm t w" by auto
    have "set (map (\<lambda>x. [x]) w) \<subseteq> TM.TM.symbols (Abs_TM (tm_to_ext_tm tm))"
    proof
      fix x
      assume "x \<in> set (map (\<lambda>x. [x]) w)"
      moreover have "hd x\<in>TM.TM.symbols tm"
        using \<open>set w \<subseteq> TM.TM.symbols tm \<and> \<not> TM.time_bounded_word tm t w\<close> calculation(1) by force
      moreover have "length x = 1"
      proof -
        have "\<And>x. x\<in>TM.TM.symbols (Abs_TM (tm_to_ext_tm tm)) \<Longrightarrow> length x = 1"
          using ext_symbol_length ext_tm_valid valid_tm_symbols by blast
        hence "\<And>x ss. ss \<subseteq> TM.TM.symbols (Abs_TM (tm_to_ext_tm tm)) \<Longrightarrow> x\<in>ss \<Longrightarrow> length x = 1" by auto
        thus "length x = 1" using \<open>x \<in> set (map (\<lambda>x. [x]) w)\<close>
            \<open>set w \<subseteq> TM.TM.symbols tm \<and> \<not> TM.time_bounded_word tm t w\<close> by auto
      qed
      hence "[hd x] = x"
        by (simp add: length_1_hd_iff)
      ultimately show "x \<in> TM.TM.symbols (Abs_TM (tm_to_ext_tm tm))"
        by (metis ext_symbols ext_tm_valid valid_tm_symbols)
    qed
    then obtain w2 :: "'a list list" where "w2 = map (\<lambda>x. [x]) w \<and>
                        set w2 \<subseteq> TM.TM.symbols (Abs_TM (tm_to_ext_tm tm))" by blast
    have "\<not> TM.time_bounded_word tm t w"
      by (simp add: \<open>set w \<subseteq> TM.TM.symbols tm \<and> \<not> TM.time_bounded_word tm t w\<close>)
    moreover have "TM.time_bounded_word (Abs_TM (tm_to_ext_tm tm)) t w2"
      using \<open>w2 = map (\<lambda>x. [x]) w \<and> set w2 \<subseteq> TM.TM.symbols (Abs_TM (tm_to_ext_tm tm))\<close>
      \<open>\<forall>w. set w \<subseteq> TM.TM.symbols (Abs_TM (tm_to_ext_tm tm)) \<longrightarrow> TM.time_bounded_word (Abs_TM (tm_to_ext_tm tm)) t w\<close>
      by auto
    moreover have "TM.time_bounded_word tm t w" using calculation(2)
      \<open>set w \<subseteq> TM.TM.symbols tm \<and> \<not> TM.time_bounded_word tm t w\<close> time_bounded_word_ext
      \<open>w2 = map (\<lambda>x. [x]) w \<and> set w2 \<subseteq> TM.TM.symbols (Abs_TM (tm_to_ext_tm tm))\<close> by auto
    ultimately show "False" by auto
  qed
  moreover have "(\<forall>w. set w \<subseteq> TM.TM.symbols tm \<longrightarrow> TM.time_bounded_word tm t w) \<Longrightarrow>
                 (\<exists>w. set w \<subseteq> TM.TM.symbols (Abs_TM (tm_to_ext_tm tm)) \<and>
                 \<not>(TM.time_bounded_word (Abs_TM (tm_to_ext_tm tm))) t w) \<Longrightarrow> False"
  proof -
    assume "\<forall>w. set w \<subseteq> TM.TM.symbols tm \<longrightarrow> TM.time_bounded_word tm t w"
    and "\<exists>w. set w \<subseteq> TM.TM.symbols (Abs_TM (tm_to_ext_tm tm)) \<and>
         \<not> TM.time_bounded_word (Abs_TM (tm_to_ext_tm tm)) t w"
    then obtain w :: "'a list list" where wdef: "set w \<subseteq> TM.TM.symbols (Abs_TM (tm_to_ext_tm tm)) \<and>
         \<not> TM.time_bounded_word (Abs_TM (tm_to_ext_tm tm)) t w" by auto
    have "set (map (\<lambda>x. hd x) w) \<subseteq> TM.TM.symbols tm"
    proof
      fix x
      assume "x \<in> set (map hd w)"
      have "\<And>x. x\<in>set w \<Longrightarrow> length x = 1"
        using wdef ext_symbol_length ext_tm_valid valid_tm_symbols by blast
      hence "\<And>x. x\<in>set w \<Longrightarrow> \<exists>y. x = [y]"
        by (metis One_nat_def length_1_ex_iff)
      hence "\<And>x. x\<in>set w \<Longrightarrow> [hd x] = x" using list.sel(1) by fastforce
      hence "[x]\<in>TM.TM.symbols (Abs_TM (tm_to_ext_tm tm))"
        using \<open>x \<in> set (map hd w)\<close> wdef by force
      thus"x \<in> TM.TM.symbols tm"
        by (metis ext_symbols ext_tm_valid valid_tm_symbols)
    qed
    then obtain w2 :: "'a list" where w2def: "w2 = map (\<lambda>x. hd x) w \<and> set w2 \<subseteq> TM.TM.symbols tm" by blast
    have "\<not> TM.time_bounded_word (Abs_TM (tm_to_ext_tm tm)) t w" using wdef by blast
    moreover have "TM.time_bounded_word tm t w2"
      using \<open>\<forall>w. set w \<subseteq> TM.TM.symbols tm \<longrightarrow> TM.time_bounded_word tm t w\<close> w2def by blast
    have "\<And>x. x\<in>set w \<Longrightarrow> length x = 1"
      using wdef ext_symbol_length ext_tm_valid valid_tm_symbols by blast
    hence "\<And>x. x\<in>set w \<Longrightarrow> \<exists>y. x = [y]"
      by (metis One_nat_def length_1_ex_iff)
    hence "\<And>x. x\<in>set w \<Longrightarrow> [hd x] = x"
      using list.sel(1) by fastforce
    hence "map (\<lambda>x. [x]) w2 = w" using wdef w2def
      by (simp add: \<open>\<And>x. x \<in> set w \<Longrightarrow> [hd x] = x\<close> list.map_ident_strong)
    moreover have "TM.time_bounded_word (Abs_TM (tm_to_ext_tm tm)) t w" using \<open>map (\<lambda>x. [x]) w2 = w\<close>
      time_bounded_word_ext \<open>\<forall>w. set w \<subseteq> TM.TM.symbols tm \<longrightarrow> TM.time_bounded_word tm t w\<close>
      \<open>TM.time_bounded_word tm t w2\<close> by blast
    ultimately show "False" by auto
  qed
  ultimately show "(\<forall>w. set w \<subseteq> TM.TM.symbols (Abs_TM (tm_to_ext_tm tm)) \<longrightarrow>
                   TM.time_bounded_word (Abs_TM (tm_to_ext_tm tm)) t w) \<noteq>
                   (\<forall>w. set w \<subseteq> TM.TM.symbols tm \<longrightarrow> TM.time_bounded_word tm t w) \<Longrightarrow> False" by blast
qed

lemma tm_single_symbol_run: "s \<in> TM.symbols M \<Longrightarrow> \<exists>M'::('q, 's, 'l) TM. TM.symbols M' = {s} \<and>
                             (\<forall>k n. state (TM.run M' k (replicate n s)) =
                             state (TM.run (M::('q, 's, 'l) TM) k (replicate n s))) \<and>
                             TM.final_states M' = TM.final_states M"
proof -
  assume a1: "s \<in> TM.symbols M"
  hence some_s_in_options: "Some s \<in> options (TM.symbols M)" by simp
  have card_is_Suc: "card (options (TM.symbols M)) = Suc (card (TM.symbols M))"
    by (simp add: card_image options_def)
  obtain f_pre :: "'s option \<Rightarrow> nat" where
    f_pre_bij: "bij_betw f_pre (options (TM.symbols M)) {0..card (TM.symbols M)}"
    by (metis atLeastLessThanSuc_atLeastAtMost card_gt_0_iff card_is_Suc ex_bij_betw_finite_nat
        zero_less_Suc)
  have 1: "Suc 0 \<le> card (TM.TM.symbols M)" by (simp add: Suc_leI card_gt_0_iff)
  note bij_two_fixed [OF f_pre_bij None_in_options some_s_in_options, of 0 1, simplified, OF 1]
  then obtain f :: "'s option \<Rightarrow> nat" where
    f_bij: "bij_betw f (options (TM.TM.symbols M)) {0..card (TM.TM.symbols M)}" and
    f_None_0: "f None = 0" and f_s_1: "f (Some s) = 1" by auto
  define f' :: "nat \<Rightarrow> 's option" where "f' \<equiv> inv_into (options (TM.TM.symbols M)) f"
  have f'_bij: "bij_betw f' {0..card (TM.TM.symbols M)} (options (TM.TM.symbols M))"
    using f_bij unfolding f'_def by (rule bij_betw_inv_into)
  have f_f': "\<And>n. n \<in> {0..card (TM.TM.symbols M)} \<Longrightarrow> f (f' n) = n"
    unfolding f'_def using f_bij by (rule bij_betw_inv_into_right)
  have f'_f: "\<And>s. s \<in> (options (TM.TM.symbols M)) \<Longrightarrow> f' (f s) = s"
    unfolding f'_def using f_bij by (rule bij_betw_inv_into_left)
  have f'_0_None: "f' 0 = None"
    using f_None_0 f'_f [OF None_in_options] by simp
  have f'_1_s: "f' 1 = Some s"
    using f_s_1 f'_f [OF some_s_in_options] by simp
  define original_hd :: "'s option list \<Rightarrow> 's option" where
    "\<And>hds. original_hd hds \<equiv> f' (length (filter (\<lambda>s. s \<noteq> None) hds))"
  define original_hds :: "'s option list \<Rightarrow> 's option list" where
    "\<And>hds. original_hds hds \<equiv> map original_hd (chunks (card (TM.symbols M)) hds)"
  define M' :: "('q, 's, 'l) TM_record" where
    "M' \<equiv> TM (TM.tape_count M * card (TM.symbols M)) {s} (TM.states M) (TM.initial_state M)
            (TM.final_states M) (TM.label M) (\<lambda>st hds. TM.next_state M st (original_hds hds))
            (\<lambda>st hds k. let nw = TM.next_write M st (original_hds hds)
              (k div card (TM.symbols M)) in if k mod card (TM.symbols M) < f nw then Some s else None)
            (\<lambda>st hds k. TM.next_move M st (original_hds hds) (k div card (TM.symbols M)))"
  have valid_M' [simp, intro]: "valid_TM M'"
    apply unfold_locales
    unfolding M'_def apply auto
      apply (metis card_gt_0_iff TM.symbol_axioms(1) TM_axioms(9))
     apply (erule TM.next_state_valid)
    unfolding original_hds_def apply auto
      apply (subst length_chunks_dvd)
       apply simp_all
    unfolding original_hd_def apply auto
  proof -
    fix hds z :: "'s option list"
    assume a1: "length hds = TM.TM.tape_count M * card (TM.TM.symbols M)" and
           a2: "set hds \<subseteq> options {s}" and
           a3: "z \<in> set (chunks (card (TM.TM.symbols M)) hds)"
    have 1: "length (filter (\<lambda>s. \<exists>y. s = Some y) z) \<le> card (TM.symbols M)"
      using a3 by (metis TM.symbol_axioms(1,2) a1 card_gt_0_iff chunks_length_eq dvd_triv_right
          length_chunks_dvd length_filter_le set_listE)
    show "f' (length (filter (\<lambda>s. \<exists>y. s = Some y) z)) \<in> options (TM.TM.symbols M)"
      using f'_bij [unfolded bij_betw_def, THEN conjunct2] 1 by fastforce
  qed
  show "\<exists>M'::('q, 's, 'l) TM. TM.symbols M' = {s} \<and>
        (\<forall>k n. state (TM.run M' k (replicate n s)) =
        state (TM.run (M::('q, 's, 'l) TM) k (replicate n s))) \<and>
         TM.TM.final_states M' = TM.TM.final_states M"
  proof (rule exI [where x="Abs_TM M'"], auto)
    fix k n :: nat
    have syms: "TM.TM.symbols (Abs_TM M') = {s}"
      unfolding valid_tm_symbols [OF valid_M'] unfolding M'_def by simp
    show "\<And>x. x \<in> TM.TM.symbols (Abs_TM M') \<Longrightarrow> x = s"
      unfolding syms by simp
    show "s \<in> TM.TM.symbols (Abs_TM M')"
      unfolding syms ..
    have f11: "cstate (TM.csteps (Abs_TM M') k (TM.cinitial_config (Abs_TM M') (s \<up> n))) =
               cstate (TM.csteps M k (TM.cinitial_config M (s \<up> n)))" and
         f12: "\<And>i. original_hds (map (\<lambda>ts. nth_ctape ts i) (ctapes (TM.csteps (Abs_TM M') k
               (TM.cinitial_config (Abs_TM M') (s \<up> n))))) =
               map (\<lambda>ts. nth_ctape ts i) (ctapes (TM.csteps M k
               (TM.cinitial_config M (s \<up> n))))"
    proof (induction k)
      case 0
      {
        case 1
        then show ?case apply (simp add: TM.cinitial_config_def)
          unfolding valid_tm_initial_state [OF valid_M'] unfolding M'_def by simp
      next
        case 2
        show ?case unfolding original_hds_def apply (rule nth_equalityI)
          unfolding original_hd_def apply auto
           apply (metis (no_types, lifting) M'_def TM.symbol_axioms(1,2) card_eq_0_iff dvd_triv_right
              length_chunks_dvd length_ctapes_initial_config length_map nonzero_mult_div_cancel_right
              simps(1) valid_M' valid_tm_tape_count)
        proof -
          fix j :: nat
          assume a1: "j < length (chunks (card (TM.TM.symbols M))
                      (map (\<lambda>ts. nth_ctape ts i) (ctapes (TM.cinitial_config (Abs_TM M') (s \<up> n)))))"
          have 3: "length (filter (\<lambda>s. \<exists>y. s = Some y) (take (card (TM.TM.symbols M))
                   (drop (card (TM.TM.symbols M) * j)
                   (None # None \<up> (TM.TM.tape_count (Abs_TM M') - Suc 0))))) = 0"
            by (smt (verit, best) filter_empty_conv in_set_dropD in_set_replicate in_set_takeD
                list.size(3) option.distinct(1) replicate_Suc)
          have 4: "take (card (TM.TM.symbols M)) (Some s # None \<up> (TM.TM.tape_count (Abs_TM M') - Suc 0)) =
                   Some s # None \<up> (min (TM.TM.tape_count (Abs_TM M') - Suc 0) (card (TM.symbols M) - Suc 0))"
            by (simp add: take_Cons')
          have 5: "length (filter (\<lambda>s. \<exists>y. s = Some y) (take (card (TM.TM.symbols M))
                   (Some s # None \<up> (TM.TM.tape_count (Abs_TM M') - Suc 0)))) = 1"
            apply simp
            unfolding length_1_ex_iff apply (rule exI [where x="Some s"])
            unfolding 4 filter.simps(2) by simp
          have 6: "length (filter (\<lambda>s. \<exists>y. s = Some y)
                   (take (card (TM.TM.symbols M)) (None # None \<up> (TM.TM.tape_count (Abs_TM M') - Suc 0)))) = 0"
            unfolding take.simps(2) apply simp
            apply (cases "card (TM.TM.symbols M)")
            by simp_all
          have 7: "j < TM.tape_count M" using a1 apply (subst (asm) length_chunks_dvd)
             apply auto
            unfolding valid_tm_tape_count [OF valid_M'] unfolding M'_def by simp_all
          have 8: "j > 0 \<Longrightarrow>
                   drop (card (TM.TM.symbols M) * j) (Some s # None \<up> (TM.TM.tape_count (Abs_TM M') - Suc 0)) =
                   None \<up> (TM.TM.tape_count (Abs_TM M') - (card (TM.symbols M) * j))"
            apply (rule nth_equalityI)
             apply auto
            unfolding nth_Cons' apply auto
            apply (subst nth_replicate)
             apply auto
            by (smt (verit, best) M'_def Suc_pred add.commute add_gr_0 bot_nat_0.not_eq_extremum
                diff_less_mono less_diff_conv nat_0_less_mult_iff nat_less_le simps(1) valid_M'
                valid_tm_tape_count zero_less_diff)
          have 9: "take (card (TM.TM.symbols M))
                   (None \<up> (TM.TM.tape_count (Abs_TM M') - card (TM.TM.symbols M) * j)) =
                   None \<up> card (TM.symbols M)"
            apply (rule nth_equalityI)
             apply (auto simp add: valid_tm_tape_count [OF valid_M'])
            unfolding M'_def apply simp
            by (metis 7 One_nat_def diff_mult_distrib[of "TM.TM.tape_count M" j "card (TM.TM.symbols M)"]
                less_not_refl[of "0"]
                min.commute[of "Suc 0 * (card (TM.TM.symbols M) * Suc undefined)"
                  "Suc 0 * card (TM.TM.symbols M)"]
                min.commute[of _ "0"] min_0R min_Suc_Suc[of "0"] min_Suc_Suc[of undefined "0"]
                mult.commute[of "min (card (TM.TM.symbols M)) (card (TM.TM.symbols M) * Suc undefined)"
                  "TM.TM.tape_count M - j"]
                mult.commute[of "min (card (TM.TM.symbols M)) (card (TM.TM.symbols M) * Suc undefined)" "Suc 0"]
                mult.commute[of "card (TM.TM.symbols M)" j] mult.commute[of "card (TM.TM.symbols M)" "Suc 0"]
                mult.right_neutral[of "min (card (TM.TM.symbols M)) (card (TM.TM.symbols M) * Suc undefined)"]
                mult.right_neutral[of "card (TM.TM.symbols M)"]
                nat_mult_min_right[of "card (TM.TM.symbols M)" "Suc 0" "TM.TM.tape_count M - j"]
                nat_mult_min_right[of "card (TM.TM.symbols M)" "Suc undefined" "Suc 0"]
                nat_mult_min_right[of "Suc 0" "card (TM.TM.symbols M)" "card (TM.TM.symbols M) * Suc undefined"]
                nat_mult_min_right[of "Suc 0" "card (TM.TM.symbols M) * Suc undefined" "card (TM.TM.symbols M)"]
                not0_implies_Suc[of "TM.TM.tape_count M - j"] zero_less_diff[of "TM.TM.tape_count M" j])
          show "f' (length (filter (\<lambda>s. \<exists>y. s = Some y) (chunks (card (TM.TM.symbols M))
                (map (\<lambda>ts. nth_ctape ts i) (ctapes (TM.cinitial_config (Abs_TM M') (s \<up> n)))) ! j))) =
                map (\<lambda>ts. nth_ctape ts i) (ctapes (TM.cinitial_config M (s \<up> n))) ! j"
            apply (subst nth_chunks)
            using 1 apply linarith
             apply fact
            apply (subst nth_map)
             apply simp
            using a1 apply (metis (no_types, lifting) M'_def TM.symbol_axioms(1,2) card_gt_0_iff
                div_mult_self_is_m dvd_triv_right length_chunks_dvd length_ctapes_initial_config
                length_map simps(1) valid_M' valid_tm_tape_count)
            unfolding TM.cinitial_config_def TM_abbrevs.cinput_tape_def apply auto
            unfolding 3 f'_0_None
             apply (metis (no_types, lifting) M'_def Suc_pred TM.at_least_one_tape TM.symbol_axioms(1,2)
                a1 card_gt_0_iff div_mult_self_is_m dvd_triv_right length_chunks_dvd
                length_ctapes_initial_config length_map nth_ctape_empty_ctape
                nth_replicate replicate_Suc simps(1) valid_M' valid_tm_tape_count)
            apply (cases "j = 0")
             apply simp_all
            apply (cases "i = 0")
              apply (simp_all add: nth_ctape_0)
            unfolding 5 f'_1_s apply standard
             apply (cases "i > 0")
              apply (simp_all add: nth_ctape_pos)
              apply (cases "i - 1 < n - Suc 0")
               apply (simp add: prepend_list_nth_less)
            unfolding 5 f'_1_s apply standard
              apply (simp add: prepend_list_nth_ge)
            unfolding 6 apply (rule f'_0_None)
             apply (simp add: nth_ctape_neg)
            unfolding 6 apply (rule f'_0_None)
            apply (cases "i = 0")
             apply (simp add: nth_ctape_0)
            unfolding 8 9 apply simp
            unfolding f'_0_None empty_ctape_def apply (simp add: 7 diff_less_mono)
            apply (cases "i > 0")
             apply (simp add: nth_ctape_pos)
             apply (cases "i - 1 < n - Suc 0")
              apply (simp add: prepend_list_nth_less 8 f'_0_None)
              apply (simp add: 7 diff_less_mono)
             apply (simp add: prepend_list_nth_ge 3)
             apply (simp add: 7 diff_less_mono f'_0_None)
            apply (simp add: nth_ctape_neg 3)
            by (simp add: 7 diff_less_mono f'_0_None)
        qed
      }
    next
      case (Suc k)
      {
        case 1
        have 2: "original_hds (cheads ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') (s \<up> n)))) =
                 cheads ((TM.cstep M ^^ k) (TM.cinitial_config M (s \<up> n)))"
          using Suc(2) [of 0, unfolded nth_ctape_0] .
        show ?case apply simp
          apply (subst (1 2) TM.cstep_def)
          apply (auto simp add: Suc(1) TM.cstep_not_final_def Let_def valid_tm_final_states)
            apply (simp add: M'_def)
           apply (simp add: M'_def)
          unfolding valid_tm_next_state [OF valid_M'] apply (subst M'_def)
          by (simp add: 2)
      next
        case 2
        have 1: "original_hds (cheads ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') (s \<up> n)))) =
                 cheads ((TM.cstep M ^^ k) (TM.cinitial_config M (s \<up> n)))"
          using Suc(2) [of 0, unfolded nth_ctape_0] .
        have 2: "\<And>i. i < TM.TM.tape_count (Abs_TM M') div card (TM.TM.symbols M) \<Longrightarrow> i < TM.tape_count M"
          unfolding valid_tm_tape_count [OF valid_M'] unfolding M'_def by simp
        show ?case apply simp
          apply (cases "cstate (TM.csteps (Abs_TM M') k (TM.cinitial_config (Abs_TM M') (s \<up> n))) \<in>
                        TM.final_states M")
           apply (subst (1 2) TM.cstep_def)
           apply auto[1]
              apply (rule Suc(2))
             apply (subst (asm) Suc(1))
             apply simp
            apply (simp add: valid_tm_final_states)
            apply (simp add: M'_def)
           apply (subst (asm) Suc(1))
           apply simp
          apply (rule nth_equalityI)
           apply auto
          unfolding original_hds_def apply simp
           apply (subst length_chunks_dvd)
            apply simp_all
          using M'_def valid_tm_tape_count apply fastforce
          using M'_def valid_tm_tape_count apply fastforce
          apply (subst (asm) length_chunks_dvd)
           apply auto
          using M'_def valid_tm_tape_count apply fastforce
          apply (subst nth_map)
           apply simp_all
          using 2 apply presburger
          unfolding original_hd_def apply simp
          apply (subst nth_chunks)
            apply (metis TM.symbol_axioms(2) TM.symbol_axioms(1) card_eq_0_iff neq0_conv)
           apply (metis (no_types, lifting) M'_def dual_order.refl dvd_triv_right length_chunks_dvd
              length_ctapes_cstep length_ctapes_csteps_eq_tc length_map simps(1) valid_M'
              valid_tm_tape_count)
        proof -
          fix j :: nat
          assume a1: "cstate ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') (s \<up> n))) \<notin>
                      TM.TM.final_states M" and
                 a2: "j < TM.TM.tape_count (Abs_TM M') div card (TM.TM.symbols M)"
          have 1: "take (card (TM.TM.symbols M)) (drop (card (TM.TM.symbols M) * j) (map (\<lambda>ts. nth_ctape ts i)
                   (ctapes (TM.cstep (Abs_TM M')
                   ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') (s \<up> n))))))) =
                   map (\<lambda>l. nth_ctape (ctapes (TM.cstep (Abs_TM M')
                   ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') (s \<up> n)))) ! l) i)
                   [card (TM.TM.symbols M) * j..<card (TM.TM.symbols M) * (j + 1)]"
            apply (rule nth_equalityI)
             apply auto
            by (smt (verit, ccfv_threshold) M'_def Suc_diff_Suc a2 diff_is_0_eq diff_mult_distrib
                div_mult_self_is_m le_add_diff_inverse2 linorder_not_less min_def mult.commute mult_0_right
                nat_0_less_mult_iff nat_less_le nat_mult_add_lt simps(1) valid_M' valid_tm_tape_count
                zero_less_Suc)
          have *: "l < card (TM.TM.symbols M) + card (TM.TM.symbols M) * j \<Longrightarrow>
                   j < TM.TM.tape_count M \<Longrightarrow> l < TM.TM.tape_count M * card (TM.TM.symbols M)" for l :: nat
          proof -
            assume a3: "l < card (TM.TM.symbols M) + card (TM.TM.symbols M) * j" and
                   a4: "j < TM.TM.tape_count M"
            have 1: "card (TM.TM.symbols M) + card (TM.TM.symbols M) * j = card (TM.TM.symbols M) * (j + 1)"
              by simp
            have 2: "j + 1 \<le> TM.tape_count M" using a4 by simp
            show "l < TM.TM.tape_count M * card (TM.TM.symbols M)" using 2 a3 [unfolded 1]
              by (smt (verit, best) lambda_zero less_mult_imp_div_less linorder_not_less mult.commute
                  nonzero_mult_div_cancel_right order_less_le_trans)
          qed
          have 2: "l \<ge> card (TM.TM.symbols M) * j \<Longrightarrow> l < card (TM.TM.symbols M) * (j + 1) \<Longrightarrow>
                   TM.next_move (Abs_TM M') (cstate ((TM.cstep (Abs_TM M') ^^ k)
                   (TM.cinitial_config (Abs_TM M') (s \<up> n)))) (cheads ((TM.cstep (Abs_TM M') ^^ k)
                   (TM.cinitial_config (Abs_TM M') (s \<up> n)))) l = Shift_Left \<Longrightarrow> i = 1 \<Longrightarrow>
                   nth_ctape (ctapes (TM.cstep (Abs_TM M')
                   ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') (s \<up> n)))) ! l) 1 =
                   TM.next_write (Abs_TM M') (cstate ((TM.cstep (Abs_TM M') ^^ k)
                   (TM.cinitial_config (Abs_TM M') (s \<up> n)))) (cheads ((TM.cstep (Abs_TM M') ^^ k)
                   (TM.cinitial_config (Abs_TM M') (s \<up> n)))) l" for l :: nat
            apply (erule nth_ctape_cstep_Shift_Left2)
            using a1 unfolding valid_tm_final_states [OF valid_M'] apply (simp add: M'_def)
             apply simp
            unfolding valid_tm_tape_count [OF valid_M'] apply (simp_all add: M'_def)
            using a2 unfolding valid_tm_tape_count [OF valid_M'] unfolding M'_def apply simp_all
            by (erule (1) *)+
          have 3: "l \<ge> card (TM.TM.symbols M) * j \<Longrightarrow> l < card (TM.TM.symbols M) * (j + 1) \<Longrightarrow>
                   TM.next_move (Abs_TM M') (cstate ((TM.cstep (Abs_TM M') ^^ k)
                   (TM.cinitial_config (Abs_TM M') (s \<up> n)))) (cheads ((TM.cstep (Abs_TM M') ^^ k)
                   (TM.cinitial_config (Abs_TM M') (s \<up> n)))) l = Shift_Left \<Longrightarrow> i \<noteq> 1 \<Longrightarrow>
                   nth_ctape (ctapes (TM.cstep (Abs_TM M')
                   ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') (s \<up> n)))) ! l) i =
                   nth_ctape (ctapes ((TM.cstep (Abs_TM M') ^^ k)
                   (TM.cinitial_config (Abs_TM M') (s \<up> n))) ! l) (i - 1)" for l :: nat
            apply (erule nth_ctape_cstep_Shift_Left1)
            using a1 unfolding valid_tm_final_states [OF valid_M'] apply (simp add: M'_def)
              using a2 apply (simp_all add: valid_tm_tape_count)
              unfolding M'_def apply simp_all
              by (erule (1) *)+
          have 4: "l \<ge> card (TM.TM.symbols M) * j \<Longrightarrow> l < card (TM.TM.symbols M) * (j + 1) \<Longrightarrow>
                   TM.next_move (Abs_TM M') (cstate ((TM.cstep (Abs_TM M') ^^ k)
                   (TM.cinitial_config (Abs_TM M') (s \<up> n)))) (cheads ((TM.cstep (Abs_TM M') ^^ k)
                   (TM.cinitial_config (Abs_TM M') (s \<up> n)))) l = Shift_Right \<Longrightarrow> i = -1 \<Longrightarrow>
                   nth_ctape (ctapes (TM.cstep (Abs_TM M')
                   ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') (s \<up> n)))) ! l) (-1) =
                   TM.next_write (Abs_TM M') (cstate ((TM.cstep (Abs_TM M') ^^ k)
                   (TM.cinitial_config (Abs_TM M') (s \<up> n)))) (cheads ((TM.cstep (Abs_TM M') ^^ k)
                   (TM.cinitial_config (Abs_TM M') (s \<up> n)))) l" for l :: nat
            apply (erule nth_ctape_cstep_Shift_Right2)
            using a1 unfolding valid_tm_final_states [OF valid_M'] apply (simp add: M'_def)
             apply simp
            unfolding valid_tm_tape_count [OF valid_M'] apply (simp_all add: M'_def)
            using a2 unfolding valid_tm_tape_count [OF valid_M'] unfolding M'_def apply simp_all
            by (erule (1) *)+
          have 5: "l \<ge> card (TM.TM.symbols M) * j \<Longrightarrow> l < card (TM.TM.symbols M) * (j + 1) \<Longrightarrow>
                   TM.next_move (Abs_TM M') (cstate ((TM.cstep (Abs_TM M') ^^ k)
                   (TM.cinitial_config (Abs_TM M') (s \<up> n)))) (cheads ((TM.cstep (Abs_TM M') ^^ k)
                   (TM.cinitial_config (Abs_TM M') (s \<up> n)))) l = Shift_Right \<Longrightarrow> i \<noteq> -1 \<Longrightarrow>
                   nth_ctape (ctapes (TM.cstep (Abs_TM M')
                   ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') (s \<up> n)))) ! l) i =
                   nth_ctape (ctapes ((TM.cstep (Abs_TM M') ^^ k)
                   (TM.cinitial_config (Abs_TM M') (s \<up> n))) ! l) (i + 1)" for l :: nat
            apply (erule nth_ctape_cstep_Shift_Right1)
            using a1 unfolding valid_tm_final_states [OF valid_M'] apply (simp add: M'_def)
              using a2 apply (simp_all add: valid_tm_tape_count)
              unfolding M'_def apply simp_all
              by (erule (1) *)+
          have 6: "l \<ge> card (TM.TM.symbols M) * j \<Longrightarrow> l < card (TM.TM.symbols M) * (j + 1) \<Longrightarrow>
                   TM.next_move (Abs_TM M') (cstate ((TM.cstep (Abs_TM M') ^^ k)
                   (TM.cinitial_config (Abs_TM M') (s \<up> n)))) (cheads ((TM.cstep (Abs_TM M') ^^ k)
                   (TM.cinitial_config (Abs_TM M') (s \<up> n)))) l = No_Shift \<Longrightarrow> i = 0 \<Longrightarrow>
                   nth_ctape (ctapes (TM.cstep (Abs_TM M')
                   ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') (s \<up> n)))) ! l) 0 =
                   TM.next_write (Abs_TM M') (cstate ((TM.cstep (Abs_TM M') ^^ k)
                   (TM.cinitial_config (Abs_TM M') (s \<up> n)))) (cheads ((TM.cstep (Abs_TM M') ^^ k)
                   (TM.cinitial_config (Abs_TM M') (s \<up> n)))) l" for l :: nat
            apply (erule nth_ctape_cstep_No_Shift2)
            using a1 unfolding valid_tm_final_states [OF valid_M'] apply (simp add: M'_def)
             apply simp
            unfolding valid_tm_tape_count [OF valid_M'] apply (simp_all add: M'_def)
            using a2 unfolding valid_tm_tape_count [OF valid_M'] unfolding M'_def apply simp_all
            by (erule (1) *)+
          have 7: "l \<ge> card (TM.TM.symbols M) * j \<Longrightarrow> l < card (TM.TM.symbols M) * (j + 1) \<Longrightarrow>
                   TM.next_move (Abs_TM M') (cstate ((TM.cstep (Abs_TM M') ^^ k)
                   (TM.cinitial_config (Abs_TM M') (s \<up> n)))) (cheads ((TM.cstep (Abs_TM M') ^^ k)
                   (TM.cinitial_config (Abs_TM M') (s \<up> n)))) l = No_Shift \<Longrightarrow> i \<noteq> 0 \<Longrightarrow>
                   nth_ctape (ctapes (TM.cstep (Abs_TM M')
                   ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') (s \<up> n)))) ! l) i =
                   nth_ctape (ctapes ((TM.cstep (Abs_TM M') ^^ k)
                   (TM.cinitial_config (Abs_TM M') (s \<up> n))) ! l) i" for l :: nat
            apply (erule nth_ctape_cstep_No_Shift1)
            using a1 unfolding valid_tm_final_states [OF valid_M'] apply (simp add: M'_def)
              using a2 apply (simp_all add: valid_tm_tape_count)
              unfolding M'_def apply simp_all
              by (erule (1) *)+
          have 8: "TM.TM.next_move M (cstate ((TM.cstep M ^^ k) (TM.cinitial_config M (s \<up> n))))
                   (cheads ((TM.cstep M ^^ k) (TM.cinitial_config M (s \<up> n)))) j = Shift_Left \<Longrightarrow>
                   i = 1 \<Longrightarrow> filter ((\<lambda>s. \<exists>y. s = Some y) \<circ> (\<lambda>l. nth_ctape (ctapes (TM.cstep (Abs_TM M')
                   ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') (s \<up> n)))) ! l) 1))
                   [card (TM.TM.symbols M) * j..<card (TM.TM.symbols M) + card (TM.TM.symbols M) * j] =
                   filter ((\<lambda>s. \<exists>y. s = Some y) \<circ> (\<lambda>l. TM.next_write (Abs_TM M')
                   (cstate ((TM.cstep (Abs_TM M') ^^ k)
                   (TM.cinitial_config (Abs_TM M') (s \<up> n)))) (cheads ((TM.cstep (Abs_TM M') ^^ k)
                   (TM.cinitial_config (Abs_TM M') (s \<up> n)))) l))
                   [card (TM.TM.symbols M) * j..<card (TM.TM.symbols M) + card (TM.TM.symbols M) * j]"
            unfolding filter_eq_iff_nth_eq apply auto
             apply (subst (asm) 2)
                 apply auto
            unfolding valid_tm_next_move [OF valid_M'] Suc(1) apply (subst M'_def)
             apply (simp add: Suc(2) [of 0, unfolded nth_ctape_0])
            apply (subst 2)
                apply (auto simp add: Suc(1))
            unfolding valid_tm_next_move [OF valid_M'] apply (subst M'_def)
            by (simp add: Suc(2) [of 0, unfolded nth_ctape_0])
          have *: "length (filter ((\<lambda>s. \<exists>y. s = Some y) \<circ> (\<lambda>k. if k mod card (TM.TM.symbols M)
                   < f (TM.TM.next_write M (cstate ((TM.cstep M ^^ k) (TM.cinitial_config M (s \<up> n))))
                   (cheads ((TM.cstep M ^^ k) (TM.cinitial_config M (s \<up> n)))) (k div card (TM.TM.symbols M)))
                   then Some s else None))
                   [card (TM.TM.symbols M) * j..<card (TM.TM.symbols M) + card (TM.TM.symbols M) * j]) \<le>
                   card (TM.symbols M)"
            by (metis (no_types, lifting) add_diff_cancel_right' length_filter_le length_upt)
          have **: "TM.TM.next_write M (cstate ((TM.cstep M ^^ k) (TM.cinitial_config M (s \<up> n))))
                    (cheads ((TM.cstep M ^^ k) (TM.cinitial_config M (s \<up> n)))) j \<in> options (TM.symbols M)"
            apply (rule TM.next_write_valid)
            unfolding cotm_steps_congruences(1) apply (rule TM_steps_valid_stateI)
            using \<open>s \<in> TM.symbols M\<close> apply fastforce
              apply simp
            unfolding cotm_heads_steps_congruence apply (rule TM_steps_valid_headsI)
            using \<open>s \<in> TM.symbols M\<close> apply fastforce
            by (metis (no_types, lifting) M'_def TM.symbol_axioms(1,2) a2 card_eq_0_iff
                nonzero_mult_div_cancel_right simps(1) valid_M' valid_tm_tape_count)
          have ***: "length (filter ((\<lambda>s. \<exists>y. s = Some y) \<circ> (\<lambda>k. if k mod card (TM.TM.symbols M)
                     < f (TM.TM.next_write M (cstate ((TM.cstep M ^^ k) (TM.cinitial_config M (s \<up> n))))
                     (cheads ((TM.cstep M ^^ k) (TM.cinitial_config M (s \<up> n)))) (k div card (TM.TM.symbols M)))
                     then Some s else None))
                     [card (TM.TM.symbols M) * j..<card (TM.TM.symbols M) + card (TM.TM.symbols M) * j]) \<in>
                     {0..card (TM.symbols M)}" using * by fastforce
          have 9: "(\<lambda>s. \<exists>y. s = Some y) \<circ> (\<lambda>l. if l mod card (TM.TM.symbols M)
                   < f (TM.TM.next_write M (cstate ((TM.cstep M ^^ k) (TM.cinitial_config M (s \<up> n))))
                   (cheads ((TM.cstep M ^^ k) (TM.cinitial_config M (s \<up> n)))) (l div card (TM.TM.symbols M)))
                   then Some s else None) = (\<lambda>l. l mod card (TM.TM.symbols M)
                   < f (TM.TM.next_write M (cstate ((TM.cstep M ^^ k) (TM.cinitial_config M (s \<up> n))))
                   (cheads ((TM.cstep M ^^ k) (TM.cinitial_config M (s \<up> n)))) (l div card (TM.TM.symbols M))))"
            apply (rule ext)
            by simp
          have 10: "filter (\<lambda>l. l mod card (TM.TM.symbols M)
                    < f (TM.TM.next_write M (cstate ((TM.cstep M ^^ k) (TM.cinitial_config M (s \<up> n))))
                    (cheads ((TM.cstep M ^^ k) (TM.cinitial_config M (s \<up> n)))) (l div card (TM.TM.symbols M))))
                    [card (TM.TM.symbols M) * j..<card (TM.TM.symbols M) + card (TM.TM.symbols M) * j] =
                    filter (\<lambda>l. l mod card (TM.TM.symbols M)
                    < f (TM.TM.next_write M (cstate ((TM.cstep M ^^ k) (TM.cinitial_config M (s \<up> n))))
                    (cheads ((TM.cstep M ^^ k) (TM.cinitial_config M (s \<up> n)))) j))
                    [card (TM.TM.symbols M) * j..<card (TM.TM.symbols M) + card (TM.TM.symbols M) * j]"
            unfolding filter_eq_iff_nth_eq by simp
          have 11: "length (filter (\<lambda>l. l mod card (TM.TM.symbols M)
                    < f (TM.TM.next_write M (cstate ((TM.cstep M ^^ k) (TM.cinitial_config M (s \<up> n))))
                    (cheads ((TM.cstep M ^^ k) (TM.cinitial_config M (s \<up> n)))) j))
                    [card (TM.TM.symbols M) * j..<card (TM.TM.symbols M) + card (TM.TM.symbols M) * j]) =
                    length (filter (\<lambda>l. l < f (TM.TM.next_write M (cstate ((TM.cstep M ^^ k)
                    (TM.cinitial_config M (s \<up> n))))
                    (cheads ((TM.cstep M ^^ k) (TM.cinitial_config M (s \<up> n)))) j))
                    [0..<card (TM.TM.symbols M)])"
            apply (rule length_filter_eqI)
            by simp_all
          have 12: "f (TM.TM.next_write M (cstate ((TM.cstep M ^^ k) (TM.cinitial_config M (s \<up> n))))
                    (cheads ((TM.cstep M ^^ k) (TM.cinitial_config M (s \<up> n)))) j) \<in> {0..card (TM.symbols M)}"
            using ** f_bij [unfolded bij_betw_def, THEN conjunct2] by blast
          have 13: "length (filter ((\<lambda>s. \<exists>y. s = Some y) \<circ> (\<lambda>l. if l mod card (TM.TM.symbols M)
                    < f (TM.TM.next_write M (cstate ((TM.cstep M ^^ k) (TM.cinitial_config M (s \<up> n))))
                    (cheads ((TM.cstep M ^^ k) (TM.cinitial_config M (s \<up> n)))) (l div card (TM.TM.symbols M)))
                    then Some s else None))
                    [card (TM.TM.symbols M) * j..<card (TM.TM.symbols M) + card (TM.TM.symbols M) * j]) =
                    f (TM.TM.next_write M (cstate ((TM.cstep M ^^ k) (TM.cinitial_config M (s \<up> n))))
                    (cheads ((TM.cstep M ^^ k) (TM.cinitial_config M (s \<up> n)))) j)"
            unfolding 9 10 11 length_filter_less_eq using 12 by simp
          have 14: "f' (length (filter ((\<lambda>s. \<exists>y. s = Some y) \<circ> (\<lambda>l. if l mod card (TM.TM.symbols M)
                    < f (TM.TM.next_write M (cstate ((TM.cstep M ^^ k) (TM.cinitial_config M (s \<up> n))))
                    (cheads ((TM.cstep M ^^ k) (TM.cinitial_config M (s \<up> n)))) (l div card (TM.TM.symbols M)))
                    then Some s else None))
                    [card (TM.TM.symbols M) * j..<card (TM.TM.symbols M) + card (TM.TM.symbols M) * j])) =
                    TM.TM.next_write M (cstate ((TM.cstep M ^^ k) (TM.cinitial_config M (s \<up> n))))
                    (cheads ((TM.cstep M ^^ k) (TM.cinitial_config M (s \<up> n)))) j"
            using 13 [THEN arg_cong, of f'] apply (subst (asm) f'_f)
            by fact
          have 15: "TM.TM.next_move M (cstate ((TM.cstep M ^^ k) (TM.cinitial_config M (s \<up> n))))
                    (cheads ((TM.cstep M ^^ k) (TM.cinitial_config M (s \<up> n)))) j = Shift_Left \<Longrightarrow>
                    i \<noteq> 1 \<Longrightarrow> filter ((\<lambda>s. \<exists>y. s = Some y) \<circ> (\<lambda>l. nth_ctape (ctapes (TM.cstep (Abs_TM M')
                    ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') (s \<up> n)))) ! l) i))
                    [card (TM.TM.symbols M) * j..<card (TM.TM.symbols M) + card (TM.TM.symbols M) * j] =
                    filter ((\<lambda>s. \<exists>y. s = Some y) \<circ> (\<lambda>l. nth_ctape (ctapes ((TM.cstep (Abs_TM M') ^^ k)
                    (TM.cinitial_config (Abs_TM M') (s \<up> n))) ! l) (i - 1)))
                    [card (TM.TM.symbols M) * j..<card (TM.TM.symbols M) + card (TM.TM.symbols M) * j]"
            unfolding filter_eq_iff_nth_eq apply auto
             apply (subst (asm) nth_ctape_cstep_Shift_Left1)
                  apply auto
            unfolding valid_tm_next_move [OF valid_M'] Suc(1) apply (subst M'_def)
                apply (simp add: Suc(2) [of 0, unfolded nth_ctape_0])
            using a1 unfolding valid_tm_final_states [OF valid_M'] Suc(1) apply (simp add: M'_def)
            unfolding valid_tm_tape_count [OF valid_M'] apply (simp add: M'_def)
              apply (metis (no_types, lifting) M'_def valid_tm_tape_count [OF valid_M'] a2 lambda_zero
                mult.commute nat_mult_add_lt nonzero_mult_div_cancel_right simps(1))
             apply (simp add: M'_def)
             apply (metis (no_types, lifting) M'_def valid_tm_tape_count [OF valid_M'] a2 lambda_zero
                mult.commute nat_mult_add_lt nonzero_mult_div_cancel_right simps(1))
            apply (subst nth_ctape_cstep_Shift_Left1)
                 apply auto
            unfolding Suc(1) valid_tm_next_move [OF valid_M'] apply (subst M'_def)
               apply (simp add: Suc(2) [of 0, unfolded nth_ctape_0])
            using a1 unfolding Suc(1) valid_tm_final_states [OF valid_M'] apply (simp add: M'_def)
            by (smt (verit, best) Euclidean_Rings.div_eq_0_iff M'_def TM.symbol_axioms(1,2)
                valid_tm_tape_count [OF valid_M'] a2 card_eq_0_iff div_less_iff_less_mult div_mult_self4
                lambda_zero nat_arith.rule0 nonzero_mult_div_cancel_right simps(1))+
          have 16: "TM.TM.next_move M (cstate ((TM.cstep M ^^ k) (TM.cinitial_config M (s \<up> n))))
                    (cheads ((TM.cstep M ^^ k) (TM.cinitial_config M (s \<up> n)))) j = Shift_Right \<Longrightarrow>
                    i = -1 \<Longrightarrow> filter ((\<lambda>s. \<exists>y. s = Some y) \<circ> (\<lambda>l. nth_ctape (ctapes (TM.cstep (Abs_TM M')
                    ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') (s \<up> n)))) ! l) (-1)))
                    [card (TM.TM.symbols M) * j..<card (TM.TM.symbols M) + card (TM.TM.symbols M) * j] =
                    filter ((\<lambda>s. \<exists>y. s = Some y) \<circ> (\<lambda>l. TM.next_write (Abs_TM M')
                    (cstate ((TM.cstep (Abs_TM M') ^^ k)
                    (TM.cinitial_config (Abs_TM M') (s \<up> n)))) (cheads ((TM.cstep (Abs_TM M') ^^ k)
                    (TM.cinitial_config (Abs_TM M') (s \<up> n)))) l))
                    [card (TM.TM.symbols M) * j..<card (TM.TM.symbols M) + card (TM.TM.symbols M) * j]"
            unfolding filter_eq_iff_nth_eq apply auto
             apply (subst (asm) 4)
                 apply auto
            unfolding valid_tm_next_move [OF valid_M'] Suc(1) apply (subst M'_def)
             apply (simp add: Suc(2) [of 0, unfolded nth_ctape_0])
            apply (subst 4)
                apply (auto simp add: Suc(1))
            unfolding valid_tm_next_move [OF valid_M'] apply (subst M'_def)
            by (simp add: Suc(2) [of 0, unfolded nth_ctape_0])
          have 17: "TM.TM.next_move M (cstate ((TM.cstep M ^^ k) (TM.cinitial_config M (s \<up> n))))
                    (cheads ((TM.cstep M ^^ k) (TM.cinitial_config M (s \<up> n)))) j = Shift_Right \<Longrightarrow>
                    i \<noteq> -1 \<Longrightarrow> filter ((\<lambda>s. \<exists>y. s = Some y) \<circ> (\<lambda>l. nth_ctape (ctapes (TM.cstep (Abs_TM M')
                    ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') (s \<up> n)))) ! l) i))
                    [card (TM.TM.symbols M) * j..<card (TM.TM.symbols M) + card (TM.TM.symbols M) * j] =
                    filter ((\<lambda>s. \<exists>y. s = Some y) \<circ> (\<lambda>l. nth_ctape (ctapes ((TM.cstep (Abs_TM M') ^^ k)
                    (TM.cinitial_config (Abs_TM M') (s \<up> n))) ! l) (i + 1)))
                    [card (TM.TM.symbols M) * j..<card (TM.TM.symbols M) + card (TM.TM.symbols M) * j]"
            unfolding filter_eq_iff_nth_eq apply auto
             apply (subst (asm) nth_ctape_cstep_Shift_Right1)
                  apply auto
            unfolding valid_tm_next_move [OF valid_M'] Suc(1) apply (subst M'_def)
                apply (simp add: Suc(2) [of 0, unfolded nth_ctape_0])
            using a1 unfolding valid_tm_final_states [OF valid_M'] Suc(1) apply (simp add: M'_def)
            unfolding valid_tm_tape_count [OF valid_M'] apply (simp add: M'_def)
              apply (metis (no_types, lifting) M'_def valid_tm_tape_count [OF valid_M'] a2 lambda_zero
                mult.commute nat_mult_add_lt nonzero_mult_div_cancel_right simps(1))
             apply (simp add: M'_def)
             apply (metis (no_types, lifting) M'_def valid_tm_tape_count [OF valid_M'] a2 lambda_zero
                mult.commute nat_mult_add_lt nonzero_mult_div_cancel_right simps(1))
            apply (subst nth_ctape_cstep_Shift_Right1)
                 apply auto
            unfolding Suc(1) valid_tm_next_move [OF valid_M'] apply (subst M'_def)
               apply (simp add: Suc(2) [of 0, unfolded nth_ctape_0])
            using a1 unfolding Suc(1) valid_tm_final_states [OF valid_M'] apply (simp add: M'_def)
            by (smt (verit, best) Euclidean_Rings.div_eq_0_iff M'_def TM.symbol_axioms(1,2)
                valid_tm_tape_count [OF valid_M'] a2 card_eq_0_iff div_less_iff_less_mult div_mult_self4
                lambda_zero nat_arith.rule0 nonzero_mult_div_cancel_right simps(1))+
          have 18: "TM.TM.next_move M (cstate ((TM.cstep M ^^ k) (TM.cinitial_config M (s \<up> n))))
                    (cheads ((TM.cstep M ^^ k) (TM.cinitial_config M (s \<up> n)))) j = No_Shift \<Longrightarrow>
                    i = 0 \<Longrightarrow> filter ((\<lambda>s. \<exists>y. s = Some y) \<circ> (\<lambda>l. nth_ctape (ctapes (TM.cstep (Abs_TM M')
                    ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') (s \<up> n)))) ! l) 0))
                    [card (TM.TM.symbols M) * j..<card (TM.TM.symbols M) + card (TM.TM.symbols M) * j] =
                    filter ((\<lambda>s. \<exists>y. s = Some y) \<circ> (\<lambda>l. TM.next_write (Abs_TM M')
                    (cstate ((TM.cstep (Abs_TM M') ^^ k)
                    (TM.cinitial_config (Abs_TM M') (s \<up> n)))) (cheads ((TM.cstep (Abs_TM M') ^^ k)
                    (TM.cinitial_config (Abs_TM M') (s \<up> n)))) l))
                    [card (TM.TM.symbols M) * j..<card (TM.TM.symbols M) + card (TM.TM.symbols M) * j]"
            unfolding filter_eq_iff_nth_eq apply auto
             apply (subst (asm) 6)
                 apply auto
            unfolding valid_tm_next_move [OF valid_M'] Suc(1) apply (subst M'_def)
             apply (simp add: Suc(2) [of 0, unfolded nth_ctape_0])
            apply (subst 6)
                apply (auto simp add: Suc(1))
            unfolding valid_tm_next_move [OF valid_M'] apply (subst M'_def)
            by (simp add: Suc(2) [of 0, unfolded nth_ctape_0])
          have 19: "TM.TM.next_move M (cstate ((TM.cstep M ^^ k) (TM.cinitial_config M (s \<up> n))))
                    (cheads ((TM.cstep M ^^ k) (TM.cinitial_config M (s \<up> n)))) j = No_Shift \<Longrightarrow>
                    i \<noteq> 0 \<Longrightarrow> filter ((\<lambda>s. \<exists>y. s = Some y) \<circ> (\<lambda>l. nth_ctape (ctapes (TM.cstep (Abs_TM M')
                    ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') (s \<up> n)))) ! l) i))
                    [card (TM.TM.symbols M) * j..<card (TM.TM.symbols M) + card (TM.TM.symbols M) * j] =
                    filter ((\<lambda>s. \<exists>y. s = Some y) \<circ> (\<lambda>l. nth_ctape (ctapes ((TM.cstep (Abs_TM M') ^^ k)
                    (TM.cinitial_config (Abs_TM M') (s \<up> n))) ! l) i))
                    [card (TM.TM.symbols M) * j..<card (TM.TM.symbols M) + card (TM.TM.symbols M) * j]"
            unfolding filter_eq_iff_nth_eq apply auto
             apply (subst (asm) nth_ctape_cstep_No_Shift1)
                  apply auto
            unfolding valid_tm_next_move [OF valid_M'] Suc(1) apply (subst M'_def)
                apply (simp add: Suc(2) [of 0, unfolded nth_ctape_0])
            using a1 unfolding valid_tm_final_states [OF valid_M'] Suc(1) apply (simp add: M'_def)
            unfolding valid_tm_tape_count [OF valid_M'] apply (simp add: M'_def)
              apply (metis (no_types, lifting) M'_def valid_tm_tape_count [OF valid_M'] a2 lambda_zero
                mult.commute nat_mult_add_lt nonzero_mult_div_cancel_right simps(1))
             apply (simp add: M'_def)
             apply (metis (no_types, lifting) M'_def valid_tm_tape_count [OF valid_M'] a2 lambda_zero
                mult.commute nat_mult_add_lt nonzero_mult_div_cancel_right simps(1))
            apply (subst nth_ctape_cstep_No_Shift1)
                 apply auto
            unfolding Suc(1) valid_tm_next_move [OF valid_M'] apply (subst M'_def)
               apply (simp add: Suc(2) [of 0, unfolded nth_ctape_0])
            using a1 unfolding Suc(1) valid_tm_final_states [OF valid_M'] apply (simp add: M'_def)
            by (smt (verit, best) Euclidean_Rings.div_eq_0_iff M'_def TM.symbol_axioms(1,2)
                valid_tm_tape_count [OF valid_M'] a2 card_eq_0_iff div_less_iff_less_mult div_mult_self4
                lambda_zero nat_arith.rule0 nonzero_mult_div_cancel_right simps(1))+
          show "f' (length (filter (\<lambda>s. \<exists>y. s = Some y) (take (card (TM.TM.symbols M))
                (drop (card (TM.TM.symbols M) * j) (map (\<lambda>ts. nth_ctape ts i) (ctapes (TM.cstep (Abs_TM M')
                ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') (s \<up> n)))))))))) =
                nth_ctape (ctapes (TM.cstep M ((TM.cstep M ^^ k) (TM.cinitial_config M (s \<up> n)))) ! j) i"
            unfolding 1 apply (cases "TM.next_move M (cstate ((TM.cstep M ^^ k)
                                      (TM.cinitial_config M (s \<up> n))))
                                      (cheads ((TM.cstep M ^^ k) (TM.cinitial_config M (s \<up> n)))) j")
              apply (cases "i = 1")
               apply simp
            unfolding 8 Suc(1) valid_tm_next_write [OF valid_M'] apply (subst M'_def)
               apply (simp add: Suc(2) [of 0, unfolded nth_ctape_0])
               apply (subst nth_ctape_cstep_Shift_Left2)
                   apply auto
            using Suc.IH(1) a1 apply argo
            using M'_def a2 valid_tm_tape_count apply fastforce
            using M'_def a2 valid_tm_tape_count apply fastforce
               apply (rule 14)
              apply (subst (2) nth_ctape_cstep_Shift_Left1)
                   apply auto
            using Suc.IH(1) a1 apply argo
                apply (metis (no_types, lifting) M'_def TM.symbol_axioms(1,2) a2 card_gt_0_iff
                div_mult_self1_is_m mult.commute simps(1) valid_M' valid_tm_tape_count)
               apply (metis (no_types, lifting) M'_def TM.symbol_axioms(1,2) a2 card_gt_0_iff
                div_mult_self1_is_m mult.commute simps(1) valid_M' valid_tm_tape_count)
            unfolding 15 using Suc(2) [unfolded original_hds_def original_hd_def, of "i - 1",
                THEN arg_cong, of "\<lambda>l. l ! j"] apply (subst (asm) (1 2) nth_map)
                apply auto
            using M'_def a2 valid_tm_tape_count apply force
               apply (metis (no_types, lifting) M'_def a2 dvd_triv_right length_chunks_dvd
                length_ctapes_csteps_eq_tc length_map simps(1) valid_M' valid_tm_tape_count)
              apply (subst (asm) nth_chunks)
            using bot_nat_0.not_eq_extremum apply fastforce
               apply (metis (no_types, lifting) M'_def a2 dvd_triv_left length_chunks_dvd
                length_ctapes_csteps_eq_tc length_map mult.commute simps(1) valid_M' valid_tm_tape_count)
              apply (erule subst [where t="nth_ctape (ctapes ((TM.cstep M ^^ k)
                      (TM.cinitial_config M (s \<up> n))) ! j) (i - 1)"])
              apply (rule arg_cong [where f=f'])
              apply (rule length_filter_eqI)
               apply auto
                apply (smt (verit, ccfv_threshold) M'_def a2 bot_nat_0.not_eq_extremum diff_is_0_eq
                diff_mult_distrib2 dvd_triv_right linorder_not_less min.absorb1 min.commute
                mult.commute mult_is_0 nat_dvd_not_less nonzero_mult_div_cancel_left simps(1) valid_M'
                valid_tm_tape_count)
               apply (subst nth_drop)
                apply auto
                apply (metis a2 div_imp_mult_less mult.commute nat_less_le)
               apply (subst nth_map)
                apply auto
               apply (smt (verit, best) Euclidean_Rings.div_eq_0_iff M'_def TM.at_least_one_tape a2
                div_less_iff_less_mult div_mult_self4 nat_0_less_mult_iff nat_arith.rule0
                nonzero_mult_div_cancel_right simps(1) valid_M' valid_tm_tape_count)
              apply (subst (asm) nth_drop)
               apply auto
               apply (metis a2 div_imp_mult_less mult.commute nat_less_le)
              apply (subst (asm) nth_map)
               apply auto
            apply (metis (no_types, lifting) M'_def a2 lambda_zero
                mult.commute[of "0" "TM.TM.tape_count (Abs_TM M') div card (TM.TM.symbols M)"]
                mult.commute[of "0" "TM.TM.tape_count M"] mult.commute[of j "card (TM.TM.symbols M)"]
                nat_mult_add_lt[of j "TM.TM.tape_count (Abs_TM M') div card (TM.TM.symbols M)" _ "0"]
                nat_mult_add_lt[of j "TM.TM.tape_count M" _ "card (TM.TM.symbols M)"]
                nonzero_mult_div_cancel_right[of "card (TM.TM.symbols M)" "TM.TM.tape_count M"]
                simps(1)[of "TM.TM.tape_count M * card (TM.TM.symbols M)" "{s}" "TM.TM.states M"
                  "TM.TM.initial_state M" "TM.TM.final_states M" "TM.TM.label M"
                  "\<lambda>uub uuc. TM.TM.next_state M uub (original_hds uuc)" "\<lambda>uud uue uuf.
          if uuf mod card (TM.TM.symbols M)
             < f (TM.TM.next_write M uud (original_hds uue) (uuf div card (TM.TM.symbols M)))
          then Some s else None"
                  "\<lambda>uub uuc uud. TM.TM.next_move M uub (original_hds uuc) (uud div card (TM.TM.symbols M))"
                  "()"] valid_M' valid_tm_tape_count[of M'])
             apply (cases "i = -1")
              apply simp
            unfolding 16 Suc(1) valid_tm_next_write [OF valid_M'] apply (subst M'_def)
              apply (simp add: Suc(2) [of 0, unfolded nth_ctape_0])
            unfolding 14 apply (subst nth_ctape_cstep_Shift_Right2)
                  apply auto
            using a1 unfolding Suc(1) apply simp
            using M'_def a2 valid_tm_tape_count apply force
            using M'_def a2 valid_tm_tape_count apply force
            unfolding 17 apply (subst nth_ctape_cstep_Shift_Right1)
                  apply auto
            using a1 unfolding Suc(1) apply simp
            using M'_def a2 valid_tm_tape_count apply force
            using M'_def a2 valid_tm_tape_count apply force
            using Suc(2) [unfolded original_hds_def original_hd_def, of "i + 1",
                THEN arg_cong, of "\<lambda>l. l ! j"] apply (subst (asm) (1 2) nth_map)
               apply auto
            using M'_def a2 valid_tm_tape_count apply force
              apply (metis (no_types, lifting) M'_def a2 dvd_triv_right length_chunks_dvd
                length_ctapes_csteps_eq_tc length_map simps(1) valid_M' valid_tm_tape_count)
             apply (subst (asm) nth_chunks)
            using card_eq_0_iff apply fastforce
              apply (metis (no_types, lifting) M'_def a2 dvd_triv_right length_chunks_dvd
                length_ctapes_csteps_eq_tc length_map simps(1) valid_M' valid_tm_tape_count)
             apply (erule subst [where t="nth_ctape (ctapes ((TM.cstep M ^^ k)
                  (TM.cinitial_config M (s \<up> n))) ! j) (i + 1)"])
             apply (rule arg_cong [where f=f'])
             apply (rule length_filter_eqI)
              apply auto
            unfolding valid_tm_tape_count [OF valid_M'] apply (simp add: M'_def)
               apply (metis M'_def One_nat_def \<open>TM.TM.tape_count (Abs_TM M') = tape_count M'\<close> a2
                less_not_refl[of "0"] min_0R min_Suc_Suc[of _ "0"] mult.commute[of "TM.TM.tape_count M"
                  "card (TM.TM.symbols M)"] mult.right_neutral[of "card (TM.TM.symbols M)"]
                nat_mult_min_right[of "card (TM.TM.symbols M)" "TM.TM.tape_count M - j" "1"]
                nonzero_mult_div_cancel_left[of "card (TM.TM.symbols M)" "TM.TM.tape_count M"]
                not0_implies_Suc[of "TM.TM.tape_count M - j"]
                right_diff_distrib'[of "card (TM.TM.symbols M)" "TM.TM.tape_count M" j]
                simps(1)[of "TM.TM.tape_count M * card (TM.TM.symbols M)" "{s}" "TM.TM.states M"
                  "TM.TM.initial_state M" "TM.TM.final_states M" "TM.TM.label M"
                  "\<lambda>uub uuc. TM.TM.next_state M uub (original_hds uuc)" "\<lambda>uud uue uuf.
          if uuf mod card (TM.TM.symbols M)
             < f (TM.TM.next_write M uud (original_hds uue) (uuf div card (TM.TM.symbols M)))
          then Some s else None"
                  "\<lambda>uub uuc uud. TM.TM.next_move M uub (original_hds uuc) (uud div card (TM.TM.symbols M))"
                  "()"] zero_less_diff[of "TM.TM.tape_count M" j])
              apply (subst nth_drop)
               apply auto
               apply (metis (no_types, lifting) M'_def valid_tm_tape_count [OF valid_M'] a2 mult.commute
                nat_less_le nat_mult_le_cancel_disj nonzero_mult_div_cancel_left simps(1))
              apply (subst nth_map)
               apply auto
              apply (smt (verit, best) Euclidean_Rings.div_eq_0_iff M'_def TM.at_least_one_tape
                valid_tm_tape_count [OF valid_M'] a2 div_less_iff_less_mult div_mult_self4 nat_0_less_mult_iff
                nat_arith.rule0 nonzero_mult_div_cancel_right simps(1))
             apply (subst (asm) nth_drop)
              apply auto
              apply (metis a2 div_imp_mult_less mult.commute nat_less_le)
             apply (subst (asm) nth_map)
              apply auto
             apply (smt (verit, best) Euclidean_Rings.div_eq_0_iff M'_def TM.at_least_one_tape
                valid_tm_tape_count [OF valid_M'] a2 div_less_iff_less_mult div_mult_self4 nat_0_less_mult_iff
                nat_arith.rule0 nonzero_mult_div_cancel_right simps(1))
            apply (cases "i = 0")
             apply simp
            unfolding 18 Suc(1) valid_tm_next_write [OF valid_M'] apply (subst M'_def)
               apply (simp add: Suc(2) [of 0, unfolded nth_ctape_0])
             apply (subst nth_ctape_cstep_No_Shift2)
                 apply auto
            using a1 unfolding Suc(1) apply simp
            using M'_def valid_tm_tape_count [OF valid_M'] a2 apply force
            using M'_def valid_tm_tape_count [OF valid_M'] a2 apply force
            unfolding 14 apply standard
            unfolding 19 apply (subst nth_ctape_cstep_No_Shift1)
                 apply auto
            using a1 unfolding Suc(1) apply simp
            using M'_def valid_tm_tape_count [OF valid_M'] a2 apply force
            using M'_def valid_tm_tape_count [OF valid_M'] a2 apply force
            using Suc(2) [unfolded original_hds_def original_hd_def, of i,
                THEN arg_cong, of "\<lambda>l. l ! j"] apply (subst (asm) (1 2) nth_map)
              apply auto
            using M'_def valid_tm_tape_count [OF valid_M'] a2 apply force
             apply (metis (no_types, lifting) M'_def valid_tm_tape_count [OF valid_M'] a2 dvd_triv_right
                length_chunks_dvd length_ctapes_csteps_eq_tc length_map simps(1))
            apply (subst (asm) nth_chunks)
            using bot_nat_0.not_eq_extremum apply fastforce
             apply (metis (no_types, lifting) M'_def valid_tm_tape_count [OF valid_M'] a2 dvd_triv_right
                length_chunks_dvd length_ctapes_csteps_eq_tc length_map simps(1))
            apply (erule subst [where t="nth_ctape (ctapes ((TM.cstep M ^^ k)
                (TM.cinitial_config M (s \<up> n))) ! j) i"])
            apply (rule arg_cong [where f=f'])
            apply (rule length_filter_eqI)
             apply auto
            unfolding valid_tm_tape_count [OF valid_M'] apply (simp add: M'_def)
              apply (metis M'_def One_nat_def \<open>TM.TM.tape_count (Abs_TM M') = tape_count M'\<close> a2
                less_not_refl[of "0"] list_decode.cases[of "TM.TM.tape_count M - j"] min_0R
                min_Suc_Suc[of _ "0"] mult.commute[of "TM.TM.tape_count M" "card (TM.TM.symbols M)"]
                mult.right_neutral[of "card (TM.TM.symbols M)"] nat_mult_min_right[of
                  "card (TM.TM.symbols M)" "TM.TM.tape_count M - j" "1"]
                nonzero_mult_div_cancel_left[of "card (TM.TM.symbols M)" "TM.TM.tape_count M"]
                right_diff_distrib'[of "card (TM.TM.symbols M)" "TM.TM.tape_count M" j]
                simps(1)[of "TM.TM.tape_count M * card (TM.TM.symbols M)" "{s}" "TM.TM.states M"
                  "TM.TM.initial_state M" "TM.TM.final_states M" "TM.TM.label M"
                  "\<lambda>uub uuc. TM.TM.next_state M uub (original_hds uuc)" "\<lambda>uud uue uuf.
          if uuf mod card (TM.TM.symbols M)
             < f (TM.TM.next_write M uud (original_hds uue) (uuf div card (TM.TM.symbols M)))
          then Some s else None"
                  "\<lambda>uub uuc uud. TM.TM.next_move M uub (original_hds uuc) (uud div card (TM.TM.symbols M))"
                  "()"] zero_less_diff[of "TM.TM.tape_count M" j])
             apply (subst nth_drop)
              apply auto
              apply (metis a2 div_imp_mult_less mult.commute nat_less_le)
             apply (subst nth_map)
              apply auto
             apply (smt (verit, best) Euclidean_Rings.div_eq_0_iff M'_def TM.at_least_one_tape
                valid_tm_tape_count [OF valid_M'] a2 div_less_iff_less_mult div_mult_self4 nat_0_less_mult_iff
                nat_arith.rule0 nonzero_mult_div_cancel_right simps(1))
            apply (subst (asm) nth_drop)
             apply auto
             apply (metis a2 div_imp_mult_less mult.commute nat_less_le)
            apply (subst (asm) nth_map)
             apply auto
            by (smt (verit, best) Euclidean_Rings.div_eq_0_iff M'_def TM.at_least_one_tape
                valid_tm_tape_count [OF valid_M'] a2 div_less_iff_less_mult div_mult_self4 nat_0_less_mult_iff
                nat_arith.rule0 nonzero_mult_div_cancel_right simps(1))
        qed
      }
    qed
    show "state (TM.run (Abs_TM M') k (s \<up> n)) = state (TM.run M k (s \<up> n))"
      using f11 unfolding TM.run_def cotm_steps_congruences(1) .
    have final_states: "TM.TM.final_states (Abs_TM M') = TM.TM.final_states M"
      unfolding valid_tm_final_states [OF valid_M'] unfolding M'_def by simp
    show "\<And>x. x \<in> TM.TM.final_states (Abs_TM M') \<Longrightarrow> x \<in> TM.TM.final_states M"
      unfolding final_states .
    show "\<And>x. x \<in> TM.TM.final_states M \<Longrightarrow> x \<in> TM.TM.final_states (Abs_TM M')"
      unfolding final_states .
  qed
qed

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

lemma typed_fully_time_constrI:
    "s \<in> TM.symbols M \<Longrightarrow> (\<And>n. TM.time (M::('q, 's, 'l) TM) (replicate n s) = T n) \<Longrightarrow>
     typed_fully_time_constr TYPE('q) TYPE('s) TYPE('l) T"
proof (unfold typed_fully_time_constr_def)
  assume a1: "s \<in> TM.symbols M" and
         a2: "\<And>n. TM.time M (replicate n s) = T n"
  define original_hds :: "'s option list \<Rightarrow> 's option list" where
    "\<And>hds. original_hds hds \<equiv> (if hds ! 1 = None then
        map_option (\<lambda>_. s) (hd hds)#(tl (tl hds)) else tl hds)"
  define M' :: "('q, 's, 'l) TM_record" where
    "M' \<equiv> TM (Suc (TM.tape_count M)) (TM.symbols M) (TM.states M) (TM.initial_state M)
           (TM.final_states M) (TM.label M)
           (\<lambda>st hds. TM.next_state M st (original_hds hds))
           (\<lambda>st hds k. if k = 0 then None else
              TM.next_write M st (original_hds hds) (k - 1))
           (\<lambda>st hds k. TM.next_move M st (original_hds hds) (k - 1))"
  have map_option_s_in_syms [simp]: "map_option (\<lambda>_. s) op \<in> options (TM.TM.symbols M)"
    for op :: "'s option" by (cases op) (auto simp add: a1)
  have valid_M' [simp, intro]: "valid_TM M'"
    apply unfold_locales
    unfolding M'_def apply auto
     apply (erule TM.next_state_valid)
    unfolding original_hds_def apply auto
       apply (metis list.sel(2) list.set_sel(2) subset_eq)
      apply (metis subset_eq set_tl_subset)
     apply (erule TM.next_write_valid)
       apply auto
     apply (metis subset_eq set_tl_subset)
    apply (erule TM.next_write_valid)
      apply auto
    by (metis subset_eq set_tl_subset)
  have f11: "cstate (TM.csteps (Abs_TM M') k (TM.cinitial_config (Abs_TM M') w)) =
             cstate (TM.csteps M k (TM.cinitial_config M (s \<up> (length w))))" and
       f12: "\<And>i j. i > 1 \<Longrightarrow> i \<le> TM.tape_count M \<Longrightarrow> nth_ctape (ctapes (TM.csteps (Abs_TM M') k
             (TM.cinitial_config (Abs_TM M') w)) ! i) j = nth_ctape (ctapes (TM.csteps M k
             (TM.cinitial_config M (s \<up> (length w)))) ! (i - 1)) j" and
       f13: "\<And>j. nth_ctape (ctapes (TM.csteps (Abs_TM M') k
             (TM.cinitial_config (Abs_TM M') w)) ! 1) j = None \<Longrightarrow>
             map_option (\<lambda>_. s) (nth_ctape (ctapes (TM.csteps (Abs_TM M') k
             (TM.cinitial_config (Abs_TM M') w)) ! 0) j) = nth_ctape (ctapes (TM.csteps M k
             (TM.cinitial_config M (s \<up> (length w)))) ! 0) j" and
       f14: "\<And>j. nth_ctape (ctapes (TM.csteps (Abs_TM M') k
             (TM.cinitial_config (Abs_TM M') w)) ! 1) j \<noteq> None \<Longrightarrow>
             nth_ctape (ctapes (TM.csteps (Abs_TM M') k
             (TM.cinitial_config (Abs_TM M') w)) ! 1) j =
             nth_ctape (ctapes (TM.csteps M k
             (TM.cinitial_config M (s \<up> (length w)))) ! 0) j"
       for w :: "'s list" and k :: nat
  proof (induction k)
    case 0
    {
      case 1
      then show ?case apply (simp add: TM.cinitial_config_def)
        unfolding valid_tm_initial_state [OF valid_M'] unfolding M'_def by simp
    next
      case 2
      then show ?case apply simp
        unfolding TM.cinitial_config_def apply simp
        unfolding valid_tm_tape_count [OF valid_M'] unfolding M'_def by simp
    next
      case 3
      then show ?case apply simp
        unfolding TM.cinitial_config_def TM_abbrevs.cinput_tape_def apply auto
        apply (cases j)
         apply (cases "j = 0")
          apply auto
        unfolding nth_ctape_0 apply simp
         apply (subst (1 2) nth_ctape_pos)
          apply auto
         apply (drule sym [where s=j])
         apply simp
         apply (cases "j - 1 < length (tl w)")
          apply simp
          apply (subst (1 2) prepend_list_nth_less)
            apply auto
         apply (subst (1 2) prepend_list_nth_ge)
           apply auto
        apply (subst (1 2) nth_ctape_neg)
        by simp_all
    next
      case 4
      then show ?case apply (auto simp add: TM.cinitial_config_def empty_ctape_def
            nth_ctape_def)
        using M'_def valid_tm_tape_count by force+
    }
  next
    case (Suc k)
    have original_hds_eq [simp]: "original_hds (cheads ((TM.cstep (Abs_TM M') ^^ k)
                                  (TM.cinitial_config (Abs_TM M') w))) =
                                  cheads ((TM.cstep M ^^ k)
                                  (TM.cinitial_config M (s \<up> length w)))"
        unfolding original_hds_def apply auto
      proof (rule nth_equalityI, auto)
        assume a1: "cheads ((TM.cstep (Abs_TM M') ^^ k)
                    (TM.cinitial_config (Abs_TM M') w)) ! Suc 0 = None"
        show lengths: "Suc (TM.TM.tape_count (Abs_TM M') - Suc (Suc 0)) = TM.TM.tape_count M"
          unfolding valid_tm_tape_count [OF valid_M'] unfolding M'_def by simp
        fix i :: nat
        assume a2: "i < Suc (TM.TM.tape_count (Abs_TM M') - Suc (Suc 0))"
        show "(map_option (\<lambda>_. s) (hd (cheads ((TM.cstep (Abs_TM M') ^^ k)
              (TM.cinitial_config (Abs_TM M') w)))) #
              tl (tl (cheads ((TM.cstep (Abs_TM M') ^^ k)
              (TM.cinitial_config (Abs_TM M') w))))) ! i =
              cheads ((TM.cstep M ^^ k) (TM.cinitial_config M (s \<up> length w))) ! i"
          unfolding nth_Cons' apply auto
          apply (smt (verit, best) M'_def One_nat_def Suc.IH(3) Zero_not_Suc
              \<open>Suc (TM.TM.tape_count (Abs_TM M') - Suc (Suc 0)) = TM.TM.tape_count M\<close> a1
              diff_Suc_1' diff_is_0_eq hd_conv_nth length_ctapes_csteps_eq_tc
              linorder_not_le list.map_sel(1) list.size(3) nth_ctape_0 nth_map simps(1)
              valid_M' valid_tm_tape_count)
          apply (subst nth_tl)
          using a2 apply simp
          apply simp
          apply (subst nth_tl)
          using a2 apply simp
          apply (subst (1 2) nth_map)
          using a2 apply simp_all
          using lengths apply argo
          apply (subst Suc(2) [THEN nth_ctape_inject])
            apply auto
          by (simp add: lengths)
      next
        fix y :: 's
        assume a1: "cheads ((TM.cstep (Abs_TM M') ^^ k)
                    (TM.cinitial_config (Abs_TM M') w)) ! Suc 0 = Some y"
        show "tl (cheads ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w))) =
              cheads ((TM.cstep M ^^ k) (TM.cinitial_config M (s \<up> length w)))"
        proof (rule nth_equalityI, auto)
          show lengths: "TM.TM.tape_count (Abs_TM M') - Suc 0 = TM.TM.tape_count M"
            unfolding valid_tm_tape_count [OF valid_M'] unfolding M'_def by simp
          fix i ::nat
          assume a2: "i < TM.TM.tape_count (Abs_TM M') - Suc 0"
          show "tl (cheads ((TM.cstep (Abs_TM M') ^^ k)
                (TM.cinitial_config (Abs_TM M') w))) ! i =
                cheads ((TM.cstep M ^^ k) (TM.cinitial_config M (s \<up> length w))) ! i"
            apply (subst nth_tl)
             apply auto
             apply fact
            apply (insert a1)
            apply (subst (1 2) nth_map)
              apply auto
            using a2 lengths apply simp_all
            apply (cases "i = 0")
            using Suc(4) [simplified, OF exI, of 0, unfolded nth_ctape_0] apply simp
            apply (subst Suc(2) [of "Suc i" 0, unfolded nth_ctape_0])
            by simp_all
        qed
      qed
    {
      case 1
      show ?case apply simp
        apply (subst (1 2) TM.cstep_def)
        apply (auto simp add: Suc(1))
        using M'_def valid_tm_final_states apply force
        using M'_def valid_tm_final_states apply force
        unfolding TM.cstep_not_final_def Let_def apply simp
        unfolding Suc(1) valid_tm_next_state [OF valid_M'] apply (subst M'_def)
        by simp
    next
      case 2
      have 1: "i < TM.tape_count (Abs_TM M')"
        unfolding valid_tm_tape_count [OF valid_M'] unfolding M'_def using 2(2) by simp
      show ?case apply simp
        apply (subst (1 2) TM.cstep_def)
        apply (auto simp add: Suc(1))
           apply (rule Suc(2) [simplified])
        using 2 apply auto
        using M'_def valid_tm_final_states apply force
        using M'_def valid_tm_final_states apply force
        unfolding TM.cstep_not_final_def Let_def apply auto
        apply (subst (1 2) nth_map2)
            apply auto
           apply (simp add: TM.next_actions_simps(2))
          apply (metis (no_types, lifting) M'_def TM.next_actions_simps(2) less_Suc_eq_le
            simps(1) valid_M' valid_tm_tape_count)
        using M'_def valid_tm_tape_count apply force
        unfolding TM.ctape_action_def TM.next_actions_def TM.next_writes_def
          TM.next_moves_def using 1 apply simp
        unfolding valid_tm_next_move [OF valid_M'] valid_tm_next_write [OF valid_M'] Suc(1)
        apply (subst M'_def)
        apply simp
        apply (subst M'_def)
        apply simp
        apply (subst Suc(2) [THEN nth_ctape_inject])
        by simp_all
    next
      case 3
      have 1: "Suc 0 < TM.tape_count (Abs_TM M')"
        unfolding valid_tm_tape_count [OF valid_M'] unfolding M'_def by simp
      show ?case using 3 apply simp
        apply (subst (1 2) TM.cstep_def)
        apply (subst (asm) TM.cstep_def)
        apply (auto simp add: Suc(1) valid_tm_final_states)
           apply (rule Suc(3))
           apply simp_all
          apply (simp add: M'_def)
         apply (simp add: M'_def)
        unfolding TM.cstep_not_final_def Let_def apply auto
        apply (subst (1 2) nth_map2)
            apply auto
          apply (metis TM.at_least_one_tape TM.next_actions_simps(2) less_numeral_extra(3)
            list.size(3))
         apply (metis TM.at_least_one_tape TM.next_actions_simps(2) less_not_refl
            list.size(3))
        apply (subst (asm) nth_map2)
          apply auto
          apply (metis (no_types, lifting) M'_def Suc_less_eq2 TM.at_least_one_tape
            TM.next_actions_simps(2) simps(1) valid_M' valid_tm_tape_count)
         apply (metis (no_types, lifting) M'_def One_nat_def TM.at_least_one_tape'
            less_Suc_eq_le simps(1) valid_M' valid_tm_tape_count)
        unfolding TM.ctape_action_def TM.next_actions_def TM.next_writes_def
          TM.next_moves_def using 1 apply simp
        unfolding Suc(1) valid_tm_next_move [OF valid_M'] apply (subst M'_def)
        apply simp
        apply (subst (asm) M'_def)
        apply simp
        unfolding valid_tm_next_write [OF valid_M'] apply (subst M'_def)
        apply simp
        apply (subst (asm) M'_def)
        apply simp
        apply (cases "TM.TM.next_move M (cstate ((TM.cstep M ^^ k)
                      (TM.cinitial_config M (s \<up> length w))))
                      (cheads ((TM.cstep M ^^ k) (TM.cinitial_config M (s \<up> length w)))) 0")
          apply auto
          apply (cases "j - 1 = 0")
        apply auto
          apply (simp add: Suc.IH(3))
         apply (cases "j + 1 = 0")
          apply auto
         apply (simp add: Suc.IH(3))
        apply (cases "j = 0")
        by (simp_all add: Suc.IH(3))
    next
      case 4
      have 1: "Suc 0 < TM.tape_count (Abs_TM M')"
        unfolding valid_tm_tape_count [OF valid_M'] unfolding M'_def by simp
      show ?case using 4 apply auto
        apply (subst TM.cstep_def)
        apply (subst (asm) TM.cstep_def)
        apply (auto simp add: Suc(1))
        apply (cases "cstate ((TM.cstep M ^^ k) (TM.cinitial_config M (s \<up> length w)))
                      \<in> TM.TM.final_states (Abs_TM M')")
          apply auto
          apply (metis One_nat_def Suc.IH(4) option.distinct(1))
        using M'_def valid_tm_final_states apply force
        apply (cases "cstate ((TM.cstep M ^^ k) (TM.cinitial_config M (s \<up> length w)))
                      \<in> TM.TM.final_states (Abs_TM M')")
         apply auto
        using M'_def valid_tm_final_states apply force
        unfolding TM.cstep_not_final_def Let_def apply simp
        apply (subst nth_map2)
          apply (metis TM.next_actions_simps(2) TM.at_least_one_tape)
         apply simp
        apply (subst (asm) nth_map2)
          apply auto
          apply (metis (no_types, lifting) M'_def One_nat_def TM.at_least_one_tape'
            TM.next_actions_simps(2) less_Suc_eq_le simps(1) valid_M' valid_tm_tape_count)
         apply (metis (no_types, lifting) M'_def One_nat_def TM.at_least_one_tape'
            less_Suc_eq_le simps(1) valid_M' valid_tm_tape_count)
        unfolding TM.ctape_action_def TM.next_actions_def TM.next_writes_def TM.next_moves_def
        using 1 apply simp
        unfolding Suc(1) valid_tm_next_move [OF valid_M'] apply (subst (asm) M'_def)
        apply simp
        unfolding valid_tm_next_write [OF valid_M'] apply (subst (asm) M'_def)
        apply simp
        apply (cases "TM.TM.next_move M (cstate ((TM.cstep M ^^ k)
                      (TM.cinitial_config M (s \<up> length w))))
                      (cheads ((TM.cstep M ^^ k) (TM.cinitial_config M (s \<up> length w)))) 0")
        apply auto
        apply (metis One_nat_def Suc.IH(4)[of "j - 1"]
            head_ctape_write[of "Some _"
              "ctapes ((TM.cstep M ^^ k) (TM.cinitial_config M (s \<up> length w))) ! 0"]
            head_ctape_write[of
              "TM.TM.next_write M (cstate ((TM.cstep M ^^ k) (TM.cinitial_config M (s \<up> length w))))
        (cheads ((TM.cstep M ^^ k) (TM.cinitial_config M (s \<up> length w)))) 0"
              "ctapes ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w)) ! Suc 0"]
            nth_ctape_def[of
              "TM_abbrevs.ctape_write (Some _)
        (ctapes ((TM.cstep M ^^ k) (TM.cinitial_config M (s \<up> length w))) ! 0)"
              "0"]
            nth_ctape_def[of
              "TM_abbrevs.ctape_write
        (TM.TM.next_write M (cstate ((TM.cstep M ^^ k) (TM.cinitial_config M (s \<up> length w))))
          (cheads ((TM.cstep M ^^ k) (TM.cinitial_config M (s \<up> length w)))) 0)
        (ctapes ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w)) ! Suc 0)"
              "0"]
            nth_ctape_tape_write_non0[of "j - 1"
              "TM.TM.next_write M (cstate ((TM.cstep M ^^ k) (TM.cinitial_config M (s \<up> length w))))
        (cheads ((TM.cstep M ^^ k) (TM.cinitial_config M (s \<up> length w)))) 0"
              "ctapes ((TM.cstep M ^^ k) (TM.cinitial_config M (s \<up> length w))) ! 0"]
            nth_ctape_tape_write_non0[of "j - 1"
              "TM.TM.next_write M (cstate ((TM.cstep M ^^ k) (TM.cinitial_config M (s \<up> length w))))
        (cheads ((TM.cstep M ^^ k) (TM.cinitial_config M (s \<up> length w)))) 0"
              "ctapes ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w)) ! Suc 0"]
            option.distinct(1))
        apply (metis One_nat_def Suc.IH(4)[of "j + 1"]
            head_ctape_write[of "Some _"
              "ctapes ((TM.cstep M ^^ k) (TM.cinitial_config M (s \<up> length w))) ! 0"]
            head_ctape_write[of
              "TM.TM.next_write M (cstate ((TM.cstep M ^^ k) (TM.cinitial_config M (s \<up> length w))))
        (cheads ((TM.cstep M ^^ k) (TM.cinitial_config M (s \<up> length w)))) 0"
              "ctapes ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w)) ! Suc 0"]
            nth_ctape_0[of
              "TM_abbrevs.ctape_write (Some _)
        (ctapes ((TM.cstep M ^^ k) (TM.cinitial_config M (s \<up> length w))) ! 0)"]
              nth_ctape_0[of
                "TM_abbrevs.ctape_write
        (TM.TM.next_write M (cstate ((TM.cstep M ^^ k) (TM.cinitial_config M (s \<up> length w))))
          (cheads ((TM.cstep M ^^ k) (TM.cinitial_config M (s \<up> length w)))) 0)
        (ctapes ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w)) ! Suc 0)"]
                nth_ctape_tape_write_non0[of "j + 1"
                  "TM.TM.next_write M (cstate ((TM.cstep M ^^ k) (TM.cinitial_config M (s \<up> length w))))
        (cheads ((TM.cstep M ^^ k) (TM.cinitial_config M (s \<up> length w)))) 0"
                  "ctapes ((TM.cstep M ^^ k) (TM.cinitial_config M (s \<up> length w))) ! 0"]
                nth_ctape_tape_write_non0[of "j + 1"
                  "TM.TM.next_write M (cstate ((TM.cstep M ^^ k) (TM.cinitial_config M (s \<up> length w))))
        (cheads ((TM.cstep M ^^ k) (TM.cinitial_config M (s \<up> length w)))) 0"
                  "ctapes ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w)) ! Suc 0"]
                option.distinct(1))
        by (metis One_nat_def Suc.IH(4)[of j]
            head_ctape_write[of
              "TM.TM.next_write M (cstate ((TM.cstep M ^^ k) (TM.cinitial_config M (s \<up> length w))))
        (cheads ((TM.cstep M ^^ k) (TM.cinitial_config M (s \<up> length w)))) 0"
              "ctapes ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w)) ! Suc 0"]
            head_ctape_write[of
              "TM.TM.next_write M (cstate ((TM.cstep M ^^ k) (TM.cinitial_config M (s \<up> length w))))
        (cheads ((TM.cstep M ^^ k) (TM.cinitial_config M (s \<up> length w)))) 0"
              "ctapes ((TM.cstep M ^^ k) (TM.cinitial_config M (s \<up> length w))) ! 0"]
            nth_ctape_def[of
              "TM_abbrevs.ctape_write
        (TM.TM.next_write M (cstate ((TM.cstep M ^^ k) (TM.cinitial_config M (s \<up> length w))))
          (cheads ((TM.cstep M ^^ k) (TM.cinitial_config M (s \<up> length w)))) 0)
        (ctapes ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w)) ! Suc 0)"
              "0"]
            nth_ctape_def[of
              "TM_abbrevs.ctape_write
        (TM.TM.next_write M (cstate ((TM.cstep M ^^ k) (TM.cinitial_config M (s \<up> length w))))
          (cheads ((TM.cstep M ^^ k) (TM.cinitial_config M (s \<up> length w)))) 0)
        (ctapes ((TM.cstep M ^^ k) (TM.cinitial_config M (s \<up> length w))) ! 0)"
              "0"]
            nth_ctape_tape_write_non0[of j
              "TM.TM.next_write M (cstate ((TM.cstep M ^^ k) (TM.cinitial_config M (s \<up> length w))))
        (cheads ((TM.cstep M ^^ k) (TM.cinitial_config M (s \<up> length w)))) 0"
              "ctapes ((TM.cstep M ^^ k) (TM.cinitial_config M (s \<up> length w))) ! 0"]
            nth_ctape_tape_write_non0[of j
              "TM.TM.next_write M (cstate ((TM.cstep M ^^ k) (TM.cinitial_config M (s \<up> length w))))
        (cheads ((TM.cstep M ^^ k) (TM.cinitial_config M (s \<up> length w)))) 0"
              "ctapes ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w)) ! Suc 0"]
            option.distinct(1))
    }
  qed
  have config_times_eq: "TM.config_time (Abs_TM M') (TM.initial_config (Abs_TM M') w) =
                         TM.config_time M (TM.initial_config M (s \<up> (length w)))"
    for w :: "'s list" unfolding TM.config_time_def TM.is_final_def
      f11 [unfolded cotm_steps_congruences(1)] valid_tm_final_states [OF valid_M']
    by (simp add: M'_def)
  show "\<exists>M::('q, 's, 'l) TM. \<forall>w. TM.time M w = T (length w)"
  proof (rule exI [where x="Abs_TM M'"], auto)
    fix w :: "'s list"
    show "TM.config_time (Abs_TM M') (TM.initial_config (Abs_TM M') w) = T (length w)"
      unfolding config_times_eq using a2 [of "length w"]
      unfolding TM.time_def .
  qed
qed

lemma typed_fully_time_constrI_ex: "\<exists>M::('q, 's, 'l) TM. s \<in> TM.symbols M \<and>
                                    (\<forall>n. TM.time M (replicate n s) = T n) \<Longrightarrow>
                                    typed_fully_time_constr TYPE('q) TYPE('s) TYPE('l) T"
  by (metis typed_fully_time_constrI)

lemma typed_fully_time_constr_natI: "typed_fully_time_constr TYPE('q) TYPE('s) TYPE('l) T \<Longrightarrow>
                                     typed_fully_time_constr TYPE(nat) TYPE('s2) TYPE('l2) T"
proof (rule typed_fully_time_constrI_ex)
  assume a1: "typed_fully_time_constr TYPE('q) TYPE('s) TYPE('l) T"
  note a1 [unfolded typed_fully_time_constr_def]
  then obtain M :: "('q, 's, 'l) TM" where M_time: "\<And>w. TM.time M w = T (length w)" by blast
  obtain s :: 's where s_in_M: "s \<in> TM.symbols M" by fastforce
  note tm_single_symbol_run [OF s_in_M]
  then obtain M_single_sym :: "('q, 's, 'l) TM" where
    M_single_sym_symbols: "TM.TM.symbols M_single_sym = {s}" and
    M_single_sym_run: "\<And>k n. state (TM.run M_single_sym k (s \<up> n)) = state (TM.run M k (s \<up> n))" and
    M_single_sym_fs: "TM.TM.final_states M_single_sym = TM.TM.final_states M" by blast
  define M' :: "('q, 's2, 'l2) TM_record" where
    "M' \<equiv> TM (TM.tape_count M_single_sym) {undefined} (TM.states M_single_sym)
            (TM.initial_state M_single_sym) (TM.final_states M_single_sym) undefined
            (\<lambda>st hds. TM.next_state M_single_sym st (map (\<lambda>os. map_option (\<lambda>_. s) os) hds))
            (\<lambda>st hds k. map_option (\<lambda>_. undefined)
              (TM.next_write M_single_sym st (map (\<lambda>os. map_option (\<lambda>_. s) os) hds) k))
            (\<lambda>st hds k. TM.next_move M_single_sym st (map (\<lambda>os. map_option (\<lambda>_. s) os) hds) k)"
  have valid_M' [simp, intro]: "valid_TM M'"
    apply unfold_locales
    unfolding M'_def apply auto
     apply (erule TM.next_state_valid)
      apply auto
    using M_single_sym_symbols set_options_eq apply fastforce
  proof -
    fix q :: 'q and hds :: "'s2 option list" and i :: nat
    show "map_option (\<lambda>_. undefined) (TM.TM.next_write M_single_sym q (map (map_option (\<lambda>_. s)) hds) i)
          \<in> options {undefined}"
      by (cases "TM.TM.next_write M_single_sym q (map (map_option (\<lambda>_. s)) hds) i") auto
  qed
  have f11: "cstate (TM.csteps (Abs_TM M') k (TM.cinitial_config (Abs_TM M') (undefined \<up> n))) =
             cstate (TM.csteps M_single_sym k (TM.cinitial_config M_single_sym (s \<up> n)))" and
       f12: "\<And>i j. i < TM.tape_count (Abs_TM M') \<Longrightarrow>
             map_option (\<lambda>_. s) (nth_ctape (ctapes (TM.csteps (Abs_TM M') k (TM.cinitial_config (Abs_TM M')
             (undefined \<up> n))) ! i) j) =
             nth_ctape (ctapes (TM.csteps M_single_sym k (TM.cinitial_config M_single_sym
             (s \<up> n))) ! i) j" for k n :: nat
  proof (induction k)
    case 0
    {
      case 1
      then show ?case apply (simp add: TM.cinitial_config_def)
        unfolding valid_tm_initial_state [OF valid_M'] unfolding M'_def by simp
    next
      case 2
      then show ?case apply (auto simp add: TM.cinitial_config_def TM_abbrevs.cinput_tape_def)
        unfolding valid_tm_tape_count [OF valid_M'] unfolding M'_def apply auto
         apply (cases "nth_ctape (((empty_ctape::'s2 ctape) #
                       empty_ctape \<up> (TM.TM.tape_count M_single_sym - Suc 0)) ! i) j")
          apply auto
          apply (metis One_nat_def Suc_diff_1 TM.at_least_one_tape nth_ctape_empty_ctape
            nth_replicate replicate_Suc)
         apply (metis Cons_replicate_eq One_nat_def TM.at_least_one_tape nth_ctape_empty_ctape nth_replicate
            option.distinct(1))
        apply (cases "j = 0")
         apply (simp add: nth_ctape_0)
         apply (subst nth_Cons')
         apply auto
        unfolding empty_ctape_def apply auto
        apply (cases "i = 0")
         apply auto
        apply (cases "j > 0")
         apply (auto simp add: nth_ctape_pos)
         apply (cases "j - 1 < n - Suc 0")
           apply (simp add: prepend_list_nth_less)
          apply (simp add: prepend_list_nth_ge)
         apply (simp add: nth_ctape_neg)
        by (metis option.simps(8) nth_ctape_empty_ctape empty_ctape_def)
    }
  next
    case (Suc k)
    have cheads_eq: "map (map_option (\<lambda>_. s) \<circ> chead)
                     (ctapes ((TM.cstep (Abs_TM M') ^^ k)
                     (TM.cinitial_config (Abs_TM M') (undefined \<up> n)))) =
                     cheads ((TM.cstep M_single_sym ^^ k) (TM.cinitial_config M_single_sym (s \<up> n)))"
      apply (rule nth_equalityI)
       apply auto
       apply (unfold valid_tm_tape_count [OF valid_M'])[1]
       apply (simp add: M'_def)
      unfolding Suc(2) [of _ 0, unfolded nth_ctape_0] apply (subst nth_map)
       apply auto
      unfolding valid_tm_tape_count [OF valid_M'] unfolding M'_def by simp
    {
      case 1
      show ?case apply simp
        apply (subst (1 2) TM.cstep_def)
        apply (auto simp add: Suc(1) valid_tm_final_states)
          apply (simp add: M'_def)
         apply (simp add: M'_def)
        unfolding TM.cstep_not_final_def Let_def apply simp
        unfolding Suc(1) valid_tm_next_state [OF valid_M'] apply (subst M'_def)
        apply simp
        unfolding cheads_eq ..
    next
      case 2
      have 1: "TM.TM.next_write M_single_sym
         (cstate ((TM.cstep M_single_sym ^^ k) (TM.cinitial_config M_single_sym (s \<up> n))))
         (cheads ((TM.cstep M_single_sym ^^ k) (TM.cinitial_config M_single_sym (s \<up> n)))) i \<in> options {s}"
        unfolding cotm_steps_congruences(1) cotm_heads_steps_congruence
        unfolding M_single_sym_symbols [symmetric] apply (rule TM.next_write_valid)
           apply auto
           apply (metis M_single_sym_symbols TM_steps_valid_stateI empty_replicate empty_set
            set_replicate subset_singleton_iff)
          apply (simp add: TM.run_tapes_len)
         apply (metis Ball_set_map M_single_sym_symbols TM_steps_valid_headsI set_replicate_subset)
        using 2 unfolding valid_tm_tape_count [OF valid_M'] unfolding M'_def by simp
      show ?case
        using 2
        apply (cases "cstate ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') (undefined \<up> n)))
                      \<in> TM.TM.final_states (Abs_TM M')")
         apply simp
         apply (subst (1 2) TM.cstep_def)
         apply auto
        using Suc.IH(2) apply blast
        unfolding Suc(1) apply (subst (asm) valid_tm_final_states [OF valid_M'])
         apply (subst (asm) (2) M'_def)
         apply simp
        apply (cases "TM.next_move M_single_sym (cstate ((TM.cstep M_single_sym ^^ k)
                      (TM.cinitial_config M_single_sym (s \<up> n)))) (cheads ((TM.cstep M_single_sym ^^ k)
                      (TM.cinitial_config M_single_sym (s \<up> n)))) i")
          apply (cases "j = 1")
           apply simp
           apply (subst nth_ctape_cstep_Shift_Left2)
        unfolding valid_tm_next_move [OF valid_M'] apply (subst M'_def)
               apply (simp add: Suc(1) cheads_eq)
        unfolding Suc(1) apply assumption
             apply simp
            apply blast
           apply (subst nth_ctape_cstep_Shift_Left2)
               apply auto
        unfolding valid_tm_final_states [OF valid_M'] apply (simp add: M'_def)
        using M'_def valid_tm_tape_count apply force
        using M'_def valid_tm_tape_count apply force
        unfolding valid_tm_next_write [OF valid_M'] apply (subst M'_def)
           apply (simp add: cheads_eq)
        apply (cases "TM.TM.next_write M_single_sym
                      (cstate ((TM.cstep M_single_sym ^^ k) (TM.cinitial_config M_single_sym (s \<up> n))))
                      (cheads ((TM.cstep M_single_sym ^^ k) (TM.cinitial_config M_single_sym (s \<up> n)))) i")
            apply auto
        using 1 apply simp
          apply (subst nth_ctape_cstep_Shift_Left1)
               apply auto
        unfolding valid_tm_next_move [OF valid_M'] Suc(1) apply (subst M'_def)
            apply (simp add: cheads_eq)
        unfolding valid_tm_final_states [OF valid_M'] apply simp
          apply (subst nth_ctape_cstep_Shift_Left1)
               apply auto
             apply (simp add: M'_def)
            apply (metis length_map length_ctapes_csteps_eq_tc cheads_eq)
           apply (metis length_map length_ctapes_csteps_eq_tc cheads_eq)
          apply (erule Suc(2))
         apply (cases "j = -1")
          apply simp
          apply (subst nth_ctape_cstep_Shift_Right2)
              apply auto
        unfolding Suc(1) valid_tm_next_move [OF valid_M'] apply (subst M'_def)
            apply (simp add: cheads_eq)
           apply (simp add: valid_tm_final_states)
          apply (subst nth_ctape_cstep_Shift_Right2)
              apply auto
             apply (simp add: M'_def)
        using M'_def valid_tm_tape_count apply fastforce
        using M'_def valid_tm_tape_count apply fastforce
        unfolding valid_tm_next_write [OF valid_M'] apply (subst M'_def)
          apply (simp add: cheads_eq)
          apply (cases "TM.TM.next_write M_single_sym (cstate ((TM.cstep M_single_sym ^^ k)
                        (TM.cinitial_config M_single_sym (s \<up> n))))
                        (cheads ((TM.cstep M_single_sym ^^ k) (TM.cinitial_config M_single_sym (s \<up> n)))) i")
           apply auto
        using 1 apply simp
         apply (subst nth_ctape_cstep_Shift_Right1)
              apply auto
        unfolding valid_tm_next_move [OF valid_M'] Suc(1) apply (subst M'_def)
           apply (simp add: cheads_eq)
          apply (simp add: valid_tm_final_states)
         apply (subst nth_ctape_cstep_Shift_Right1)
              apply auto
            apply (simp add: M'_def)
        using M'_def valid_tm_tape_count apply fastforce
        using M'_def valid_tm_tape_count apply fastforce
         apply (erule Suc(2))
        apply (cases "j = 0")
         apply simp
         apply (subst nth_ctape_cstep_No_Shift2)
             apply auto
        unfolding valid_tm_next_move [OF valid_M'] Suc(1) apply (subst M'_def)
           apply (simp add: cheads_eq)
          apply (simp add: valid_tm_final_states)
        apply (subst nth_ctape_cstep_No_Shift2)
             apply auto
            apply (simp add: M'_def)
        using M'_def valid_tm_tape_count apply fastforce
        using M'_def valid_tm_tape_count apply fastforce
        unfolding valid_tm_next_write [OF valid_M'] apply (subst M'_def)
         apply (simp add: cheads_eq)
         apply (cases "TM.TM.next_write M_single_sym (cstate ((TM.cstep M_single_sym ^^ k)
                       (TM.cinitial_config M_single_sym (s \<up> n))))
                       (cheads ((TM.cstep M_single_sym ^^ k) (TM.cinitial_config M_single_sym (s \<up> n)))) i")
          apply auto
        using 1 apply simp
        apply (subst nth_ctape_cstep_No_Shift1)
             apply auto
        unfolding valid_tm_next_move [OF valid_M'] Suc(1) apply (subst M'_def)
          apply (simp add: cheads_eq)
         apply (simp add: valid_tm_final_states)
        apply (subst nth_ctape_cstep_No_Shift1)
             apply auto
           apply (simp add: M'_def)
        using M'_def valid_tm_tape_count apply fastforce
        using M'_def valid_tm_tape_count apply fastforce
        by (erule Suc(2))
    }
  qed
  define f :: "'q \<Rightarrow> nat" where "f \<equiv> (SOME f. inj_on f (TM.states (Abs_TM M')))"
  have 1: "\<exists>f::'q\<Rightarrow>nat. inj_on f (TM.states (Abs_TM M'))"
    by (metis bij_betw_def TM.state_axioms(1) ex_bij_betw_finite_nat)
  note f_inj = someI_ex [OF 1, folded f_def]
  define M_final :: "(nat, 's2, 'l2) TM_record" where "M_final \<equiv> map_states_tmrec f (Abs_TM M')"
  have valid_M_final: "valid_TM M_final"
    unfolding M_final_def apply (rule map_states_tmrec_valid)
    by fact
  show "\<exists>(M::(nat, 's2, 'l2) TM). undefined \<in> TM.TM.symbols M \<and> (\<forall>n. TM.time M (undefined \<up> n) = T n)"
  proof (standard, standard)
    show "undefined \<in> TM.TM.symbols (Abs_TM M_final)"
      unfolding valid_tm_symbols [OF valid_M_final]
      unfolding M_final_def apply (simp add: map_states_tmrec_def [OF f_inj])
      unfolding valid_tm_symbols [OF valid_M'] unfolding M'_def by simp
    show "\<forall>n. TM.time (Abs_TM M_final) (undefined \<up> n) = T n"
    proof
      fix n :: nat
      have 1: "\<And>k. TM.is_final (Abs_TM M_final) ((TM.step (Abs_TM M_final) ^^ k)
               (TM.initial_config (Abs_TM M_final) (undefined \<up> n))) \<longleftrightarrow>
               TM.is_final M ((TM.step M ^^ k) (TM.initial_config M (s \<up> n)))"
        unfolding TM.is_final_def M_final_def
        apply (subst map_states_tmrec_run(1) [unfolded TM.run_def, OF f_inj])
         apply auto
        using M'_def valid_tm_symbols apply fastforce
        unfolding valid_tm_final_states [OF valid_M_final [unfolded M_final_def]]
        unfolding map_states_tmrec_def [OF f_inj] apply auto
        unfolding valid_tm_final_states [OF valid_M'] apply (subst (asm) M'_def)
         apply simp
        unfolding M_single_sym_fs apply (drule f_inj [THEN inj_onD])
        unfolding f11 [unfolded cotm_steps_congruences(1)] valid_tm_states [OF valid_M'] apply (simp add: M'_def)
           apply (simp add: M_single_sym_symbols TM_steps_valid_stateI set_replicate_subset)
          apply (simp add: M'_def M_single_sym_fs [symmetric])
          apply blast
         apply (metis M_single_sym_run TM.run_def)
        unfolding M'_def apply auto
        by (metis M_single_sym_fs M_single_sym_run TM.run_def)
      show "TM.time (Abs_TM M_final) (undefined \<up> n) = T n"
        unfolding TM.time_def TM.config_time_def 1 using M_time [of "s \<up> n"]
        unfolding TM.time_def TM.config_time_def by simp
    qed
  qed
qed

lemmas typed_fully_time_constr_natI' = typed_fully_time_constr_natI [OF typed_fully_time_constrI]

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
  where "typed_computable_in_time TYPE('q) TYPE('l) T f \<equiv> \<exists>M::('q, 's, 'l) TM. TM.computes M f \<and> TM.time_bounded M T \<and> TM.symbols M = UNIV"

abbreviation "computable_in_time \<equiv> typed_computable_in_time TYPE(nat) TYPE(unit)"

lemma typed_computable_in_time_implies_symbols_finite:
  "typed_computable_in_time TYPE('q) TYPE('l) T (f::'s list \<Rightarrow> 's list) \<Longrightarrow> finite (UNIV::'s set)"
  unfolding typed_computable_in_time_def apply auto
  by (metis TM.symbol_axioms(1))

lemma computableE[elim]:
  assumes "typed_computable_in_time TYPE('q) TYPE('l) T f"
  obtains M::"('q, 's, 'l) TM" where "TM.computes M f" and "TM.time_bounded M T" and
    "TM.symbols M = UNIV"
  using assms that unfolding typed_computable_in_time_def by blast

lemma computable_mono:
  assumes "typed_computable_in_time TYPE('q) TYPE('l) t f" and
          "\<And>n. t n \<le> T n"
        shows "typed_computable_in_time TYPE('q) TYPE('l) T f"
proof -
  note assms(1) [unfolded typed_computable_in_time_def]
  then obtain M :: "('q, 'a, 'l) TM" where comp: "TM.computes M f" and
    tb: "\<And>w. TM.time_bounded_word M t w" and syms: "TM.TM.symbols M = UNIV" by blast
  have 1: "\<And>w. TM.time_bounded_word M T w" using tb assms(2) TM.time_bounded_word_mono by blast
  show "typed_computable_in_time TYPE('q) TYPE('l) T f" using comp 1 syms
    unfolding typed_computable_in_time_def by blast
qed

lemma typed_comp_in_time_natI: "typed_computable_in_time TYPE('q) TYPE('l) T f \<Longrightarrow>
                                typed_computable_in_time TYPE(nat) TYPE('l2) T f"
proof (erule computableE)
  fix M :: "('q, 'a, 'l) TM"
  assume a1: "TM.computes M f" and a2: "\<forall>w. TM.time_bounded_word M T w" and
      a3: "TM.symbols M = UNIV"
  obtain m :: "'q \<Rightarrow> nat" where m_inj_on: "inj_on m (TM.states M)"
    by (meson TM.state_axioms(1) finite_imp_inj_to_nat_seg)
  define M' :: "(nat, 'a , 'l) TM" where "M' \<equiv> Abs_TM (map_states_tmrec m M)"
  note map_states_tmrec_comp_word_iff [OF m_inj_on, folded M'_def]
  hence 1: "TM.computes M' f" using a1 a3 unfolding TM.computes_def by simp
  have 2: "TM.symbols M' = UNIV"
    unfolding M'_def valid_tm_symbols [OF map_states_tmrec_valid [OF m_inj_on]]
    unfolding map_states_tmrec_def [OF m_inj_on] by simp fact
  have 3: "\<And>w. TM.time_bounded_word M' T w"
    using a2 unfolding TM.time_bounded_word_def
    by (metis 1 M'_def TM.computes_haltsD TM.final_run_compute a3 halts_compD is_finalD
        is_finalI m_inj_on map_states_tmrec_comp_state map_states_tmrec_run_state
        subset_UNIV)
  define M2 :: "(nat, 'a, 'l2) TM_record" where
    "M2 \<equiv> TM (TM.tape_count M') (TM.symbols M') (TM.states M') (TM.initial_state M')
          (TM.final_states M') (\<lambda>_. undefined) (TM.next_state M') (TM.next_write M')
          (TM.next_move M')"
  have M2_valid [simp, intro]: "valid_TM M2"
    unfolding M2_def by standard auto
  have 4: "TM.symbols (Abs_TM M2) = UNIV"
    using 3 unfolding M2_def using 2 M2_def valid_tm_symbols by fastforce
  have 5: "TM.steps (Abs_TM M2) n (TM.initial_config (Abs_TM M2) w) =
           TM.steps M' n (TM.initial_config M' w)" for w :: "'a list" and n :: nat
  proof (induction n)
    case 0
    then show ?case apply simp
      unfolding TM.initial_config_def apply auto
      using M2_def valid_tm_initial_state apply fastforce
      using M2_def valid_tm_tape_count by fastforce
  next
    case (Suc n)
    have 1: "TM.TM.next_write (Abs_TM M2)
             (state ((TM.step M' ^^ n) (TM.initial_config M' w)))
             (heads ((TM.step M' ^^ n) (TM.initial_config M' w))) =
             TM.TM.next_write M'
             (state ((TM.step M' ^^ n) (TM.initial_config M' w)))
             (heads ((TM.step M' ^^ n) (TM.initial_config M' w)))"
      unfolding valid_tm_next_write [OF M2_valid] unfolding M2_def by simp
    have 2: "TM.TM.next_move (Abs_TM M2) (state ((TM.step M' ^^ n)
             (TM.initial_config M' w)))
             (heads ((TM.step M' ^^ n) (TM.initial_config M' w))) =
             TM.TM.next_move M' (state ((TM.step M' ^^ n)
             (TM.initial_config M' w)))
             (heads ((TM.step M' ^^ n) (TM.initial_config M' w)))"
      unfolding valid_tm_next_move [OF M2_valid] unfolding M2_def by simp
    have 3: "TM.TM.tape_count (Abs_TM M2) = TM.TM.tape_count M'"
      unfolding valid_tm_tape_count [OF M2_valid] unfolding M2_def by simp
    show ?case apply simp
      unfolding Suc apply (subst (1 2) TM.step_def)
      apply auto
       apply (metis M2_def M2_valid select_convs(5) valid_tm_final_states)
      using M2_def valid_tm_final_states apply force
      unfolding TM.step_not_final_def Let_def apply auto
      using M2_def valid_tm_next_state apply fastforce
      unfolding TM.next_actions_def TM.next_writes_def TM.next_moves_def 1 2 3 ..
  qed
  have 6: "\<And>w. TM.time_bounded_word (Abs_TM M2) T w"
    using 3 unfolding TM.time_bounded_word_def TM.run_def 5
    by (metis M2_def M2_valid is_finalD is_finalI select_convs(5) valid_tm_final_states)
  have 7: "TM.computes (Abs_TM M2) f"
    using 1 unfolding TM.computes_def TM.computes_word_def TM.halts_def TM.compute_def
      TM.compute_config_def 5 TM.halts_config_def apply auto
     apply (metis 5 6 TM.run_def TM.time_bounded_word_def)
    by (metis (mono_tags, lifting) 3 5 6 Least_eqD TM.final_run_compute TM.run_def
        TM.time_bounded_word_def)
  show "typed_computable_in_time TYPE(nat) TYPE('l2) T f"
    using 4 6 7 unfolding typed_computable_in_time_def by blast
qed

subsection\<open>DTIME\<close>

(* Maybe introduce a second argument that restricts the set of symbols to be used by
   a TM to decide the language. *)
text\<open>\<open>DTIME(T)\<close> is the set of languages decided by TMs in time \<open>T\<close> or less.\<close>
definition typed_DTIME :: "'q itself \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> 's lang set"
  where "typed_DTIME TYPE('q) T \<equiv> {L. \<exists>M::('q, 's) TM_decider. TM_decider.decides M L \<and> TM.time_bounded_symbols M T}"

definition typed_PDTIME :: "'q itself \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> 's lang set"
  where "typed_PDTIME TYPE('q) T \<equiv> {L. \<exists>M::('q, 's) PTM_decider.
    TM_decider.decides (valid_PTM M) L \<and> TM.time_bounded_symbols (valid_PTM M) T}"

abbreviation DTIME where
  "DTIME \<equiv> typed_DTIME TYPE(nat)"

abbreviation PDTIME where
  "PDTIME \<equiv> typed_PDTIME TYPE(nat)"

lemma max_two_states_only_trivial_dec: "card (TM.states (M::('q, 's) TM_decider)) \<le> 2 \<Longrightarrow>
       TM_decider.decides M L \<Longrightarrow> words L = {} \<or> words L = (alphabet L)*"
proof (cases "card (TM.states M) = 1")
  assume a1: "TM_decider.decides M L"
  case True
  then obtain q :: 'q where states: "TM.states M = {q}" by (rule card_1_singletonE)
  have "TM.final_states M \<noteq> {}" using a1 no_final_states_not_decides by blast
  hence [simp]: "TM.final_states M = {q}" using states by auto
  have [simp]: "\<And>w. (LEAST n. TM.is_final M ((TM.step M ^^ n)
                (TM.initial_config M w))) = 0"
    unfolding TM.is_final_def apply standard
     apply auto
    unfolding TM.initial_config_def apply simp
    using states by auto
  show ?thesis
  proof (cases "TM.label M q")
    case True
    then show ?thesis using a1 apply auto
      unfolding atomize_ball [symmetric]
      unfolding TM_decider.decides_def apply auto
      unfolding TM_decider.accepts_def TM_decider.acc_def apply auto
      unfolding TM.compute_def TM.compute_config_def apply simp
      unfolding TM.initial_config_def using states by auto
  next
    case False
    then show ?thesis using a1 apply auto
      unfolding atomize_ball [symmetric]
      unfolding TM_decider.decides_def apply auto
      unfolding TM_decider.rejects_def TM_decider.rej_def apply auto
      unfolding TM.compute_def TM.compute_config_def apply simp
      unfolding TM.initial_config_def using states apply auto
      by (meson lists_member member_lang_iff)
  qed
next
  assume a1: "card (TM.states M) \<le> 2" and a2: "TM_decider.decides M L"
  hence 1: "TM.final_states M \<noteq> {}" using no_final_states_not_decides by blast
  case False
  hence "card (TM.states M) = 2" using a1
    by (metis One_nat_def Orderings.order_eq_iff Suc_1 TM_axioms(3,4) card_0_eq empty_iff
        less_Suc0 linorder_not_less not_less_eq_eq)
  then obtain q1 q2 :: 'q where states: "TM.states M = {q1, q2}" and
                                q2_final: "q2 \<in> TM.final_states M"
    by (smt (verit, best) 1 Suc_1 TM.state_axioms(3) card_1_singletonE card_Suc_eq
        insert_commute singletonI subset_insert subset_singletonD)
  show ?thesis
  proof (cases "q1 \<in> TM.final_states M")
    case True
    hence final_states: "TM.final_states M = {q1, q2}" using states q2_final by auto
    hence init_is_final: "TM.initial_state M \<in> TM.final_states M" using states by auto
    have 1 [simp]: "\<And>w. (LEAST n. TM.is_final M ((TM.step M ^^ n)
                    (TM.initial_config M w))) = 0"
      apply standard
       apply auto
      unfolding TM.is_final_def TM.initial_config_def by (simp add: init_is_final)
    show ?thesis using a2 apply auto
      unfolding TM_decider.decides_def apply auto
      unfolding TM_decider.accepts_def TM_decider.rejects_def TM_decider.acc_def
        TM_decider.rej_def apply auto
      unfolding TM.compute_def TM.compute_config_def apply auto
      by (metis TM.init_conf_state member_langE)
  next
    case False
    hence final_states: "TM.final_states M = {q2}" using states q2_final by auto
    have 1: "\<And>w. set w \<subseteq> alphabet L \<Longrightarrow>
             TM.is_final M ((TM.step M ^^ (LEAST n. TM.is_final M ((TM.step M ^^ n)
             (TM.initial_config M w)))) (TM.initial_config M w))"
      apply (rule LeastI_ex) using a2
      by (metis TM.compute_altdef2 TM.run_def TM_decider.decides_halts halts_compD
          lists_member)
    have [simp]: "\<And>w. set w \<subseteq> alphabet L \<Longrightarrow> state (TM.compute M w) = q2"
      unfolding TM.compute_def TM.compute_config_def
      apply (frule 1)
      using final_states by blast
    show ?thesis
    proof (cases "TM.initial_state M = q1")
      case True
      then show ?thesis using a2 apply auto
        unfolding TM_decider.decides_def TM_decider.accepts_def TM_decider.rejects_def
        apply auto
        unfolding TM_decider.rej_def apply (auto simp add: final_states)
        unfolding TM_decider.acc_def apply (auto simp add: final_states)
        by blast
    next
      case False
      hence 1: "TM.initial_state M = q2" using states by auto
      have init_is_final: "TM.initial_state M \<in> TM.final_states M"
        using final_states 1 by simp
      have 1 [simp]: "\<And>w. (LEAST n. TM.is_final M ((TM.step M ^^ n)
                    (TM.initial_config M w))) = 0"
      apply standard
       apply auto
      unfolding TM.is_final_def TM.initial_config_def by (simp add: init_is_final)
    show ?thesis using a2 apply auto
      unfolding TM_decider.decides_def apply auto
      unfolding TM_decider.accepts_def TM_decider.rejects_def TM_decider.acc_def
        TM_decider.rej_def apply auto
      by (metis member_langE)
    qed
  qed
qed

lemma time_bound_0: "T n = 0 \<Longrightarrow> L \<in> typed_DTIME TYPE('q) T \<Longrightarrow> words L = {} \<or>
                     words L = (alphabet L)*"
proof -
  assume a1: "T n = 0" and a2: "L \<in> typed_DTIME TYPE('q) T"
  then obtain M :: "('q, 'a) TM_decider" where
    M_dec: "TM_decider.decides M L" and
    M_tb: "TM.time_bounded_symbols M T"
    unfolding typed_DTIME_def by blast
  define w :: "'a list" where "w \<equiv> replicate n (SOME s. s \<in> TM.symbols M)"
  have 1: "length w = n" unfolding w_def by simp
  have 2: "(SOME s. s \<in> TM.symbols M) \<in> TM.symbols M"
    by (rule someI_ex) (simp add: ex_in_conv)
  have 3: "TM.time_bounded_word M T w" using M_tb 2 unfolding w_def
    by (metis in_set_replicate subsetI)
  note 3 [unfolded TM.time_bounded_word_def 1 a1 TM.run_def, simplified]
  hence 4: "TM.initial_state M \<in> TM.final_states M"
    by (simp add: TM.init_conf_state TM.is_final_def)
  have 5: "\<And>w. (LEAST n. TM.is_final M ((TM.step M ^^ n) (TM.initial_config M w))) =
           0"
    using 4 by (simp add: TM.init_conf_state TM.is_final_def)
  have "(\<forall>w. TM_decider.accepts M w) \<or> (\<forall>w. TM_decider.rejects M w)"
    unfolding TM_decider.accepts_def TM_decider.rejects_def TM.compute_def
      TM.compute_config_def 5
    by (simp add: 4 TM.init_conf_state TM_decider.acc_def TM_decider.rej_def)
  moreover have "\<forall>w. TM_decider.accepts M w \<Longrightarrow> words L = (alphabet L)*"
    using M_dec TM_decider.decides_def by blast
  moreover have "\<forall>w. TM_decider.rejects M w \<Longrightarrow> words L = {}"
    using M_dec TM_decider.decides_def by blast
  ultimately show "words L = {} \<or> words L = (alphabet L)*" by auto
qed

lemma in_dtime_tb_words_language_alphabet_iff_helper: "(\<exists>M::('q, 's) TM_decider.
                  TM_decider.decides M L \<and> TM.time_bounded M T) \<longleftrightarrow>
                  (\<exists>M::('q, 's) TM_decider.
                  TM_decider.decides M L \<and> (\<forall>w\<in>(alphabet L)*. TM.time_bounded_word M T w))"
proof (auto, cases "alphabet L = {}")
  case True
  fix M :: "('q, 's) TM_decider"
  assume a1: "\<forall>w\<in>(alphabet L)*. TM_decider.decides_word M L w" and
         a2: "\<forall>w\<in>(alphabet L)*. TM.time_bounded_word M T w"
  have "\<And>w. w \<in>\<^sub>L L \<Longrightarrow> w = []" using True unfolding words_def by simp
  hence "words L = {} \<or> words L = {[]}" by auto
  moreover have "words L = {} \<Longrightarrow> \<exists>M::('q, 's) TM_decider. alphabet L \<subseteq> TM.TM.symbols M \<and>
                                  (\<forall>x\<in>(alphabet L)*. TM_decider.decides_word M L x) \<and>
                                  (\<forall>w. TM.time_bounded_word M T w)"
  proof
    assume a3: "words L = {}"
    define M' :: "('q, 's, bool) TM_record" where
      "M' \<equiv> halting_TM_rec undefined {undefined} False"
    have M'_valid: "valid_TM M'" unfolding M'_def by (simp add: halting_TM_valid)
    have "alphabet L \<subseteq> TM.symbols (Abs_TM M')" unfolding True by simp
    moreover have "\<And>w. set w \<subseteq> alphabet L \<Longrightarrow> TM_decider.decides_word (Abs_TM M') L w"
    proof (unfold TM_decider.decides_def, auto simp add: a3)
      fix w :: "'s list"
      assume a4: "set w \<subseteq> alphabet L"
      have [simp]: "(LEAST n. TM.is_final (Abs_TM M') ((TM.step (Abs_TM M') ^^ n)
                    (TM.initial_config (Abs_TM M') w))) = 0"
        apply standard
         apply auto
        unfolding TM.is_final_def TM.initial_config_def apply simp
        unfolding M'_def
        by (metis Rej_TM.M_fields(4,5) Rej_TM_def finite.emptyI finite_insert
            insert_not_empty rejecting_TM_def singletonI)
      show "TM_decider.rejects (Abs_TM M') w" unfolding TM_decider.rejects_def
        TM_decider.rej_def TM.compute_def TM.compute_config_def apply auto
        unfolding TM.initial_config_def M'_def apply auto
         apply (metis Rej_TM.M_fields(4,5) Rej_TM_def finite.emptyI finite_insert
            insert_not_empty rejecting_TM_def singletonI)
        by (metis Rej_TM.M_fields(6) Rej_TM_def finite.emptyI finite_insert insert_not_empty
            rejecting_TM_def)
      thus "TM_decider.accepts (Abs_TM M') w \<Longrightarrow> False"
        by (simp add: TM_decider.acc_not_rej)
    qed
    moreover have "TM.time_bounded_word (Abs_TM M') T w" for w :: "'s list"
    proof (rule TM.time_bounded_word_mono [where t="\<lambda>_. 0"], auto)
      show "TM.time_bounded_word (Abs_TM M') (\<lambda>_. 0) w"
        unfolding TM.time_bounded_word_def TM.run_def TM.is_final_def apply simp
        unfolding TM.initial_config_def apply simp
        unfolding M'_def
        by (metis Rej_TM.M_fields(4,5) Rej_TM_def finite.emptyI finite_insert
            insert_not_empty rejecting_TM_def singletonI)
    qed
    ultimately show "alphabet L \<subseteq> TM.TM.symbols (Abs_TM M') \<and>
                     (\<forall>x\<in>(alphabet L)*. TM_decider.decides_word (Abs_TM M') L x) \<and>
                     (\<forall>w. TM.time_bounded_word (Abs_TM M') T w)"
      by blast
  qed
  moreover have "words L = {[]} \<Longrightarrow> \<exists>M::('q, 's) TM_decider. alphabet L \<subseteq> TM.TM.symbols M \<and>
                                    (\<forall>x\<in>(alphabet L)*. TM_decider.decides_word M L x) \<and>
                                    (\<forall>w. TM.time_bounded_word M T w)"
  proof -
    assume a3: "words L = {[]}"
    show "\<exists>M::('q, 's) TM_decider. alphabet L \<subseteq> TM.TM.symbols M \<and>
          (\<forall>x\<in>(alphabet L)*. TM_decider.decides_word M L x) \<and>
          (\<forall>w. TM.time_bounded_word M T w)"
    proof -
      define M' :: "('q, 's, bool) TM_record" where
        "M' \<equiv> halting_TM_rec undefined {undefined} True"
      have M'_valid: "valid_TM M'" unfolding M'_def
        apply (rule halting_TM_valid)
        by auto
      show ?thesis using True apply auto
        apply (rule exI [where x="Abs_TM M'"])
        apply auto
        unfolding TM_decider.decides_def a3 apply auto
      proof -
        fix w :: "'s list"
        show "TM.time_bounded_word (Abs_TM M') T w"
          apply (rule TM.time_bounded_word_mono [where t="\<lambda>_. 0"])
           apply auto
          unfolding TM.time_bounded_word_def TM.is_final_def
            valid_tm_final_states [OF M'_valid]
          unfolding M'_def halting_TM_rec_def apply simp
          unfolding TM.run_def TM.initial_config_def apply simp
          unfolding valid_tm_initial_state
            [OF M'_valid [unfolded M'_def halting_TM_rec_def], simplified] ..
        have [simp]: "(LEAST n. TM.is_final (Abs_TM M')
                      ((TM.step (Abs_TM M') ^^ n) (TM.initial_config (Abs_TM M') []))) = 0"
          apply standard
           apply auto
          unfolding TM.is_final_def TM.initial_config_def apply simp
          unfolding valid_tm_final_states [OF M'_valid] valid_tm_initial_state [OF M'_valid]
          unfolding M'_def halting_TM_rec_def by simp
        show "TM_decider.accepts (Abs_TM M') []"
          unfolding TM_decider.accepts_def TM_decider.acc_def apply auto
          unfolding TM.compute_def TM.compute_config_def apply auto
          unfolding TM.initial_config_def apply auto
          apply (metis M'_def M'_valid halting_TM_rec_def select_convs(4,5) singletonI
              valid_tm_final_states valid_tm_initial_state)
          unfolding valid_tm_label [OF M'_valid] valid_tm_initial_state [OF M'_valid]
          unfolding M'_def halting_TM_rec_def by simp
        thus "TM_decider.rejects (Abs_TM M') [] \<Longrightarrow> False"
          by (simp add: TM_decider.acc_not_rej)
      qed
    qed
  qed
  ultimately show "\<exists>M::('q, 's) TM_decider.
                   alphabet L \<subseteq> TM.TM.symbols M \<and> (\<forall>x\<in>(alphabet L)*. TM_decider.decides_word M L x) \<and>
                   (\<forall>w. TM.time_bounded_word M T w)" ..
next
  case False
  fix M :: "('q, 's) TM_decider"
  assume a1: "\<forall>w\<in>(alphabet L)*. TM_decider.decides_word M L w" and
         a2: "\<forall>w\<in>(alphabet L)*. TM.time_bounded_word M T w" and
         a3: "alphabet L \<subseteq> TM.TM.symbols M"
  define fs :: 'q where "fs \<equiv> (SOME s. s \<in> TM.final_states M)"
  have fs_final: "fs \<in> TM.final_states M"
    unfolding fs_def apply (rule someI_ex)
    by (metis a2 lists.Nil TM.time_bounded_wordD is_finalD)
  define M' :: "('q, 's, bool) TM_record" where
    "M' \<equiv> TM (Suc (TM.tape_count M)) (TM.symbols M) (TM.states M) (TM.initial_state M)
             (TM.final_states M) (TM.label M)
             (\<lambda>st hds. if hds ! 0 \<in> options (alphabet L) then
                if hds ! 1 = None then TM.next_state M st (hd hds#tl (tl hds)) else
                  TM.next_state M st (tl hds) else fs)
             (\<lambda>st hds k. if k = 0 then None else if hds ! 1 = None then
                TM.next_write M st (hd hds#tl (tl hds)) (k - 1) else TM.next_write M st (tl hds) (k - 1))
             (\<lambda>st hds k. if hds ! 1 = None then TM.next_move M st (hd hds#tl (tl hds)) (k - 1) else
                TM.next_move M st (tl hds) (k - 1))"
  have valid_M' [intro, simp]: "valid_TM M'"
    apply standard
    unfolding M'_def apply auto
    apply (smt (verit, best) Cons_in_lists_iff Suc_length_conv TM.at_least_one_tape TM.next_state_valid
        bot_nat_0.extremum_strict length_1_hd_iff length_Cons list.collapse list.sel(1,3) lists_member)
    using fs_final apply blast
    apply (metis (no_types, lifting) Cons_in_lists_iff Suc_length_conv TM.next_state_valid list.sel(3)
        lists_member)
    using fs_final apply blast
     apply (rule TM.next_write_valid)
        apply auto
      apply (metis Cons_in_lists_iff bot_nat_0.extremum_strict list.collapse list.size(3) lists_member)
     apply (metis Nitpick.size_list_simp(2) TM.at_least_one_tape less_not_refl list.set_sel(2) nat.distinct(1)
        old.nat.inject subsetD)
    apply (rule TM.next_write_valid)
       apply auto
    by (metis length_greater_0_conv list.set_sel(2) subset_code(1) zero_less_Suc)
  have f11: "cstate (TM.csteps (Abs_TM M') k (TM.cinitial_config (Abs_TM M') w)) =
             cstate (TM.csteps M k (TM.cinitial_config M w))" and
       f12: "\<And>i. i > 0 \<Longrightarrow> i < TM.tape_count M \<Longrightarrow>
             ctapes (TM.csteps (Abs_TM M') k (TM.cinitial_config (Abs_TM M') w)) ! (Suc i) =
             ctapes (TM.csteps M k (TM.cinitial_config M w)) ! i" and
       f13: "cleft (ctapes (TM.csteps (Abs_TM M') k (TM.cinitial_config (Abs_TM M') w)) ! 1) =
             cleft (ctapes (TM.csteps M k (TM.cinitial_config M w)) ! 0)" and
       f14: "chead (ctapes (TM.csteps (Abs_TM M') k (TM.cinitial_config (Abs_TM M') w)) ! 1) = None \<Longrightarrow>
             chead (ctapes (TM.csteps (Abs_TM M') k (TM.cinitial_config (Abs_TM M') w)) ! 0) =
             chead (ctapes (TM.csteps M k (TM.cinitial_config M w)) ! 0)" and
       f15: "chead (ctapes (TM.csteps (Abs_TM M') k (TM.cinitial_config (Abs_TM M') w)) ! 1) \<noteq> None \<Longrightarrow>
             chead (ctapes (TM.csteps (Abs_TM M') k (TM.cinitial_config (Abs_TM M') w)) ! 1) =
             chead (ctapes (TM.csteps M k (TM.cinitial_config M w)) ! 0)" and
       f16: "\<And>i. nth_clist (cright (ctapes (TM.csteps (Abs_TM M') k
             (TM.cinitial_config (Abs_TM M') w)) ! 1)) i = None \<Longrightarrow>
             nth_clist (cright (ctapes (TM.csteps (Abs_TM M') k
             (TM.cinitial_config (Abs_TM M') w)) ! 0)) i =
             nth_clist (cright (ctapes (TM.csteps M k (TM.cinitial_config M w)) ! 0)) i" and
       f17: "\<And>i. nth_clist (cright (ctapes (TM.csteps (Abs_TM M') k
             (TM.cinitial_config (Abs_TM M') w)) ! 1)) i \<noteq> None \<Longrightarrow>
             nth_clist (cright (ctapes (TM.csteps (Abs_TM M') k
             (TM.cinitial_config (Abs_TM M') w)) ! 1)) i =
             nth_clist (cright (ctapes (TM.csteps M k (TM.cinitial_config M w)) ! 0)) i" and
       f18: "cleft (ctapes (TM.csteps (Abs_TM M') k (TM.cinitial_config (Abs_TM M') w)) ! 0) =
             replicated_clist None" and
       f19: "ctape.set_ctape (ctapes (TM.csteps (Abs_TM M') k (TM.cinitial_config (Abs_TM M') w)) ! 0) \<subseteq> set w"
       if "\<And>n. n < k \<Longrightarrow>
           cheads (TM.csteps (Abs_TM M') n (TM.cinitial_config (Abs_TM M') w)) ! 0 \<in> options (alphabet L)"
    for k :: nat and w :: "'s list" using that
  proof (induction k)
    case 0
    {
      case 1
      show ?case apply simp
        unfolding TM.cinitial_config_def valid_tm_initial_state [OF valid_M'] apply simp
        unfolding M'_def by simp
    next
      case 2
      show ?case apply simp
        unfolding TM.cinitial_config_def TM_abbrevs.cinput_tape_def apply auto
        unfolding valid_tm_tape_count [OF valid_M'] unfolding M'_def apply auto
         apply (metis Suc_pred TM.at_least_one_tape replicate_Suc)
        by (metis "2.prems"(1) Suc_pred TM.at_least_one_tape nth_Cons_Suc replicate_Suc)
    next
      case 3
      show ?case apply simp
        unfolding TM.cinitial_config_def TM_abbrevs.cinput_tape_def apply auto
        unfolding valid_tm_tape_count [OF valid_M'] unfolding M'_def apply auto
        unfolding empty_ctape_def by simp
    next
      case 4
      show ?case apply simp
        unfolding TM.cinitial_config_def TM_abbrevs.cinput_tape_def by simp
    next
      case 5
      then show ?case apply auto
        unfolding TM.cinitial_config_def TM_abbrevs.cinput_tape_def apply auto
        unfolding valid_tm_tape_count [OF valid_M'] unfolding M'_def apply auto
        unfolding empty_ctape_def by simp
    next
      case 6
      show ?case apply simp
        unfolding TM.cinitial_config_def TM_abbrevs.cinput_tape_def by simp
    next
      case 7
      then show ?case apply auto
        unfolding TM.cinitial_config_def TM_abbrevs.cinput_tape_def apply auto
        unfolding valid_tm_tape_count [OF valid_M'] unfolding M'_def apply auto
        unfolding empty_ctape_def by simp
    next
      case 8
      show ?case apply simp
        unfolding TM.cinitial_config_def TM_abbrevs.cinput_tape_def apply auto
        unfolding empty_ctape_def by simp
    next
      case 9
      show ?case apply simp
        unfolding TM.cinitial_config_def TM_abbrevs.cinput_tape_def apply auto
        unfolding empty_ctape_def apply auto
        using list.set_intros(2)[of _ "tl w" "hd w"] set_clist_prepend_list[of "map Some (tl w)"
            "replicated_clist None"] by auto
    }
  next
    case (Suc k)
    {
      case 1
      hence *: "\<And>n. n < k \<Longrightarrow> cheads ((TM.cstep (Abs_TM M') ^^ n)
                (TM.cinitial_config (Abs_TM M') w)) ! 0 \<in> options (alphabet L)" by simp
      have **: "chead (ctapes ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w)) ! 0) \<in>
                options (alphabet L)" using 1 by simp
      have 2: "cheads ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w)) ! Suc 0 = None \<Longrightarrow>
               hd (cheads ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w))) #
               tl (tl (cheads ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w)))) =
               cheads ((TM.cstep M ^^ k) (TM.cinitial_config M w))"
        apply (rule nth_equalityI)
         apply auto
        unfolding valid_tm_tape_count [OF valid_M'] apply (subst M'_def)
         apply simp
        apply (subst nth_Cons')
        apply auto
         apply (subst Suc(4) [OF _ *, simplified, symmetric])
          apply (subst (asm) nth_map)
           apply auto
        using M'_def valid_tm_tape_count [OF valid_M'] apply force
         apply (subst hd_map)
          apply auto
          apply (metis (no_types, lifting) M'_def valid_tm_tape_count [OF valid_M'] length_ctapes_csteps_eq_tc
            list.size(3) nat.distinct(1) simps(1))
         apply (subst zeroth_is_head)
          apply auto
         apply (metis (no_types, lifting) M'_def valid_tm_tape_count [OF valid_M'] length_ctapes_csteps_eq_tc
            list.size(3) nat.distinct(1) simps(1))
      proof -
        fix i :: nat
        assume a1: "cheads ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w)) ! Suc 0 = None" and
               a2: "i < Suc (tape_count M' - Suc (Suc 0))" and
               a3: "0 < i"
        have 1: "Suc (Suc (i - Suc 0)) = Suc i" using a3 by simp
        show "tl (tl (cheads ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w)))) ! (i - Suc 0) =
              cheads ((TM.cstep M ^^ k) (TM.cinitial_config M w)) ! i"
          apply (subst nth_tl)
          using a2 apply (auto simp add: valid_tm_tape_count)
           apply (metis Suc_pred a3 not_less_eq)
          apply (subst nth_tl)
           apply (auto simp add: valid_tm_tape_count)
           apply (simp add: M'_def a3)
          unfolding 1 apply (subst (1 2) nth_map)
          using a2 apply auto
            apply (simp add: M'_def)
           apply (simp add: valid_tm_tape_count)
           apply (simp add: M'_def)
          apply (subst Suc(2))
             apply auto
            apply (rule a3)
           apply (simp add: M'_def)
          apply (drule *)
          apply (subst (asm) nth_map)
          by simp
      qed
      have 3: "\<And>y. cheads ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w)) ! Suc 0 = Some y \<Longrightarrow>
               tl (cheads ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w))) =
               cheads ((TM.cstep M ^^ k) (TM.cinitial_config M w))"
        apply (rule nth_equalityI)
         apply auto
        unfolding valid_tm_tape_count [OF valid_M'] apply (subst M'_def)
         apply simp
        apply (subst (asm) (3) M'_def)
        apply simp
        apply (subst nth_tl)
         apply auto
        using M'_def valid_tm_tape_count [OF valid_M'] apply force
        apply (subst nth_map)
         apply auto
        using M'_def valid_tm_tape_count [OF valid_M'] apply force
      proof -
        fix i :: nat and y :: 's
        assume a1: "chead (ctapes ((TM.cstep (Abs_TM M') ^^ k)
                    (TM.cinitial_config (Abs_TM M') w)) ! Suc 0) = Some y" and
               a2: "i < TM.TM.tape_count M"
        show "chead (ctapes ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w)) ! Suc i) =
              chead (ctapes ((TM.cstep M ^^ k) (TM.cinitial_config M w)) ! i)"
          apply (cases "i = 0")
           apply auto
           apply (subst Suc(5) [OF _ *, simplified])
          using a1 apply auto
          apply (subst Suc(2))
             apply auto
           apply (rule a2)
          using * by simp
      qed
      show ?case apply simp
        apply (subst (1 2) TM.cstep_def)
        apply auto
        unfolding Suc(1) [OF *, simplified] valid_tm_final_states [OF valid_M'] apply auto
          apply (subst (asm) M'_def)
          apply simp
        apply (subst (asm) M'_def)
         apply simp
        unfolding TM.cstep_not_final_def Let_def apply simp
        unfolding Suc(1) [OF *, simplified] valid_tm_next_state [OF valid_M'] apply (subst M'_def)
        apply (auto simp add: **)
        unfolding 2 apply standard
        unfolding 3 ..
    next
      case 2
      hence *: "\<And>n. n < k \<Longrightarrow> cheads ((TM.cstep (Abs_TM M') ^^ n)
                (TM.cinitial_config (Abs_TM M') w)) ! 0 \<in> options (alphabet L)" by simp
      have **: "chead (ctapes ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w)) ! 0) \<in>
                options (alphabet L)" using 2 by simp
      have 1: "[0..<tape_count M'] ! Suc i = Suc i" using 2(2) unfolding M'_def apply simp
        by (simp add: nth_append)
      have 3: "cheads ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w)) ! Suc 0 = None \<Longrightarrow>
               hd (cheads ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w))) #
               tl (tl (cheads ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w)))) =
               cheads ((TM.cstep M ^^ k) (TM.cinitial_config M w))"
        apply (rule nth_equalityI)
         apply auto
        using M'_def valid_tm_tape_count apply fastforce
        apply (subst nth_Cons')
        apply auto
         apply (subst Suc(4) [symmetric])
           apply auto
        using M'_def valid_tm_tape_count apply fastforce
        using * apply fastforce
         apply (metis (no_types, lifting) M'_def Nitpick.size_list_simp(2) hd_conv_nth
            length_ctapes_csteps_eq_tc list.map_sel(1) nat.distinct(1) select_convs(1) valid_M'
            valid_tm_tape_count)
        apply (subst nth_tl)
         apply auto
        apply (subst nth_tl)
         apply auto
        apply (subst Suc(2) [OF _ _ *, simplified])
          apply auto
        using M'_def valid_tm_tape_count apply force
        apply (subst nth_map)
         apply auto
        using M'_def valid_tm_tape_count by force
      have 4: "[0..<TM.TM.tape_count M] ! i = i" using 2(2) by simp
      have 5: "\<And>y. cheads ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w)) ! Suc 0 = Some y \<Longrightarrow>
               tl (cheads ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w))) =
               cheads ((TM.cstep M ^^ k) (TM.cinitial_config M w))" apply (rule nth_equalityI)
         apply auto
        using M'_def valid_tm_tape_count apply fastforce
        apply (subst nth_tl)
         apply auto
      proof -
        fix i :: nat and y :: 's
        assume a1: "chead (ctapes ((TM.cstep (Abs_TM M') ^^ k)
                    (TM.cinitial_config (Abs_TM M') w)) ! Suc 0) = Some y" and
               a2: "i < TM.TM.tape_count (Abs_TM M') - Suc 0"
        show "chead (ctapes ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w)) ! Suc i) =
              cheads ((TM.cstep M ^^ k) (TM.cinitial_config M w)) ! i"
          apply (cases "i = 0")
           apply auto
           apply (subst Suc(5) [simplified])
             apply auto
          using a1 apply simp
          using * apply simp
          using Suc(2) [of i, OF _ _ *, simplified] a2 apply auto
          unfolding valid_tm_tape_count [OF valid_M'] apply (subst (asm) (2) M'_def)
          by simp
      qed
      show ?case apply simp
        apply (subst (1 2) TM.cstep_def)
        apply auto
        unfolding Suc(1) [OF *, simplified] valid_tm_final_states [OF valid_M']
        unfolding Suc(2) [OF 2(1, 2) *, simplified] apply auto
          apply (subst (asm) M'_def)
          apply simp
         apply (subst (asm) M'_def)
         apply simp
        unfolding TM.cstep_not_final_def Let_def apply auto
        apply (subst (1 2) nth_map2)
            apply auto
            apply (metis "2.prems"(2) TM.next_actions_simps(2))
           apply (rule 2(2))
        using "2.prems"(2) M'_def
          TM.next_actions_simps(2)[of "Abs_TM M'" "cstate ((TM.cstep (Abs_TM M') ^^ k)
            (TM.cinitial_config (Abs_TM M') w))"
            "cheads ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w))"]
          not_less_eq[of i "TM.TM.tape_count M"] not_less_eq[of "TM.TM.tape_count M" "Suc i"]
          simps(1)[of "Suc (TM.TM.tape_count M)" "TM.TM.symbols M" "TM.TM.states M" "TM.TM.initial_state M"
            "TM.TM.final_states M" "TM.TM.label M"
            "\<lambda>uuc uud.
          if uud ! 0 \<in> options (alphabet L)
          then if uud ! 1 = None then TM.TM.next_state M uuc (hd uud # tl (tl uud))
               else TM.TM.next_state M uuc (tl uud)
          else fs"
            "\<lambda>uua uub uuc.
          if uuc = 0 then None
          else if uub ! 1 = None then TM.TM.next_write M uua (hd uub # tl (tl uub)) (uuc - 1)
               else TM.TM.next_write M uua (tl uub) (uuc - 1)"
            "\<lambda>uua uub uuc.
          if uub ! 1 = None then TM.TM.next_move M uua (hd uub # tl (tl uub)) (uuc - 1)
          else TM.TM.next_move M uua (tl uub) (uuc - 1)"
            "()"]
          valid_M' valid_tm_tape_count[of M'] apply presburger
        using "2.prems"(2) M'_def valid_tm_tape_count apply force
        unfolding TM.ctape_action_def TM.next_actions_def Suc(1) [OF *, simplified]
          TM.next_writes_def TM.next_moves_def apply (subst (1 2 3 4) nth_zip)
            apply auto
            apply (rule 2(2))+
        unfolding valid_tm_tape_count [OF valid_M'] using 2(2) apply (simp add: M'_def)
        using 2(2) apply (simp add: M'_def)
        apply (subst (1 2 3 4) nth_map)
          apply auto
          apply (rule 2(2))
        using 2(2) apply (simp add: M'_def)
        unfolding 1 valid_tm_next_move [OF valid_M'] valid_tm_next_write [OF valid_M'] apply (subst M'_def)
        apply auto
         apply (subst (5) M'_def)
         apply simp
        unfolding 3 4 apply (cases "TM.TM.next_move M (cstate ((TM.cstep M ^^ k) (TM.cinitial_config M w)))
                                  (cheads ((TM.cstep M ^^ k) (TM.cinitial_config M w))) i")
           apply auto
        unfolding TM_abbrevs.ctape_write_def Suc(2) [OF 2(1, 2) *, simplified] apply auto
        unfolding 5 apply (cases "TM.TM.next_move M (cstate ((TM.cstep M ^^ k) (TM.cinitial_config M w)))
                                  (cheads ((TM.cstep M ^^ k) (TM.cinitial_config M w))) i")
          apply auto
          apply (cases "cleft (ctapes ((TM.cstep M ^^ k) (TM.cinitial_config M w)) ! i)")
          apply auto
        unfolding TM_abbrevs.ctape_shift.simps apply auto
          apply (subst M'_def)
          apply simp
        unfolding 5 apply simp
         apply (cases "cright (ctapes ((TM.cstep M ^^ k) (TM.cinitial_config M w)) ! i)")
         apply auto
        unfolding TM_abbrevs.ctape_shift.simps apply auto
        unfolding 5 apply (subst M'_def)
         apply (simp add: 5)
        apply (subst M'_def)
        apply simp
        unfolding 5 ..
    next
      case 3
      hence *: "\<And>n. n < k \<Longrightarrow> cheads ((TM.cstep (Abs_TM M') ^^ n)
                (TM.cinitial_config (Abs_TM M') w)) ! 0 \<in> options (alphabet L)" by simp
      have **: "chead (ctapes ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w)) ! 0) \<in>
                options (alphabet L)" using 3 by simp
      have 1: "[0..<TM.TM.tape_count (Abs_TM M')] ! Suc 0 = Suc 0" using 3
        unfolding valid_tm_tape_count [OF valid_M'] apply (subst M'_def)
        apply simp
        by (metis Suc_lessI TM.at_least_one_tape diff_Suc_1' diff_Suc_Suc length_Cons length_upt
            list.size(4) nth_append nth_append_length nth_upt)
      have 2: "cheads ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w)) ! Suc 0 = None \<Longrightarrow>
               hd (cheads ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w))) #
               tl (tl (cheads ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w)))) =
               cheads ((TM.cstep M ^^ k) (TM.cinitial_config M w))"
        apply (rule nth_equalityI)
         apply auto
        using M'_def valid_tm_tape_count apply fastforce
        apply (subst nth_Cons')
        apply auto
         apply (subst Suc(4) [symmetric])
           apply auto
        using M'_def valid_tm_tape_count apply fastforce
        using * apply fastforce
         apply (metis (no_types, lifting) M'_def Nitpick.size_list_simp(2) hd_conv_nth
            length_ctapes_csteps_eq_tc list.map_sel(1) nat.distinct(1) select_convs(1) valid_M'
            valid_tm_tape_count)
        apply (subst nth_tl)
         apply auto
        apply (subst nth_tl)
         apply auto
        apply (subst Suc(2) [OF _ _ *, simplified])
          apply auto
        using M'_def valid_tm_tape_count apply force
        apply (subst nth_map)
         apply auto
        using M'_def valid_tm_tape_count by force
      have 4: "\<And>y. cheads ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w)) ! Suc 0 = Some y \<Longrightarrow>
               tl (cheads ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w))) =
               cheads ((TM.cstep M ^^ k) (TM.cinitial_config M w))" apply (rule nth_equalityI)
         apply auto
        using M'_def valid_tm_tape_count apply fastforce
        apply (subst nth_tl)
         apply auto
      proof -
        fix i :: nat and y :: 's
        assume a1: "chead (ctapes ((TM.cstep (Abs_TM M') ^^ k)
                    (TM.cinitial_config (Abs_TM M') w)) ! Suc 0) = Some y" and
               a2: "i < TM.TM.tape_count (Abs_TM M') - Suc 0"
        show "chead (ctapes ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w)) ! Suc i) =
              cheads ((TM.cstep M ^^ k) (TM.cinitial_config M w)) ! i"
          apply (cases "i = 0")
           apply auto
           apply (subst Suc(5) [simplified])
             apply auto
          using a1 apply simp
          using * apply simp
          using Suc(2) [of i, OF _ _ *, simplified] a2 apply auto
          unfolding valid_tm_tape_count [OF valid_M'] apply (subst (asm) (2) M'_def)
          by simp
      qed
      show ?case apply simp
        apply (subst (1 2) TM.cstep_def)
        apply (auto simp add: Suc(1) [OF *] valid_tm_final_states)
           apply (subst Suc(3) [simplified])
            apply auto
        using * apply simp
          apply (subst (asm) M'_def)
          apply simp
         apply (subst (asm) M'_def)
         apply simp
        unfolding TM.cstep_not_final_def Let_def apply auto
        apply (subst (1 2) nth_map2)
            apply auto
           apply (metis TM.at_least_one_tape TM.next_actions_simps(2) gr0_conv_Suc list.size(3) nat.distinct(1))
        apply (metis (no_types, lifting) M'_def One_nat_def Suc_lessI TM.at_least_one_tape' TM.next_actions_simps(2)
            diff_Suc_1' linorder_not_less simps(1) valid_M' valid_tm_tape_count zero_less_Suc)
        using M'_def valid_tm_tape_count apply force
        unfolding TM.ctape_action_def TM.next_actions_def TM.next_writes_def TM.next_moves_def apply auto
        apply (subst (1 2) nth_zip)
          apply auto
        using M'_def valid_tm_tape_count apply force
        using M'_def valid_tm_tape_count apply force
        apply (subst (1 2) nth_map)
        using M'_def valid_tm_tape_count apply force
        unfolding 1 valid_tm_next_move [OF valid_M'] valid_tm_next_write [OF valid_M'] Suc(1) [OF *, simplified]
        apply (subst M'_def)
        apply auto
        unfolding 2 apply (subst M'_def)
         apply simp
        unfolding 2 TM_abbrevs.ctape_write_def
        apply (cases "TM.TM.next_move M (cstate ((TM.cstep M ^^ k) (TM.cinitial_config M w)))
                      (cheads ((TM.cstep M ^^ k) (TM.cinitial_config M w))) 0")
           apply auto
        unfolding Suc(3) [OF *, simplified]
           apply (cases "cleft (ctapes ((TM.cstep M ^^ k) (TM.cinitial_config M w)) ! 0)")
           apply simp
        unfolding TM_abbrevs.ctape_shift.simps apply simp
          apply (simp add: TM_abbrevs.left_ctape_shift_right)
         apply simp
        unfolding 4 apply (cases "TM.TM.next_move M (cstate ((TM.cstep M ^^ k) (TM.cinitial_config M w)))
                                  (cheads ((TM.cstep M ^^ k) (TM.cinitial_config M w))) 0")
          apply auto
          apply (cases "cleft (ctapes ((TM.cstep M ^^ k) (TM.cinitial_config M w)) ! 0)")
          apply simp
        unfolding TM_abbrevs.ctape_shift.simps apply simp
        apply (subst M'_def)
         apply simp
        unfolding 4 apply (simp add: TM_abbrevs.left_ctape_shift_right)
        apply (subst M'_def)
        by simp
    next
      case 4
      hence *: "\<And>n. n < k \<Longrightarrow> cheads ((TM.cstep (Abs_TM M') ^^ n)
                (TM.cinitial_config (Abs_TM M') w)) ! 0 \<in> options (alphabet L)" by simp
      have **: "chead (ctapes ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w)) ! 0) \<in>
                options (alphabet L)" using 4 by simp
      have 1: "cstate ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w)) \<in>
               TM.TM.final_states (Abs_TM M') \<Longrightarrow>
               chead (ctapes ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w)) ! 1) = None"
        using 4(1) apply simp
        apply (subst (asm) TM.cstep_def)
        by simp
      have 2: "cheads ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w)) ! Suc 0 = None \<Longrightarrow>
               hd (cheads ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w))) #
               tl (tl (cheads ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w)))) =
               cheads ((TM.cstep M ^^ k) (TM.cinitial_config M w))"
        apply (rule nth_equalityI)
         apply auto
        using M'_def valid_tm_tape_count apply fastforce
        apply (subst nth_Cons')
        apply auto
         apply (subst Suc(4) [symmetric])
           apply auto
        using M'_def valid_tm_tape_count apply fastforce
        using * apply fastforce
         apply (metis (no_types, lifting) M'_def Nitpick.size_list_simp(2) hd_conv_nth
            length_ctapes_csteps_eq_tc list.map_sel(1) nat.distinct(1) select_convs(1) valid_M'
            valid_tm_tape_count)
        apply (subst nth_tl)
         apply auto
        apply (subst nth_tl)
         apply auto
        apply (subst Suc(2) [OF _ _ *, simplified])
          apply auto
        using M'_def valid_tm_tape_count apply force
        apply (subst nth_map)
         apply auto
        using M'_def valid_tm_tape_count by force
      have 3: "\<And>y. cheads ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w)) ! Suc 0 = Some y \<Longrightarrow>
               tl (cheads ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w))) =
               cheads ((TM.cstep M ^^ k) (TM.cinitial_config M w))" apply (rule nth_equalityI)
         apply auto
        using M'_def valid_tm_tape_count apply fastforce
        apply (subst nth_tl)
         apply auto
      proof -
        fix i :: nat and y :: 's
        assume a1: "chead (ctapes ((TM.cstep (Abs_TM M') ^^ k)
                    (TM.cinitial_config (Abs_TM M') w)) ! Suc 0) = Some y" and
               a2: "i < TM.TM.tape_count (Abs_TM M') - Suc 0"
        show "chead (ctapes ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w)) ! Suc i) =
              cheads ((TM.cstep M ^^ k) (TM.cinitial_config M w)) ! i"
          apply (cases "i = 0")
           apply auto
           apply (subst Suc(5) [simplified])
             apply auto
          using a1 apply simp
          using * apply simp
          using Suc(2) [of i, OF _ _ *, simplified] a2 apply auto
          unfolding valid_tm_tape_count [OF valid_M'] apply (subst (asm) (2) M'_def)
          by simp
      qed
      have 5: "[0..<TM.TM.tape_count (Abs_TM M')] ! Suc 0 = Suc 0"
        by (metis (no_types, lifting) M'_def One_nat_def TM.at_least_one_tape' add_0 less_Suc_eq_le
            nth_upt simps(1) valid_M' valid_tm_tape_count)
      show ?case using 4(1) apply simp
        apply (subst (1 2) TM.cstep_def)
        apply (subst (asm) TM.cstep_def)
        apply auto
           apply (drule 1 [simplified])
        unfolding Suc(4) [OF _ *, simplified] apply standard
        unfolding Suc(1) [OF *, simplified] valid_tm_final_states [OF valid_M'] apply (subst (asm) (3) M'_def)
          apply simp
        apply (subst (asm) (4) M'_def)
         apply simp
        unfolding TM.cstep_not_final_def Let_def apply auto
        unfolding Suc(1) [OF *, simplified] apply (subst (1 2) nth_map2)
            apply (subst (asm) nth_map2)
              apply auto
            apply (metis (no_types, lifting) M'_def One_nat_def Suc_lessI TM.at_least_one_tape'
            TM.next_actions_simps(2) diff_Suc_1' linorder_not_less simps(1) valid_M'
            valid_tm_tape_count zero_less_Suc)
        using M'_def valid_tm_tape_count apply force
          apply (metis TM.at_least_one_tape TM.next_actions_simps(2) less_numeral_extra(3) list.size(3))
        apply (metis TM.at_least_one_tape TM.next_actions_simps(2) less_numeral_extra(3) list.size(3))
        unfolding TM.ctape_action_def TM.next_actions_def TM.next_moves_def TM.next_writes_def apply auto
        apply (subst (asm) nth_map2)
          apply auto
        using M'_def valid_tm_tape_count apply force
        using M'_def valid_tm_tape_count apply force
        apply (subst (asm) (1 2) nth_zip)
          apply auto
        using M'_def valid_tm_tape_count apply force
        using M'_def valid_tm_tape_count apply force
        apply (subst (asm) (1 2) nth_map)
        using M'_def valid_tm_tape_count apply force
        unfolding 5 valid_tm_next_move [OF valid_M'] valid_tm_next_write [OF valid_M'] apply (subst M'_def)
        apply auto
        unfolding 2 apply (subst M'_def)
         apply (subst (asm) M'_def)
         apply auto
        unfolding TM_abbrevs.ctape_write_def 2
        apply (cases "TM.TM.next_move M (cstate ((TM.cstep M ^^ k) (TM.cinitial_config M w)))
                      (cheads ((TM.cstep M ^^ k) (TM.cinitial_config M w))) 0")
           apply auto
        unfolding TM_abbrevs.ctape_shift.simps 3
      proof -
        assume a1: "chead (TM_abbrevs.ctape_shift Shift_Left
                    (CTape (cleft (ctapes ((TM.cstep (Abs_TM M') ^^ k)
                    (TM.cinitial_config (Abs_TM M') w)) ! Suc 0))
                    (next_write M' (cstate ((TM.cstep M ^^ k) (TM.cinitial_config M w)))
                    (cheads ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w))) (Suc 0))
                    (cright (ctapes ((TM.cstep (Abs_TM M') ^^ k)
                    (TM.cinitial_config (Abs_TM M') w)) ! Suc 0)))) = None" and
               a2: "cheads ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w)) ! Suc 0 = None"
        thus "chead (TM_abbrevs.ctape_shift Shift_Left
              (CTape (cleft (ctapes ((TM.cstep (Abs_TM M') ^^ k)
              (TM.cinitial_config (Abs_TM M') w)) ! 0)) None
              (cright (ctapes ((TM.cstep (Abs_TM M') ^^ k)
              (TM.cinitial_config (Abs_TM M') w)) ! 0)))) =
              chead (TM_abbrevs.ctape_shift Shift_Left
              (CTape (cleft (ctapes ((TM.cstep M ^^ k) (TM.cinitial_config M w)) ! 0))
              (TM.TM.next_write M (cstate ((TM.cstep M ^^ k) (TM.cinitial_config M w)))
              (cheads ((TM.cstep M ^^ k) (TM.cinitial_config M w))) 0)
              (cright (ctapes ((TM.cstep M ^^ k) (TM.cinitial_config M w)) ! 0))))"
          apply (subst (asm) (3) M'_def)
          apply simp
          unfolding 2 Suc(3) [OF *, simplified]
          apply (cases "cleft (ctapes ((TM.cstep M ^^ k) (TM.cinitial_config M w)) ! 0)")
          apply auto
          unfolding TM_abbrevs.ctape_shift.simps apply auto
          by (metis * Suc.IH(8) TM_abbrevs.head_ctape_shift_left ctape.sel(1) replicated_clist.simps(1))
      next
        assume a1: "chead (TM_abbrevs.ctape_shift Shift_Right
                    (CTape (cleft (ctapes ((TM.cstep (Abs_TM M') ^^ k)
                    (TM.cinitial_config (Abs_TM M') w)) ! Suc 0))
                    (next_write M' (cstate ((TM.cstep M ^^ k) (TM.cinitial_config M w)))
                    (cheads ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w))) (Suc 0))
                    (cright (ctapes ((TM.cstep (Abs_TM M') ^^ k)
                    (TM.cinitial_config (Abs_TM M') w)) ! Suc 0)))) = None" and
               a2: "cheads ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w)) ! Suc 0 = None"
        thus "chead (TM_abbrevs.ctape_shift Shift_Right (CTape (cleft (ctapes
              ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w)) ! 0)) None
              (cright (ctapes ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w)) ! 0)))) =
              chead (TM_abbrevs.ctape_shift Shift_Right
              (CTape (cleft (ctapes ((TM.cstep M ^^ k) (TM.cinitial_config M w)) ! 0))
              (TM.TM.next_write M (cstate ((TM.cstep M ^^ k) (TM.cinitial_config M w)))
              (cheads ((TM.cstep M ^^ k) (TM.cinitial_config M w))) 0)
              (cright (ctapes ((TM.cstep M ^^ k) (TM.cinitial_config M w)) ! 0))))"
          apply (subst (asm) (3) M'_def)
          apply simp
          unfolding 2 apply (cases "nth_clist (cright (ctapes ((TM.cstep (Abs_TM M') ^^ k)
                                    (TM.cinitial_config (Abs_TM M') w)) ! 1)) 0")
           apply auto
          using Suc(6) [OF _ *, simplified, of 0] apply (simp add: TM_abbrevs.head_ctape_shift_right)
          using Suc(7) [OF _ *, simplified, of 0] by (simp add: TM_abbrevs.head_ctape_shift_right)
      next
        assume a1: "chead (CTape (cleft (ctapes ((TM.cstep (Abs_TM M') ^^ k)
                    (TM.cinitial_config (Abs_TM M') w)) ! Suc 0))
                    (next_write M' (cstate ((TM.cstep M ^^ k) (TM.cinitial_config M w)))
                    (cheads ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w))) (Suc 0))
                    (cright (ctapes ((TM.cstep (Abs_TM M') ^^ k)
                    (TM.cinitial_config (Abs_TM M') w)) ! Suc 0))) = None" and
               a2: "cheads ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w)) ! Suc 0 = None"
        show "chead (CTape (cleft (ctapes ((TM.cstep (Abs_TM M') ^^ k)
              (TM.cinitial_config (Abs_TM M') w)) ! 0)) None
              (cright (ctapes ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w)) ! 0))) =
              chead (CTape (cleft (ctapes ((TM.cstep M ^^ k) (TM.cinitial_config M w)) ! 0))
              (TM.TM.next_write M (cstate ((TM.cstep M ^^ k) (TM.cinitial_config M w)))
              (cheads ((TM.cstep M ^^ k) (TM.cinitial_config M w))) 0)
              (cright (ctapes ((TM.cstep M ^^ k) (TM.cinitial_config M w)) ! 0)))"
          using 2 M'_def a1 a2 by fastforce
      next
        fix y :: 's
        assume a1: "chead (TM_abbrevs.ctape_shift (next_move M' (cstate ((TM.cstep M ^^ k)
                    (TM.cinitial_config M w))) (cheads ((TM.cstep (Abs_TM M') ^^ k)
                    (TM.cinitial_config (Abs_TM M') w))) (Suc 0))
                    (CTape (cleft (ctapes ((TM.cstep (Abs_TM M') ^^ k)
                    (TM.cinitial_config (Abs_TM M') w)) ! Suc 0))
                    (next_write M' (cstate ((TM.cstep M ^^ k) (TM.cinitial_config M w)))
                    (cheads ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w))) (Suc 0))
                    (cright (ctapes ((TM.cstep (Abs_TM M') ^^ k)
                    (TM.cinitial_config (Abs_TM M') w)) ! Suc 0)))) = None" and
               a2: "cheads ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w)) ! Suc 0 = Some y"
        thus "chead (TM_abbrevs.ctape_shift (TM.TM.next_move M (cstate ((TM.cstep M ^^ k)
              (TM.cinitial_config M w))) (cheads ((TM.cstep M ^^ k) (TM.cinitial_config M w))) 0)
              (CTape (cleft (ctapes ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w)) ! 0))
              (next_write M' (cstate ((TM.cstep M ^^ k) (TM.cinitial_config M w)))
              (cheads ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w))) 0)
              (cright (ctapes ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w)) ! 0)))) =
              chead (TM_abbrevs.ctape_shift (TM.TM.next_move M (cstate ((TM.cstep M ^^ k)
              (TM.cinitial_config M w))) (cheads ((TM.cstep M ^^ k) (TM.cinitial_config M w))) 0)
              (CTape (cleft (ctapes ((TM.cstep M ^^ k) (TM.cinitial_config M w)) ! 0))
              (TM.TM.next_write M (cstate ((TM.cstep M ^^ k) (TM.cinitial_config M w)))
              (cheads ((TM.cstep M ^^ k) (TM.cinitial_config M w))) 0)
              (cright (ctapes ((TM.cstep M ^^ k) (TM.cinitial_config M w)) ! 0))))"
          apply (subst (asm) M'_def)
          apply simp
          unfolding 3 apply (cases "TM.TM.next_move M (cstate ((TM.cstep M ^^ k) (TM.cinitial_config M w)))
                                    (cheads ((TM.cstep M ^^ k) (TM.cinitial_config M w))) 0")
            apply auto
          apply (metis * One_nat_def Suc.IH(3,8) TM_abbrevs.head_ctape_shift_left ctape.sel(1)
              replicated_clist.simps(1))
           apply (metis * One_nat_def Suc.IH(6) TM_abbrevs.head_ctape_shift_right ctape.sel(3)
              zeroth_clist_is_chd)
          unfolding TM_abbrevs.ctape_shift.simps apply simp
          apply (subst M'_def)
          apply simp
          apply (subst (asm) M'_def)
          apply simp
          unfolding 3 by simp
      qed
    next
      case 5
      hence *: "\<And>n. n < k \<Longrightarrow> cheads ((TM.cstep (Abs_TM M') ^^ n)
                (TM.cinitial_config (Abs_TM M') w)) ! 0 \<in> options (alphabet L)" by simp
      have **: "chead (ctapes ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w)) ! 0) \<in>
                options (alphabet L)" using 5 by simp
      have 1: "[0..<TM.TM.tape_count (Abs_TM M')] ! Suc 0 = Suc 0"
        by (metis (no_types, lifting) M'_def One_nat_def TM.at_least_one_tape add.commute not_less_eq
            nth_upt plus_1_eq_Suc simps(1) valid_M' valid_tm_tape_count)
      have 2: "cheads ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w)) ! Suc 0 = None \<Longrightarrow>
               hd (cheads ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w))) #
               tl (tl (cheads ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w)))) =
               cheads ((TM.cstep M ^^ k) (TM.cinitial_config M w))"
        apply (rule nth_equalityI)
         apply auto
        using M'_def valid_tm_tape_count apply fastforce
        apply (subst nth_Cons')
        apply auto
         apply (subst Suc(4) [symmetric])
           apply auto
        using M'_def valid_tm_tape_count apply fastforce
        using * apply fastforce
         apply (metis (no_types, lifting) M'_def Nitpick.size_list_simp(2) hd_conv_nth
            length_ctapes_csteps_eq_tc list.map_sel(1) nat.distinct(1) select_convs(1) valid_M'
            valid_tm_tape_count)
        apply (subst nth_tl)
         apply auto
        apply (subst nth_tl)
         apply auto
        apply (subst Suc(2) [OF _ _ *, simplified])
          apply auto
        using M'_def valid_tm_tape_count apply force
        apply (subst nth_map)
         apply auto
        using M'_def valid_tm_tape_count by force
      have 3: "\<And>y. cheads ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w)) ! Suc 0 = Some y \<Longrightarrow>
               tl (cheads ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w))) =
               cheads ((TM.cstep M ^^ k) (TM.cinitial_config M w))" apply (rule nth_equalityI)
         apply auto
        using M'_def valid_tm_tape_count apply fastforce
        apply (subst nth_tl)
         apply auto
      proof -
        fix i :: nat and y :: 's
        assume a1: "chead (ctapes ((TM.cstep (Abs_TM M') ^^ k)
                    (TM.cinitial_config (Abs_TM M') w)) ! Suc 0) = Some y" and
               a2: "i < TM.TM.tape_count (Abs_TM M') - Suc 0"
        show "chead (ctapes ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w)) ! Suc i) =
              cheads ((TM.cstep M ^^ k) (TM.cinitial_config M w)) ! i"
          apply (cases "i = 0")
           apply auto
           apply (subst Suc(5) [simplified])
             apply auto
          using a1 apply simp
          using * apply simp
          using Suc(2) [of i, OF _ _ *, simplified] a2 apply auto
          unfolding valid_tm_tape_count [OF valid_M'] apply (subst (asm) (2) M'_def)
          by simp
      qed
      show ?case using 5(1) apply auto
        apply (subst (asm) TM.cstep_def)
        apply (subst TM.cstep_def)
        apply (cases "cstate ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w))
                      \<in> TM.TM.final_states (Abs_TM M')")
         apply auto
           apply (metis * One_nat_def Suc.IH(5) option.distinct(1))
        unfolding Suc(1) [OF *, simplified] valid_tm_final_states [OF valid_M'] apply (subst (asm) (3) M'_def)
          apply simp
         apply (subst (asm) (4) M'_def)
         apply simp
        unfolding TM.cstep_not_final_def Let_def apply auto
        apply (subst (asm) nth_map2)
          apply auto
          apply (metis (no_types, lifting) M'_def TM.at_least_one_tape TM.next_actions_simps(2)
            not_less_eq simps(1) valid_M' valid_tm_tape_count)
         apply (metis (no_types, lifting) M'_def One_nat_def Suc_lessI TM.at_least_one_tape'
            diff_Suc_1' linorder_not_less simps(1) valid_M' valid_tm_tape_count zero_less_Suc)
        apply (subst nth_map2)
          apply auto
         apply (metis TM.at_least_one_tape TM.next_actions_simps(2) less_not_refl list.size(3))
        unfolding TM.ctape_action_def TM.next_actions_def TM.next_writes_def TM.next_moves_def apply auto
        apply (subst (asm) (1 2) nth_zip)
          apply auto
          apply (metis (no_types, lifting) M'_def One_nat_def Suc_lessI TM.at_least_one_tape'
            diff_Suc_1' linorder_not_less simps(1) valid_M' valid_tm_tape_count zero_less_Suc)
         apply (metis (no_types, lifting) M'_def One_nat_def Suc_lessI TM.at_least_one_tape'
            diff_Suc_1' linorder_not_less simps(1) valid_M' valid_tm_tape_count zero_less_Suc)
        apply (subst (asm) (1 2) nth_map)
         apply auto
        using M'_def valid_tm_tape_count apply fastforce
        unfolding valid_tm_next_move [OF valid_M'] valid_tm_next_write [OF valid_M'] Suc(1) [OF *, simplified]
          1 apply (subst (asm) M'_def)
        apply auto
        apply (cases "cheads ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w)) ! Suc 0 = None")
         apply auto
        unfolding 2 3 apply (cases "TM.TM.next_move M (cstate ((TM.cstep M ^^ k) (TM.cinitial_config M w)))
                                    (cheads ((TM.cstep M ^^ k) (TM.cinitial_config M w))) 0")
           apply auto
           apply (metis * One_nat_def Suc.IH(3) TM_abbrevs.head_ctape_shift_left left_ctape_write)
          apply (metis * One_nat_def Suc.IH(7) TM_abbrevs.head_ctape_shift_right right_ctape_write
            option.distinct(1) zeroth_clist_is_chd)
        unfolding TM_abbrevs.ctape_shift.simps apply (subst (asm) M'_def)
         apply simp
        unfolding 2 apply argo
        apply (subst (asm) M'_def)
        apply simp
        unfolding 3 apply (cases "TM.TM.next_move M (cstate ((TM.cstep M ^^ k) (TM.cinitial_config M w)))
                                  (cheads ((TM.cstep M ^^ k) (TM.cinitial_config M w))) 0")
          apply auto
          apply (metis * One_nat_def Suc.IH(3) TM_abbrevs.head_ctape_shift_left left_ctape_write)
         apply (metis * One_nat_def Suc.IH(7) TM_abbrevs.head_ctape_shift_right right_ctape_write
            option.distinct(1) zeroth_clist_is_chd)
        unfolding TM_abbrevs.ctape_shift.simps by (metis head_ctape_write)
    next
      case 6
      hence *: "\<And>n. n < k \<Longrightarrow> cheads ((TM.cstep (Abs_TM M') ^^ n)
                (TM.cinitial_config (Abs_TM M') w)) ! 0 \<in> options (alphabet L)" by simp
      have **: "chead (ctapes ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w)) ! 0) \<in>
                options (alphabet L)" using 6 by simp
      have 1: "[0..<TM.TM.tape_count (Abs_TM M')] ! Suc 0 = Suc 0"
        by (metis (no_types, lifting) M'_def One_nat_def TM.at_least_one_tape' add_0 less_Suc_eq_le
            nth_upt simps(1) valid_M' valid_tm_tape_count)
      have 2: "cheads ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w)) ! Suc 0 = None \<Longrightarrow>
               hd (cheads ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w))) #
               tl (tl (cheads ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w)))) =
               cheads ((TM.cstep M ^^ k) (TM.cinitial_config M w))"
        apply (rule nth_equalityI)
         apply auto
        using M'_def valid_tm_tape_count apply fastforce
        apply (subst nth_Cons')
        apply auto
         apply (subst Suc(4) [symmetric])
           apply auto
        using M'_def valid_tm_tape_count apply fastforce
        using * apply fastforce
         apply (metis (no_types, lifting) M'_def Nitpick.size_list_simp(2) hd_conv_nth
            length_ctapes_csteps_eq_tc list.map_sel(1) nat.distinct(1) select_convs(1) valid_M'
            valid_tm_tape_count)
        apply (subst nth_tl)
         apply auto
        apply (subst nth_tl)
         apply auto
        apply (subst Suc(2) [OF _ _ *, simplified])
          apply auto
        using M'_def valid_tm_tape_count apply force
        apply (subst nth_map)
         apply auto
        using M'_def valid_tm_tape_count by force
      have 3: "\<And>y. cheads ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w)) ! Suc 0 = Some y \<Longrightarrow>
               tl (cheads ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w))) =
               cheads ((TM.cstep M ^^ k) (TM.cinitial_config M w))" apply (rule nth_equalityI)
         apply auto
        using M'_def valid_tm_tape_count apply fastforce
        apply (subst nth_tl)
         apply auto
      proof -
        fix i :: nat and y :: 's
        assume a1: "chead (ctapes ((TM.cstep (Abs_TM M') ^^ k)
                    (TM.cinitial_config (Abs_TM M') w)) ! Suc 0) = Some y" and
               a2: "i < TM.TM.tape_count (Abs_TM M') - Suc 0"
        show "chead (ctapes ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w)) ! Suc i) =
              cheads ((TM.cstep M ^^ k) (TM.cinitial_config M w)) ! i"
          apply (cases "i = 0")
           apply auto
           apply (subst Suc(5) [simplified])
             apply auto
          using a1 apply simp
          using * apply simp
          using Suc(2) [of i, OF _ _ *, simplified] a2 apply auto
          unfolding valid_tm_tape_count [OF valid_M'] apply (subst (asm) (2) M'_def)
          by simp
      qed
      show ?case using 6(1) apply auto
        apply (subst (1 2) TM.cstep_def)
        apply (subst (asm) TM.cstep_def)
        unfolding Suc(1) [OF *, simplified] apply auto
        unfolding valid_tm_final_states [OF valid_M'] apply (metis * One_nat_def Suc.IH(6))
        apply (subst (asm) (3) M'_def)
          apply simp
         apply (subst (asm) (4) M'_def)
         apply simp
        unfolding TM.cstep_not_final_def Let_def apply auto
        apply (subst (1 2) nth_map2)
            apply auto
          apply (metis TM.at_least_one_tape TM.next_actions_simps(2) less_numeral_extra(3) list.size(3))
         apply (metis TM.at_least_one_tape TM.next_actions_simps(2) less_not_refl list.size(3))
        apply (subst (asm) nth_map2)
          apply auto
          apply (metis (no_types, lifting) M'_def TM.at_least_one_tape TM.next_actions_simps(2)
            not_less_eq simps(1) valid_M' valid_tm_tape_count)
        using M'_def valid_tm_tape_count apply fastforce
        unfolding TM.ctape_action_def TM.next_actions_def TM.next_writes_def TM.next_moves_def apply auto
        apply (subst (asm) (1 2) nth_zip)
          apply auto
        using M'_def valid_tm_tape_count apply fastforce
        using M'_def valid_tm_tape_count apply fastforce
        apply (subst (asm) (1 2) nth_map)
         apply auto
        using M'_def valid_tm_tape_count apply fastforce
        unfolding 1 valid_tm_next_move [OF valid_M'] valid_tm_next_write [OF valid_M']
          Suc(1) [OF *, simplified] apply (subst M'_def)
        apply (subst (asm) M'_def)
        apply auto
        unfolding 2 3 apply (cases "TM.TM.next_move M (cstate ((TM.cstep M ^^ k) (TM.cinitial_config M w)))
                                    (cheads ((TM.cstep M ^^ k) (TM.cinitial_config M w))) 0")
           apply auto
           apply (subst M'_def)
           apply (subst (asm) M'_def)
           apply auto
        unfolding 2 TM_abbrevs.ctape_write_def Suc(3) [OF *, simplified]
           apply (cases "cleft (ctapes ((TM.cstep M ^^ k) (TM.cinitial_config M w)) ! 0)")
           apply auto
        unfolding TM_abbrevs.ctape_shift.simps apply auto
           apply (cases "cleft (ctapes ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w)) ! 0)")
           apply auto
        unfolding TM_abbrevs.ctape_shift.simps apply auto
           apply (cases i)
            apply auto
           apply (metis * One_nat_def Suc.IH(6))
        unfolding TM_abbrevs.right_ctape_shift_right apply auto
        unfolding Sucth_clist_from_ctl [symmetric]
          apply (metis * One_nat_def Suc.IH(6))
         apply (metis * One_nat_def Suc.IH(6))
        apply (subst (3) M'_def)
        apply (subst (asm) M'_def)
        apply auto
        unfolding 3 apply (cases "TM.TM.next_move M (cstate ((TM.cstep M ^^ k) (TM.cinitial_config M w)))
                                  (cheads ((TM.cstep M ^^ k) (TM.cinitial_config M w))) 0")
          apply auto
        unfolding TM_abbrevs.right_ctape_shift_left apply auto
          apply (cases i)
           apply auto
          apply (metis Suc.IH(6) One_nat_def *)
        unfolding TM_abbrevs.right_ctape_shift_right apply auto
        unfolding Sucth_clist_from_ctl [symmetric]
         apply (metis Suc.IH(6) One_nat_def *)
        unfolding TM_abbrevs.ctape_shift.simps apply simp
        by (metis Suc.IH(6) One_nat_def *)
    next
      case 7
      hence *: "\<And>n. n < k \<Longrightarrow> cheads ((TM.cstep (Abs_TM M') ^^ n)
                (TM.cinitial_config (Abs_TM M') w)) ! 0 \<in> options (alphabet L)" by simp
      have **: "chead (ctapes ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w)) ! 0) \<in>
                options (alphabet L)" using 7 by simp
      have 1: "[0..<TM.TM.tape_count (Abs_TM M')] ! Suc 0 = Suc 0"
        by (metis (no_types, lifting) M'_def One_nat_def TM.at_least_one_tape' add_0 less_Suc_eq_le
            nth_upt simps(1) valid_M' valid_tm_tape_count)
      have 2: "cheads ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w)) ! Suc 0 = None \<Longrightarrow>
               hd (cheads ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w))) #
               tl (tl (cheads ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w)))) =
               cheads ((TM.cstep M ^^ k) (TM.cinitial_config M w))"
        apply (rule nth_equalityI)
         apply auto
        using M'_def valid_tm_tape_count apply fastforce
        apply (subst nth_Cons')
        apply auto
         apply (subst Suc(4) [symmetric])
           apply auto
        using M'_def valid_tm_tape_count apply fastforce
        using * apply fastforce
         apply (metis (no_types, lifting) M'_def Nitpick.size_list_simp(2) hd_conv_nth
            length_ctapes_csteps_eq_tc list.map_sel(1) nat.distinct(1) select_convs(1) valid_M'
            valid_tm_tape_count)
        apply (subst nth_tl)
         apply auto
        apply (subst nth_tl)
         apply auto
        apply (subst Suc(2) [OF _ _ *, simplified])
          apply auto
        using M'_def valid_tm_tape_count apply force
        apply (subst nth_map)
         apply auto
        using M'_def valid_tm_tape_count by force
      have 3: "\<And>y. cheads ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w)) ! Suc 0 = Some y \<Longrightarrow>
               tl (cheads ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w))) =
               cheads ((TM.cstep M ^^ k) (TM.cinitial_config M w))" apply (rule nth_equalityI)
         apply auto
        using M'_def valid_tm_tape_count apply fastforce
        apply (subst nth_tl)
         apply auto
      proof -
        fix i :: nat and y :: 's
        assume a1: "chead (ctapes ((TM.cstep (Abs_TM M') ^^ k)
                    (TM.cinitial_config (Abs_TM M') w)) ! Suc 0) = Some y" and
               a2: "i < TM.TM.tape_count (Abs_TM M') - Suc 0"
        show "chead (ctapes ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w)) ! Suc i) =
              cheads ((TM.cstep M ^^ k) (TM.cinitial_config M w)) ! i"
          apply (cases "i = 0")
           apply auto
           apply (subst Suc(5) [simplified])
             apply auto
          using a1 apply simp
          using * apply simp
          using Suc(2) [of i, OF _ _ *, simplified] a2 apply auto
          unfolding valid_tm_tape_count [OF valid_M'] apply (subst (asm) (2) M'_def)
          by simp
      qed
      show ?case using 7(1) apply auto
        apply (subst (asm) TM.cstep_def)
        apply (subst TM.cstep_def)
        unfolding Suc(1) [OF *, simplified]
        apply (cases "cstate ((TM.cstep M ^^ k) (TM.cinitial_config M w)) \<in> TM.TM.final_states (Abs_TM M')")
         apply auto
           apply (metis * One_nat_def Suc.IH(7) option.distinct(1))
        unfolding valid_tm_final_states [OF valid_M'] apply (subst (asm) (3) M'_def)
          apply simp
         apply (subst (asm) (4) M'_def)
         apply simp
        unfolding TM.cstep_not_final_def Let_def apply auto
        apply (subst (asm) nth_map2)
          apply auto
          apply (metis (no_types, lifting) M'_def Suc_lessI TM.at_least_one_tape TM.next_actions_simps(2)
            diff_Suc_1' gr0_conv_Suc nat.distinct(1) simps(1) valid_M' valid_tm_tape_count)
        using M'_def valid_tm_tape_count apply fastforce
        unfolding TM.ctape_action_def TM.next_actions_def apply (subst nth_map2)
          apply auto
          apply (metis TM.at_least_one_tape TM.next_writes_simps(2) less_numeral_extra(3) list.size(3))
         apply (metis TM.at_least_one_tape TM.next_moves_simps(2) less_numeral_extra(3) list.size(3))
        apply (subst (1 2) nth_zip)
          apply auto
          apply (metis TM.at_least_one_tape TM.next_writes_simps(2) less_numeral_extra(3) list.size(3))
         apply (metis TM.at_least_one_tape TM.next_moves_simps(2) less_not_refl list.size(3))
        apply (subst (asm) (1 2) nth_zip)
          apply auto
          apply (metis (no_types, lifting) M'_def Suc_lessI TM.at_least_one_tape TM.next_writes_simps(2)
            less_numeral_extra(3) old.nat.inject simps(1) valid_M' valid_tm_tape_count)
         apply (metis (lifting) M'_def Suc_lessI TM.at_least_one_tape TM.next_moves_simps(2)
            less_numeral_extra(3) old.nat.inject simps(1) valid_M' valid_tm_tape_count)
        unfolding TM.next_moves_def TM.next_writes_def apply auto
        apply (subst (asm) (1 2) nth_map)
         apply auto
        using M'_def valid_tm_tape_count apply fastforce
        unfolding 1 Suc(1) [OF *, simplified] valid_tm_next_write [OF valid_M'] valid_tm_next_move [OF valid_M']
        apply (subst (asm) (1 4) M'_def)
        apply simp
        apply (cases "cheads ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w)) ! Suc 0 = None")
         apply auto
        unfolding 2 3 apply (cases "TM.TM.next_move M (cstate ((TM.cstep M ^^ k) (TM.cinitial_config M w)))
                                    (cheads ((TM.cstep M ^^ k) (TM.cinitial_config M w))) 0")
           apply auto
        unfolding TM_abbrevs.right_ctape_shift_left TM_abbrevs.ctape_write_def apply auto
           apply (cases i)
            apply auto
           apply (metis * One_nat_def Suc.IH(7) option.distinct(1))
        unfolding TM_abbrevs.right_ctape_shift_right apply auto
        unfolding Sucth_clist_from_ctl [symmetric]
          apply (metis * One_nat_def Suc.IH(7) option.distinct(1))
        unfolding TM_abbrevs.ctape_shift.simps apply auto
         apply (metis * One_nat_def Suc.IH(7) option.distinct(1))
        apply (cases "TM.TM.next_move M (cstate ((TM.cstep M ^^ k) (TM.cinitial_config M w)))
                      (cheads ((TM.cstep M ^^ k) (TM.cinitial_config M w))) 0")
          apply auto
        unfolding TM_abbrevs.right_ctape_shift_left apply auto
          apply (cases i)
           apply auto
          apply (metis * One_nat_def Suc.IH(7) option.distinct(1))
        unfolding TM_abbrevs.right_ctape_shift_right apply auto
        unfolding Sucth_clist_from_ctl [symmetric]
         apply (metis * One_nat_def Suc.IH(7) option.distinct(1))
        unfolding TM_abbrevs.ctape_shift.simps apply simp
        by (metis * One_nat_def Suc.IH(7) option.distinct(1))
    next
      case 8
      hence *: "\<And>n. n < k \<Longrightarrow> cheads ((TM.cstep (Abs_TM M') ^^ n)
                (TM.cinitial_config (Abs_TM M') w)) ! 0 \<in> options (alphabet L)" by simp
      have **: "chead (ctapes ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w)) ! 0) \<in>
                options (alphabet L)" using 8 by simp
      show ?case apply simp
        apply (subst TM.cstep_def)
        apply auto
         apply (rule Suc(8) [OF *, simplified])
        unfolding TM.cstep_not_final_def Let_def apply auto
        apply (subst nth_map2)
          apply auto
         apply (metis TM.at_least_one_tape TM.next_actions_simps(2) less_not_refl list.size(3))
        unfolding TM.ctape_action_def TM.next_actions_def TM.next_writes_def TM.next_moves_def apply simp
        unfolding valid_tm_next_write [OF valid_M'] apply (subst (6) M'_def)
        apply simp
        apply (cases "TM.TM.next_move (Abs_TM M') (cstate ((TM.cstep (Abs_TM M') ^^ k)
                      (TM.cinitial_config (Abs_TM M') w)))
                      (cheads ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w))) 0")
          apply auto
        unfolding TM_abbrevs.left_ctape_shift_left TM_abbrevs.ctape_write_def apply auto
        unfolding Suc(8) [OF *, simplified] apply simp
        unfolding TM_abbrevs.left_ctape_shift_right apply simp
         apply (metis replicated_clist.code)
        unfolding TM_abbrevs.ctape_shift.simps by simp
    next
      case 9
      hence *: "\<And>n. n < k \<Longrightarrow> cheads ((TM.cstep (Abs_TM M') ^^ n)
                (TM.cinitial_config (Abs_TM M') w)) ! 0 \<in> options (alphabet L)" by simp
      have **: "chead (ctapes ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w)) ! 0) \<in>
                options (alphabet L)" using 9 by simp
      show ?case apply simp
        apply (subst TM.cstep_def)
        apply auto
        using Suc(9) [OF *, simplified] apply auto
        unfolding TM.cstep_not_final_def Let_def apply auto
        apply (subst (asm) nth_map2)
          apply auto
        apply (metis One_nat_def TM.at_least_one_tape' TM.next_actions_simps(2) lessI less_Suc_eq_le list.size(3)
            not_less_eq_eq)
        unfolding TM.ctape_action_def TM.next_actions_def TM.next_writes_def TM.next_moves_def apply auto
        unfolding valid_tm_next_write [OF valid_M'] apply (subst (asm) (9) M'_def)
        apply simp
        unfolding TM_abbrevs.ctape_write_def
        apply (cases "TM.TM.next_move (Abs_TM M') (cstate ((TM.cstep (Abs_TM M') ^^ k)
                      (TM.cinitial_config (Abs_TM M') w)))
                      (cheads ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w))) 0")
          apply auto
          apply (drule subsetD)
           apply auto
          apply (cases "cleft (ctapes ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w)) ! 0)")
          apply auto
        unfolding TM_abbrevs.ctape_shift.simps apply auto
             apply (metis (no_types, lifting) * Suc.IH(8) clist.inject option.distinct(1) replicated_clist.code
            set_clist_replicated_singleton singletonD)
            apply (metis (no_types, lifting) * Suc.IH(8) clist.inject option.distinct(1) replicated_clist.code)
           apply (cases "ctapes ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w)) ! 0")
        unfolding ctape.set apply auto
          apply (drule subsetD)
           apply auto
          apply (cases "ctapes ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w)) ! 0")
          apply (cases "cright (ctapes ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w)) ! 0)")
        unfolding ctape.set apply auto
        unfolding TM_abbrevs.ctape_shift.simps apply auto
         apply (drule subsetD)
          apply auto
        using * Suc.IH(8) apply fastforce
        apply (drule subsetD)
         apply auto
        apply (cases "ctapes ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w)) ! 0")
        by simp
    }
  qed
  have f21: "state (TM.steps (Abs_TM M') k (TM.initial_config (Abs_TM M') w)) =
             state (TM.steps M k (TM.initial_config M w))" and
       f22: "tape.set_tape (tapes (TM.steps (Abs_TM M') k (TM.initial_config (Abs_TM M') w)) ! 0) \<subseteq> set w"
    if "\<And>n. n < k \<Longrightarrow> heads (TM.steps (Abs_TM M') n (TM.initial_config (Abs_TM M') w)) ! 0 \<in>
        options (alphabet L)" for k :: nat and w :: "'s list"
    using f11 that unfolding cotm_heads_steps_congruence cotm_steps_congruences(1) apply simp
    apply auto
    apply (rule f19 [unfolded cotm_heads_steps_congruence, OF that, of k, simplified,
        unfolded cotm_steps_congruences(2), THEN subsetD])
    apply (subst nth_map)
     apply auto
     apply (metis TM.at_least_one_tape TM.run_tapes_len list.size(3) less_not_refl)
    apply (cases "tapes ((TM.step (Abs_TM M') ^^ k) (TM.initial_config (Abs_TM M') w)) ! 0")
    apply auto
    by (simp_all add: set_clist_prepend_list)
  have f22': "tape.set_tape (tapes (TM.steps (Abs_TM M') k (TM.initial_config (Abs_TM M') w)) ! 0) \<subseteq> set w"
    for w :: "'s list" and k :: nat
  proof -
    have 1: "set_tape (tapes ((TM.step (Abs_TM M') ^^ (Suc n)) (TM.initial_config (Abs_TM M') w)) ! 0) \<subseteq>
             set_tape (tapes ((TM.step (Abs_TM M') ^^ n) (TM.initial_config (Abs_TM M') w)) ! 0)" for n :: nat
      apply simp
      apply (subst TM.step_def)
      apply auto
      apply (subst (asm) nth_map2)
        apply auto
        apply (metis TM.at_least_one_tape TM.next_actions_simps(2) less_not_refl list.size(3))
       apply (metis TM.at_least_one_tape TM.run_tapes_len less_not_refl list.size(3))
      unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_writes_def TM.next_moves_def apply auto
      unfolding TM_abbrevs.tape_shift_set valid_tm_next_write [OF valid_M'] apply (subst (asm) (4) M'_def)
      apply auto
      unfolding TM_abbrevs.tape_write_def apply auto
      by (simp_all add: tape.set_sel(1, 3))
    show "set_tape (tapes ((TM.step (Abs_TM M') ^^ k) (TM.initial_config (Abs_TM M') w)) ! 0) \<subseteq> set w"
    proof (induction k)
      case 0
      then show ?case apply simp unfolding TM.initial_config_def TM_abbrevs.input_tape_def apply auto
        by (metis list.set_sel(2))
    next
      case (Suc k)
      then show ?case using 1 [of k] by order
    qed
  qed
  show "\<exists>M::('q, 's) TM_decider. alphabet L \<subseteq> TM.TM.symbols M \<and>
        (\<forall>w\<in>(alphabet L)*. TM_decider.decides_word M L w) \<and>
        (\<forall>w. TM.time_bounded_word M T w)"
  proof (rule exI [where x="Abs_TM M'"], auto)
    show "\<And>s. s \<in> alphabet L \<Longrightarrow> s \<in> TM.symbols (Abs_TM M')"
      unfolding valid_tm_symbols [OF valid_M'] unfolding M'_def using a3 by auto
    show "TM_decider.decides_word (Abs_TM M') L w" if "set w \<subseteq> alphabet L" for w :: "'s list"
    proof (unfold TM_decider.decides_def, auto)
      have 1: "heads (TM.steps (Abs_TM M') n (TM.initial_config (Abs_TM M') w)) ! 0 \<in>
               options (alphabet L)" for n :: nat using f22' [of n w] that
        apply (cases "tapes ((TM.step (Abs_TM M') ^^ n) (TM.initial_config (Abs_TM M') w)) ! 0")
        apply auto
        apply (cases "heads ((TM.step (Abs_TM M') ^^ n) (TM.initial_config (Abs_TM M') w)) ! 0")
         apply auto
        by (metis (no_types, lifting) M'_def Some_options_iff TM.run_tapes_len nth_map order_trans
            set_options_eq simps(1) tape.sel(2) valid_M' valid_tm_tape_count zero_less_Suc)
      have 2: "state (TM.steps (Abs_TM M') n (TM.initial_config (Abs_TM M') w)) =
               state (TM.steps M n (TM.initial_config M w))" for n :: nat
        using f21 [of n w] 1 by blast
      show "w \<in>\<^sub>L L \<Longrightarrow> TM_decider.accepts (Abs_TM M') w"
        apply (drule a1 [THEN bspec, of w, simplified, OF that, unfolded TM_decider.decides_def,
            THEN conjunct1, THEN iffD1])
        unfolding TM_decider.accepts_def
        unfolding TM.compute_def TM.compute_config_def TM_decider.acc_def apply auto
        unfolding valid_tm_final_states [OF valid_M'] valid_tm_label [OF valid_M']
        unfolding TM.is_final_def 2 valid_tm_final_states [OF valid_M'] unfolding M'_def by simp_all
      thus "TM_decider.rejects (Abs_TM M') w \<Longrightarrow> w \<in>\<^sub>L L \<Longrightarrow> False"
        using TM_decider.acc_not_rej by blast
      show "w \<notin> words L \<Longrightarrow> TM_decider.rejects (Abs_TM M') w"
        apply (drule a1 [THEN bspec, of w, simplified, OF that, unfolded TM_decider.decides_def,
            THEN conjunct2, THEN iffD1])
        unfolding TM_decider.rejects_def
        unfolding TM.compute_def TM.compute_config_def TM_decider.rej_def apply auto
        unfolding valid_tm_final_states [OF valid_M'] valid_tm_label [OF valid_M']
        unfolding TM.is_final_def 2 valid_tm_final_states [OF valid_M'] unfolding M'_def by simp_all
      thus "TM_decider.accepts (Abs_TM M') w \<Longrightarrow> w \<in>\<^sub>L L"
        using TM_decider.acc_not_rej by blast
    qed
    show "TM.time_bounded_word (Abs_TM M') T w"
      for w :: "'s list"
    proof (cases "set w \<subseteq> alphabet L")
      case True
      have 1: "heads (TM.steps (Abs_TM M') n (TM.initial_config (Abs_TM M') w)) ! 0 \<in>
               options (alphabet L)" for n :: nat using f22' [of n w] True
        apply (cases "tapes ((TM.step (Abs_TM M') ^^ n) (TM.initial_config (Abs_TM M') w)) ! 0")
        apply auto
        apply (cases "heads ((TM.step (Abs_TM M') ^^ n) (TM.initial_config (Abs_TM M') w)) ! 0")
         apply auto
        by (metis (no_types, lifting) M'_def Some_options_iff TM.run_tapes_len nth_map order_trans
            set_options_eq simps(1) tape.sel(2) valid_M' valid_tm_tape_count zero_less_Suc)
      have 2: "state (TM.steps (Abs_TM M') n (TM.initial_config (Abs_TM M') w)) =
               state (TM.steps M n (TM.initial_config M w))" for n :: nat
        using f21 [of n w] 1 by blast
      show ?thesis unfolding TM.time_bounded_word_def TM.run_def TM.is_final_def 2
          valid_tm_final_states [OF valid_M'] apply (subst M'_def)
        apply simp
        using a2 [THEN bspec, of w, simplified, OF True, unfolded TM.time_bounded_word_def
            TM.is_final_def TM.run_def] .
    next
      case False
      then show ?thesis
      proof (cases "\<forall>n<T (length w). heads (TM.steps (Abs_TM M') n (TM.initial_config (Abs_TM M') w)) ! 0 \<in>
                    options (alphabet L)")
        case [THEN spec, THEN mp]: True
        obtain s :: 's where s_in_L: "s \<in> alphabet L" using \<open>alphabet L \<noteq> {}\<close> by blast
        define w' :: "'s list" where "w' \<equiv> map (\<lambda>x. if x \<in> alphabet L then x else s) w"
        have 1: "set w' \<subseteq> alphabet L"
          unfolding w'_def apply auto
          by (rule s_in_L)
        have 2: "length w' = length w" unfolding w'_def by simp
        show ?thesis unfolding TM.time_bounded_word_def TM.is_final_def TM.run_def
          f21 [OF True, of "T (length w)", simplified] valid_tm_final_states [OF valid_M'] apply (subst M'_def)
          apply simp
        proof (cases "T (length w) = 0")
          case True
          show "state ((TM.step M ^^ T (length w)) (TM.initial_config M w)) \<in> TM.TM.final_states M"
            unfolding True using a2 [THEN bspec, of w', simplified, OF 1, unfolded TM.time_bounded_word_def
                TM.is_final_def TM.run_def True [folded 2]] apply auto
            unfolding TM.initial_config_def by simp
        next
          case [simplified]: False
          have 3: "n < T (length w) \<Longrightarrow> heads (TM.steps (Abs_TM M') n (TM.initial_config (Abs_TM M') w)) =
                   heads (TM.steps (Abs_TM M') n (TM.initial_config (Abs_TM M') w'))" and
               4: "state (TM.steps (Abs_TM M') n (TM.initial_config (Abs_TM M') w)) =
                   state (TM.steps (Abs_TM M') n (TM.initial_config (Abs_TM M') w'))" and
               5: "\<And>i. i > 0 \<Longrightarrow> i < TM.tape_count (Abs_TM M') \<Longrightarrow> n < T (length w) \<Longrightarrow>
                   tapes (TM.steps (Abs_TM M') n (TM.initial_config (Abs_TM M') w)) ! i =
                   tapes (TM.steps (Abs_TM M') n (TM.initial_config (Abs_TM M') w')) ! i" and
               6: "n < T (length w) \<Longrightarrow> tape.left (tapes (TM.steps (Abs_TM M') n
                   (TM.initial_config (Abs_TM M') w)) ! 0) =
                   tape.left (tapes (TM.steps (Abs_TM M') n (TM.initial_config (Abs_TM M') w')) ! 0)" and
               7: "n < T (length w) \<Longrightarrow>
                   \<exists>l r. tape.right (tapes (TM.steps (Abs_TM M') n (TM.initial_config (Abs_TM M') w)) ! 0) =
                   r @ (drop l (map Some w)) \<and>
                   tape.right (tapes (TM.steps (Abs_TM M') n (TM.initial_config (Abs_TM M') w')) ! 0) =
                   r @ (drop l (map Some w'))"
                  if "n \<le> T (length w)" for n :: nat using that
          proof (induction n)
            case 0
            {
              case 1
              then show ?case using True [OF False] apply simp
                unfolding TM.initial_config_def TM_abbrevs.input_tape_def apply auto
                unfolding w'_def apply auto
                unfolding hd_map by simp
            next
              case 2
              then show ?case apply simp
                unfolding TM.initial_config_def valid_tm_initial_state [OF valid_M'] by simp
            next
              case 3
              then show ?case apply simp
                unfolding TM.initial_config_def TM_abbrevs.input_tape_def by simp
            next
              case 4
              then show ?case apply simp
                unfolding TM.initial_config_def TM_abbrevs.input_tape_def by simp
            next
              case 5
              then show ?case apply simp
                unfolding TM.initial_config_def TM_abbrevs.input_tape_def apply auto
                  apply (rule exI [where x=1])
                  apply simp
                unfolding drop_Suc apply simp
                unfolding map_tl apply standard
                 apply (rule exI [where x=1])
                 apply simp
                unfolding drop_Suc apply simp
                apply (rule exI [where x=1])
                apply (rule exI [where x="[]"])
                apply auto
                unfolding drop_Suc by simp_all
            }
          next
            case (Suc n)
            {
              case 1
              hence *: "n \<le> T (length w)" by simp
              have **: "n < T (length w)" using 1 by simp
              show ?case using True [OF 1(1)] 1 apply simp
                apply (subst (1 2) TM.step_def)
                apply (subst (asm) TM.step_def)
                apply auto
                unfolding Suc(1) [OF ** *] Suc(2) [OF *] apply auto
                apply (rule nth_equalityI)
                 apply auto
                 apply (simp add: TM.run_tapes_len)
                apply (subst nth_map)
                 apply auto
                 apply (metis TM.run_tapes_len)
                apply (subst (asm) nth_map)
                 apply auto
                apply (subst (asm) nth_zip)
                  apply auto
                apply (subst nth_zip)
                  apply auto
                 apply (simp add: TM.run_tapes_len)
                unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_writes_def TM.next_moves_def
                apply auto
              proof -
                fix i :: nat
                assume a1: "i < TM.TM.tape_count (Abs_TM M')" and
                       a2: "tape.head (TM_abbrevs.tape_shift (TM.TM.next_move (Abs_TM M')
                            (state ((TM.step (Abs_TM M') ^^ n) (TM.initial_config (Abs_TM M') w')))
                            (heads ((TM.step (Abs_TM M') ^^ n) (TM.initial_config (Abs_TM M') w'))) 0)
                            (TM_abbrevs.tape_write (TM.TM.next_write (Abs_TM M')
                            (state ((TM.step (Abs_TM M') ^^ n) (TM.initial_config (Abs_TM M') w')))
                            (heads ((TM.step (Abs_TM M') ^^ n) (TM.initial_config (Abs_TM M') w'))) 0)
                            (tapes ((TM.step (Abs_TM M') ^^ n) (TM.initial_config (Abs_TM M') w)) ! 0)))
                            \<in> options (alphabet L)"
                show "tape.head (TM_abbrevs.tape_shift (TM.TM.next_move (Abs_TM M')
                      (state ((TM.step (Abs_TM M') ^^ n) (TM.initial_config (Abs_TM M') w')))
                      (heads ((TM.step (Abs_TM M') ^^ n) (TM.initial_config (Abs_TM M') w'))) i)
                      (TM_abbrevs.tape_write (TM.TM.next_write (Abs_TM M') (state ((TM.step (Abs_TM M') ^^ n)
                      (TM.initial_config (Abs_TM M') w'))) (heads ((TM.step (Abs_TM M') ^^ n)
                      (TM.initial_config (Abs_TM M') w'))) i)
                      (tapes ((TM.step (Abs_TM M') ^^ n) (TM.initial_config (Abs_TM M') w)) ! i))) =
                      tape.head (TM_abbrevs.tape_shift (TM.TM.next_move (Abs_TM M')
                      (state ((TM.step (Abs_TM M') ^^ n) (TM.initial_config (Abs_TM M') w')))
                      (heads ((TM.step (Abs_TM M') ^^ n) (TM.initial_config (Abs_TM M') w'))) i)
                      (TM_abbrevs.tape_write (TM.TM.next_write (Abs_TM M') (state ((TM.step (Abs_TM M') ^^ n)
                      (TM.initial_config (Abs_TM M') w')))
                      (heads ((TM.step (Abs_TM M') ^^ n) (TM.initial_config (Abs_TM M') w'))) i)
                      (tapes ((TM.step (Abs_TM M') ^^ n) (TM.initial_config (Abs_TM M') w')) ! i)))"
                  apply (cases "i = 0")
                   using a2 apply auto
                   apply (cases "TM.TM.next_move (Abs_TM M') (state ((TM.step (Abs_TM M') ^^ n)
                                 (TM.initial_config (Abs_TM M') w')))
                                 (heads ((TM.step (Abs_TM M') ^^ n) (TM.initial_config (Abs_TM M') w'))) 0")
                     apply auto
                  unfolding TM_abbrevs.tape_write_def
                     apply (cases "tape.left (tapes ((TM.step (Abs_TM M') ^^ n)
                                   (TM.initial_config (Abs_TM M') w)) ! 0)")
                  using Suc(4) [OF ** *] apply auto
                  unfolding TM_abbrevs.tape_shift.simps apply auto
                  using Suc(5) [OF ** *] apply auto
                proof -
                  fix l :: nat and r :: "'s option list"
                  assume "tape.head (TM_abbrevs.tape_shift Shift_Right (Tape (tape.left (tapes
                          ((TM.step (Abs_TM M') ^^ n) (TM.initial_config (Abs_TM M') w')) ! 0))
                          (TM.TM.next_write (Abs_TM M') (state ((TM.step (Abs_TM M') ^^ n)
                          (TM.initial_config (Abs_TM M') w')))
                          (heads ((TM.step (Abs_TM M') ^^ n) (TM.initial_config (Abs_TM M') w'))) 0)
                          (r @ drop l (map Some w)))) \<in> options (alphabet L)"
                  thus "tape.head (TM_abbrevs.tape_shift Shift_Right
                        (Tape (tape.left (tapes ((TM.step (Abs_TM M') ^^ n)
                        (TM.initial_config (Abs_TM M') w')) ! 0))
                        (TM.TM.next_write (Abs_TM M') (state ((TM.step (Abs_TM M') ^^ n)
                        (TM.initial_config (Abs_TM M') w')))
                        (heads ((TM.step (Abs_TM M') ^^ n) (TM.initial_config (Abs_TM M') w'))) 0)
                        (r @ drop l (map Some w)))) =
                        tape.head (TM_abbrevs.tape_shift Shift_Right
                        (Tape (tape.left (tapes ((TM.step (Abs_TM M') ^^ n)
                        (TM.initial_config (Abs_TM M') w')) ! 0))
                        (TM.TM.next_write (Abs_TM M') (state ((TM.step (Abs_TM M') ^^ n)
                        (TM.initial_config (Abs_TM M') w'))) (heads ((TM.step (Abs_TM M') ^^ n)
                        (TM.initial_config (Abs_TM M') w'))) 0) (r @ drop l (map Some w'))))"
                    apply (cases r)
                     apply auto
                     apply (cases "drop l (map Some w)")
                    using 2 apply auto
                    unfolding TM_abbrevs.tape_shift.simps apply auto
                    apply (subst Shift_Right_is_right_not_empty)
                     apply auto
                    unfolding w'_def apply auto
                    apply (subst hd_drop_conv_nth)
                     apply auto
                    using linorder_not_less apply fastforce
                    apply (subst nth_map)
                     apply auto
                    using linorder_not_less apply fastforce
                     apply (metis drop_eq_Nil drop_map hd_drop_conv_nth length_map linorder_not_less
                        list.distinct(1) list.map_sel(1) list.sel(1))
                    by (metis Some_options_iff drop_eq_Nil2 drop_map hd_drop_conv_nth length_map
                        linorder_le_less_linear list.discI list.map_sel(1) list.sel(1))
                next
                  fix l :: nat and r :: "'s option list"
                  assume a3: "0 < i" and
                         a4: "tape.head (TM_abbrevs.tape_shift (TM.TM.next_move (Abs_TM M')
                              (state ((TM.step (Abs_TM M') ^^ n) (TM.initial_config (Abs_TM M') w')))
                              (heads ((TM.step (Abs_TM M') ^^ n) (TM.initial_config (Abs_TM M') w'))) 0)
                              (Tape (tape.left (tapes ((TM.step (Abs_TM M') ^^ n)
                              (TM.initial_config (Abs_TM M') w')) ! 0))
                              (TM.TM.next_write (Abs_TM M') (state ((TM.step (Abs_TM M') ^^ n)
                              (TM.initial_config (Abs_TM M') w')))
                              (heads ((TM.step (Abs_TM M') ^^ n) (TM.initial_config (Abs_TM M') w'))) 0)
                              (r @ drop l (map Some w)))) \<in> options (alphabet L)"
                  show "tape.head (TM_abbrevs.tape_shift (TM.TM.next_move (Abs_TM M')
                        (state ((TM.step (Abs_TM M') ^^ n) (TM.initial_config (Abs_TM M') w')))
                        (heads ((TM.step (Abs_TM M') ^^ n) (TM.initial_config (Abs_TM M') w'))) i)
                        (Tape (tape.left (tapes ((TM.step (Abs_TM M') ^^ n)
                        (TM.initial_config (Abs_TM M') w)) ! i)) (TM.TM.next_write (Abs_TM M')
                        (state ((TM.step (Abs_TM M') ^^ n) (TM.initial_config (Abs_TM M') w')))
                        (heads ((TM.step (Abs_TM M') ^^ n) (TM.initial_config (Abs_TM M') w'))) i)
                        (tape.right (tapes ((TM.step (Abs_TM M') ^^ n)
                        (TM.initial_config (Abs_TM M') w)) ! i)))) =
                        tape.head (TM_abbrevs.tape_shift (TM.TM.next_move (Abs_TM M')
                        (state ((TM.step (Abs_TM M') ^^ n) (TM.initial_config (Abs_TM M') w')))
                        (heads ((TM.step (Abs_TM M') ^^ n) (TM.initial_config (Abs_TM M') w'))) i)
                        (Tape (tape.left (tapes ((TM.step (Abs_TM M') ^^ n)
                        (TM.initial_config (Abs_TM M') w')) ! i))
                        (TM.TM.next_write (Abs_TM M') (state ((TM.step (Abs_TM M') ^^ n)
                        (TM.initial_config (Abs_TM M') w')))
                        (heads ((TM.step (Abs_TM M') ^^ n) (TM.initial_config (Abs_TM M') w'))) i)
                        (tape.right (tapes ((TM.step (Abs_TM M') ^^ n)
                        (TM.initial_config (Abs_TM M') w')) ! i))))"
                    unfolding Suc(3) [OF a3 a1 ** *] by auto
                qed
              qed
            next
              case 2
              hence *: "n \<le> T (length w)" by simp
              have **: "n < T (length w)" using 2 by simp
              show ?case apply simp
                apply (subst (1 2) TM.step_def)
                apply auto
                unfolding Suc(2) [OF *] apply auto
                unfolding Suc(1) [OF ** *] ..
            next
              case 3
              hence *: "n \<le> T (length w)" by simp
              have **: "n < T (length w)" using 3 by simp
              have 1: "[0..<TM.TM.tape_count (Abs_TM M')] ! i = i" using 3(2) by simp
              show ?case apply simp
                apply (subst (1 2) TM.step_def)
                unfolding Suc(2) [OF *] Suc(1) [OF ** *] apply auto
                 apply (rule Suc(3) [OF 3(1, 2) ** *])
                apply (subst (1 2) nth_map2)
                    apply (simp add: "3.prems"(2) TM.next_actions_simps(2))
                   apply (simp add: "3.prems"(2) TM.run_tapes_len)
                  apply (simp add: "3.prems"(2) TM.next_actions_simps(2))
                 apply (simp add: "3.prems"(2) TM.run_tapes_len)
                unfolding TM.next_actions_def TM_abbrevs.tape_action_def TM.next_writes_def TM.next_moves_def
                apply (subst (1 2 3 4) nth_zip)
                  apply auto
                using "3.prems"(2) apply fastforce
                using "3.prems"(2) apply fastforce
                using "3.prems"(2) apply fastforce
                using "3.prems"(2) apply fastforce
                apply (subst (1 2 3 4) nth_map)
                 apply auto
                using "3.prems"(2) apply fastforce
                unfolding 1 Suc(1) [OF ** *] Suc(2) [OF *]
                apply (cases "TM.TM.next_move (Abs_TM M') (state ((TM.step (Abs_TM M') ^^ n)
                              (TM.initial_config (Abs_TM M') w')))
                              (heads ((TM.step (Abs_TM M') ^^ n) (TM.initial_config (Abs_TM M') w'))) i")
                  apply auto
                unfolding Suc(3) [OF 3(1, 2) ** *] by simp_all
            next
              case 4
              hence *: "n \<le> T (length w)" by simp
              have **: "n < T (length w)" using 4 by simp
              show ?case apply simp
                apply (subst (1 2) TM.step_def)
                apply auto
                unfolding Suc(2) [OF *] apply auto
                 apply (rule Suc(4) [OF ** *])
                apply (subst (1 2) nth_map2)
                    apply auto
                    apply (metis One_nat_def TM.at_least_one_tape' TM.next_actions_simps(2) le_refl list.size(3)
                    not_less_eq_eq)
                   apply (metis (no_types, lifting) M'_def TM.run_tapes_len list.size(3) nat.distinct(1)
                    select_convs(1) valid_M' valid_tm_tape_count)
                  apply (metis One_nat_def TM.at_least_one_tape' TM.next_actions_simps(2) le_refl list.size(3)
                    not_less_eq_eq)
                 apply (metis TM.run_tapes_len list.size(3) TM.at_least_one_tape not_less_eq_eq lessI
                    linorder_not_less)
                unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_writes_def TM.next_moves_def
                apply auto
                unfolding Suc(1) [OF ** *]
                apply (cases "TM.TM.next_move (Abs_TM M') (state ((TM.step (Abs_TM M') ^^ n)
                              (TM.initial_config (Abs_TM M') w')))
                              (heads ((TM.step (Abs_TM M') ^^ n) (TM.initial_config (Abs_TM M') w'))) 0")
                  apply auto
                unfolding Suc(4) [OF ** *] apply auto
                unfolding TM_abbrevs.tape_shift.simps apply auto
                unfolding TM_abbrevs.tape_write_def apply auto
                by (rule Suc(4) [OF ** *])
            next
              case 5
              hence *: "n \<le> T (length w)" by simp
              have **: "n < T (length w)" using 5 by simp
              note Suc(5) [OF ** *]
              then obtain l :: nat and r :: "'s option list" where
                lr_w: "tape.right (tapes ((TM.step (Abs_TM M') ^^ n) (TM.initial_config (Abs_TM M') w)) ! 0) =
                       r @ drop l (map Some w)" and
                lr_w': "tape.right (tapes ((TM.step (Abs_TM M') ^^ n) (TM.initial_config (Abs_TM M') w')) ! 0) =
                        r @ drop l (map Some w')" by blast
              show ?case apply simp
                apply (subst (1 2) TM.step_def)
                apply auto
                unfolding Suc(2) [OF *] apply auto
                 apply (rule Suc(5) [OF ** *])
                apply (subst (1 2) nth_map2)
                    apply auto
                    apply (metis (no_types, lifting) M'_def TM.next_actions_simps(2) list.size(3)
                    nat.distinct(1) select_convs(1) valid_M' valid_tm_tape_count)
                   apply (metis TM.run_tapes_len list.size(3) One_nat_def linorder_not_less
                    TM.at_least_one_tape' lessI)
                  apply (metis One_nat_def TM.at_least_one_tape' TM.next_actions_simps(2) le_refl list.size(3)
                    not_less_eq_eq) 
                 apply (metis list.size(3) TM.at_least_one_tape TM.init_conf_len TM.steps_l_tps
                    bot_nat_0.not_eq_extremum)
                unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_writes_def TM.next_moves_def
                apply auto
                unfolding Suc(1) [OF ** *]
                apply (cases "TM.TM.next_move (Abs_TM M') (state ((TM.step (Abs_TM M') ^^ n)
                              (TM.initial_config (Abs_TM M') w')))
                              (heads ((TM.step (Abs_TM M') ^^ n) (TM.initial_config (Abs_TM M') w'))) 0")
                  apply auto
                unfolding TM_abbrevs.tape_write_def apply auto
                  apply (rule exI [where x=l])
                unfolding lr_w lr_w' apply auto
                 apply (cases r)
                 apply (rule exI [where x="Suc l"])
                 apply (rule exI [where x=r])
                  apply auto
                unfolding drop_Suc tl_drop apply simp_all
                unfolding TM_abbrevs.tape_shift.simps by auto
            }
          qed
          have 8: "\<And>x. x < T (length w) \<Longrightarrow>
                   heads ((TM.step (Abs_TM M') ^^ x) (TM.initial_config (Abs_TM M') w')) ! 0 \<in>
                   options (alphabet L)" using True 3 by simp
          show "state ((TM.step M ^^ T (length w)) (TM.initial_config M w)) \<in> TM.TM.final_states M"
            unfolding f21 [OF True, of "T (length w)", simplified, symmetric] 4 [OF Nat.le_refl]
            unfolding f21 [OF 8, of "T (length w)", simplified] using a2 [THEN bspec, of w',
                simplified, OF 1, unfolded TM.time_bounded_word_def TM.is_final_def TM.run_def 2] .
        qed                 
      next
        case [simplified]: False
        then obtain n :: nat where n_bound: "n < T (length w)" and
          n_steps: "heads ((TM.step (Abs_TM M') ^^ n) (TM.initial_config (Abs_TM M') w)) ! 0 \<notin>
                    options (alphabet L)" by blast
        show ?thesis apply (rule TM.time_bounded_word_mono [where t="\<lambda>_. Suc n"])
          using n_bound apply auto
          unfolding TM.time_bounded_word_def TM.is_final_def TM.run_def apply simp
          apply (subst TM.step_def)
          apply auto
          unfolding valid_tm_next_state [OF valid_M'] apply (subst M'_def)
          using n_steps apply auto
          unfolding valid_tm_final_states [OF valid_M'] apply (subst M'_def)
          apply simp
          by (rule fs_final)
      qed
    qed
  qed
qed

lemma in_dtime_tb_words_language_alphabet_iff: "L \<in> typed_DTIME TYPE('q) T \<longleftrightarrow>
                  (\<exists>M::('q, 's) TM_decider.
                  TM_decider.decides M L \<and> (\<forall>w\<in>(alphabet L)*. TM.time_bounded_word M T w))"
  unfolding typed_DTIME_def using in_dtime_tb_words_language_alphabet_iff_helper [of L T] by auto

(* Use this definition to prove decidability of a language *)
lemma typed_DTIME_altdef: "typed_DTIME TYPE('q) T \<equiv> {L. \<exists>M::('q, 's) TM_decider.
                           TM_decider.decides M L \<and> (\<forall>w\<in>(alphabet L)*. TM.time_bounded_word M T w)}"
  apply (rule eq_reflection)
  using in_dtime_tb_words_language_alphabet_iff [of _ T] by auto

(* This is the original definition of typed_DTIME (until at least ~ May 2024) - turns out,
   it's equivalent to the new one! *)
(* Use this definition to obtain a TM that decides the language *)
lemma typed_DTIME_altdef2: "typed_DTIME TYPE('q) T \<equiv> {L. \<exists>M::('q, 's) TM_decider.
                            TM_decider.decides M L \<and> TM.time_bounded M T}"
  apply (rule eq_reflection)
  unfolding typed_DTIME_altdef apply auto
  using in_dtime_tb_words_language_alphabet_iff_helper [of _ T] by blast

lemma ext_DTIME: "L \<in> DTIME T \<Longrightarrow> ext_lang L \<in> DTIME T"
  unfolding typed_DTIME_def apply auto
  by (smt (verit, del_insts) time_bounded_symbols_ext tm_ext_decides)

lemma in_dtimeI[intro]:
  fixes M :: "('q, 's) TM_decider"
  assumes "alphabet L \<subseteq> TM.\<Sigma> M"
    and "TM_decider.decides M L"
    and "TM.time_bounded M T"
  shows "L \<in> typed_DTIME TYPE('q) T"
  unfolding typed_DTIME_def using assms by blast

lemma in_pdtimeI[intro]:
  fixes M :: "('q, 's) PTM_decider"
  assumes "alphabet L \<subseteq> TM.\<Sigma> (valid_PTM M)"
    and "TM_decider.decides (valid_PTM M) L"
    and "TM.time_bounded (valid_PTM M) T"
  shows "L \<in> typed_PDTIME TYPE('q) T"
  unfolding typed_PDTIME_def using assms by blast

lemma in_dtimeI' [intro]:
  fixes M :: "('q, 's) TM_decider"
  assumes "alphabet L \<subseteq> TM.\<Sigma> M"
    and "TM_decider.decides M L"
    and "TM.time_bounded_symbols M T"
  shows "L \<in> typed_DTIME TYPE('q) T"
  unfolding typed_DTIME_def using assms by blast

lemma in_dtimeI'':
  fixes M :: "('q, 's) TM_decider"
  assumes "alphabet L \<subseteq> TM.\<Sigma> M"
    and "TM_decider.decides M L"
    and "\<And>w. set w \<subseteq> alphabet L \<Longrightarrow> TM.time_bounded_word M T w"
  shows "L \<in> typed_DTIME TYPE('q) T"
  unfolding typed_DTIME_altdef using assms by blast

lemma in_pdtimeI' [intro]:
  fixes M :: "('q, 's) PTM_decider"
  assumes "alphabet L \<subseteq> TM.\<Sigma> (valid_PTM M)"
    and "TM_decider.decides (valid_PTM M) L"
    and "TM.time_bounded_symbols (valid_PTM M) T"
  shows "L \<in> typed_PDTIME TYPE('q) T"
  unfolding typed_PDTIME_def using assms by blast

lemma in_dtimeE[elim]:
  assumes "L \<in> typed_DTIME TYPE('q) T"
  obtains M :: "('q, 's) TM_decider"
  where "alphabet L \<subseteq> TM.symbols M"
    and "TM_decider.decides M L"
    and "TM.time_bounded_symbols M T"
  using assms unfolding typed_DTIME_def by blast

lemma in_dtimeE'[elim]:
  assumes "L \<in> typed_DTIME TYPE('q) T"
  obtains M :: "('q, 's) TM_decider"
  where "alphabet L \<subseteq> TM.symbols M"
    and "TM_decider.decides M L"
    and "TM.time_bounded M T"
  using assms unfolding typed_DTIME_altdef2 by blast

lemma in_pdtimeE[elim]:
  assumes "L \<in> typed_PDTIME TYPE('q) T"
  obtains M :: "('q, 's) PTM_decider"
  where "alphabet L \<subseteq> TM.symbols (valid_PTM M)"
    and "TM_decider.decides (valid_PTM M) L"
    and "TM.time_bounded_symbols (valid_PTM M) T"
  using assms unfolding typed_PDTIME_def by blast

lemma in_dtimeD[dest]:
  fixes L :: "'s lang"
  assumes "L \<in> typed_DTIME TYPE('q) T"
  shows "\<exists>M::('q, 's) TM_decider. TM_decider.decides M L \<and> TM.time_bounded_symbols M T"
  using assms unfolding typed_DTIME_def ..

lemma in_dtimeD'[dest]:
  fixes L :: "'s lang"
  assumes "L \<in> typed_DTIME TYPE('q) T"
  shows "\<exists>M::('q, 's) TM_decider. TM_decider.decides M L \<and> TM.time_bounded M T"
  using assms unfolding typed_DTIME_altdef2 ..

corollary in_dtime_mono[dest]:
  fixes T t
  assumes "L \<in> typed_DTIME TYPE('q) t"
    and "\<And>n. t n \<le> T n"
  shows "L \<in> typed_DTIME TYPE('q) T"
  using assms unfolding typed_DTIME_def
  using TM.time_bounded_word_mono by blast

corollary in_pdtime_mono[dest]:
  fixes T t
  assumes "L \<in> typed_PDTIME TYPE('q) t"
    and "\<And>n. t n \<le> T n"
  shows "L \<in> typed_PDTIME TYPE('q) T"
  using assms unfolding typed_PDTIME_def
  using TM.time_bounded_word_mono by blast

lemma in_dtime_min:
  fixes T\<^sub>1 T\<^sub>2 :: "nat \<Rightarrow> nat" and L :: "'s lang"
  assumes "L \<in> typed_DTIME TYPE('q) (\<lambda>n. min (T\<^sub>1 n) (T\<^sub>2 n))"
  shows in_dtime_minD1: "L \<in> typed_DTIME TYPE('q) T\<^sub>1" and in_dtime_minD2: "L \<in> typed_DTIME TYPE('q) T\<^sub>2"
proof -
  show "L \<in> typed_DTIME TYPE('q) T\<^sub>1"
    apply (rule in_dtime_mono)
     apply (rule assms)
    by simp
  show "L \<in> typed_DTIME TYPE('q) T\<^sub>2"
    apply (rule in_dtime_mono)
     apply (rule assms)
    by simp
qed

lemma PDTIME_in_DTIME: "L \<in> typed_PDTIME TYPE('q) T \<Longrightarrow> L \<in> typed_DTIME TYPE('q) T"
  unfolding typed_PDTIME_def typed_DTIME_def by blast

lemma in_dtime_finite_alphabet: "L \<in> typed_DTIME TYPE('q) t \<Longrightarrow> finite (alphabet L)"
  by (meson TM_axioms(8) finite_subset in_dtimeE)

lemma in_pdtime_finite_alphabet: "L \<in> typed_PDTIME TYPE('q) t \<Longrightarrow> finite (alphabet L)"
  by (drule PDTIME_in_DTIME) (rule in_dtime_finite_alphabet)

lemma finite_length_is_finite_words: "finite (alphabet L) \<Longrightarrow>
    finite {w. length w \<le> n \<and> set w \<subseteq> alphabet L}"
  by (metis (no_types, lifting) Collect_mono finite_lists_length_le finite_subset)

lemma empty_alphabet_constant_time: "alphabet L = {} \<Longrightarrow> L \<in> DTIME (\<lambda>n. 1)"
proof -
  assume a: "alphabet L = {}"
  hence "words L = {} \<or> words L = {[]}"
    by (simp add: empty_alphabet_only_empty_word subset_singletonD)
  moreover have "words L = {} \<Longrightarrow> ?thesis"
  proof
    assume a1: "words L = {}"
    show "alphabet L \<subseteq> TM.TM.symbols (Abs_TM (halting_TM_rec 0 {undefined} False))"
      using a by simp
    show "alphabet L \<subseteq> TM.TM.symbols (Abs_TM (halting_TM_rec 0 {undefined} False)) \<and>
          (\<forall>w\<in>(alphabet L)*. TM_decider.decides_word
          (Abs_TM (halting_TM_rec 0 {undefined} False)) L w)"
      unfolding a apply auto unfolding TM_decider.decides_def a1
    proof auto
      have 1: "TM.is_final (Abs_TM (halting_TM_rec 0 {undefined} False))
               (TM.step (Abs_TM (halting_TM_rec 0 {undefined} False))
               (TM.initial_config (Abs_TM (halting_TM_rec 0 {undefined} False)) []))"
        unfolding TM.step_def apply auto
        by (metis Rej_TM.M_fields(4) Rej_TM.M_fields(5) Rej_TM_def
            TM.init_conf_state finite.emptyI finite_insert insert_not_empty
            rejecting_TM_def singletonI)
      show "TM_decider.rejects (Abs_TM (halting_TM_rec 0 {undefined} False)) []"
        unfolding TM_decider.rejects_def TM.compute_def TM.compute_config_def
          TM_decider.rej_def apply auto using 1
         apply (metis (no_types, lifting) TM.final_steps_final TM.init_conf_state
            TM.step_def finite.intros(1) finite_insert halting_TM_rec_def
            halting_TM_valid insert_not_empty is_finalD select_convs(4)
            select_convs(5) singletonI valid_tm_final_states valid_tm_initial_state)
        by (metis Rej_TM.M_fields(6) Rej_TM_def finite.emptyI finite_insert
            insert_not_empty rejecting_TM_def)
      thus "TM_decider.accepts (Abs_TM (halting_TM_rec 0 {undefined} False)) [] \<Longrightarrow>
            False" using TM_decider.rejects_accepts by blast
    qed
    show "\<forall>w. set w \<subseteq> TM.TM.symbols (Abs_TM (halting_TM_rec 0 {undefined} False)) \<longrightarrow>
          TM.time_bounded_word (Abs_TM (halting_TM_rec 0 {undefined} False))
          (\<lambda>n. 1) w" apply auto unfolding TM.time_bounded_word_def TM.run_def
       apply auto
      by (metis Rej_TM.M_fields(4) Rej_TM.M_fields(5) Rej_TM_def TM.final_step_final
          TM.init_conf_state finite.intros(1) finite_insert insertCI insert_not_empty
          is_finalI rejecting_TM_def)
  qed
  moreover have "words L = {[]} \<Longrightarrow> ?thesis"
  proof
    assume a1: "words L = {[]}"
    define M :: "(nat, 'a, bool) TM_record" where
      "M \<equiv> TM 1 {undefined} {0, 1, 2} 0 {1, 2} (\<lambda>s. if s = 1 then True else False)
           (\<lambda>_ hds. if hds ! 0 = None then 1 else 2)
           (\<lambda>_ hds k. hds ! k)
           (\<lambda>_ _ _. No_Shift)"
    have M_valid [intro]: "valid_TM M"
      apply standard
      unfolding M_def by auto
    show "alphabet L \<subseteq> TM.TM.symbols (Abs_TM M)" unfolding a by simp
    show "alphabet L \<subseteq> TM.TM.symbols (Abs_TM M) \<and>
          (\<forall>w\<in>(alphabet L)*. TM_decider.decides_word (Abs_TM M) L w)"
      unfolding a apply auto
      using a1 unfolding TM_decider.decides_def apply simp
    proof
      have 1: "state (TM.initial_config (Abs_TM M) []) = 0"
        unfolding TM.initial_config_def apply auto
        using M_def M_valid valid_tm_initial_state by fastforce
      have 2: "TM.final_states (Abs_TM M) = {1, 2}"
        by (smt (verit, del_insts) M_def M_valid select_convs(5)
            valid_tm_final_states)
      have 3: "state (TM.step (Abs_TM M) (TM.initial_config (Abs_TM M) [])) = 1"
        unfolding TM.step_def apply (auto simp add: 1 2)
        unfolding valid_tm_next_state [OF M_valid] TM.initial_config_def apply simp
        unfolding TM_abbrevs.input_tape_def apply simp unfolding M_def by simp
      have 4: "(LEAST n. TM.is_final (Abs_TM M)
               ((TM.step (Abs_TM M) ^^ n) (TM.initial_config (Abs_TM M) []))) = 1"
        apply (rule Least_natI)
        by (auto simp add: 1 2 3)
      show "TM_decider.accepts (Abs_TM M) []"
        unfolding TM_decider.accepts_def TM.compute_def TM.compute_config_def
          TM_decider.acc_def apply (auto simp add: 1 2 3 4)
        unfolding valid_tm_label [OF M_valid] unfolding M_def by simp
      thus "\<not> TM_decider.rejects (Abs_TM M) []"
        by (simp add: TM_decider.acc_not_rej)
    qed
    have 1: "TM.TM.symbols (Abs_TM M) = {undefined}"
      using M_def M_valid valid_tm_symbols by fastforce
    have 2: "state (TM.initial_config (Abs_TM M) w) = 0" for w
      unfolding TM.initial_config_def apply auto
      using M_def M_valid valid_tm_initial_state by fastforce
    show "\<forall>w. set w \<subseteq> TM.TM.symbols (Abs_TM M) \<longrightarrow> TM.time_bounded_word (Abs_TM M)
          (\<lambda>n. 1) w" apply (auto simp add: 1)
      unfolding TM.time_bounded_word_def TM.run_def apply auto
      unfolding TM.step_def apply auto
      unfolding TM.step_not_final_def Let_def 2 valid_tm_next_state [OF M_valid]
      apply (subst (2) M_def) apply auto
      by (smt (verit, del_insts) M_def M_valid TM_config.sel(1) insertCI is_finalI
          select_convs(5) select_convs(7) valid_tm_final_states)
  qed
  ultimately show ?thesis ..
qed

lemma typed_DTIME_inj: "inj (f::'q1 \<Rightarrow> 'q2) \<Longrightarrow> L \<in> typed_DTIME TYPE('q1) T \<Longrightarrow>
                        L \<in> typed_DTIME TYPE('q2) T"
proof (erule in_dtimeE, erule conjE, rule in_dtimeI')
  fix M :: "('q1, 'a) TM_decider"
  assume a1: "inj f" and a2: "alphabet L \<subseteq> TM.TM.symbols M" and
         a3: "\<forall>w. set w \<subseteq> TM.TM.symbols M \<longrightarrow> TM.time_bounded_word M T w" and
         a4: "alphabet L \<subseteq> TM.TM.symbols M" and
         a5: "\<forall>w\<in>(alphabet L)*. TM_decider.decides_word M L w"
  hence inj_on: "inj_on f (TM.states M)" by auto
  have 1: "TM.TM.symbols (Abs_TM (map_states_tmrec f M)) = TM.TM.symbols M"
    unfolding valid_tm_symbols [OF map_states_tmrec_valid [OF inj_on]]
    unfolding map_states_tmrec_def [OF inj_on] by simp
  show "alphabet L \<subseteq> TM.TM.symbols (Abs_TM (map_states_tmrec f M))"
    unfolding 1 by fact
  thus "alphabet L \<subseteq> TM.TM.symbols (Abs_TM (map_states_tmrec f M)) \<and>
    (\<forall>w\<in>(alphabet L)*. TM_decider.decides_word (Abs_TM (map_states_tmrec f M)) L w)"
    using map_states_tmrec_decides_iff a1 a4 a5 by blast
  have 2: "\<And>w. set w \<subseteq> TM.symbols M \<Longrightarrow>
           state (TM.run (Abs_TM (map_states_tmrec f M)) (T (length w)) w) =
           f (state (TM.run M (T (length w)) w))"
    apply (rule map_states_tmrec_run_state)
    by (rule inj_on)
  have 3: "\<And>s. f s \<in> TM.final_states (Abs_TM (map_states_tmrec f M)) \<longleftrightarrow>
           s \<in> TM.final_states M"
    unfolding valid_tm_final_states [OF map_states_tmrec_valid [OF inj_on]]
    unfolding map_states_tmrec_def [OF inj_on] using a1 by auto
  show "\<forall>w. set w \<subseteq> TM.TM.symbols (Abs_TM (map_states_tmrec f M)) \<longrightarrow>
        TM.time_bounded_word (Abs_TM (map_states_tmrec f M)) T w"
    unfolding TM.time_bounded_word_def 1 TM.is_final_def
    by (metis 2 3 TM.time_bounded_wordD a3 is_finalD)
qed

lemma typed_DTIME_bij: "bij (f::'q1 \<Rightarrow> 'q2) \<Longrightarrow> typed_DTIME TYPE('q1) T =
                        typed_DTIME TYPE('q2) T"
  apply (rule set_eqI)
  using typed_DTIME_inj by (smt (verit, del_insts) bij_betw_inv bij_is_inj)
                                                                     
lemma typed_DTIME_nat_eq: "typed_DTIME TYPE(nat + nat) T = DTIME T"
  by (rule typed_DTIME_bij) (fact bij_sum_encode)

lemma typed_DTIME_nat_tuple_eq: "typed_DTIME TYPE(nat \<times> nat) T = DTIME T"
  by (rule typed_DTIME_bij) (fact bij_prod_encode)

lemma typed_DTIME_impl_DTIME: "L \<in> typed_DTIME TYPE('q) T \<Longrightarrow> L \<in> DTIME T"
proof (erule in_dtimeE, erule conjE, rule in_dtimeI')
  fix M :: "('q, 'a) TM_decider"
  assume a1: "alphabet L \<subseteq> TM.TM.symbols M" and
         a2: "\<forall>w. set w \<subseteq> TM.TM.symbols M \<longrightarrow> TM.time_bounded_word M T w" and
         a3: "\<forall>w\<in>(alphabet L)*. TM_decider.decides_word M L w"
  have inj_ex: "\<exists>f::'q \<Rightarrow> nat. inj_on f (TM.states M)"
    by (meson TM.state_axioms(1) finite_imp_inj_to_nat_seg)
  define f :: "'q \<Rightarrow> nat" where "f \<equiv> (SOME f::'q \<Rightarrow> nat. inj_on f (TM.states M))"
  have 1: "inj_on f (TM.states M)" unfolding f_def
    using inj_ex by (rule someI_ex)
  show "alphabet L \<subseteq> TM.TM.symbols (Abs_TM (map_states_tmrec f M))"
    unfolding valid_tm_symbols [OF map_states_tmrec_valid [OF 1]]
    unfolding map_states_tmrec_def [OF 1] using a1 by simp
  thus "alphabet L \<subseteq> TM.TM.symbols (Abs_TM (map_states_tmrec f M)) \<and>
        (\<forall>w\<in>(alphabet L)*. TM_decider.decides_word
        (Abs_TM (map_states_tmrec f M)) L w)"
    apply auto
    using map_states_tmrec_decides_iff [THEN iffD2, THEN conjunct2] 1 a1 a3 by blast
  show "\<forall>w. set w \<subseteq> TM.TM.symbols
        (Abs_TM (map_states_tmrec f M)) \<longrightarrow> TM.time_bounded_word
        (Abs_TM (map_states_tmrec f M)) T w" apply auto
    by (smt (verit, best) 1 TM.is_final_def TM.time_bounded_wordD
        TM.time_bounded_wordI a2 map_states_tmrec_def map_states_tmrec_run_state
        map_states_tmrec_valid mem_Collect_eq select_convs(5) simps(2)
        valid_tm_final_states valid_tm_symbols)
qed

lemma inj_nat_fun_DTIME_eq: "inj (f::nat \<Rightarrow> 'q) \<Longrightarrow> typed_DTIME TYPE('q) T = DTIME T"
  apply (rule set_eqI)
  apply standard
   apply (erule typed_DTIME_impl_DTIME)
  by (rule typed_DTIME_inj)

lemma infinite_DTIME_eq: "infinite (UNIV :: 'q set) \<Longrightarrow> typed_DTIME TYPE('q) T = DTIME T"
proof (rule inj_nat_fun_DTIME_eq)
  assume a1: "infinite (UNIV :: 'q set)"
  define f :: "nat \<Rightarrow> 'q" where "f \<equiv> (SOME f. inj f)"
  show "inj f"
    unfolding f_def apply (rule someI_ex [of "\<lambda>f::nat \<Rightarrow> 'q. inj f"])
    using infinite_countable_subset [OF a1] by auto
qed

lemma typed_DTIME_infinite: "L \<in> typed_DTIME TYPE('q) T \<Longrightarrow> infinite (UNIV :: 'q2 set) \<Longrightarrow> L \<in> typed_DTIME TYPE('q2) T"
proof (drule typed_DTIME_impl_DTIME, rule typed_DTIME_inj)
  assume a1: "infinite (UNIV :: 'q2 set)" and a2: "L \<in> DTIME T"
  define f :: "nat \<Rightarrow> 'q2" where "f \<equiv> (SOME f. inj f)"
  have f_ex: "\<exists>f::nat \<Rightarrow> 'q2. inj f"
    using a1 by (metis infinite_countable_subset)
  note someI_ex [OF f_ex, folded f_def]
  show "inj f" by fact
qed

lemma typed_DTIME_tb_le_n: "L \<in> typed_DTIME TYPE('q) t \<Longrightarrow> t n \<le> n \<Longrightarrow>
                            L \<in> typed_DTIME TYPE('q) (\<lambda>n'. if n' \<le> n then t n' else t n)"
proof (erule in_dtimeE', rule in_dtimeI'', auto)
  fix M :: "('q, 'a) TM_decider" and w :: "'a list"
  assume a1: "t n \<le> n" and a2: "TM.time_bounded M t" and a3: "set w \<subseteq> alphabet L"
  define w' :: "'a list" where "w' \<equiv> take n w"
  show "TM.time_bounded_word M (\<lambda>n'. if n' \<le> n then t n' else t n) w"
    apply (cases "alphabet L = {}")
    using a3 a2 apply auto[1]
     apply (drule spec [where x="[]"])
     apply (unfold TM.time_bounded_word_def)[1]
     apply simp
  proof (cases "n = 0")
    case True
    show ?thesis using a2 [THEN spec, of "[]", unfolded TM.time_bounded_word_def, simplified, unfolded True]
      using a1 unfolding True apply simp
      unfolding TM.is_final_def TM.run_def apply simp
      unfolding TM.initial_config_def apply simp
      unfolding TM.time_bounded_word_def TM.is_final_def TM.run_def apply simp
      unfolding TM.initial_config_def by simp
  next
    case False
    assume a4: "alphabet L \<noteq> {}"
    then obtain s :: 'a where s_in_L: "s \<in> alphabet L" by auto
    have f11: "state (TM.steps M k (TM.initial_config M w')) =
               state (TM.steps M k (TM.initial_config M w))" and
         f12: "state (TM.steps M k (TM.initial_config M w')) \<notin> TM.final_states M \<Longrightarrow>
               heads (TM.steps M k (TM.initial_config M w')) =
               heads (TM.steps M k (TM.initial_config M w))" and
         f13: "\<And>i. i < TM.tape_count M \<Longrightarrow>
               left (tapes (TM.steps M k (TM.initial_config M w')) ! i) =
               left (tapes (TM.steps M k (TM.initial_config M w)) ! i)" and
         f14: "\<And>i. i < TM.tape_count M \<Longrightarrow> i > 0 \<Longrightarrow>
               right (tapes (TM.steps M k (TM.initial_config M w')) ! i) =
               right (tapes (TM.steps M k (TM.initial_config M w)) ! i)" and
         f15: "state (TM.steps M k (TM.initial_config M w')) \<notin> TM.final_states M \<Longrightarrow>
               right (tapes (TM.steps M k (TM.initial_config M w')) ! 0) =
               take (nat (n - (cell_index M w 0 k) - 1))
               (right (tapes (TM.steps M k (TM.initial_config M w)) ! 0))" if "n < length w"
         for k :: nat using that
    proof (induction k)
      case 0
      {
        case 1
        then show ?case by (simp add: TM.initial_config_def)
      next
        case 2
        then show ?case apply simp
          unfolding TM.initial_config_def TM_abbrevs.input_tape_def apply auto
          unfolding w'_def apply (auto simp add: False)
          using False by simp
      next
        case 3
        then show ?case apply simp
          unfolding TM.initial_config_def TM_abbrevs.input_tape_def apply auto
            apply (simp_all add: False w'_def)
          by (simp add: nth_Cons')
      next
        case 4
        then show ?case apply simp
          unfolding TM.initial_config_def TM_abbrevs.input_tape_def by simp
      next
        case 5
        then show ?case apply simp
          unfolding TM.initial_config_def TM_abbrevs.input_tape_def apply auto
          unfolding w'_def apply auto
          by (simp add: Suc_nat_eq_nat_zadd1 take_map take_tl)
      }
    next
      case (Suc k)
      {
        case 1
        show ?case apply simp
          apply (subst (1 2) TM.step_def)
          unfolding Suc(1) [OF 1] apply auto
           apply (rule Suc(1) [OF 1])
          unfolding Suc(2) [OF _ 1, unfolded Suc(1) [OF 1]] Suc(1) [OF 1] ..
      next
        case 2
        have 1: "state ((TM.step M ^^ k) (TM.initial_config M w')) \<notin> TM.TM.final_states M"
          using 2 by (metis TM.final_steps_le is_finalD is_finalI not_add_less2 plus_1_eq_Suc)
        have "int n - cell_index M w 0 k \<le> 1 \<Longrightarrow> n \<le> cell_index M w 0 k + 1" by linarith
        hence *: "int n - cell_index M w 0 k \<le> 1 \<Longrightarrow> n \<le> k + 1"
          using cell_index_abs_bound [of M w 0 k] by linarith
        have **: "right (tapes ((TM.step M ^^ k) (TM.initial_config M w')) ! 0) = [] \<longleftrightarrow>
                  right (tapes ((TM.step M ^^ k) (TM.initial_config M w)) ! 0) = []"
          unfolding Suc(5) [OF 1 2(2)] apply auto
          apply (frule *)
          using 2(1) a2 [THEN spec, of w', unfolded TM.time_bounded_word_def TM.run_def]
          apply (subst (asm) (2) w'_def)
          apply simp
          unfolding TM.is_final_def apply (cases "length w \<le> n")
           apply auto
          using Suc(5) [OF 1 2(2)] apply (simp add: w'_def)
          by (metis 2(1) TM.final_le_steps a1 is_finalI)
        have 3: "n = 1 \<Longrightarrow> ?case"
          apply (cases w)
          unfolding w'_def apply simp_all
          using 2(1) a2 [THEN spec, of w'] a1 apply (cases "t n < 1")
           apply (auto simp add: w'_def)
           apply (metis 1 One_nat_def TM.final_steps_le TM.run_def TM.time_bounded_def diff_Suc_1'
              is_finalD le_zero_eq length_Cons linorder_not_less list.size(3) nat.distinct(1) not_less_eq
              take_Cons' take_eq_Nil w'_def)
          by (metis 2(1) One_nat_def TM.final_steps_le TM.run_def TM.time_bounded_def diff_Suc_1' is_finalD
              length_Cons list.size(3) nat_less_le not_add_less1 not_less_eq plus_1_eq_Suc take_Cons'
              take_eq_Nil w'_def)
        show ?case apply (cases "n = 1")
           apply (erule 3)
          using 2 apply simp
          apply (subst (1 2) TM.step_def)
          apply (subst (asm) TM.step_def)
          unfolding Suc(1) apply auto
          unfolding Suc(1) apply simp
          apply (rule nth_equalityI)
           apply auto
           apply (simp add: TM.next_actions_simps(2) TM.run_tapes_len)
          unfolding TM.next_actions_def TM_abbrevs.tape_action_def TM.next_moves_def TM.next_writes_def
          apply simp
          apply (subst nth_map)
           apply auto
           apply (metis TM.run_tapes_len)
          apply (subst nth_zip)
            apply auto
           apply (metis TM.run_tapes_len)
        proof -
          fix i :: nat
          assume a1: "i < TM.TM.tape_count M" and
                 a2: "state ((TM.step M ^^ k) (TM.initial_config M w)) \<notin> TM.TM.final_states M" and
                 a3: "n \<noteq> Suc 0"
          show "head (TM_abbrevs.tape_shift (TM.TM.next_move M (state ((TM.step M ^^ k) (TM.initial_config M w)))
                (heads ((TM.step M ^^ k) (TM.initial_config M w'))) i)
                (TM_abbrevs.tape_write (TM.TM.next_write M (state ((TM.step M ^^ k) (TM.initial_config M w)))
                (heads ((TM.step M ^^ k) (TM.initial_config M w'))) i)
                (tapes ((TM.step M ^^ k) (TM.initial_config M w')) ! i))) =
                head (TM_abbrevs.tape_shift (TM.TM.next_move M (state ((TM.step M ^^ k) (TM.initial_config M w)))
                (heads ((TM.step M ^^ k) (TM.initial_config M w))) i)
                (TM_abbrevs.tape_write (TM.TM.next_write M (state ((TM.step M ^^ k) (TM.initial_config M w)))
                (heads ((TM.step M ^^ k) (TM.initial_config M w))) i)
                (tapes ((TM.step M ^^ k) (TM.initial_config M w)) ! i)))"
            apply (cases "TM.TM.next_move M (state ((TM.step M ^^ k) (TM.initial_config M w)))
                          (heads ((TM.step M ^^ k) (TM.initial_config M w'))) i")
              apply auto
              apply (cases "left (tapes ((TM.step M ^^ k) (TM.initial_config M w')) ! i)")
               apply auto
               apply (metis (no_types, lifting) 2 Suc.IH(2,3) TM.final_steps_le a1 head_left_empty
                is_finalD is_finalI left_after_write not_add_less2 plus_1_eq_Suc)
              apply (subst Shift_Left_is_left_not_empty)
               apply auto
              apply (metis (no_types, lifting) 2 Shift_Left_is_left_not_empty Suc.IH(2,3) TM.final_steps_le
                a1 is_finalD is_finalI left_after_write list.distinct(1) list.sel(1) not_add_less2
                plus_1_eq_Suc)
             apply (cases "right (tapes ((TM.step M ^^ k) (TM.initial_config M w')) ! i)")
              apply (cases "i = 0")
               apply auto
            using ** 1 Suc.IH(2) [OF _ 2(2)] apply fastforce
              apply (simp add: 1 Suc.IH(2,4) 2 a1)
            apply (metis 1
                Shift_Right_is_right_not_empty[of
                  "TM_abbrevs.tape_write
        (TM.TM.next_write M (state ((TM.step M ^^ k) (TM.initial_config M w)))
          (heads ((TM.step M ^^ k) (TM.initial_config M w'))) i)
        (tapes ((TM.step M ^^ k) (TM.initial_config M w')) ! i)"]
                  Shift_Right_is_right_not_empty[of
                    "TM_abbrevs.tape_write
        (TM.TM.next_write M (state ((TM.step M ^^ k) (TM.initial_config M w)))
          (heads ((TM.step M ^^ k) (TM.initial_config M w'))) i)
        (tapes ((TM.step M ^^ k) (TM.initial_config M w)) ! i)"]
                    Suc.IH(4)[of i] Suc.IH(5)
                    \<open>state ((TM.step M ^^ k) (TM.initial_config M w')) \<notin> TM.TM.final_states M \<Longrightarrow>
  heads ((TM.step M ^^ k) (TM.initial_config M w')) = heads ((TM.step M ^^ k) (TM.initial_config M w))\<close>
                    a1 bot_nat_0.not_eq_extremum[of i] list.distinct(1) list.sel(1)
                    right_after_write[of
                      "TM.TM.next_write M (state ((TM.step M ^^ k) (TM.initial_config M w)))
        (heads ((TM.step M ^^ k) (TM.initial_config M w'))) i"
                      "tapes ((TM.step M ^^ k) (TM.initial_config M w')) ! i"]
                    right_after_write[of
                      "TM.TM.next_write M (state ((TM.step M ^^ k) (TM.initial_config M w)))
        (heads ((TM.step M ^^ k) (TM.initial_config M w'))) i"
                      "tapes ((TM.step M ^^ k) (TM.initial_config M w)) ! i"]
                    starts_with_takeD[of "nat (int n - cell_index M w 0 k - 1)"
                      "right (tapes ((TM.step M ^^ k) (TM.initial_config M w)) ! 0)"]
                    that)
            unfolding TM_abbrevs.tape_shift.simps Suc(1) Suc(2) [OF 1 2(2)] apply simp
            unfolding TM_abbrevs.tape_shift.simps TM_abbrevs.tape_write_def by simp
        qed
      next
        case 3
        then show ?case apply simp
          apply (subst (1 2) TM.step_def)
          apply auto
          unfolding Suc(1) [OF 3(2)] Suc(2) [OF _ 3(2), unfolded Suc(1) [OF 3(2)]] apply auto
           apply (erule Suc(3) [OF _ 3(2)])
          unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_writes_def TM.next_moves_def
          apply (subst (1 2) nth_map2)
             apply auto
            apply (simp add: TM.run_tapes_len)
           apply (simp add: TM.run_tapes_len)
          apply (cases "TM.TM.next_move M (state ((TM.step M ^^ k) (TM.initial_config M w)))
                        (heads ((TM.step M ^^ k) (TM.initial_config M w))) i")
            apply auto
          unfolding Suc(3) [OF _ 3(2)] apply auto
           apply (subst (1 2) TM_abbrevs.tape_write_def)
           apply simp
          unfolding TM_abbrevs.tape_shift.simps apply simp
          by (rule Suc(3))
      next
        case 4
        then show ?case apply simp
          apply (subst (1 2) TM.step_def)
          apply auto
          unfolding Suc(1) apply auto
           apply (erule (1) Suc(4) [OF _ _ 4(3)])
          unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_moves_def TM.next_writes_def
          apply (subst (1 2) nth_map2)
              apply auto
            apply (simp_all add: TM.run_tapes_len)
          unfolding Suc(1) [OF 4(3)] Suc(2) [OF _ 4(3), unfolded Suc(1) [OF 4(3)]]
          apply (cases "TM.TM.next_move M (state ((TM.step M ^^ k) (TM.initial_config M w)))
                        (heads ((TM.step M ^^ k) (TM.initial_config M w))) i")
            apply auto
             apply (simp add: TM_abbrevs.tape_write_hd)
            apply (erule (1) Suc(4) [OF _ _ 4(3)])
          unfolding Suc(4) apply standard
          unfolding TM_abbrevs.tape_shift.simps apply simp
          by (rule Suc(4))
      next
        case 5
        hence 1: "state ((TM.step M ^^ k) (TM.initial_config M w')) \<notin> TM.TM.final_states M"
          by (metis 5(1) TM.is_final_def plus_1_eq_Suc TM.final_steps_le not_add_less2)
        have 2: "int n > k"
          using 5 a2 [THEN spec, of w', unfolded TM.time_bounded_word_def TM.run_def TM.is_final_def]
          apply (subst (asm) (2) w'_def)
          apply simp
          by (metis 1 TM.final_le_steps TM.final_steps_le a1 is_finalD is_finalI)
        hence 3: "int n - cell_index M w 0 k > 0" by (smt (verit, ccfv_SIG) cell_index_abs_bound)
        show ?case
          using 5 apply simp
          apply (subst (1 2) TM.step_def)
          apply auto
          unfolding Suc(1) apply auto
           apply (simp add: Suc.IH(1) TM.is_final_def)
          apply (subst (1 2) nth_map2)
              apply (metis TM.at_least_one_tape TM.next_actions_simps(2))
             apply (simp add: TM.run_tapes_len)
            apply (metis TM.at_least_one_tape TM.next_actions_simps(2))
           apply (simp add: TM.run_tapes_len)
          unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_writes_def TM.next_moves_def
          apply simp
          unfolding Suc(1) Suc(2) [unfolded Suc(1)]
          apply (cases "TM.TM.next_move M (state ((TM.step M ^^ k) (TM.initial_config M w)))
                        (heads ((TM.step M ^^ k) (TM.initial_config M w))) 0")
            apply auto
          unfolding TM_abbrevs.tape_write_def apply auto
          unfolding Suc(5) [OF 1 5(2)]
          using tl_take [where xs="(TM.TM.next_write M (state ((TM.step M ^^ k) (TM.initial_config M w)))
                                   (heads ((TM.step M ^^ k) (TM.initial_config M w))) 0 #
                                   right (tapes ((TM.step M ^^ k) (TM.initial_config M w)) ! 0))", simplified,
              of "nat (int n - cell_index M w 0 k)", symmetric] 3
            apply (smt (verit, best) 1 Suc.IH(2) Suc_nat_eq_nat_zadd1 right_Shift_Left take_Suc_Cons
              tape.sel(2,3))
           apply (smt (verit, ccfv_SIG) 1 Suc.IH(2) Suc_nat_eq_nat_zadd1 nat_le_0 right_Shift_Right
              take_eq_Nil take_tl tape.sel(3))
          unfolding TM_abbrevs.tape_shift.simps apply simp
          by (simp add: 1 Suc.IH(2) TM_abbrevs.tape_shift.simps(5))
      }
    qed
    show ?thesis using a2 [THEN spec, of w'] unfolding TM.time_bounded_word_def
        TM.run_def apply auto
       apply (subst (asm) w'_def)
       apply simp
       apply (unfold w'_def)[1]
       apply simp
      unfolding TM.is_final_def apply (subst (asm) f11)
       apply simp
      apply (subst (asm) w'_def)
      by simp
  qed
qed

lemma typed_DTIME_tb_le_n_const: "L \<in> typed_DTIME TYPE('q) t \<Longrightarrow> t n \<le> n \<Longrightarrow>
                                  \<exists>c::nat. L \<in> typed_DTIME TYPE('q) (\<lambda>_. c)"
proof -
  assume a1: "L \<in> typed_DTIME TYPE('q) t" and a2: "t n \<le> n"
  note 1 = typed_DTIME_tb_le_n [OF a1 a2]
  show "\<exists>c::nat. L \<in> typed_DTIME TYPE('q) (\<lambda>_. c)"
    apply (rule exI [where x="Max (t ` {0..n})"])
    apply (rule in_dtime_mono)
     apply (rule 1)
    by simp
qed

  (* Feels like an interesting result, especially, because it is very general. But
     it will be complicated, and I haven't verified it yet, so I will write it down, but make it
     unavailable. *)
lemma DTIME_min: "L \<in> DTIME t1 \<Longrightarrow> L \<in> DTIME t2 \<Longrightarrow> L \<in> DTIME (\<lambda>n. min (t1 n) (t2 n))"
  oops

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

lemma DTIME_ae_tcomp:
  assumes "\<exists>M::('q, 's) TM_decider. alphabet L \<subseteq> TM.symbols M \<and>
    (\<forall>\<^sub>\<infinity>w\<in>(alphabet L)*. TM_decider.decides_word M L w \<and> TM.time_bounded_word M T w)"
  shows "L \<in> DTIME (tcomp T)"
proof (insert assms, auto, erule ae_list_lengthE')
  fix M :: "('q, 's) TM_decider" and n :: nat
  assume "alphabet L \<subseteq> TM.TM.symbols M" and
    "\<And>x. n \<le> length x \<Longrightarrow> set x \<subseteq> alphabet L \<longrightarrow>
    TM_decider.decides_word M L x \<and> TM.time_bounded_word M T x" and n_gt_0: "n > 0"
  hence 1: "\<And>x. n \<le> length x \<Longrightarrow> set x \<subseteq> alphabet L \<Longrightarrow>
            TM_decider.decides_word M L x" and
        2: "\<And>x. n \<le> length x \<Longrightarrow> set x \<subseteq> alphabet L \<Longrightarrow> TM.time_bounded_word M T x"
    by auto
  have finite_words_le: "finite {w. set w \<subseteq> alphabet L \<and> length w < n}"
    by (smt (verit, best) Collect_mono TM.symbol_axioms(1) assms
        dual_order.order_iff_strict finite_lists_length_le finite_subset)
  define states :: "('q \<times> 's option list \<times> nat \<times> bool) set" where
    "states \<equiv> {(s, w, i, _). s \<in> TM.states M \<and> length w \<le> Suc n \<and>
                set w \<subseteq> options (TM.symbols M) \<and> i \<le> Suc n}"
  have 3: "states \<noteq> {}" unfolding states_def apply auto
    by (metis bot_nat_0.extremum list.size(3) lists.Nil lists_member)
  define final_states :: "('q \<times> 's option list \<times> nat \<times> bool) set" where
    "final_states \<equiv> states \<inter> ({(s, w, i, _). s \<in> TM.final_states M \<and> length w = Suc n \<and> last w \<noteq> None} \<union>
                    {(s, w, i, _). w \<noteq> [] \<and> last w = None})"
  define init_state :: "'q \<times> 's option list \<times> nat \<times> bool" where
    "init_state \<equiv> (TM.initial_state M, [], 0, False)"
  have finite_states: "finite states"
    unfolding states_def
  proof -
    have "finite (TM.TM.states M)" by simp
    moreover have "finite {w. length w \<le> Suc n \<and> set w \<subseteq> TM.TM.symbols M}" by auto
    moreover have "finite {i. i \<le> Suc n}" by simp
    moreover have "finite (UNIV::bool set)" by simp
    ultimately have "finite (TM.TM.states M \<times>
                     {w. length w \<le> Suc n \<and> set w \<subseteq> options (TM.TM.symbols M)} \<times>
                     {i. i \<le> Suc n} \<times> (UNIV::bool set))" by blast
    moreover have "{(s, w, i, _::bool). s \<in> TM.TM.states M \<and>
                   length w \<le> Suc n \<and> set w \<subseteq> options (TM.TM.symbols M) \<and>
                   i \<le> Suc n} \<subseteq> TM.TM.states M \<times>
                   {w. length w \<le> Suc n \<and> set w \<subseteq> options (TM.TM.symbols M)} \<times>
                   {i. i \<le> Suc n} \<times> (UNIV::bool set)" by auto
    ultimately show "finite {(s, w, i, _::bool). s \<in> TM.TM.states M \<and>
                     length w \<le> Suc n \<and> set w \<subseteq> options (TM.TM.symbols M) \<and>
                     i \<le> Suc n}"
      by (rule rev_finite_subset)
  qed
  have final_subset_states: "final_states \<subseteq> states"
    unfolding final_states_def states_def by simp
  have init_state_in_states: "init_state \<in> states"
    unfolding init_state_def states_def by simp
  show "L \<in> DTIME (tcomp (\<lambda>x. real (T x)))"
    apply (cases "alphabet L = {}")
     apply (drule empty_alphabet_constant_time)
     apply (meson add_leD2 in_dtime_mono tcomp_min)
  proof -
    assume a1: "alphabet L \<noteq> {}"
    then obtain s :: 's where s_def: "s \<in> alphabet L" by auto
    have M_has_final_states: "TM.final_states M \<noteq> {}"
  proof
    assume a2: "TM.TM.final_states M = {}"
    have 1: "\<And>M T w. TM.time_bounded_word M T w \<Longrightarrow> TM.halts M w"
      using TM.time_bounded_def by blast
    obtain w :: "'s list" where M_halts_w: "TM.halts M w"
      using 2 [THEN 1, of "replicate n s", simplified] s_def by (simp add: subset_iff)
    show False using M_halts_w a2 unfolding TM.halts_def TM.halts_config_def
      TM.is_final_def by simp
  qed
  have final_states_not_empty: "final_states \<noteq> {}"
  proof -
    obtain f :: 'q where f_def: "f \<in> TM.final_states M"
      using M_has_final_states by auto
    have "(f, [None], 0, False) \<in> final_states" unfolding final_states_def
        states_def apply auto
      using f_def by auto
    thus "final_states \<noteq> {}" by auto
  qed
  define extra_sym :: 's where "extra_sym \<equiv> (SOME s. s \<in> TM.symbols M)"
  have extra_sym_valid: "extra_sym \<in> TM.symbols M" unfolding extra_sym_def
    by (rule someI_ex) (simp add: ex_in_conv)
  define original_hds :: "'s option list \<Rightarrow> 's option list \<Rightarrow> nat \<Rightarrow>  's option list" where
    "\<And>hds w m. original_hds hds w m \<equiv> if hds ! 2 \<noteq> None then hd (tl hds)#(tl (tl (tl (tl hds))))
                                else if length w \<le> m then hd hds#(tl (tl (tl (tl hds)))) else
                                if m > 0 \<or> m = 0 \<and> hds ! 3 \<noteq> None then (w!m)#(tl (tl (tl (tl hds)))) else
                                None#(tl (tl (tl (tl hds))))"
  define M' :: "('q \<times> 's option list \<times> nat \<times> bool, 's, bool) TM_record" where
    "M' \<equiv> TM (TM.tape_count M + 3) (TM.symbols M)
          states init_state final_states
            (\<lambda>(q, w, _, _). if w \<noteq> [] \<and> last w = None then (butlast (map the w)) \<in>\<^sub>L L
              else TM.label M q)
            (\<lambda>(q, w, m, b) hds. let q' = if q \<in> TM.final_states M then q else
                                          TM.next_state M q (original_hds hds w m);
                                    w' = if length w \<le> n then w@[hds!0] else w;
                                    m' = if q \<in> TM.final_states M then m else
                                      case TM.next_move M q (original_hds hds w m) 0
                                      of Shift_Left \<Rightarrow>
                                      if m \<le> n then m - 1 else m | No_Shift \<Rightarrow> m | Shift_Right \<Rightarrow>
                                      if m \<le> n \<and> (m > 0 \<or> hds ! 3 \<noteq> None \<or> w = [])
                                      then Suc m else m;
                                    b' = b \<or> m \<ge> Suc n in (q', w', m', b'))
            (\<lambda>(q, w, m, b) hds k. if k > 3 then if q \<in> TM.final_states M then hds ! k else
                                   TM.next_write M q (original_hds hds w m)
                                    (k - 3) else
                                  if k = 0 then hds ! k else
                                  if k = 1 then if q \<in> TM.final_states M then hds ! k else
                                     TM.next_write M q (original_hds hds w m) 0 else
                                  if k = 2 then if q \<in> TM.final_states M then hds ! k else Some extra_sym else
                                    if w = [] then Some extra_sym else hds ! k)
            (\<lambda>(q, w, m, b) hds k. if k > 3 then if q \<in> TM.final_states M then No_Shift else
                                  TM.next_move M q (original_hds hds w m)
                                    (k - 3) else
                                  if k = 0 then (if length w > n then (if (b \<or> m \<ge> Suc n) \<and> q \<notin> TM.final_states M then
                                      TM.next_move M q (original_hds hds w m) 0 else
                                      No_Shift) else Shift_Right) else
                                    if q \<in> TM.final_states M then No_Shift else
                                      TM.next_move M q (original_hds hds w m) 0)"
  have valid_M' [simp, intro]: "valid_TM M'"
    apply standard
    unfolding M'_def apply simp_all
        apply fact+
  proof (erule conjE)
    fix q :: "'q \<times> 's option list \<times> nat \<times> bool" and hds :: "'s option list"
    assume a1: "q \<in> states" and a2: "length hds = TM.TM.tape_count M + 3" and
           a3: "set hds \<subseteq> options (TM.TM.symbols M)"
    obtain q' :: 'q and w :: "'s option list" and m :: nat and b :: bool where
       q_def: "q = (q', w, m, b)" by (rule prod_cases4)
    have m_le_Sucn: "m \<le> Suc n" using a1 [unfolded states_def] q_def by simp
    have next_state_helper: "\<And>h. h \<in> options (TM.symbols M) \<Longrightarrow>
                             TM.TM.next_state M q' (h # tl (tl (tl (tl hds)))) \<in>
                             TM.TM.states M"
      apply (rule TM.next_state_valid)
      using a1 [unfolded q_def states_def] apply simp
      using a2 apply simp
      apply auto
      using a3 by (smt (verit) list.sel(2) list.set_sel(2) subset_eq)
    have helper1: "hd (tl hds) \<in> options (TM.TM.symbols M)"
      using a2 a3 by (metis Nitpick.size_list_simp(2) One_nat_def hd_in_set le_add2
          list.set_sel(2) numeral_le_one_iff semiring_norm(70) subset_code(1)
          zero_eq_add_iff_both_eq_0 zero_neq_numeral)
    have helper2: "hd hds \<in> options (TM.symbols M)"
      using a2 a3 by (metis hd_in_set helper1 subsetD tl_eqI)
    have 1: "TM.TM.next_state M q' (original_hds hds w m) \<in> TM.states M"
      unfolding original_hds_def
      apply (auto intro!: next_state_helper simp add: helper1 helper2)
      using a1 unfolding q_def states_def by auto
    show "(case q of (q, w, m, b) \<Rightarrow>
          \<lambda>hds. (if q \<in> TM.TM.final_states M then q else TM.TM.next_state M q (original_hds hds w m),
                 if length w \<le> n then w @ [hds ! 0] else w,
                 if q \<in> TM.TM.final_states M then m
                 else case TM.TM.next_move M q (original_hds hds w m) 0 of Shift_Left \<Rightarrow> if m \<le> n then m - 1 else m
                      | Shift_Right \<Rightarrow> if m \<le> n \<and> (0 < m \<or> hds ! 3 \<noteq> None \<or> w = [])
                    then Suc m else m | No_Shift \<Rightarrow> m, b \<or> Suc n \<le> m)) hds \<in> states"
      unfolding q_def apply auto
    proof -
      assume a4: "m \<le> n" and a5: "length w \<le> n"
      have 2: "length (w @ [hds ! 0]) \<le> Suc n" using a5 by simp
      have 3: "m - Suc 0 \<le> Suc n" using a4 by simp
      have 4: "set (w @ [hds ! 0]) \<subseteq> options (TM.symbols M)"
        using a1 unfolding q_def states_def apply auto using a2 a3 by auto
      have 5: "q' \<in> TM.states M"
        using a1 unfolding q_def states_def by simp
      show 6: "(q', w @ [hds ! 0], m, b) \<in> states"
        using 1 2 a4 4 5 unfolding states_def by auto
      thus "(q', w @ [hds ! 0], m, b) \<in> states" .
      show "(TM.TM.next_state M q' (original_hds hds w m), w @ [hds ! 0],
            case TM.TM.next_move M q' (original_hds hds w m) 0 of Shift_Left \<Rightarrow> m - 1
            | Shift_Right \<Rightarrow> Suc m | No_Shift \<Rightarrow> m, b) \<in> states"
        apply (cases "TM.TM.next_move M q' (original_hds hds w m) 0")
          apply auto
        unfolding states_def using 1 2 3 4 apply blast
        using 1 2 4 a4 by fastforce+
      thus "(TM.TM.next_state M q' (original_hds hds w m), w @ [hds ! 0],
            case TM.TM.next_move M q' (original_hds hds w m) 0 of Shift_Left \<Rightarrow> m - 1
            | Shift_Right \<Rightarrow> Suc m | No_Shift \<Rightarrow> m, b) \<in> states" .
    next
      assume a4: "m \<le> n"
      show "(TM.TM.next_state M q' (original_hds hds w m), w,
            case TM.TM.next_move M q' (original_hds hds w m) 0 of Shift_Left \<Rightarrow> m - 1
            | Shift_Right \<Rightarrow> Suc m | No_Shift \<Rightarrow> m, b) \<in> states"
        unfolding states_def apply auto
           apply fact
        using a1 unfolding q_def states_def apply auto
        apply (cases "TM.TM.next_move M q' (original_hds hds w m) 0")
          apply auto
        using a4 by force
      thus "(TM.TM.next_state M q' (original_hds hds w m), w,
            case TM.TM.next_move M q' (original_hds hds w m) 0 of Shift_Left \<Rightarrow> m - 1
            | Shift_Right \<Rightarrow> Suc m | No_Shift \<Rightarrow> m, b) \<in> states" .
      show "(q', w, m, b) \<in> states"
        using a1 unfolding q_def states_def by simp
      thus "(q', w, m, b) \<in> states" .
      show "(q', [hds ! 0], m, b) \<in> states"
        using a1 unfolding q_def states_def apply auto
        by (metis Suc3_eq_add_3 a2 add.commute hd_conv_nth helper2 list.size(3) nat.distinct(1))
    next
      assume a4: "m = 0" and a5: "length w \<le> n"
      show "(TM.TM.next_state M q' (original_hds hds w 0), w @ [hds ! 0],
            case TM.TM.next_move M q' (original_hds hds w 0) 0 of Shift_Left \<Rightarrow>
            0 - 1 | _ \<Rightarrow> 0, b) \<in> states"
        unfolding states_def apply auto
            apply (subst a4 [symmetric])
            apply fact+
        using a2 a3 apply fastforce
        using a1 unfolding q_def states_def apply fast
        by (metis a4 diff_0_eq_0 head_move.case_distrib m_le_Sucn)
      show "(q', w @ [hds ! 0], 0, b) \<in> states"
        using a1 unfolding q_def states_def apply auto
         apply (rule a5)
        by (metis helper2 list.size(3) hd_conv_nth a2 zero_eq_add_iff_both_eq_0 TM.at_least_one_tape
            linorder_not_le eq_imp_le)
    next
      assume a4: "m = 0"
      show "(TM.TM.next_state M q' (original_hds hds w 0), w,
            case TM.TM.next_move M q' (original_hds hds w 0) 0 of Shift_Left \<Rightarrow>
            0 - 1 | _ \<Rightarrow> 0, b) \<in> states"
        unfolding states_def apply auto
           apply (subst a4 [symmetric])
           apply fact
        using a1 unfolding q_def states_def apply simp
        using a1 unfolding q_def states_def apply fast
        by (metis a4 diff_0_eq_0 head_move.case_distrib m_le_Sucn)
      show "(q', w, 0, b) \<in> states"
        using a1 unfolding q_def states_def by simp
    next
      assume a4: "\<not> m \<le> n" and a5: "length w \<le> n"
      show "(TM.TM.next_state M q' (original_hds hds w m), w @ [hds ! 0],
            case TM.TM.next_move M q' (original_hds hds w m) 0 of Shift_Left \<Rightarrow> m | _ \<Rightarrow> m, True)
            \<in> states"
        unfolding states_def apply auto
            apply (rule TM.next_state_valid)
        using a1 [unfolded q_def states_def, simplified] apply simp
             apply (subst original_hds_def)
        using a2 apply auto
            apply (subst (asm) original_hds_def)
            apply (cases "hds ! 2 \<noteq> None")
             apply auto
        using helper1 apply force
             apply (smt (verit, best) a3 list.set_sel(2) subsetD tl_eqI)
        using a5 a4 apply auto
        using helper2 apply force
        apply (rule a3 [THEN subsetD])
           apply (drule set_tl_subset [THEN subsetD])+
           apply assumption
        using a3 apply fastforce
        using a1 [unfolded q_def states_def, simplified] apply auto
        by (smt (verit, del_insts) diff_diff_cancel diff_is_0_eq head_move.case_distrib le_Suc_eq
            not_less_eq_eq)
      show "(q', w @ [hds ! 0], m, True) \<in> states"
        using a1 unfolding q_def states_def apply auto
         apply (rule a5)
        by (metis a2 hd_conv_nth helper2 list.size(3) nat.distinct(1) numeral_3_eq_3 zero_eq_add_iff_both_eq_0)
    next
      assume a4: "\<not> m \<le> n" and a5: "\<not> length w \<le> n"
      have 1: "m = Suc n" using a4 a1 [unfolded q_def states_def, simplified] by linarith
      have 2: "length w = Suc n" using a5 a1 [unfolded q_def states_def, simplified] by linarith
      show "(TM.TM.next_state M q' (original_hds hds w m), w,
            case TM.TM.next_move M q' (original_hds hds w m) 0 of Shift_Left \<Rightarrow> m | _ \<Rightarrow> m, True)
            \<in> states"
        unfolding states_def apply auto
           apply (rule TM.next_state_valid)
        using a1 [unfolded q_def states_def, simplified] apply simp
        using a2 apply (subst original_hds_def)
            apply auto
        using a3 apply (subst (asm) original_hds_def)
           apply (cases "hds ! 2 \<noteq> None")
            apply auto
        using helper1 apply blast
            apply (drule set_tl_subset [THEN subsetD])+
            apply (erule subsetD)
            apply assumption
           apply (cases "length w \<le> m")
            apply auto
        using helper2 apply blast
            apply (drule set_tl_subset [THEN subsetD])+
            apply (erule subsetD)
            apply assumption
           apply (cases "0 < m \<or> m = 0 \<and> (\<exists>y. hds ! 3 = Some y)")
            apply auto
               apply (simp add: 1 2)
        using a4 apply blast
             apply (drule set_tl_subset [THEN subsetD])+
             apply (erule subsetD)
             apply assumption
        using 1 apply force
           apply (drule set_tl_subset [THEN subsetD])+
           apply (erule subsetD)
           apply assumption
        unfolding 2 apply (rule Nat.le_refl)
        using a1 [unfolded q_def states_def, simplified] apply blast
        unfolding 1 apply (cases "TM.TM.next_move M q' (original_hds hds w (Suc n)) 0 = Shift_Left")
         apply auto
        by (metis head_move.case_distrib 1 le_refl bot_nat_0.extremum diff_is_0_eq diff_diff_cancel)
      show "(q', w, m, True) \<in> states"
        using a1 unfolding q_def states_def by simp
    next
      have *: "TM.TM.next_state M q' (original_hds hds [] m) \<in> TM.TM.states M"
        apply (rule TM.next_state_valid)
        using a1 [unfolded states_def q_def, simplified] apply auto
              apply (subst original_hds_def)
        using a2 apply auto
        using a3 apply (subst (asm) original_hds_def)
             apply (cases "hds ! 2 \<noteq> None")
              apply auto
        using helper1 apply blast
               apply (meson set_tl_subset subsetD)
        using helper2 apply force
        by (meson set_tl_subset subsetD)
      show "m \<le> n \<Longrightarrow> w = [] \<Longrightarrow>(TM.TM.next_state M q' (original_hds hds [] m), [hds ! 0],
            case TM.TM.next_move M q' (original_hds hds [] m) 0 of Shift_Left \<Rightarrow> m - 1 |
            Shift_Right \<Rightarrow> Suc m | No_Shift \<Rightarrow> m, b) \<in> states"
        apply (cases "TM.TM.next_move M q' (original_hds hds [] m) 0")
          apply auto
        unfolding states_def apply auto
             apply (rule *)
            apply (metis a2 hd_conv_nth helper2 list.size(3) nat.distinct(1) numeral_3_eq_3
            zero_eq_add_iff_both_eq_0)
           apply (rule *)
          apply (metis a2 hd_conv_nth helper2 list.size(3) nat.distinct(1) numeral_3_eq_3
            zero_eq_add_iff_both_eq_0)
         apply (rule *)
        by (metis a2 hd_conv_nth helper2 list.size(3) nat.distinct(1) numeral_3_eq_3
            zero_eq_add_iff_both_eq_0)
    qed
  next
    fix q :: "'q \<times> 's option list \<times> nat \<times> bool" and hds :: "'s option list" and
        i :: nat
    assume a1: "q \<in> states" and
           a2: "length hds = TM.TM.tape_count M + 3 \<and>
                set hds \<subseteq> options (TM.TM.symbols M)" and
           a3: "i < TM.TM.tape_count M + 3"
    have 1: "length hds = TM.TM.tape_count M + 3" using a2 ..
    have 2: "set hds \<subseteq> options (TM.TM.symbols M)" using a2 ..
    obtain q' and w and m and b where q_def: "q = (q', w, m, b)" by (rule prod_cases4)
    have 3: "set w \<subseteq> options (TM.symbols M)" using a1 [unfolded states_def] q_def by simp
    show "(case q of
        (q, w, m, b) \<Rightarrow>
          \<lambda>hds k.
             if 3 < k
             then if q \<in> TM.TM.final_states M then hds ! k else TM.TM.next_write M q (original_hds hds w m) (k - 3)
             else if k = 0 then hds ! k
                  else if k = 1
                       then if q \<in> TM.TM.final_states M then hds ! k
                            else TM.TM.next_write M q (original_hds hds w m) 0
                       else if k = 2 then if q \<in> TM.TM.final_states M then hds ! k else Some extra_sym
                            else if w = [] then Some extra_sym else hds ! k)
        hds i
       \<in> options (TM.TM.symbols M)"
      unfolding q_def apply (auto intro: extra_sym_valid)
    proof -
      have 1: "q' \<in> TM.states M" using a1 unfolding q_def states_def by simp
      have 2: "Suc (length hds - Suc (Suc (Suc (Suc 0)))) = TM.TM.tape_count M"
        by (simp add: a2)
      have 3: "\<And>x. x \<in> set (tl (tl (tl (tl hds)))) \<Longrightarrow> x \<in> options (TM.TM.symbols M)"
        by (metis (full_types) a2 list.set_sel(2) subset_code(1) tl_eqI)
      show 4: "hds ! 0 \<in> options (TM.TM.symbols M)"
        using a2 by fastforce
      thus "hds ! 0 \<in> options (TM.TM.symbols M)" .
      show "TM.TM.next_write M q' (original_hds hds [] m) 0 \<in> options (TM.TM.symbols M)"
        unfolding original_hds_def
        apply (auto del: TM.next_write_valid intro!: TM.next_write_valid 1 2 simp add: 3)
           apply (metis Nitpick.size_list_simp(2) a2 add_Suc_right diff_Suc_1 hd_in_set
            list.set_sel(2) numeral_2_eq_2 numeral_3_eq_3 subset_code(1)
            zero_eq_add_iff_both_eq_0 zero_neq_numeral)
        using 4 by (metis a2 a3 less_nat_zero_code list.size(3) zeroth_is_head)
      have 5: "i - 3 < TM.TM.tape_count M"
        by (metis TM.at_least_one_tape a3 diff_is_0_eq' less_diff_conv2 nat_le_linear)
      show "TM.TM.next_write M q' (original_hds hds [] m) (i - 3) \<in>
            options (TM.TM.symbols M)"
        unfolding original_hds_def
        apply (auto del: TM.next_write_valid intro!: TM.next_write_valid 1 2 simp add: 3 5)
          apply (metis Nitpick.size_list_simp(2) a2 add_Suc_right diff_Suc_1 hd_in_set
            list.set_sel(2) numeral_2_eq_2 numeral_3_eq_3 subset_code(1)
            zero_eq_add_iff_both_eq_0 zero_neq_numeral)
        using 4 by (metis a2 a3 less_nat_zero_code list.size(3) zeroth_is_head)
      have 6: "hd (tl hds) \<in> options (TM.TM.symbols M)"
        by (metis Suc3_eq_add_3 Zero_not_Suc a2 add.commute diff_Suc_1 hd_in_set
            length_tl list.set_sel(2) list.size(3) subsetD)
      show "i = Suc 0 \<Longrightarrow> TM.TM.next_write M q' (original_hds hds w m) 0 \<in> options (TM.TM.symbols M)"
        unfolding original_hds_def
        apply (auto del: TM.next_write_valid intro!: TM.next_write_valid 1 2 simp add: 3 6)
        using 4 apply (metis 6 tl_eqI zeroth_is_head)
        using a1 unfolding q_def states_def apply force
          apply (metis 4 6 tl_eqI hd_conv_nth)
        using a1 unfolding q_def states_def apply fastforce
        by (metis 4 6 tl_eqI hd_conv_nth)
      show "TM.TM.next_write M q' (original_hds hds w m) (i - 3) \<in>
            options (TM.TM.symbols M)"
        unfolding original_hds_def
        apply (auto del: TM.next_write_valid intro!: TM.next_write_valid 1 2
            simp add: 3 5 6)
        using a1 unfolding q_def states_def apply auto
        by (metis 4 6 tl_eqI hd_conv_nth)+
      show "hds ! i \<in> options (TM.TM.symbols M)"
        using a2 a3 by fastforce
      thus "hds ! i \<in> options (TM.TM.symbols M)" .
      thus 7: "hds ! i \<in> options (TM.TM.symbols M)" .
      thus "i = 0 \<Longrightarrow> hds ! 0 \<in> options (TM.TM.symbols M)" by simp
      thus "i = 0 \<Longrightarrow> hds ! 0 \<in> options (TM.TM.symbols M)" .
      show "i = Suc 0 \<Longrightarrow> hds ! Suc 0 \<in> options (TM.TM.symbols M)" using 7 by simp
      thus "i = Suc 0 \<Longrightarrow> hds ! Suc 0 \<in> options (TM.TM.symbols M)" .
      show "hds ! 2 \<in> options (TM.TM.symbols M)"
        using a2 by force
      thus "hds ! 2 \<in> options (TM.TM.symbols M)" .
    qed
  qed
  have 3 [simp]: "state (TM.initial_config (Abs_TM M') w) = init_state" for w :: "'s list"
    unfolding TM.initial_config_def apply simp
    using M'_def valid_tm_initial_state by force
  have 4 [simp]: "init_state \<notin> TM.TM.final_states (Abs_TM M')"
    unfolding init_state_def valid_tm_final_states [OF valid_M']
    unfolding M'_def apply simp
    unfolding final_states_def by simp
  have 5 [simp]: "TM.tape_count (Abs_TM M') = TM.tape_count M + 3"
    using M'_def valid_tm_tape_count by force
  have 6: "k \<le> Suc n \<Longrightarrow> k < length w \<Longrightarrow>
           tapes (TM.steps (Abs_TM M') k (TM.initial_config (Abs_TM M') w)) ! 0 =
           Tape (rev (take k (map Some w@[None]))) (Some (w ! k))
            (drop (Suc k) (map Some w)) \<and>
           fst (snd (state (TM.steps (Abs_TM M') k (TM.initial_config (Abs_TM M') w)))) =
           take k (map Some w@[None])" for k :: nat and w :: "'s list"
  proof (induction k)
    case 0
    then show ?case apply (auto simp add: TM.initial_config_def TM_abbrevs.input_tape_def)
      using hd_conv_nth apply blast
       apply (simp add: drop_Suc map_tl)
      unfolding valid_tm_initial_state [OF valid_M'] unfolding M'_def apply simp
      unfolding init_state_def by simp
  next
    case (Suc k)
    hence 1: "tapes ((TM.step (Abs_TM M') ^^ k) (TM.initial_config (Abs_TM M') w)) ! 0 =
             Tape (rev (take k (map Some w @ [None]))) (Some (w ! k))
             (drop (Suc k) (map Some w))" and
         2: "fst (snd (state ((TM.step (Abs_TM M') ^^ k)
             (TM.initial_config (Abs_TM M') w)))) = take k (map Some w @ [None])" by simp_all
    have 3 [simp]: "state ((TM.step (Abs_TM M') ^^ k) (TM.initial_config (Abs_TM M') w))
                    \<notin> TM.TM.final_states (Abs_TM M')"
      unfolding valid_tm_final_states [OF valid_M']
      apply (subst (3) M'_def) apply simp
      unfolding final_states_def using 2 apply auto
      using Suc.prems(1) apply linarith
       apply (metis Suc.prems(2) append_Nil2 last_map less_SucI neq0_conv not_less_eq
          option.distinct(1) take_eq_Nil take_map zero_less_diff)
      using Suc.prems(2) Suc_lessD less_imp_le_nat by blast
    obtain q :: 'q and w' :: "'s option list" and m :: nat and b :: bool where
      state_split: "state ((TM.step (Abs_TM M') ^^ k) (TM.initial_config (Abs_TM M') w)) =
                    (q, w', m, b)" by (rule prod_cases4)
    have 4: "n \<ge> length w'" using state_split 2 apply simp using Suc(2) by linarith
    have 5: "next_move M' (state ((TM.step (Abs_TM M') ^^ k)
             (TM.initial_config (Abs_TM M') w))) (heads ((TM.step (Abs_TM M') ^^ k)
             (TM.initial_config (Abs_TM M') w))) 0 = Shift_Right"
      apply (subst M'_def)
      apply (auto simp add: state_split)
      using 4 by linarith+
    have 6: "next_write M' (state ((TM.step (Abs_TM M') ^^ k)
             (TM.initial_config (Abs_TM M') w))) (heads ((TM.step (Abs_TM M') ^^ k)
             (TM.initial_config (Abs_TM M') w))) 0 = (heads ((TM.step (Abs_TM M') ^^ k)
             (TM.initial_config (Abs_TM M') w))) ! 0"
      apply (subst M'_def)
      by (simp add: state_split)
    have 7: "heads ((TM.step (Abs_TM M') ^^ k) (TM.initial_config (Abs_TM M') w)) ! 0 =
             Some (w ! k)"
      using 1 by (simp add: M'_def TM.run_tapes_len)
    have 8: "\<And>w'. take (k - length w) w' = []"
      using Suc(3) by simp
    have 9: "\<And>w'. take (Suc k - length w) w' = []"
      using Suc(3) by simp
    have 10: "drop (Suc k) (map Some w) \<noteq> []"
      using Suc(3) by simp
    have 11: "drop (Suc k) (map Some w) =
              Some (w ! (Suc k)) # drop (Suc (Suc k)) (map Some w)"
      using 10 by (metis Cons_nth_drop_Suc Suc.prems(2) length_map nth_map)
    show ?case apply simp
      apply (subst TM.step_def)
      apply auto
       apply (subst map2_subst)
          apply auto
         apply (metis TM.at_least_one_tape TM.next_actions_simps(2) list.size(3) neq0_conv)
        apply (metis TM.run_def TM.run_tapes_non_empty)
      unfolding TM.next_actions_def apply (subst zip_subst) apply auto
         apply (metis TM.at_least_one_tape TM.next_writes_simps(2) length_greater_0_conv)
        apply (metis TM.at_least_one_tape TM.next_moves_simps(2) length_greater_0_conv)
      unfolding TM.next_moves_def TM.next_writes_def apply auto
      unfolding TM_abbrevs.tape_action_def apply auto
      unfolding valid_tm_next_move [OF valid_M'] valid_tm_next_write [OF valid_M']
       apply (simp add: 5 6 7)
      unfolding 1 TM_abbrevs.tape_shift.simps TM_abbrevs.tape_write_def apply (simp add: 8 9)
      unfolding 11 unfolding TM_abbrevs.tape_shift.simps
       apply (simp add: Suc.prems(2) Suc_lessD take_Suc_conv_app_nth)
      apply (subst TM.step_def)
      apply auto
      unfolding valid_tm_next_state [OF valid_M'] apply (subst M'_def)
      apply (auto simp add: state_split 7)
      using state_split 2 apply (simp_all add: 8 9)
       apply (simp add: Suc.prems(2) Suc_lessD take_Suc_conv_app_nth)
      using Suc.prems(1) by linarith
  qed
  have 7 [simp]: "TM.symbols (Abs_TM M') = TM.symbols M"
    unfolding valid_tm_symbols [OF valid_M']
    unfolding M'_def by simp
  have 8: "k \<le> n \<Longrightarrow> k < length w \<Longrightarrow>
           state ((TM.step (Abs_TM M') ^^ k) (TM.initial_config (Abs_TM M') w))
           \<notin> TM.TM.final_states (Abs_TM M')" for k :: nat and w :: "'s list"
     using 6 [THEN conjunct2] apply auto
    unfolding valid_tm_final_states [OF valid_M']
    apply (subst (asm) (5) M'_def)
    apply simp
    apply (rule prod_cases4 [where y="state ((TM.step (Abs_TM M') ^^ k)
      (TM.initial_config (Abs_TM M') w))"])
    unfolding final_states_def apply auto
    using le_Suc_eq apply fastforce
    by (metis (no_types, opaque_lifting) fst_conv last_map le_Suc_eq list.map_disc_iff
        option.distinct(1) snd_conv take_map)
  have 21: "(heads ((TM.step (Abs_TM M') ^^ k) (TM.initial_config (Abs_TM M') w)) ! 3
            \<noteq> None \<longleftrightarrow> heads ((TM.step (Abs_TM M') ^^ k)
            (TM.initial_config (Abs_TM M') w)) ! 3 = Some extra_sym) \<and>
            set (left ((tapes ((TM.step (Abs_TM M') ^^ k)
            (TM.initial_config (Abs_TM M') w)) ! 3))) \<subseteq> {None, Some extra_sym} \<and>
            set (right ((tapes ((TM.step (Abs_TM M') ^^ k)
            (TM.initial_config (Abs_TM M') w)) ! 3))) \<subseteq> {None, Some extra_sym}"
    for k :: nat and w :: "'s list"
  proof (induction k)
    case 0
    then show ?case by (simp add: TM.init_conf_len TM.initial_tapes_empty)
  next
    case (Suc k)
    obtain q :: 'q and w' :: "'s option list" and m :: nat and b :: bool where
      state_split: "state ((TM.step (Abs_TM M') ^^ k) (TM.initial_config (Abs_TM M') w)) =
                    (q, w', m, b)" by (rule prod_cases4)
    have 1: "TM.next_write (Abs_TM M') (state ((TM.step (Abs_TM M') ^^ k)
             (TM.initial_config (Abs_TM M') w))) (heads ((TM.step (Abs_TM M') ^^ k)
             (TM.initial_config (Abs_TM M') w))) 3 = None \<or>
             TM.next_write (Abs_TM M') (state ((TM.step (Abs_TM M') ^^ k)
             (TM.initial_config (Abs_TM M') w))) (heads ((TM.step (Abs_TM M') ^^ k)
             (TM.initial_config (Abs_TM M') w))) 3 = Some extra_sym"
      unfolding valid_tm_next_write [OF valid_M'] apply (subst (1 6) M'_def)
      using Suc by (auto simp add: state_split)
    from Suc show ?case apply auto
      apply (subst (asm) TM.step_def)
      apply (cases "state ((TM.step (Abs_TM M') ^^ k) (TM.initial_config (Abs_TM M') w))
                    \<in> TM.TM.final_states (Abs_TM M')")
       apply auto
      apply (subst (asm) nth_map)
       apply (simp add: TM.next_actions_simps(2) TM.run_tapes_len)
      apply (subst (asm) nth_map)
        apply (simp add: TM.next_actions_simps(2))
       apply (simp add: TM.run_tapes_len)
           apply simp
           apply (subst (asm) nth_zip)
             apply (simp add: TM.next_actions_simps(2))
            apply (simp add: TM.run_tapes_len)
      apply simp
      unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_moves_def
        TM.next_writes_def apply simp
      apply (cases "TM.TM.next_move (Abs_TM M')
              (state ((TM.step (Abs_TM M') ^^ k) (TM.initial_config (Abs_TM M') w)))
              (heads ((TM.step (Abs_TM M') ^^ k) (TM.initial_config (Abs_TM M') w))) 3")
             apply auto
             apply (smt (verit) head_in_left_tape head_left_empty insert_iff
          left_after_write option.discI option.inject singleton_iff subsetD)
            apply (metis (no_types, opaque_lifting) empty_iff head_in_right_tape
          head_right_empty insertE not_Some_eq option.inject right_after_write
          subset_code(1)) using 1
           apply (simp add: TM_abbrevs.tape_shift.simps(5) TM_abbrevs.tape_write_hd)
          apply (subst (asm) TM.step_def)
      apply (cases "state ((TM.step (Abs_TM M') ^^ k) (TM.initial_config (Abs_TM M') w))
                    \<in> TM.TM.final_states (Abs_TM M')")
           apply auto
          apply (subst (asm) nth_map2)
            apply (simp add: TM.next_actions_simps(2))
           apply (simp add: TM.run_tapes_len)
      unfolding TM.next_actions_def TM_abbrevs.tape_action_def TM.next_writes_def
        TM.next_moves_def apply (subst (asm) nth_zip)
            apply auto
      apply (cases "TM.TM.next_move (Abs_TM M') (state
                    ((TM.step (Abs_TM M') ^^ k) (TM.initial_config (Abs_TM M') w)))
                    (heads ((TM.step (Abs_TM M') ^^ k) (TM.initial_config (Abs_TM M') w)))
                    3")
      apply auto
            apply (metis (no_types, lifting) empty_iff insertE list.sel(2) list.set_sel(2)
          option.distinct(1) option.inject subset_code(1))
           apply (metis 1 TM_abbrevs.tape_write_hd option.discI option.inject)
          apply (metis (no_types, opaque_lifting) TM_abbrevs.tape_shift.simps(5) insert_iff
          left_after_write not_None_eq option.inject singleton_iff subset_iff)
         apply (subst (asm) TM.step_def)
      apply (cases "state ((TM.step (Abs_TM M') ^^ k) (TM.initial_config (Abs_TM M') w))
                    \<in> TM.TM.final_states (Abs_TM M')")
           apply auto
          apply (subst (asm) nth_map2)
            apply (simp add: TM.next_actions_simps(2))
           apply (simp add: TM.run_tapes_len)
      unfolding TM.next_actions_def TM_abbrevs.tape_action_def TM.next_writes_def
        TM.next_moves_def apply (subst (asm) nth_zip)
            apply auto
      apply (cases "TM.TM.next_move (Abs_TM M') (state
                    ((TM.step (Abs_TM M') ^^ k) (TM.initial_config (Abs_TM M') w)))
                    (heads ((TM.step (Abs_TM M') ^^ k) (TM.initial_config (Abs_TM M') w)))
                    3")
           apply auto
      apply (metis 1 TM_abbrevs.tape_write_hd option.distinct(1) option.inject)
          apply (metis (no_types, lifting) insertE list.sel(2) list.set_sel(2) option.discI
          option.inject singletonD subset_code(1))
      apply (metis TM_abbrevs.tape_shift.simps(5) emptyE insertE insert_absorb
          insert_subset option.distinct(1) option.inject right_after_write)
        apply (subst (asm) (3) TM.step_def)
      apply (cases "state ((TM.step (Abs_TM M') ^^ k) (TM.initial_config (Abs_TM M') w))
                    \<in> TM.TM.final_states (Abs_TM M')")
         apply auto
        apply (subst (asm) nth_map)
         apply (metis 5 TM.at_least_one_tape TM.run_tapes_len less_add_same_cancel2)
        apply (subst (asm) nth_map)
         apply (simp add: TM.next_actions_simps(2) TM.run_tapes_len)
        apply (subst (asm) nth_zip)
          apply (simp add: TM.next_actions_simps(2))
         apply (simp add: TM.run_tapes_len)
        apply simp
      unfolding TM.next_actions_def TM_abbrevs.tape_action_def TM.next_writes_def
        TM.next_moves_def apply simp
      apply (cases "TM.TM.next_move (Abs_TM M')
              (state ((TM.step (Abs_TM M') ^^ k) (TM.initial_config (Abs_TM M') w)))
              (heads ((TM.step (Abs_TM M') ^^ k) (TM.initial_config (Abs_TM M') w))) 3")
      apply auto
          apply (metis (no_types, lifting) head_in_left_tape head_left_empty insertE
          left_after_write option.distinct(1) option.inject singletonD subset_code(1))
         apply (metis (no_types, opaque_lifting) head_in_right_tape head_right_empty
          insertE option.discI option.inject right_after_write singleton_iff subset_code(1))
      apply (metis 1 TM_abbrevs.tape_shift.simps(5) TM_abbrevs.tape_write_hd option.discI
          option.inject)
       apply (subst (asm) TM.step_def)
      apply (cases "state ((TM.step (Abs_TM M') ^^ k) (TM.initial_config (Abs_TM M') w))
                    \<in> TM.TM.final_states (Abs_TM M')")
        apply auto
       apply (subst (asm) nth_map2)
         apply (simp add: TM.next_actions_simps(2))
        apply (simp add: TM.run_tapes_len)
      unfolding TM.next_actions_def TM.next_writes_def TM.next_moves_def
        TM_abbrevs.tape_action_def apply simp
      apply (cases "TM.TM.next_move (Abs_TM M')
                    (state ((TM.step (Abs_TM M') ^^ k) (TM.initial_config (Abs_TM M') w)))
                    (heads ((TM.step (Abs_TM M') ^^ k) (TM.initial_config (Abs_TM M') w)))
                    3")
         apply auto
         apply (smt (verit, ccfv_threshold) insertE list.set_sel(2) option.discI
          option.inject singletonD subset_iff tl_eqI)
        apply (metis 1 TM_abbrevs.tape_write_hd option.discI option.inject)
       apply (metis TM_abbrevs.tape_shift.simps(5) emptyE insertE insert_absorb
          insert_subset left_after_write option.distinct(1) option.inject)
      apply (subst (asm) TM.step_def)
      apply (cases "state ((TM.step (Abs_TM M') ^^ k) (TM.initial_config (Abs_TM M') w))
                    \<in> TM.TM.final_states (Abs_TM M')")
       apply auto
      apply (subst (asm) nth_map2)
        apply (simp add: TM.next_actions_simps(2))
       apply (simp add: TM.run_tapes_len)
      unfolding TM.next_actions_def TM.next_moves_def TM.next_writes_def
        TM_abbrevs.tape_action_def apply simp
      apply (cases "TM.TM.next_move (Abs_TM M')
                    (state ((TM.step (Abs_TM M') ^^ k) (TM.initial_config (Abs_TM M') w)))
                    (heads ((TM.step (Abs_TM M') ^^ k) (TM.initial_config (Abs_TM M') w)))
                    3")
        apply auto
        apply (metis 1 TM_abbrevs.tape_write_hd option.distinct(1) option.inject)
       apply (metis (no_types, opaque_lifting) insertE list.sel(2) list.set_sel(2)
          option.discI option.inject singleton_iff subset_code(1))
      by (metis TM_abbrevs.tape_shift.simps(5) emptyE insertE insert_absorb insert_subset
          option.distinct(1) option.inject right_after_write)
  qed
  have 24: "heads ((TM.step (Abs_TM M') ^^ k) (TM.initial_config (Abs_TM M') w)) ! 3 =
            Some extra_sym \<Longrightarrow> k > 0" for k :: nat and w :: "'s list"
  proof (rule ccontr, auto)
    assume "heads (TM.initial_config (Abs_TM M') w) ! 3 = Some extra_sym"
    thus False unfolding TM.initial_config_def by simp
  qed
  have 25: "heads ((TM.step (Abs_TM M') ^^ k) (TM.initial_config (Abs_TM M') w)) ! 2 =
            Some extra_sym \<Longrightarrow> k > 0" for k :: nat and w :: "'s list"
  proof (rule ccontr, auto)
    assume "heads (TM.initial_config (Abs_TM M') w) ! 2 = Some extra_sym"
    thus False unfolding TM.initial_config_def by simp
  qed
  have 26: "nth_ctape (ctapes ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w)) ! 2) i \<noteq> None \<Longrightarrow>
            nth_ctape (ctapes ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w)) ! 2) i =
            Some extra_sym" for i :: int and k :: nat and w :: "'s list"
  proof (induction k arbitrary: i)
    case 0
    then show ?case by (simp add: TM.cinitial_config_def)
  next
    case (Suc k)
    obtain q1 and w1 and m1 and b1 where
      cstate_tuple: "cstate ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w)) = (q1, w1, m1, b1)"
      by (rule prod_cases4)
    show ?case using Suc(2) apply auto
      apply (cases "cstate ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w)) \<in>
                    TM.TM.final_states (Abs_TM M')") 
      using Suc(1) [of i] apply (metis TM.cstep_def option.discI option.inject)
      apply (cases "TM.TM.next_move (Abs_TM M') (cstate ((TM.cstep (Abs_TM M') ^^ k)
                    (TM.cinitial_config (Abs_TM M') w)))
                    (cheads ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w))) 2")
        apply (cases "i = 1")
         apply simp
         apply (subst (asm) nth_ctape_cstep_Shift_Left2)
             apply simp_all
      unfolding valid_tm_next_write [OF valid_M'] apply (subst (asm) M'_def)
         apply (simp add: cstate_tuple valid_tm_final_states)
         apply (cases "q1 \<in> TM.TM.final_states M")
          apply simp_all
      using Suc(1) [of 0, unfolded nth_ctape_0] apply simp
        apply (subst (asm) nth_ctape_cstep_Shift_Left1)
             apply simp_all
      using Suc(1) [of "i - 1"] apply simp
       apply (cases "i = -1")
        apply simp
        apply (subst (asm) nth_ctape_cstep_Shift_Right2)
            apply simp_all
      unfolding valid_tm_next_write [OF valid_M'] apply (subst (asm) M'_def)
        apply (simp add: cstate_tuple valid_tm_final_states)
        apply (cases "q1 \<in> TM.TM.final_states M")
         apply simp_all
      using Suc(1) [of 0, unfolded nth_ctape_0] apply simp
       apply (subst (asm) nth_ctape_cstep_Shift_Right1)
            apply simp_all
      using Suc(1) [of "i + 1"] apply simp
      apply (cases "i = 0")
       apply simp
       apply (subst (asm) nth_ctape_cstep_No_Shift2)
           apply simp_all
      unfolding valid_tm_next_write [OF valid_M'] apply (subst (asm) M'_def)
       apply (simp add: cstate_tuple valid_tm_final_states)
       apply (cases "q1 \<in> TM.TM.final_states M")
        apply simp_all
      using Suc(1) [of 0, unfolded nth_ctape_0] apply simp
      apply (subst (asm) nth_ctape_cstep_No_Shift1)
           apply simp_all
      using Suc(1) [of i] by simp
  qed
  have 27: "nth_ctape (ctapes ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w)) ! 3) i \<noteq> None \<Longrightarrow>
            nth_ctape (ctapes ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w)) ! 3) i =
            Some extra_sym" for i :: int and k :: nat and w :: "'s list"
  proof (induction k arbitrary: i)
    case 0
    then show ?case by (simp add: TM.cinitial_config_def)
  next
    case (Suc k)
    obtain q' and w' and m' and b' where
      cstate_tuple: "cstate ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w)) = (q', w', m', b')"
      by (rule prod_cases4)
    show ?case using Suc(2) apply auto
      apply (cases "cstate ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w)) \<in>
                    TM.TM.final_states (Abs_TM M')")
      using Suc apply (metis TM.cstep_def option.discI option.inject)
      apply (cases "TM.TM.next_move (Abs_TM M') (cstate ((TM.cstep (Abs_TM M') ^^ k)
                    (TM.cinitial_config (Abs_TM M') w)))
                    (cheads ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w))) 3")
        apply (cases "i = 1")
         apply simp
         apply (subst (asm) nth_ctape_cstep_Shift_Left2)
             apply simp_all
      unfolding valid_tm_next_write [OF valid_M'] apply (subst (asm) M'_def)
         apply (simp add: cstate_tuple)
         apply (cases "w' = []")
          apply simp_all
      using Suc(1) [of 0, unfolded nth_ctape_0] apply simp
        apply (subst (asm) nth_ctape_cstep_Shift_Left1)
             apply simp_all
      using Suc(1) [of "i - 1"] apply simp
       apply (cases "i = -1")
        apply simp
        apply (subst (asm) nth_ctape_cstep_Shift_Right2)
            apply simp_all
      unfolding valid_tm_next_write [OF valid_M'] apply (subst (asm) M'_def)
        apply (simp add: cstate_tuple)
        apply (cases "w' = []")
         apply simp_all
      using Suc(1) [of 0, unfolded nth_ctape_0] apply simp
       apply (subst (asm) nth_ctape_cstep_Shift_Right1)
            apply simp_all
      using Suc(1) [of "i + 1"] apply simp
      apply (cases "i = 0")
       apply simp
       apply (subst (asm) nth_ctape_cstep_No_Shift2)
           apply simp_all
      unfolding valid_tm_next_write [OF valid_M'] apply (subst (asm) M'_def)
       apply (simp add: cstate_tuple)
       apply (cases "w' = []")
        apply simp_all
      using Suc(1) [of 0, unfolded nth_ctape_0] apply simp
      apply (subst (asm) nth_ctape_cstep_No_Shift1)
           apply simp_all
      using Suc(1) [of i] by simp
  qed
  have f101: "cstate (TM.csteps (Abs_TM M') k (TM.cinitial_config (Abs_TM M') w)) =
              (cstate (TM.csteps M k (TM.cinitial_config M w)), take k ((map Some w) @ [None]),
              nat (cell_index (Abs_TM M') w 3 k), False)" and
       f102: "\<And>i. i \<ge> 4 \<Longrightarrow> i < TM.tape_count (Abs_TM M') \<Longrightarrow>
              ctapes (TM.csteps (Abs_TM M') k (TM.cinitial_config (Abs_TM M') w)) ! i =
              ctapes (TM.csteps M k (TM.cinitial_config M w)) ! (i - 3)" and
       f103: "\<And>i j. nth_ctape (ctapes (TM.csteps (Abs_TM M') k
              (TM.cinitial_config (Abs_TM M') w)) ! 3) i = Some extra_sym \<Longrightarrow>
              nth_ctape (ctapes (TM.csteps (Abs_TM M') k
              (TM.cinitial_config (Abs_TM M') w)) ! 3) j = Some extra_sym \<Longrightarrow> i = j" and
       f104: "\<And>i. nth_ctape (ctapes (TM.csteps (Abs_TM M') k
              (TM.cinitial_config (Abs_TM M') w)) ! 0) i =
              nth_ctape (ctapes (TM.cinitial_config (Abs_TM M') w) ! 0) (i + cell_index (Abs_TM M') w 0 k)" and
       f105: "\<And>i. nth_ctape (ctapes (TM.csteps (Abs_TM M') k
              (TM.cinitial_config (Abs_TM M') w)) ! 2) i \<noteq> None \<Longrightarrow> nth_ctape (ctapes (TM.csteps (Abs_TM M') k
              (TM.cinitial_config (Abs_TM M') w)) ! 1) i = nth_ctape (ctapes (TM.csteps M k
              (TM.cinitial_config M w)) ! 0) i" and
       f106: "k > 0 \<Longrightarrow> nth_ctape (ctapes (TM.csteps (Abs_TM M') k
              (TM.cinitial_config (Abs_TM M') w)) ! 3) (-cell_index (Abs_TM M') w 3 k) = Some extra_sym" and
       f107: "\<And>k'. k' > 0 \<Longrightarrow> k' \<le> k \<Longrightarrow> cstate (TM.csteps M k' (TM.cinitial_config M w)) \<in> TM.final_states M \<Longrightarrow>
              tl (ctapes (TM.csteps (Abs_TM M') k (TM.cinitial_config (Abs_TM M') w))) =
              tl (ctapes (TM.csteps (Abs_TM M') k' (TM.cinitial_config (Abs_TM M') w)))" and
       f108: "cstate (TM.csteps M k (TM.cinitial_config M w)) \<notin> TM.final_states M \<Longrightarrow>
              chead (ctapes (TM.csteps (Abs_TM M') k (TM.cinitial_config (Abs_TM M') w)) ! 3) = Some extra_sym \<longleftrightarrow>
              cell_index M w 0 k = 0 \<and> k > 0" and
       f109: "cell_index (Abs_TM M') w 0 k = k" and
       f110: "cstate ((TM.cstep M ^^ (k - 1)) (TM.cinitial_config M w)) \<notin> TM.TM.final_states M \<Longrightarrow>
              cell_index (Abs_TM M') w 3 k = cell_index M w 0 k" and
       f111: "\<And>i. 0 < k \<Longrightarrow> cstate ((TM.cstep M ^^ k) (TM.cinitial_config M w)) \<notin> TM.TM.final_states M \<Longrightarrow>
              i \<le> max_cell_index (Abs_TM M') w 3 (k - 1) - cell_index (Abs_TM M') w 3 k \<Longrightarrow>
              i \<ge> min_cell_index (Abs_TM M') w 3 (k - 1) - cell_index (Abs_TM M') w 3 k \<Longrightarrow>
              nth_ctape (ctapes (TM.csteps (Abs_TM M') k (TM.cinitial_config (Abs_TM M') w)) ! 2) i = Some extra_sym"
       if "k \<le> n" and "k \<le> Suc (length w)" for k :: nat and w :: "'s list" using that
  proof (induction k rule: full_nat_induct3)
    case 0
    {
      case 1
      then show ?case apply (simp add: TM.cinitial_config_def valid_tm_initial_state)
        by (simp add: M'_def init_state_def)
    next
      case 2
      then show ?case by (simp add: TM.cinitial_config_def TM_abbrevs.cinput_tape_def)
    next
      case 3
      then show ?case by (simp add: TM.cinitial_config_def)
    next
      case 4
      then show ?case by simp
    next
      case 5
      then show ?case by (simp add: TM.cinitial_config_def)
    next
      case 6
      then show ?case by simp
    next
      case 7
      then show ?case by simp
    next
      case 8
      then show ?case by (simp add: TM.cinitial_config_def empty_ctape_def)
    next
      case 9
      then show ?case by simp
    next
      case 10
      then show ?case by simp
    next
      case 11
      then show ?case by simp
    }
  next
    case (le_Suc k)
    note Suc = le_Suc [OF Nat.le_refl]
    have original_hds_spec: "k \<le> n \<Longrightarrow> k \<le> Suc (length w) \<Longrightarrow>
                             original_hds (cheads ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w)))
                             (take k (map Some w) @ take (k - length w) [None]) (nat (cell_index (Abs_TM M') w 3 k)) =
                             cheads ((TM.cstep M ^^ k) (TM.cinitial_config M w))"
    proof -
      assume *: "k \<le> n" and **: "k \<le> Suc (length w)"
      have 1: "original_hds (cheads ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w)))
               (take k (map Some w) @ take (k - length w) [None]) (nat (cell_index (Abs_TM M') w 3 k)) ! 0 =
               chead (ctapes ((TM.cstep M ^^ k) (TM.cinitial_config M w)) ! 0)"
        unfolding original_hds_def apply auto
      proof -
        fix y :: 's
        assume a1: "chead (ctapes ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w)) ! 2) = Some y"
        show "hd (tl (cheads ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w)))) =
              chead (ctapes ((TM.cstep M ^^ k) (TM.cinitial_config M w)) ! 0)"
          apply (subst zeroth_is_head [symmetric])
           apply auto
           apply (drule arg_cong [where f=length])
           apply simp
          apply (subst nth_tl)
           apply simp
          apply (subst nth_map)
           apply simp
          using Suc(5) [simplified, OF exI * **, of 0, unfolded nth_ctape_0, OF a1] .
        thus "hd (tl (cheads ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w)))) =
              chead (ctapes ((TM.cstep M ^^ k) (TM.cinitial_config M w)) ! 0)" .
        thus "hd (tl (cheads ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w)))) =
              chead (ctapes ((TM.cstep M ^^ k) (TM.cinitial_config M w)) ! 0)" .
        thus "hd (tl (cheads ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w)))) =
              chead (ctapes ((TM.cstep M ^^ k) (TM.cinitial_config M w)) ! 0)" .
        thus "hd (tl (cheads ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w)))) =
              chead (ctapes ((TM.cstep M ^^ k) (TM.cinitial_config M w)) ! 0)" .
        thus "hd (tl (cheads ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w)))) =
              chead (ctapes ((TM.cstep M ^^ k) (TM.cinitial_config M w)) ! 0)" .
      next
        assume a1: "min (length w) k + min (Suc 0) (k - length w) \<le> nat (cell_index (Abs_TM M') w 3 k)"
        have 1: "cell_index (Abs_TM M') w 3 k = k"
          using a1 * ** cell_index_abs_bound [of "Abs_TM M'" w 3 k] by auto
        show "hd (cheads ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w))) =
              chead (ctapes ((TM.cstep M ^^ k) (TM.cinitial_config M w)) ! 0)"
        proof (cases "k = 0")
          case True
          then show ?thesis by (simp add: TM.cinitial_config_def)
        next
          case False
          hence 2: "k = Suc (k - 1)" by simp
          have 3: "cell_index (Abs_TM M') w 3 (k - 1) = k - 1"
            using 1 2 cell_index_eq_steps_all_lower_eq suc_is_ge by blast
          have 4: "TM.next_move (Abs_TM M') (cstate (TM.csteps (Abs_TM M') (k - 1)
                   (TM.cinitial_config (Abs_TM M') w))) (cheads (TM.csteps (Abs_TM M') (k - 1)
                   (TM.cinitial_config (Abs_TM M') w))) 3 = Shift_Right"
            apply (cases "TM.next_move (Abs_TM M') (cstate (TM.csteps (Abs_TM M') (k - 1)
                          (TM.cinitial_config (Abs_TM M') w))) (cheads (TM.csteps (Abs_TM M') (k - 1)
                          (TM.cinitial_config (Abs_TM M') w))) 3")
            using 1 apply (subst (asm) (3 4) 2)
              apply (subst (asm) cell_index.simps(2))
               apply (simp add: cotm_heads_steps_congruence cotm_steps_congruences(1))
            using 3 apply simp
             apply assumption
            using 1 apply (subst (asm) (3 4) 2)
            apply (subst (asm) cell_index.simps(4))
             apply (simp add: cotm_heads_steps_congruence cotm_steps_congruences(1))
            using 3 by simp
          have 5: "cstate (TM.csteps M (k - 1) (TM.cinitial_config M w)) \<notin> TM.final_states M"
            apply standard
            using 4 unfolding valid_tm_next_move [OF valid_M'] apply (subst (asm) le_Suc(1) [of "k - 1"])
               apply simp
            using * apply simp
            using ** apply simp
            apply (subst (asm) M'_def)
            by simp
          note 6 = le_Suc(10) [OF le_refl 5 * **, unfolded 1, symmetric]
          have 7: "cell_index M w 0 (k - 1) = k - 1" using 6 cell_index_eq_steps_all_lower_eq diff_le_self by blast
          have 8: "TM.next_move M (cstate (TM.csteps M (k - 1) (TM.cinitial_config M w))) (cheads (TM.csteps M (k - 1)
                   (TM.cinitial_config M w))) 0 = Shift_Right"
            using 6 apply (subst (asm) (1 2) 2)
            apply (cases "TM.next_move M (cstate (TM.csteps M (k - 1)
                          (TM.cinitial_config M w))) (cheads (TM.csteps M (k - 1) (TM.cinitial_config M w))) 0")
              apply (subst (asm) cell_index.simps(2))
               apply (simp add: cotm_heads_steps_congruence cotm_steps_congruences(1))
            using 7 apply simp
             apply assumption
            apply (subst (asm) (3 4) 2)
            apply (subst (asm) cell_index.simps(4))
             apply (simp add: cotm_heads_steps_congruence cotm_steps_congruences(1))
            using 7 by simp
          note 9 = csteps_untouched_cells_head [of 0, simplified, unfolded TM.cis_final_def,
              OF 5 [simplified] 6 [symmetric] False [simplified]]
          have 10: "cstate (TM.csteps (Abs_TM M') (k - 1) (TM.cinitial_config (Abs_TM M') w)) \<notin>
                    TM.final_states (Abs_TM M')" apply (subst le_Suc(1) [of "k - 1"])
               apply simp
            using * apply simp
            using ** apply simp
            unfolding valid_tm_final_states [OF valid_M'] 3 unfolding M'_def apply simp
            unfolding final_states_def using 5 * ** apply auto
            apply (rule ccontr)
            by (simp add: last_map take_map)
          note 11 = csteps_untouched_cells_head [of 0, simplified, unfolded TM.cis_final_def,
              OF 10 [simplified] Suc(9) [OF * **, symmetric] False [simplified]]
          show ?thesis apply (subst zeroth_is_head [symmetric])
             apply auto
             apply (drule arg_cong [where f=length])
             apply simp
            unfolding 9 11 unfolding TM.cinitial_config_def TM_abbrevs.cinput_tape_def by simp
        qed
      next
        assume a1: "0 < cell_index (Abs_TM M') w 3 k" and
               a2: "\<not> min (length w) k + min (Suc 0) (k - length w) \<le> nat (cell_index (Abs_TM M') w 3 k)" and
               a3: "chead (ctapes ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w)) ! 2) = None"
        have 1: "k = 0 \<Longrightarrow> False"
          using a1 by simp
        hence 2: "k > 0" by blast
        have 3: "k' \<le> k \<Longrightarrow> cstate (TM.csteps M (k - k') (TM.cinitial_config M w)) \<in> TM.final_states M \<Longrightarrow>
                 cell_index (Abs_TM M') w 3 k = cell_index (Abs_TM M') w 3 (k - k')" for k' :: nat
        proof (induction k')
          case 0
          show ?case by simp
        next
          case (Suc k')
          have 1: "k' \<le> k" using Suc(2) by simp
          have 2: "cstate ((TM.cstep M ^^ (k - k')) (TM.cinitial_config M w)) \<in> TM.TM.final_states M"
            using Suc(3) unfolding TM.cis_final_def [symmetric]
            by (metis (no_types, lifting) add.commute cis_final_sub_imp diff_diff_left plus_1_eq_Suc)
          note 3 = Suc(1) [OF 1 2]
          have 4: "k - k' = Suc (k - Suc k')" using Suc(2) by force
          show ?case unfolding 3 4 apply (subst cell_index.simps(4))
            unfolding cotm_steps_congruences(1) [symmetric] cotm_heads_steps_congruence [symmetric]
            unfolding valid_tm_next_move [OF valid_M'] apply (subst le_Suc(1) [of "k - Suc k'"])
            using * ** apply simp_all
            apply (subst M'_def)
            using Suc(3) by simp
        qed
        note 4 = 3 [OF le_refl, simplified]
        note Suc(11) [OF 2]
        show "(take k (map Some w) @ take (k - length w) [None]) ! nat (cell_index (Abs_TM M') w 3 k) =
              chead (ctapes ((TM.cstep M ^^ k) (TM.cinitial_config M w)) ! 0)"
        proof (cases "cstate (TM.cinitial_config M w) \<in> TM.TM.final_states M")
          case True
          note 5 = 4 [OF True]
          have 6: "(TM.cstep M ^^ k) (TM.cinitial_config M w) = TM.cinitial_config M w"
            using True by (simp add: TM.cstep_def funpow_fixpoint)
          show ?thesis unfolding 5 6 unfolding TM.cinitial_config_def TM_abbrevs.cinput_tape_def apply auto
            unfolding empty_ctape_def using 2 apply simp_all
            by (simp add: hd_conv_nth)
        next
          case False
          show ?thesis
          proof (cases "cstate ((TM.cstep M ^^ k) (TM.cinitial_config M w)) \<in> TM.TM.final_states M")
            case True
            define k' :: nat where "k' \<equiv> (LEAST k'. cstate ((TM.cstep M ^^ k') (TM.cinitial_config M w)) \<in>
                                    TM.TM.final_states M) - 1"
            note 5 = LeastI [of "\<lambda>k. cstate ((TM.cstep M ^^ k) (TM.cinitial_config M w)) \<in> TM.TM.final_states M",
                OF True, folded TM.cis_final_def]
            have 6: "cstate ((TM.cstep M ^^ k') (TM.cinitial_config M w)) \<notin> TM.TM.final_states M"
              apply standard
              by (metis (no_types, lifting) False One_nat_def diff_Suc_Suc diff_is_0_eq diff_zero funpow_0 k'_def
                  lessI list_decode.cases nat_le_linear not_less_Least)
            have 7: "cstate ((TM.cstep M ^^ (Suc k')) (TM.cinitial_config M w)) \<in> TM.TM.final_states M"
              unfolding k'_def using 5 unfolding TM.cis_final_def [symmetric]
              by (smt (verit, del_insts) False Least_Suc One_nat_def Suc_diff_Suc TM.cis_final_def diff_zero funpow_0
                  zero_less_Suc)
            have 8: "k' \<le> k" using True 6 unfolding TM.cis_final_def [symmetric]
              by (metis (no_types, lifting) True diff_le_self k'_def le_trans linorder_not_le not_less_Least)
            have "k' = k \<Longrightarrow> False" using True 6 by simp
            hence 9: "k' < k" using 8 by force
            have 10: "k2 \<le> k - Suc k' \<Longrightarrow> cell_index (Abs_TM M') w 3 k = cell_index (Abs_TM M') w 3 (k - k2)"
              for k2 :: nat using 9 7
            proof (induction k2)
              case 0
              then show ?case by simp
            next
              case (Suc k2)
              have 1: "k2 \<le> k - Suc k'" using Suc(2) by simp
              note 2 = Suc(1) [OF 1 Suc(3, 4)]
              have 3: "k - k2 = Suc (k - Suc k2)" using Suc by linarith
              have 4: "k - Suc k2 \<ge> Suc k'" using Suc(2) by linarith
              show ?case unfolding 2 3 apply (subst cell_index.simps(4))
                unfolding cotm_heads_steps_congruence [symmetric] cotm_steps_congruences(1) [symmetric]
                 apply (subst le_Suc(1))
                    apply simp
                using * apply simp
                using ** apply simp
                unfolding valid_tm_next_move [OF valid_M'] apply (subst M'_def)
                 apply auto
                using Suc(4) 4 unfolding TM.cis_final_def [symmetric] by (metis cis_final_sub_imp diff_diff_cancel)
            qed
            note 10 [OF le_refl]
            hence 11: "cell_index (Abs_TM M') w 3 k = cell_index (Abs_TM M') w 3 (Suc k')"
              using 9 by fastforce
            have 12: "(TM.cstep M ^^ k) (TM.cinitial_config M w) = (TM.cstep M ^^ (Suc k')) (TM.cinitial_config M w)"
              apply (rule cis_final_csteps_stay_eq)
              using 9 apply simp
              unfolding TM.cis_final_def by fact
            note Suc(7) [OF zero_less_Suc 9 [THEN Suc_leI] 7 * **]
            hence 13: "ctapes ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w)) ! 2 =
                       ctapes ((TM.cstep (Abs_TM M') ^^ (Suc k')) (TM.cinitial_config (Abs_TM M') w)) ! 2"
              by (metis (no_types, lifting) M'_def One_nat_def add_Suc_right diff_Suc_1' length_ctapes_csteps_eq_tc
                  length_tl less_add_Suc2 nth_tl numeral_2_eq_2 numeral_3_eq_3 simps(1) valid_M' valid_tm_tape_count)
            note 14 = a3 [unfolded 13]
            have 15: "k' \<le> n" using * 9 by simp
            have 16: "k' \<le> Suc (length w)" using ** 9 by simp
            have 17: "cstate ((TM.cstep (Abs_TM M') ^^ k') (TM.cinitial_config (Abs_TM M') w)) \<notin>
                      TM.TM.final_states (Abs_TM M')"
              using * ** 9 apply (simp add: le_Suc(1) [of k'])
              unfolding valid_tm_final_states [OF valid_M'] apply (subst (2) M'_def)
              apply simp
              unfolding final_states_def apply auto
              apply (rule ccontr)
              using cell_index_abs_bound [of "Abs_TM M'" w 3 k'] 9
              by (metis take_eq_Nil option.distinct(1) bot_nat_0.not_eq_extremum take_map last_map)
            have 18: "- 1 \<le> max_cell_index (Abs_TM M') w 3 (k' - 1) - cell_index (Abs_TM M') w 3 k'"
              apply (cases k')
               apply simp_all
              apply (cases "max_cell_index (Abs_TM M') w 3 (k' - Suc 0) = max_cell_index (Abs_TM M') w 3 k'")
               apply simp_all
               apply (smt (verit, ccfv_SIG) max_cell_index_ge_cell_index)
              by (smt (verit, ccfv_threshold) max_cell_index_Suc2 max_cell_index_ge_cell_index)
            have 19: "0 < cell_index (Abs_TM M') w 3 k' \<Longrightarrow>
                      min_cell_index (Abs_TM M') w 3 (k' - 1) - cell_index (Abs_TM M') w 3 k' \<le> - 1"
              by (smt (verit, best) min_cell_index_le_0)
            have 20: "cell_index (Abs_TM M') w 3 k2 = cell_index M w 0 k2" if "k2 \<le> Suc k'" for k2 :: nat
              using le_Suc(10) [of k2] that 6 * ** 9 unfolding TM.cis_final_def [symmetric] apply simp
              by (smt (verit, del_insts) False Least_Suc One_nat_def TM.cis_final_def cis_final_sub_imp
                  diff_Suc_1 funpow_0 k'_def le_eq_less_or_eq not_less_Least)
            have 21: "TM.TM.next_move (Abs_TM M') (cstate ((TM.cstep (Abs_TM M') ^^ k')
                      (TM.cinitial_config (Abs_TM M') w)))
                      (cheads ((TM.cstep (Abs_TM M') ^^ k') (TM.cinitial_config (Abs_TM M') w))) 3 =
                      TM.TM.next_move M (cstate ((TM.cstep M ^^ k') (TM.cinitial_config M w)))
                      (cheads ((TM.cstep M ^^ k') (TM.cinitial_config M w))) 0"
              unfolding cotm_steps_congruences(1) cotm_heads_steps_congruence
              apply (rule cell_index_eq_next_moves_eq' [where k="Suc k'"])
               apply (erule 20)
              by simp
            have 22: "min_cell_index (Abs_TM M') w 3 (k' - Suc 0) - cell_index (Abs_TM M') w 3 k' \<le> 1"
              using a1 [unfolded 11] min_cell_index_le_0 [of "Abs_TM M'" w 3 "k' - Suc 0"]
              apply (cases "TM.TM.next_move (Abs_TM M') (state ((TM.step (Abs_TM M') ^^ k')
                            (TM.initial_config (Abs_TM M') w)))
                            (heads ((TM.step (Abs_TM M') ^^ k') (TM.initial_config (Abs_TM M') w))) 3")
              by simp_all
            have 23: "cell_index M w 0 k2 = cell_index (Abs_TM M') w 3 k2" if "k2 \<le> k'" for k2 :: nat
              using le_Suc(10) [of k2] 6 unfolding TM.cis_final_def [symmetric] using 15 16
              by (metis 20 le_Suc_eq that)
            have "{ci. \<exists>n\<le>k'. cell_index M w 0 n = ci} = {ci. \<exists>n\<le>k'. cell_index (Abs_TM M') w 3 n = ci}"
              using 23 by auto
            hence 24: "max_cell_index M w 0 k' = max_cell_index (Abs_TM M') w 3 k'"
              unfolding max_cell_index_def by simp
            have 25: "\<not> max_cell_index (Abs_TM M') w 3 k' \<le> cell_index (Abs_TM M') w 3 k' \<Longrightarrow>
                      max_cell_index (Abs_TM M') w 3 k' = max_cell_index (Abs_TM M') w 3 (k' - 1)"
              apply (cases k')
               apply auto
              by (smt (verit) max_cell_index_Suc1 max_cell_index_Suc2)
            have "cell_index (Abs_TM M') w 3 k \<noteq> k"
              using a2 by fastforce
            hence 26: "cell_index (Abs_TM M') w 3 k < k"
              using cell_index_abs_bound [of "Abs_TM M'" w 3 k] by simp
            show ?thesis unfolding 11 12 using 14 a1 [unfolded 11] apply simp
              unfolding nth_ctape_0 [symmetric]
              apply (cases "TM.TM.next_move (Abs_TM M') (cstate ((TM.cstep (Abs_TM M') ^^ k')
                            (TM.cinitial_config (Abs_TM M') w)))
                            (cheads ((TM.cstep (Abs_TM M') ^^ k') (TM.cinitial_config (Abs_TM M') w))) 3")
                apply (subst (asm) cell_index.simps(2))
                 apply (simp add: cotm_heads_steps_congruence cotm_steps_congruences(1))
                apply (subst (asm) nth_ctape_cstep_Shift_Left1)
                     apply simp_all
              using * ** 9 apply (simp add: valid_tm_next_move le_Suc(1) [of k'])
                  apply (subst M'_def)
                  apply (subst (asm) (2) M'_def)
                  apply simp
                 apply (rule 17)
                apply (cases "k' = 0")
                 apply simp_all
              using le_Suc(11) [OF 8 _ 6 _ _ 15 16, of "-1", OF _ 18 19] apply force
               apply (subst cell_index.simps(3))
                apply (simp add: cotm_heads_steps_congruence cotm_steps_congruences(1))
               apply (subst nth_ctape_cstep_Shift_Right1)
                    apply simp_all
                 apply (simp only: 21)
                apply (rule 6)
               apply (subst (asm) nth_ctape_cstep_Shift_Right1)
                    apply simp_all
                 apply (simp add: valid_tm_next_move)
              using le_Suc(1) [of k'] 9 * ** apply simp
                 apply (subst M'_def)
                 apply (subst (asm) (2) M'_def)
                 apply simp
                apply (rule 17)
               apply (subst (asm) cell_index.simps(3))
                apply (simp add: cotm_heads_steps_congruence cotm_steps_congruences(1))
               apply simp
               apply (cases "k' = 0")
                apply simp_all
                apply (auto simp add: TM.cinitial_config_def TM_abbrevs.cinput_tape_def)[1]
              using 9 ** apply simp
              using a1 a2 apply fastforce
                apply (subst nth_ctape_pos)
                 apply simp
                apply (subst nth_append)
                apply (auto simp del: zeroth_clist_is_chd)
                  apply (subst prepend_list_nth_less)
                   apply simp
                  apply simp
                  apply (metis list.collapse nth_Cons_Suc)
                 apply (subst prepend_list_nth_ge)
                  apply simp_all
                 apply (subst nth_take)
              using a1 a2 apply linarith
              using 2 less_eq_Suc_le apply auto[1]
              using a1 a2 apply linarith
               apply (subst nth_ctape_pos)
                apply simp
               apply (subst csteps_untouched_cells_right2)
                   apply simp_all
              using 6 unfolding TM.cis_final_def [symmetric]
              using cis_final_sub_imp apply blast
              unfolding 24 23 [OF le_refl] apply (rule ccontr)
              using le_Suc(11) [of k', OF _ _ 6, of 1] 15 16 9 22 25 apply simp
                apply assumption
               apply (subst TM.cinitial_config_def)
              unfolding TM_abbrevs.cinput_tape_def apply (auto simp add: empty_ctape_def)
                apply (subst nth_take)
                 apply (metis 9 ** le_Suc_eq 8 linorder_not_less bot_nat_0.not_eq_extremum length_greater_0_conv)
              using ** 9 cell_index_abs_bound [of "Abs_TM M'" w 3 k'] apply simp
               apply (auto simp add: nth_append)[1]
                 apply (subst prepend_list_nth_less)
                  apply auto
                 apply (subst nth_tl)
                  apply simp_all
                 apply (simp add: Suc_nat_eq_nat_zadd1 add.commute)
                apply (subst prepend_list_nth_ge)
                 apply simp_all
                apply (subst nth_take)
              using ** 9 cell_index_abs_bound [of "Abs_TM M'" w 3 k'] apply simp
              using 26 [unfolded 11] apply (subst (asm) cell_index.simps(3))
                  apply (simp add: cotm_heads_steps_congruence cotm_steps_congruences(1))
                 apply force
              using 26 [unfolded 11] apply (subst (asm) cell_index.simps(3))
                 apply (simp add: cotm_heads_steps_congruence cotm_steps_congruences(1))
              using ** apply force
               apply (subst nth_take)
              using 26 [unfolded 11] apply (subst (asm) cell_index.simps(3))
                 apply (simp add: cotm_heads_steps_congruence cotm_steps_congruences(1))
                apply fastforce
              using 26 [unfolded 11] apply (subst (asm) cell_index.simps(3))
                apply (simp add: cotm_heads_steps_congruence cotm_steps_congruences(1))
               apply simp
              apply (subst (asm) cell_index.simps(4))
               apply (simp add: cotm_heads_steps_congruence cotm_steps_congruences(1))
              apply (subst cell_index.simps(4))
               apply (simp add: cotm_heads_steps_congruence cotm_steps_congruences(1))
              apply (subst (asm) nth_ctape_cstep_No_Shift2)
                  apply simp_all
                apply (simp add: valid_tm_next_move)
              using le_Suc(1) [of k'] 9 * ** apply simp
                apply (subst M'_def)
                apply (subst (asm) (2) M'_def)
                apply simp
               apply (rule 17)
              unfolding valid_tm_next_write [OF valid_M'] using le_Suc(1) [of k'] 9 * ** apply simp
              apply (subst (asm) M'_def)
              using 6 by simp
          next
            case False
            have 5: "cell_index (Abs_TM M') w 3 k \<noteq> k"
              using a2 by force
            have 6: "cell_index (Abs_TM M') w 3 k < k"
              using 5 cell_index_abs_bound [of "Abs_TM M'" w 3 k] by simp
            have 7: "min_cell_index (Abs_TM M') w 3 (k - 1) - cell_index (Abs_TM M') w 3 k \<le> 0"
              using a1 by (smt (verit, best) min_cell_index_le_0)
            have 8: "cell_index (Abs_TM M') w 3 k > max_cell_index (Abs_TM M') w 3 (k - 1)"
              using Suc(11) [OF 2 False _ _ * **, of 0, OF _ 7] a3 unfolding nth_ctape_0 by fastforce
            have 9: "max_cell_index (Abs_TM M') w 3 k = cell_index (Abs_TM M') w 3 k" using 8
              apply (cases k)
               apply simp_all
              by (smt (verit, ccfv_SIG) max_cell_index_Suc2 max_cell_index_ge_cell_index)
            have 10: "max_cell_index (Abs_TM M') w 3 (k - 1) = cell_index (Abs_TM M') w 3 (k - 1)"
              apply (cases k)
               apply simp_all
              by (metis 8 9 One_nat_def diff_Suc_1' max_cell_index_Suc_gt_impl_eq_cell_index)
            have 11: "cell_index (Abs_TM M') w 3 k' = cell_index M w 0 k'" if "k' \<le> k" for k' :: nat
              apply (rule le_Suc(10) [OF that _])
              using False unfolding TM.cis_final_def [symmetric]
                apply (metis cis_final_csteps_stay_eq cis_final_sub_imp that)
              using * ** that by simp_all
            have 12: "max_cell_index (Abs_TM M') w 3 k' = max_cell_index M w 0 k'" if "k' \<le> k" for k' :: nat
              apply (rule max_cell_index_eq_from_cell_index_eqs)
               apply (erule 11)
              by fact
            show ?thesis apply (subst csteps_untouched_cells_head2_right)
                  apply simp
              using False unfolding TM.cis_final_def using TM.cis_final_def cis_final_sub_imp apply blast
                apply (subst Suc(10) [OF _ * **, symmetric])
              using False unfolding TM.cis_final_def using TM.cis_final_def cis_final_sub_imp apply blast
                apply (subst 12 [symmetric])
                 apply simp
                apply (rule 8)
               apply (rule 2)
              unfolding TM.cinitial_config_def TM_abbrevs.cinput_tape_def apply (auto simp add: empty_ctape_def)
               apply (subst nth_take)
                apply (metis ** 2 One_nat_def Suc_eq_plus1 a2 diff_zero gr0_conv_Suc le_add2 length_take
                  list.size(3) min.idem not_less_eq_eq old.nat.exhaust take_eq_Nil)
              using a2 apply force
              unfolding nth_append apply auto
                apply (subst prepend_list_nth_less)
                 apply simp
              using a1 6 unfolding 11 [OF le_refl, symmetric] apply simp
                apply (subst nth_map)
              using a1 6 unfolding 11 [OF le_refl, symmetric] apply simp
              using a1 apply simp
                apply (subst nth_tl)
              using a1 6 unfolding 11 [OF le_refl, symmetric] apply simp
                apply simp
               apply (subst nth_take)
              using a2 apply linarith
              using 6 ** apply simp
               apply (subst prepend_list_nth_ge)
                apply simp_all
              using 6 2 by simp
          qed
        qed
      next
        fix y y' :: 's
        assume a1: "chead (ctapes (TM.cinitial_config (Abs_TM M') w) ! 3) = Some y"
        have 1: False using a1 unfolding TM.cinitial_config_def TM_abbrevs.cinput_tape_def empty_ctape_def by simp
        show "hd (tl (cheads (TM.cinitial_config (Abs_TM M') w))) = chead (ctapes (TM.cinitial_config M w) ! 0)"
          using 1 ..
        show "hd (cheads (TM.cinitial_config (Abs_TM M') w)) = chead (ctapes (TM.cinitial_config M w) ! 0)"
          using 1 ..
      next
        fix y :: 's
        assume a1: "cell_index (Abs_TM M') w 3 k \<le> 0" and
               a2: "chead (ctapes ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w)) ! 3) = Some y" and
               a3: "w \<noteq> []" and a4: "0 < k" and
               a5: "chead (ctapes ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w)) ! 2) = None"
        have 0 [simp]: "y = extra_sym" using 21 [THEN conjunct1, THEN iffD1, simplified, OF exI,
              folded cotm_heads_steps_congruence, of k w] a2 by simp
        have 1: "cell_index (Abs_TM M') w 3 k = 0"
          using Suc(3) [OF Suc(6) [OF a4 * **] a2 [folded nth_ctape_0, simplified] * **] by simp
        have 2: "0 \<le> max_cell_index (Abs_TM M') w 3 (k - 1) - cell_index (Abs_TM M') w 3 k"
          using a1 by (simp add: 1 max_cell_index_ge_0)
        note 3 = Suc(11) [OF a4, of 0, OF _ 2 _ * **, unfolded 1, simplified]
        show "Some (w ! 0) = chead (ctapes ((TM.cstep M ^^ k) (TM.cinitial_config M w)) ! 0)"
        proof (cases "cstate (TM.cinitial_config M w) \<in> TM.final_states M")
          case True
          have 4: "(TM.cstep M ^^ k) (TM.cinitial_config M w) = TM.cinitial_config M w" using True
            by (simp add: TM.cstep_def funpow_fixpoint)
          show ?thesis unfolding 4 unfolding TM.cinitial_config_def TM_abbrevs.cinput_tape_def
            using zeroth_is_head a3 by auto
        next
          case False
          show ?thesis
          proof (cases "cstate (TM.csteps M k (TM.cinitial_config M w)) \<in> TM.final_states M")
            case True
            define k' :: nat where "k' \<equiv> (LEAST k'. cstate ((TM.cstep M ^^ k') (TM.cinitial_config M w)) \<in>
                                    TM.TM.final_states M) - 1"
            note 5 = LeastI [of "\<lambda>k. cstate ((TM.cstep M ^^ k) (TM.cinitial_config M w)) \<in> TM.TM.final_states M",
                OF True, folded TM.cis_final_def]
            have 6: "cstate ((TM.cstep M ^^ k') (TM.cinitial_config M w)) \<notin> TM.TM.final_states M"
              apply standard
              by (metis (no_types, lifting) False One_nat_def diff_Suc_Suc diff_is_0_eq diff_zero funpow_0 k'_def
                  lessI list_decode.cases nat_le_linear not_less_Least)
            have 7: "cstate ((TM.cstep M ^^ (Suc k')) (TM.cinitial_config M w)) \<in> TM.TM.final_states M"
              unfolding k'_def using 5 unfolding TM.cis_final_def [symmetric]
              by (smt (verit, del_insts) False Least_Suc One_nat_def Suc_diff_Suc TM.cis_final_def diff_zero funpow_0
                  zero_less_Suc)
            have 8: "k' \<le> k" using True 6 unfolding TM.cis_final_def [symmetric]
              by (metis (no_types, lifting) True diff_le_self k'_def le_trans linorder_not_le not_less_Least)
            have "k' = k \<Longrightarrow> False" using True 6 by simp
            hence 9: "k' < k" using 8 by force
            have 10: "k2 \<le> k - Suc k' \<Longrightarrow> cell_index (Abs_TM M') w 3 k = cell_index (Abs_TM M') w 3 (k - k2)"
              for k2 :: nat using 9 7
            proof (induction k2)
              case 0
              then show ?case by simp
            next
              case (Suc k2)
              have 1: "k2 \<le> k - Suc k'" using Suc(2) by simp
              note 2 = Suc(1) [OF 1 Suc(3, 4)]
              have 3: "k - k2 = Suc (k - Suc k2)" using Suc by linarith
              have 4: "k - Suc k2 \<ge> Suc k'" using Suc(2) by linarith
              show ?case unfolding 2 3 apply (subst cell_index.simps(4))
                unfolding cotm_heads_steps_congruence [symmetric] cotm_steps_congruences(1) [symmetric]
                 apply (subst le_Suc(1))
                    apply simp
                using * apply simp
                using ** apply simp
                unfolding valid_tm_next_move [OF valid_M'] apply (subst M'_def)
                 apply auto
                using Suc(4) 4 unfolding TM.cis_final_def [symmetric] by (metis cis_final_sub_imp diff_diff_cancel)
            qed
            note 10 [OF le_refl]
            hence 11: "cell_index (Abs_TM M') w 3 k = cell_index (Abs_TM M') w 3 (Suc k')"
              using 9 by fastforce
            have 12: "(TM.cstep M ^^ k) (TM.cinitial_config M w) = (TM.cstep M ^^ (Suc k')) (TM.cinitial_config M w)"
              apply (rule cis_final_csteps_stay_eq)
              using 9 apply simp
              unfolding TM.cis_final_def by fact
            note Suc(7) [OF zero_less_Suc 9 [THEN Suc_leI] 7 * **]
            hence 13: "ctapes ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w)) ! 2 =
                       ctapes ((TM.cstep (Abs_TM M') ^^ (Suc k')) (TM.cinitial_config (Abs_TM M') w)) ! 2"
              by (metis (no_types, lifting) M'_def One_nat_def add_Suc_right diff_Suc_1' length_ctapes_csteps_eq_tc
                  length_tl less_add_Suc2 nth_tl numeral_2_eq_2 numeral_3_eq_3 simps(1) valid_M' valid_tm_tape_count)
            note 14 = a3 [unfolded 13]
            have 15: "k' \<le> n" using * 9 by simp
            have 16: "k' \<le> Suc (length w)" using ** 9 by simp
            have 17: "cstate ((TM.cstep (Abs_TM M') ^^ k') (TM.cinitial_config (Abs_TM M') w)) \<notin>
                      TM.TM.final_states (Abs_TM M')"
              using * ** 9 apply (simp add: le_Suc(1) [of k'])
              unfolding valid_tm_final_states [OF valid_M'] apply (subst (2) M'_def)
              apply simp
              unfolding final_states_def apply auto
              apply (rule ccontr)
              using cell_index_abs_bound [of "Abs_TM M'" w 3 k'] 9
              by (metis take_eq_Nil option.distinct(1) bot_nat_0.not_eq_extremum take_map last_map)
            have 18: "chead (ctapes ((TM.cstep (Abs_TM M') ^^ (Suc k')) (TM.cinitial_config (Abs_TM M') w)) ! 2) = None"
              using Suc(7) [of "Suc k'", OF _ _ 7 * **] 9 a5 apply simp
              apply (drule arg_cong [where f="\<lambda>l. l ! 1"])
              apply (subst (asm) (1 2) nth_tl)
                apply simp_all
              by (simp add: numeral_2_eq_2)
            have 19: "cell_index (Abs_TM M') w 3 k2 = cell_index M w 0 k2" if "k2 \<le> Suc k'" for k2 :: nat
              using le_Suc(10) [of k2] that 6 * ** 9 unfolding TM.cis_final_def [symmetric] apply simp
              by (smt (verit, del_insts) False Least_Suc One_nat_def TM.cis_final_def cis_final_sub_imp
                  diff_Suc_1 funpow_0 k'_def le_eq_less_or_eq not_less_Least)
            have 20: "TM.TM.next_move (Abs_TM M') (cstate ((TM.cstep (Abs_TM M') ^^ k')
                      (TM.cinitial_config (Abs_TM M') w)))
                      (cheads ((TM.cstep (Abs_TM M') ^^ k') (TM.cinitial_config (Abs_TM M') w))) 3 =
                      TM.TM.next_move M (cstate ((TM.cstep M ^^ k') (TM.cinitial_config M w)))
                      (cheads ((TM.cstep M ^^ k') (TM.cinitial_config M w))) 0"
              unfolding cotm_steps_congruences(1) cotm_heads_steps_congruence
              apply (rule cell_index_eq_next_moves_eq' [where k="Suc k'"])
               apply (erule 19)
              by simp
            have 21: "- 1 \<le> max_cell_index (Abs_TM M') w 3 (k' - 1) - cell_index (Abs_TM M') w 3 k'"
              using 1 unfolding 11
              apply (cases "TM.TM.next_move (Abs_TM M') (state ((TM.step (Abs_TM M') ^^ k')
                            (TM.initial_config (Abs_TM M') w)))
                            (heads ((TM.step (Abs_TM M') ^^ k') (TM.initial_config (Abs_TM M') w))) 3")
              apply simp_all
              by (smt (verit, del_insts) max_cell_index_ge_0)+
            have 22: "min_cell_index (Abs_TM M') w 3 (k' - 1) - cell_index (Abs_TM M') w 3 k' \<le> 1"
              using 1 unfolding 11
              apply (cases "TM.TM.next_move (Abs_TM M') (state ((TM.step (Abs_TM M') ^^ k')
                            (TM.initial_config (Abs_TM M') w)))
                            (heads ((TM.step (Abs_TM M') ^^ k') (TM.initial_config (Abs_TM M') w))) 3")
                apply simp_all
              by (smt (verit, del_insts) min_cell_index_le_0)+
            show ?thesis using 18 apply (simp add: nth_ctape_0 [symmetric])
              apply (cases "TM.TM.next_move (Abs_TM M') (cstate ((TM.cstep (Abs_TM M') ^^ k')
                            (TM.cinitial_config (Abs_TM M') w)))
                            (cheads ((TM.cstep (Abs_TM M') ^^ k') (TM.cinitial_config (Abs_TM M') w))) 3")
                apply (subst (asm) nth_ctape_cstep_Shift_Left1)
                     apply simp_all
                  apply (simp add: valid_tm_next_move)
              using le_Suc(1) [of k'] 9 * ** apply simp
                  apply (subst M'_def)
                  apply (subst (asm) M'_def)
                  apply simp
                 apply (rule 17)
              using 1 [unfolded 11] apply (subst (asm) cell_index.simps(2))
                 apply (simp add: cotm_heads_steps_congruence cotm_steps_congruences(1))
                apply simp
                apply (cases "k' = 0")
                 apply simp_all
              using le_Suc(11) [OF 8 _ 6, of "-1", OF _ 21 _ 15 16] apply simp
                apply (cases "min_cell_index (Abs_TM M') w 3 (k' - Suc 0) > 0")
                 apply simp_all
                apply (metis min_cell_index_le_0 linorder_not_less)
              using 1 [unfolded 11] apply (subst (asm) cell_index.simps(3))
                apply (simp add: cotm_heads_steps_congruence cotm_steps_congruences(1))
               apply (subst (asm) nth_ctape_cstep_Shift_Right1)
                    apply simp_all
                 apply (simp add: valid_tm_next_move)
              using le_Suc(1) [of k'] 9 * ** apply simp
                 apply (subst M'_def)
                 apply (subst (asm) M'_def)
                 apply simp
                apply (rule 17)
               apply (cases "k' = 0")
                apply simp_all
              using le_Suc(11) [OF 8 _ 6, of 1, OF _ _ 22 15 16] apply simp
              apply (cases "1 \<le> max_cell_index (Abs_TM M') w 3 (k' - Suc 0) - cell_index (Abs_TM M') w 3 k'")
                apply simp_all
               apply (smt (verit, ccfv_SIG) max_cell_index_ge_0)
              using 1 [unfolded 11] apply (subst (asm) cell_index.simps(4))
                apply (simp add: cotm_heads_steps_congruence cotm_steps_congruences(1))
              apply (subst (asm) nth_ctape_cstep_No_Shift2)
                  apply simp_all
                apply (simp add: valid_tm_next_move)
              using le_Suc(1) [of k'] 9 * ** apply simp
                apply (subst M'_def)
                apply (subst (asm) M'_def)
                apply simp
               apply (rule 17)
              unfolding valid_tm_next_write [OF valid_M'] using le_Suc(1) [of k'] 9 * ** apply simp
              apply (subst (asm) M'_def)
              using 6 by simp
          next
            case False
            show ?thesis using a5 Suc(11) [OF a4 False _ _ * **, of 0, unfolded 1, simplified]
              unfolding nth_ctape_0 [symmetric] by (simp add: max_cell_index_ge_0 min_cell_index_le_0)
          qed
        qed
      next
        fix y :: 's
        assume a1: "cell_index (Abs_TM M') w 3 k \<le> 0" and
               a2: "chead (ctapes ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w)) ! 3) = Some y" and
               a3: "length w < k" and
               a4: "chead (ctapes ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w)) ! 2) = None"
        have 0: "0 < k" using a3 by simp
        have [simp]: "y = extra_sym" using 21 [THEN conjunct1, THEN iffD1, simplified, OF exI,
              folded cotm_heads_steps_congruence, of k w] a2 by simp
        have 1: "cell_index (Abs_TM M') w 3 k = 0"
          using Suc(3) [OF Suc(6) [OF 0 * **] a2 [folded nth_ctape_0, simplified] * **] by simp
        have 2: "k = Suc (length w)" using a3 ** by simp
        have 3: "length w < n" using a3 * by simp
        show "(map Some w @ [None]) ! 0 = chead (ctapes ((TM.cstep M ^^ k) (TM.cinitial_config M w)) ! 0)"
        proof (cases "cstate (TM.cinitial_config M w) \<in> TM.final_states M")
          case True
          have 1: "(TM.cstep M ^^ k) (TM.cinitial_config M w) = TM.cinitial_config M w"
            using True [folded TM.cis_final_def] by (simp add: TM.cstep_final funpow_fixpoint)
          show ?thesis unfolding 1 unfolding TM.cinitial_config_def TM_abbrevs.cinput_tape_def empty_ctape_def apply auto
            by (metis hd_conv_nth)
        next
          case False
          show ?thesis
          proof (cases "cstate (TM.csteps M k (TM.cinitial_config M w)) \<in> TM.final_states M")
            case True
            define k' :: nat where "k' \<equiv> (LEAST k'. cstate ((TM.cstep M ^^ k') (TM.cinitial_config M w)) \<in>
                                    TM.TM.final_states M) - 1"
            note 5 = LeastI [of "\<lambda>k. cstate ((TM.cstep M ^^ k) (TM.cinitial_config M w)) \<in> TM.TM.final_states M",
                OF True, folded TM.cis_final_def]
            have 6: "cstate ((TM.cstep M ^^ k') (TM.cinitial_config M w)) \<notin> TM.TM.final_states M"
              apply standard
              by (metis (no_types, lifting) False One_nat_def diff_Suc_Suc diff_is_0_eq diff_zero funpow_0 k'_def
                  lessI list_decode.cases nat_le_linear not_less_Least)
            have 7: "cstate ((TM.cstep M ^^ (Suc k')) (TM.cinitial_config M w)) \<in> TM.TM.final_states M"
              unfolding k'_def using 5 unfolding TM.cis_final_def [symmetric]
              by (smt (verit, del_insts) False Least_Suc One_nat_def Suc_diff_Suc TM.cis_final_def diff_zero funpow_0
                  zero_less_Suc)
            have 8: "k' \<le> k" using True 6 unfolding TM.cis_final_def [symmetric]
              by (metis (no_types, lifting) True diff_le_self k'_def le_trans linorder_not_le not_less_Least)
            have "k' = k \<Longrightarrow> False" using True 6 by simp
            hence 9: "k' < k" using 8 by force
            have 10: "k2 \<le> k - Suc k' \<Longrightarrow> cell_index (Abs_TM M') w 3 k = cell_index (Abs_TM M') w 3 (k - k2)"
              for k2 :: nat using 9 7
            proof (induction k2)
              case 0
              then show ?case by simp
            next
              case (Suc k2)
              have 1: "k2 \<le> k - Suc k'" using Suc(2) by simp
              note 2 = Suc(1) [OF 1 Suc(3, 4)]
              have 3: "k - k2 = Suc (k - Suc k2)" using Suc by linarith
              have 4: "k - Suc k2 \<ge> Suc k'" using Suc(2) by linarith
              show ?case unfolding 2 3 apply (subst cell_index.simps(4))
                unfolding cotm_heads_steps_congruence [symmetric] cotm_steps_congruences(1) [symmetric]
                 apply (subst le_Suc(1))
                    apply simp
                using * apply simp
                using ** apply simp
                unfolding valid_tm_next_move [OF valid_M'] apply (subst M'_def)
                 apply auto
                using Suc(4) 4 unfolding TM.cis_final_def [symmetric] by (metis cis_final_sub_imp diff_diff_cancel)
            qed
            note 10 [OF le_refl]
            hence 11: "cell_index (Abs_TM M') w 3 k = cell_index (Abs_TM M') w 3 (Suc k')"
              using 9 by fastforce
            have 12: "(TM.cstep M ^^ k) (TM.cinitial_config M w) = (TM.cstep M ^^ (Suc k')) (TM.cinitial_config M w)"
              apply (rule cis_final_csteps_stay_eq)
              using 9 apply simp
              unfolding TM.cis_final_def by fact
            note Suc(7) [OF zero_less_Suc 9 [THEN Suc_leI] 7 * **]
            hence 13: "ctapes ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w)) ! 2 =
                       ctapes ((TM.cstep (Abs_TM M') ^^ (Suc k')) (TM.cinitial_config (Abs_TM M') w)) ! 2"
              by (metis (no_types, lifting) M'_def One_nat_def add_Suc_right diff_Suc_1' length_ctapes_csteps_eq_tc
                  length_tl less_add_Suc2 nth_tl numeral_2_eq_2 numeral_3_eq_3 simps(1) valid_M' valid_tm_tape_count)
            note 14 = a3 [unfolded 13]
            have 15: "k' \<le> n" using * 9 by simp
            have 16: "k' \<le> Suc (length w)" using ** 9 by simp
            have 17: "cstate ((TM.cstep (Abs_TM M') ^^ k') (TM.cinitial_config (Abs_TM M') w)) \<notin>
                      TM.TM.final_states (Abs_TM M')"
              using * ** 9 apply (simp add: le_Suc(1) [of k'])
              unfolding valid_tm_final_states [OF valid_M'] apply (subst (2) M'_def)
              apply simp
              unfolding final_states_def apply auto
              apply (rule ccontr)
              using cell_index_abs_bound [of "Abs_TM M'" w 3 k'] 9
              by (metis take_eq_Nil option.distinct(1) bot_nat_0.not_eq_extremum take_map last_map)
            have 18: "chead (ctapes ((TM.cstep (Abs_TM M') ^^ (Suc k')) (TM.cinitial_config (Abs_TM M') w)) ! 2) = None"
              using Suc(7) [of "Suc k'", OF _ _ 7 * **] 9 a4 apply simp
              apply (drule arg_cong [where f="\<lambda>l. l ! 1"])
              apply (subst (asm) (1 2) nth_tl)
                apply simp_all
              by (simp add: numeral_2_eq_2)
            have 19: "cell_index (Abs_TM M') w 3 k2 = cell_index M w 0 k2" if "k2 \<le> Suc k'" for k2 :: nat
              using le_Suc(10) [of k2] that 6 * ** 9 unfolding TM.cis_final_def [symmetric] apply simp
              by (smt (verit, del_insts) False Least_Suc One_nat_def TM.cis_final_def cis_final_sub_imp
                  diff_Suc_1 funpow_0 k'_def le_eq_less_or_eq not_less_Least)
            have 20: "TM.TM.next_move (Abs_TM M') (cstate ((TM.cstep (Abs_TM M') ^^ k')
                      (TM.cinitial_config (Abs_TM M') w)))
                      (cheads ((TM.cstep (Abs_TM M') ^^ k') (TM.cinitial_config (Abs_TM M') w))) 3 =
                      TM.TM.next_move M (cstate ((TM.cstep M ^^ k') (TM.cinitial_config M w)))
                      (cheads ((TM.cstep M ^^ k') (TM.cinitial_config M w))) 0"
              unfolding cotm_steps_congruences(1) cotm_heads_steps_congruence
              apply (rule cell_index_eq_next_moves_eq' [where k="Suc k'"])
               apply (erule 19)
              by simp
            have 21: "- 1 \<le> max_cell_index (Abs_TM M') w 3 (k' - 1) - cell_index (Abs_TM M') w 3 k'"
              using 1 unfolding 11
              apply (cases "TM.TM.next_move (Abs_TM M') (state ((TM.step (Abs_TM M') ^^ k')
                            (TM.initial_config (Abs_TM M') w)))
                            (heads ((TM.step (Abs_TM M') ^^ k') (TM.initial_config (Abs_TM M') w))) 3")
              apply simp_all
              by (smt (verit, del_insts) max_cell_index_ge_0)+
            have 22: "min_cell_index (Abs_TM M') w 3 (k' - 1) - cell_index (Abs_TM M') w 3 k' \<le> 1"
              using 1 unfolding 11
              apply (cases "TM.TM.next_move (Abs_TM M') (state ((TM.step (Abs_TM M') ^^ k')
                            (TM.initial_config (Abs_TM M') w)))
                            (heads ((TM.step (Abs_TM M') ^^ k') (TM.initial_config (Abs_TM M') w))) 3")
                apply simp_all
              by (smt (verit, del_insts) min_cell_index_le_0)+
            show ?thesis using 18 1 [unfolded 11] apply simp
              unfolding nth_ctape_0 [symmetric]
              apply (cases "TM.TM.next_move (Abs_TM M') (cstate ((TM.cstep (Abs_TM M') ^^ k')
                            (TM.cinitial_config (Abs_TM M') w)))
                            (cheads ((TM.cstep (Abs_TM M') ^^ k') (TM.cinitial_config (Abs_TM M') w))) 3")
                apply (subst (asm) cell_index.simps(2))
                 apply (simp add: cotm_heads_steps_congruence cotm_steps_congruences(1))
                apply simp
                apply (subst (asm) nth_ctape_cstep_Shift_Left1)
                     apply simp_all
                  apply (simp add: valid_tm_next_move)
              using le_Suc(1) [of k'] 9 * ** apply simp
                  apply (subst M'_def)
                  apply (subst (asm) (2) M'_def)
                  apply simp
                 apply (rule 17)
                apply (cases "k' = 0")
                 apply simp_all
              using le_Suc(11) [OF 8 _ 6, of "-1", OF _ 21 _ 15 16] apply simp
              using min_cell_index_le_0 apply blast
               apply (subst (asm) cell_index.simps(3))
                apply (simp add: cotm_heads_steps_congruence cotm_steps_congruences(1))
               apply (subst (asm) nth_ctape_cstep_Shift_Right1)
                    apply simp_all
                 apply (simp add: valid_tm_next_move)
              using le_Suc(1) [of k'] 9 * ** apply simp
                 apply (subst M'_def)
                 apply (subst (asm) (2) M'_def)
                 apply simp
                apply (rule 17)
               apply (cases "k' = 0")
                apply simp_all
              using le_Suc(11) [OF 8 _ 6, of 1, OF _ _ 22 15 16] apply simp
               apply (smt (verit) max_cell_index_ge_0)
              apply (subst (asm) nth_ctape_cstep_No_Shift2)
                  apply simp_all
                apply (simp add: valid_tm_next_move)
              using le_Suc(1) [of k'] 9 * ** apply simp
                apply (subst M'_def)
                apply (subst (asm) (2) M'_def)
                apply simp
               apply (rule 17)
              unfolding valid_tm_next_write [OF valid_M'] using le_Suc(1) [of k'] 9 * ** apply simp
              apply (subst (asm) M'_def)
              using 6 by simp
          next
            case False
            show ?thesis using a4 Suc(11) [OF 0 False _ _ * **, of 0, unfolded 1, simplified]
              unfolding nth_ctape_0 [symmetric] by (simp add: max_cell_index_ge_0 min_cell_index_le_0)
          qed
        qed
      next
        fix y :: 's
        assume a1: "chead (ctapes (TM.cinitial_config (Abs_TM M') w) ! 2) = Some y"
        have 1: False using a1 unfolding TM.cinitial_config_def TM_abbrevs.cinput_tape_def empty_ctape_def by simp
        show "hd (tl (cheads (TM.cinitial_config (Abs_TM M') w))) = chead (ctapes (TM.cinitial_config M w) ! 0)"
          using 1 ..
      next
        show "hd (cheads (TM.cinitial_config (Abs_TM M') w)) = chead (ctapes (TM.cinitial_config M w) ! 0)"
          apply (subst hd_map)
           apply (metis TM.at_least_one_tape length_ctapes_initial_config list.size(3) not_gr_zero)
          apply (subst zeroth_is_head)
           apply (metis TM.at_least_one_tape length_ctapes_initial_config less_not_refl list.size(3))
          unfolding TM.cinitial_config_def by simp
      next
        assume a1: "\<not> 0 < cell_index (Abs_TM M') w 3 k" and
               a2: "chead (ctapes ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w)) ! 3) = None" and
               a3: "chead (ctapes ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w)) ! 2) = None" and
               a4: "w \<noteq> []" and a5: "k > 0"
        have "cell_index (Abs_TM M') w 3 k \<noteq> 0"
          apply standard
          using Suc(6) [OF a5 * **] a2 unfolding nth_ctape_0 [symmetric] by simp
        hence 1: "cell_index (Abs_TM M') w 3 k < 0" using a1 by simp
        have 2: "cstate (TM.cinitial_config M w) \<notin> TM.final_states M"
        proof
          assume a6: "cstate (TM.cinitial_config M w) \<in> TM.TM.final_states M"
          have 2: "TM.TM.next_move (Abs_TM M') (cstate ((TM.cstep (Abs_TM M') ^^ k')
                   (TM.cinitial_config (Abs_TM M') w)))
                   (cheads ((TM.cstep (Abs_TM M') ^^ k') (TM.cinitial_config (Abs_TM M') w))) 3 = No_Shift" if "k' \<le> k"
            for k' :: nat
            unfolding valid_tm_next_move [OF valid_M'] using le_Suc(1) [of k'] that * ** apply simp
            apply (subst M'_def)
            apply auto
            using a6 unfolding TM.cis_final_def [symmetric] by (metis cis_final_sub_imp diff_self_eq_0 funpow_0)
          have 3: "cell_index (Abs_TM M') w 3 k' = 0" if "k' \<le> k" for k' :: nat using that
          proof (induction k')
            case 0
            then show ?case by simp
          next
            case (Suc k')
            then show ?case apply (subst cell_index.simps(4))
               apply simp_all
              using 2 [of k'] by (simp add: cotm_heads_steps_congruence cotm_steps_congruences(1))
          qed
          show False using 1 3 [OF le_refl] by simp
        qed
        show "None = chead (ctapes ((TM.cstep M ^^ k) (TM.cinitial_config M w)) ! 0)"
        proof (cases "cstate (TM.csteps M k (TM.cinitial_config M w)) \<in> TM.final_states M")
          case True
          define k' :: nat where "k' \<equiv> (LEAST k'. cstate ((TM.cstep M ^^ k') (TM.cinitial_config M w)) \<in>
                                  TM.TM.final_states M) - 1"
          note 5 = LeastI [of "\<lambda>k. cstate ((TM.cstep M ^^ k) (TM.cinitial_config M w)) \<in> TM.TM.final_states M",
              OF True, folded TM.cis_final_def]
          have 6: "cstate ((TM.cstep M ^^ k') (TM.cinitial_config M w)) \<notin> TM.TM.final_states M"
            apply standard
            by (metis (no_types, lifting) 2 One_nat_def diff_Suc_Suc diff_is_0_eq diff_zero funpow_0 k'_def
                  lessI list_decode.cases nat_le_linear not_less_Least)
          have 7: "cstate ((TM.cstep M ^^ (Suc k')) (TM.cinitial_config M w)) \<in> TM.TM.final_states M"
            unfolding k'_def using 5 unfolding TM.cis_final_def [symmetric]
            by (smt (verit, del_insts) 2 Least_Suc One_nat_def Suc_diff_Suc TM.cis_final_def diff_zero funpow_0
                zero_less_Suc)
          have 8: "k' \<le> k" using True 6 unfolding TM.cis_final_def [symmetric]
            by (metis (no_types, lifting) True diff_le_self k'_def le_trans linorder_not_le not_less_Least)
          have "k' = k \<Longrightarrow> False" using True 6 by simp
          hence 9: "k' < k" using 8 by force
          have 10: "k2 \<le> k - Suc k' \<Longrightarrow> cell_index (Abs_TM M') w 3 k = cell_index (Abs_TM M') w 3 (k - k2)"
            for k2 :: nat using 9 7
          proof (induction k2)
            case 0
            then show ?case by simp
          next
            case (Suc k2)
            have 1: "k2 \<le> k - Suc k'" using Suc(2) by simp
            note 2 = Suc(1) [OF 1 Suc(3, 4)]
            have 3: "k - k2 = Suc (k - Suc k2)" using Suc by linarith
            have 4: "k - Suc k2 \<ge> Suc k'" using Suc(2) by linarith
            show ?case unfolding 2 3 apply (subst cell_index.simps(4))
              unfolding cotm_heads_steps_congruence [symmetric] cotm_steps_congruences(1) [symmetric]
               apply (subst le_Suc(1))
                  apply simp
              using * apply simp
              using ** apply simp
              unfolding valid_tm_next_move [OF valid_M'] apply (subst M'_def)
               apply auto
              using Suc(4) 4 unfolding TM.cis_final_def [symmetric] by (metis cis_final_sub_imp diff_diff_cancel)
          qed
          note 10 [OF le_refl]
          hence 11: "cell_index (Abs_TM M') w 3 k = cell_index (Abs_TM M') w 3 (Suc k')"
            using 9 by fastforce
          have 12: "(TM.cstep M ^^ k) (TM.cinitial_config M w) = (TM.cstep M ^^ (Suc k')) (TM.cinitial_config M w)"
            apply (rule cis_final_csteps_stay_eq)
            using 9 apply simp
            unfolding TM.cis_final_def by fact
          note Suc(7) [OF zero_less_Suc 9 [THEN Suc_leI] 7 * **]
          hence 13: "ctapes ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w)) ! 2 =
                     ctapes ((TM.cstep (Abs_TM M') ^^ (Suc k')) (TM.cinitial_config (Abs_TM M') w)) ! 2"
            by (metis (no_types, lifting) M'_def One_nat_def add_Suc_right diff_Suc_1' length_ctapes_csteps_eq_tc
                length_tl less_add_Suc2 nth_tl numeral_2_eq_2 numeral_3_eq_3 simps(1) valid_M' valid_tm_tape_count)
          note 14 = a3 [unfolded 13]
          have 15: "k' \<le> n" using * 9 by simp
          have 16: "k' \<le> Suc (length w)" using ** 9 by simp
          have 17: "cstate ((TM.cstep (Abs_TM M') ^^ k') (TM.cinitial_config (Abs_TM M') w)) \<notin>
                    TM.TM.final_states (Abs_TM M')"
            using * ** 9 apply (simp add: le_Suc(1) [of k'])
            unfolding valid_tm_final_states [OF valid_M'] apply (subst (2) M'_def)
            apply simp
            unfolding final_states_def apply auto
            apply (rule ccontr)
            using cell_index_abs_bound [of "Abs_TM M'" w 3 k'] 9
            by (metis take_eq_Nil option.distinct(1) bot_nat_0.not_eq_extremum take_map last_map)
          have 18: "chead (ctapes ((TM.cstep (Abs_TM M') ^^ (Suc k')) (TM.cinitial_config (Abs_TM M') w)) ! 2) = None"
            using Suc(7) [of "Suc k'", OF _ _ 7 * **] 9 a3 apply simp
            apply (drule arg_cong [where f="\<lambda>l. l ! 1"])
            apply (subst (asm) (1 2) nth_tl)
              apply simp_all
            by (simp add: numeral_2_eq_2)
          have 19: "cell_index (Abs_TM M') w 3 k2 = cell_index M w 0 k2" if "k2 \<le> Suc k'" for k2 :: nat
            using le_Suc(10) [of k2] that 6 * ** 9 unfolding TM.cis_final_def [symmetric] apply simp
            by (smt (verit, del_insts) 2 Least_Suc One_nat_def TM.cis_final_def cis_final_sub_imp
                diff_Suc_1 funpow_0 k'_def le_eq_less_or_eq not_less_Least)
          have 20: "TM.TM.next_move (Abs_TM M') (cstate ((TM.cstep (Abs_TM M') ^^ k')
                    (TM.cinitial_config (Abs_TM M') w)))
                    (cheads ((TM.cstep (Abs_TM M') ^^ k') (TM.cinitial_config (Abs_TM M') w))) 3 =
                    TM.TM.next_move M (cstate ((TM.cstep M ^^ k') (TM.cinitial_config M w)))
                    (cheads ((TM.cstep M ^^ k') (TM.cinitial_config M w))) 0"
            unfolding cotm_steps_congruences(1) cotm_heads_steps_congruence
            apply (rule cell_index_eq_next_moves_eq' [where k="Suc k'"])
             apply (erule 19)
            by simp
          have 21: "min_cell_index (Abs_TM M') w 3 k2 = min_cell_index M w 0 k2" if "k2 \<le> Suc k'" for k2 :: nat
            using 19 min_cell_index_eq_from_cell_index_eqs that by blast
          have 22: "k' - Suc 0 \<le> Suc k'" by simp
          have 23: "- 1 \<le> max_cell_index (Abs_TM M') w 3 (k' - Suc 0) - cell_index (Abs_TM M') w 3 k'"
            apply (cases k')
             apply simp_all
            apply (cases "TM.TM.next_move (Abs_TM M') (state ((TM.step (Abs_TM M') ^^ (k' - 1))
                          (TM.initial_config (Abs_TM M') w)))
                          (heads ((TM.step (Abs_TM M') ^^ (k' - 1)) (TM.initial_config (Abs_TM M') w))) 3")
              apply (simp_all add: max_cell_index_ge_cell_index)
            by (smt (verit, ccfv_threshold) max_cell_index_ge_cell_index)
          have 24: "cell_index (Abs_TM M') w 3 k' + 1 < 0 \<Longrightarrow>
                    1 \<le> max_cell_index (Abs_TM M') w 3 (k' - Suc 0) - cell_index (Abs_TM M') w 3 k'"
            by (smt (verit, del_insts) max_cell_index_ge_0)
          show ?thesis unfolding 12 using 18 1 [unfolded 11] unfolding nth_ctape_0 [symmetric] apply simp
            apply (cases "TM.TM.next_move M (cstate ((TM.cstep M ^^ k') (TM.cinitial_config M w)))
                          (cheads ((TM.cstep M ^^ k') (TM.cinitial_config M w))) 0")
              apply (subst nth_ctape_cstep_Shift_Left1)
                   apply simp_all
               apply (rule 6)
              apply (subst (asm) nth_ctape_cstep_Shift_Left1)
                   apply simp_all
            unfolding 20 [symmetric] apply (simp add: valid_tm_next_move)
                apply (simp add: le_Suc(1) [OF 8 15 16])
                apply (subst (asm) (2) M'_def)
                apply (subst M'_def)
                apply simp
               apply (rule 17)
              apply (subst (asm) cell_index.simps(2))
               apply (simp add: cotm_heads_steps_congruence cotm_steps_congruences(1))
              apply simp
              apply (subst nth_ctape_neg)
               apply (simp_all del: zeroth_clist_is_chd)
              apply (cases "cell_index (Abs_TM M') w 3 k' = 0")
               apply (simp del: zeroth_clist_is_chd)
               apply (subst csteps_untouched_cells_left2)
                   apply simp
            using 6 unfolding TM.cis_final_def [symmetric] using cis_final_sub_imp apply blast
                 apply (subst le_Suc(10) [OF 8 _ 15 16, symmetric])
            using 6 unfolding TM.cis_final_def [symmetric] using cis_final_sub_imp apply blast
                 apply simp
                 apply (rule ccontr)
                 apply (cases "k' = 0")
                  apply simp_all
            using le_Suc(11) [OF 8 _ 6 _ _ 15 16, of "-1"] apply simp
                 apply (cases k')
                  apply simp_all
                 apply (subst (asm) min_cell_index_Suc1)
                  apply (simp add: 19 min_cell_index_le_0)
            using 21 [of "k' - 1"] apply simp
                 apply (smt (verit, ccfv_SIG) max_cell_index_ge_0)
            using 19 apply force
            using 19 [of k'] apply simp
               apply (subst TM.cinitial_config_def)
               apply (simp add: TM_abbrevs.cinput_tape_def empty_ctape_def)
              apply (simp flip: zeroth_clist_is_chd)
              apply (subst csteps_untouched_cells_left2(2))
                  apply simp
            using 6 unfolding TM.cis_final_def [symmetric] using cis_final_sub_imp apply blast
                apply (rule ccontr)
                apply simp
                apply (cases "k' = 0")
                 apply simp
            using le_Suc(11) [OF 8 _ 6 _ _ 15 16, of "-1"] apply simp
            unfolding 21 [OF 22] using 23 apply simp
                apply (subst (asm) le_Suc(10) [OF 8 _ 15 16, symmetric])
            using 6 unfolding TM.cis_final_def [symmetric] using cis_final_sub_imp apply blast
                apply (cases "min_cell_index M w 0 (k' - Suc 0) - cell_index (Abs_TM M') w 3 k' > - 1")
                 apply simp_all
                apply (cases k')
                 apply simp_all
                apply (subst (asm) (2) min_cell_index_Suc1 [symmetric])
                 apply (smt (verit, best) 19 min_cell_Suc_uneq_m1 suc_is_ge)
                apply linarith
               apply (simp add: 19)
              apply (subst TM.cinitial_config_def)
              apply (simp add: TM_abbrevs.cinput_tape_def empty_ctape_def)
             apply (subst (asm) cell_index.simps(3))
              apply (simp add: cotm_heads_steps_congruence cotm_steps_congruences(1))
             apply (subst (asm) nth_ctape_cstep_Shift_Right1)
                  apply simp_all
               apply (simp add: valid_tm_next_move le_Suc(1) [OF 8 15 16])
               apply (subst M'_def)
               apply (subst (asm) (2) M'_def)
               apply simp
              apply (rule 17)
             apply (subst nth_ctape_cstep_Shift_Right1)
                  apply simp_all
            using 20 apply argo
              apply (rule 6)
             apply (cases "k' = 0")
              apply simp
            using le_Suc(11) [OF 8 _ 6 _ _ 15 16, of 1] 24 apply simp
             apply (cases "cell_index (Abs_TM M') w 3 k' = min_cell_index (Abs_TM M') w 3 (k' - Suc 0)")
              apply simp_all
             apply (cases k')
              apply simp_all
             apply (smt (verit, best) min_cell_Suc_uneq_m1 min_cell_index_le_cell_index)
            apply (subst (asm) cell_index.simps(4))
             apply (simp add: cotm_heads_steps_congruence cotm_steps_congruences(1))
            apply (subst (asm) nth_ctape_cstep_No_Shift2)
                apply simp_all
              apply (simp add: valid_tm_next_move le_Suc(1) [OF 8 15 16])
              apply (subst M'_def)
              apply (subst (asm) (2) M'_def)
              apply simp
             apply (rule 17)
            unfolding valid_tm_next_write [OF valid_M'] le_Suc(1) [OF 8 15 16] apply (subst (asm) M'_def)
            using 6 by simp
        next
          case False
          have 4: "min_cell_index (Abs_TM M') w 3 (k - Suc 0) = min_cell_index M w 0 (k - Suc 0)"
            apply (rule min_cell_index_eq_from_cell_index_eqs [where k=k])
             apply (frule le_Suc(10))
            using False unfolding TM.cis_final_def [symmetric]
                apply (metis cis_final_csteps_stay_eq cis_final_sub_imp)
               apply simp_all
            using * apply simp
            using ** by simp
          show ?thesis using a3 apply (subst csteps_untouched_cells_head2_left)
                apply simp
            using False [folded TM.cis_final_def] using cis_final_sub_imp apply blast
            unfolding nth_ctape_0 [symmetric] using Suc(11) [OF a5 False _ _ * **, of 0] apply simp
              apply (rule ccontr)
              apply (subst (asm) Suc(10) [OF _ * **, symmetric])
            using TM.cis_final_def False [folded TM.cis_final_def] cis_final_sub_imp apply blast
            unfolding 4 [symmetric] apply (smt (verit) a1 max_cell_index_ge_0)
             apply (rule a5)
            apply (subst TM.cinitial_config_def)
            by (simp add: TM_abbrevs.cinput_tape_def empty_ctape_def)
        qed
      next
        assume a1: "\<not> 0 < cell_index (Abs_TM M') w 3 k" and
               a2: "chead (ctapes ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w)) ! 3) = None" and
               a3: "length w < k" and
               a4: "chead (ctapes ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w)) ! 2) = None"
        have 0: "0 < k" using a3 by simp
        have "cell_index (Abs_TM M') w 3 k \<noteq> 0"
          apply standard
          using Suc(6) [OF 0 * **] a2 unfolding nth_ctape_0 [symmetric] by simp
        hence 1: "cell_index (Abs_TM M') w 3 k < 0" using a1 by simp
        have 2: "cstate (TM.cinitial_config M w) \<notin> TM.final_states M"
        proof
          assume a6: "cstate (TM.cinitial_config M w) \<in> TM.TM.final_states M"
          have 2: "TM.TM.next_move (Abs_TM M') (cstate ((TM.cstep (Abs_TM M') ^^ k')
                   (TM.cinitial_config (Abs_TM M') w)))
                   (cheads ((TM.cstep (Abs_TM M') ^^ k') (TM.cinitial_config (Abs_TM M') w))) 3 = No_Shift" if "k' \<le> k"
            for k' :: nat
            unfolding valid_tm_next_move [OF valid_M'] using le_Suc(1) [of k'] that * ** apply simp
            apply (subst M'_def)
            apply auto
            using a6 unfolding TM.cis_final_def [symmetric] by (metis cis_final_sub_imp diff_self_eq_0 funpow_0)
          have 3: "cell_index (Abs_TM M') w 3 k' = 0" if "k' \<le> k" for k' :: nat using that
          proof (induction k')
            case 0
            then show ?case by simp
          next
            case (Suc k')
            then show ?case apply (subst cell_index.simps(4))
               apply simp_all
              using 2 [of k'] by (simp add: cotm_heads_steps_congruence cotm_steps_congruences(1))
          qed
          show False using 1 3 [OF le_refl] by simp
        qed
        show "None = chead (ctapes ((TM.cstep M ^^ k) (TM.cinitial_config M w)) ! 0)"
        proof (cases "cstate (TM.csteps M k (TM.cinitial_config M w)) \<in> TM.final_states M")
          case True
          define k' :: nat where "k' \<equiv> (LEAST k'. cstate ((TM.cstep M ^^ k') (TM.cinitial_config M w)) \<in>
                                  TM.TM.final_states M) - 1"
          note 5 = LeastI [of "\<lambda>k. cstate ((TM.cstep M ^^ k) (TM.cinitial_config M w)) \<in> TM.TM.final_states M",
              OF True, folded TM.cis_final_def]
          have 6: "cstate ((TM.cstep M ^^ k') (TM.cinitial_config M w)) \<notin> TM.TM.final_states M"
            apply standard
            by (metis (no_types, lifting) 2 One_nat_def diff_Suc_Suc diff_is_0_eq diff_zero funpow_0 k'_def
                  lessI list_decode.cases nat_le_linear not_less_Least)
          have 7: "cstate ((TM.cstep M ^^ (Suc k')) (TM.cinitial_config M w)) \<in> TM.TM.final_states M"
            unfolding k'_def using 5 unfolding TM.cis_final_def [symmetric]
            by (smt (verit, del_insts) 2 Least_Suc One_nat_def Suc_diff_Suc TM.cis_final_def diff_zero funpow_0
                zero_less_Suc)
          have 8: "k' \<le> k" using True 6 unfolding TM.cis_final_def [symmetric]
            by (metis (no_types, lifting) True diff_le_self k'_def le_trans linorder_not_le not_less_Least)
          have "k' = k \<Longrightarrow> False" using True 6 by simp
          hence 9: "k' < k" using 8 by force
          have 10: "k2 \<le> k - Suc k' \<Longrightarrow> cell_index (Abs_TM M') w 3 k = cell_index (Abs_TM M') w 3 (k - k2)"
            for k2 :: nat using 9 7
          proof (induction k2)
            case 0
            then show ?case by simp
          next
            case (Suc k2)
            have 1: "k2 \<le> k - Suc k'" using Suc(2) by simp
            note 2 = Suc(1) [OF 1 Suc(3, 4)]
            have 3: "k - k2 = Suc (k - Suc k2)" using Suc by linarith
            have 4: "k - Suc k2 \<ge> Suc k'" using Suc(2) by linarith
            show ?case unfolding 2 3 apply (subst cell_index.simps(4))
              unfolding cotm_heads_steps_congruence [symmetric] cotm_steps_congruences(1) [symmetric]
               apply (subst le_Suc(1))
                  apply simp
              using * apply simp
              using ** apply simp
              unfolding valid_tm_next_move [OF valid_M'] apply (subst M'_def)
               apply auto
              using Suc(4) 4 unfolding TM.cis_final_def [symmetric] by (metis cis_final_sub_imp diff_diff_cancel)
          qed
          note 10 [OF le_refl]
          hence 11: "cell_index (Abs_TM M') w 3 k = cell_index (Abs_TM M') w 3 (Suc k')"
            using 9 by fastforce
          have 12: "(TM.cstep M ^^ k) (TM.cinitial_config M w) = (TM.cstep M ^^ (Suc k')) (TM.cinitial_config M w)"
            apply (rule cis_final_csteps_stay_eq)
            using 9 apply simp
            unfolding TM.cis_final_def by fact
          note Suc(7) [OF zero_less_Suc 9 [THEN Suc_leI] 7 * **]
          hence 13: "ctapes ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w)) ! 2 =
                     ctapes ((TM.cstep (Abs_TM M') ^^ (Suc k')) (TM.cinitial_config (Abs_TM M') w)) ! 2"
            by (metis (no_types, lifting) M'_def One_nat_def add_Suc_right diff_Suc_1' length_ctapes_csteps_eq_tc
                length_tl less_add_Suc2 nth_tl numeral_2_eq_2 numeral_3_eq_3 simps(1) valid_M' valid_tm_tape_count)
          note 14 = a3 [unfolded 13]
          have 15: "k' \<le> n" using * 9 by simp
          have 16: "k' \<le> Suc (length w)" using ** 9 by simp
          have 17: "cstate ((TM.cstep (Abs_TM M') ^^ k') (TM.cinitial_config (Abs_TM M') w)) \<notin>
                    TM.TM.final_states (Abs_TM M')"
            using * ** 9 apply (simp add: le_Suc(1) [of k'])
            unfolding valid_tm_final_states [OF valid_M'] apply (subst (2) M'_def)
            apply simp
            unfolding final_states_def apply auto
            apply (rule ccontr)
            using cell_index_abs_bound [of "Abs_TM M'" w 3 k'] 9
            by (metis take_eq_Nil option.distinct(1) bot_nat_0.not_eq_extremum take_map last_map)
          have 18: "chead (ctapes ((TM.cstep (Abs_TM M') ^^ (Suc k')) (TM.cinitial_config (Abs_TM M') w)) ! 2) = None"
            using Suc(7) [of "Suc k'", OF _ _ 7 * **] 9 a4 apply simp
            apply (drule arg_cong [where f="\<lambda>l. l ! 1"])
            apply (subst (asm) (1 2) nth_tl)
              apply simp_all
            by (simp add: numeral_2_eq_2)
          have 19: "cell_index (Abs_TM M') w 3 k2 = cell_index M w 0 k2" if "k2 \<le> Suc k'" for k2 :: nat
            using le_Suc(10) [of k2] that 6 * ** 9 unfolding TM.cis_final_def [symmetric] apply simp
            by (smt (verit, del_insts) 2 Least_Suc One_nat_def TM.cis_final_def cis_final_sub_imp
                diff_Suc_1 funpow_0 k'_def le_eq_less_or_eq not_less_Least)
          have 20: "TM.TM.next_move (Abs_TM M') (cstate ((TM.cstep (Abs_TM M') ^^ k')
                    (TM.cinitial_config (Abs_TM M') w)))
                    (cheads ((TM.cstep (Abs_TM M') ^^ k') (TM.cinitial_config (Abs_TM M') w))) 3 =
                    TM.TM.next_move M (cstate ((TM.cstep M ^^ k') (TM.cinitial_config M w)))
                    (cheads ((TM.cstep M ^^ k') (TM.cinitial_config M w))) 0"
            unfolding cotm_steps_congruences(1) cotm_heads_steps_congruence
            apply (rule cell_index_eq_next_moves_eq' [where k="Suc k'"])
             apply (erule 19)
            by simp
          have 21: "min_cell_index (Abs_TM M') w 3 k2 = min_cell_index M w 0 k2" if "k2 \<le> Suc k'" for k2 :: nat
            using 19 min_cell_index_eq_from_cell_index_eqs that by blast
          have 22: "k' - Suc 0 \<le> Suc k'" by simp
          have 23: "- 1 \<le> max_cell_index (Abs_TM M') w 3 (k' - Suc 0) - cell_index (Abs_TM M') w 3 k'"
            apply (cases k')
             apply simp_all
            apply (cases "TM.TM.next_move (Abs_TM M') (state ((TM.step (Abs_TM M') ^^ (k' - 1))
                          (TM.initial_config (Abs_TM M') w)))
                          (heads ((TM.step (Abs_TM M') ^^ (k' - 1)) (TM.initial_config (Abs_TM M') w))) 3")
              apply (simp_all add: max_cell_index_ge_cell_index)
            by (smt (verit, ccfv_threshold) max_cell_index_ge_cell_index)
          have 24: "cell_index (Abs_TM M') w 3 k' + 1 < 0 \<Longrightarrow>
                    1 \<le> max_cell_index (Abs_TM M') w 3 (k' - Suc 0) - cell_index (Abs_TM M') w 3 k'"
            by (smt (verit, del_insts) max_cell_index_ge_0)
          show ?thesis unfolding 12 using 18 1 [unfolded 11] unfolding nth_ctape_0 [symmetric] apply simp
            apply (cases "TM.TM.next_move M (cstate ((TM.cstep M ^^ k') (TM.cinitial_config M w)))
                          (cheads ((TM.cstep M ^^ k') (TM.cinitial_config M w))) 0")
              apply (subst nth_ctape_cstep_Shift_Left1)
                   apply simp_all
               apply (rule 6)
              apply (subst (asm) nth_ctape_cstep_Shift_Left1)
                   apply simp_all
            unfolding 20 [symmetric] apply (simp add: valid_tm_next_move)
                apply (simp add: le_Suc(1) [OF 8 15 16])
                apply (subst (asm) (2) M'_def)
                apply (subst M'_def)
                apply simp
               apply (rule 17)
              apply (subst (asm) cell_index.simps(2))
               apply (simp add: cotm_heads_steps_congruence cotm_steps_congruences(1))
              apply simp
              apply (subst nth_ctape_neg)
               apply (simp_all del: zeroth_clist_is_chd)
              apply (cases "cell_index (Abs_TM M') w 3 k' = 0")
               apply (simp del: zeroth_clist_is_chd)
               apply (subst csteps_untouched_cells_left2)
                   apply simp
            using 6 unfolding TM.cis_final_def [symmetric] using cis_final_sub_imp apply blast
                 apply (subst le_Suc(10) [OF 8 _ 15 16, symmetric])
            using 6 unfolding TM.cis_final_def [symmetric] using cis_final_sub_imp apply blast
                 apply simp
                 apply (rule ccontr)
                 apply (cases "k' = 0")
                  apply simp_all
            using le_Suc(11) [OF 8 _ 6 _ _ 15 16, of "-1"] apply simp
                 apply (cases k')
                  apply simp_all
                 apply (subst (asm) min_cell_index_Suc1)
                  apply (simp add: 19 min_cell_index_le_0)
            using 21 [of "k' - 1"] apply simp
                 apply (smt (verit, ccfv_SIG) max_cell_index_ge_0)
            using 19 apply force
            using 19 [of k'] apply simp
               apply (subst TM.cinitial_config_def)
               apply (simp add: TM_abbrevs.cinput_tape_def empty_ctape_def)
              apply (simp flip: zeroth_clist_is_chd)
              apply (subst csteps_untouched_cells_left2(2))
                  apply simp
            using 6 unfolding TM.cis_final_def [symmetric] using cis_final_sub_imp apply blast
                apply (rule ccontr)
                apply simp
                apply (cases "k' = 0")
                 apply simp
            using le_Suc(11) [OF 8 _ 6 _ _ 15 16, of "-1"] apply simp
            unfolding 21 [OF 22] using 23 apply simp
                apply (subst (asm) le_Suc(10) [OF 8 _ 15 16, symmetric])
            using 6 unfolding TM.cis_final_def [symmetric] using cis_final_sub_imp apply blast
                apply (cases "min_cell_index M w 0 (k' - Suc 0) - cell_index (Abs_TM M') w 3 k' > - 1")
                 apply simp_all
                apply (cases k')
                 apply simp_all
                apply (subst (asm) (2) min_cell_index_Suc1 [symmetric])
                 apply (smt (verit, best) 19 min_cell_Suc_uneq_m1 suc_is_ge)
                apply linarith
               apply (simp add: 19)
              apply (subst TM.cinitial_config_def)
              apply (simp add: TM_abbrevs.cinput_tape_def empty_ctape_def)
             apply (subst (asm) cell_index.simps(3))
              apply (simp add: cotm_heads_steps_congruence cotm_steps_congruences(1))
             apply (subst (asm) nth_ctape_cstep_Shift_Right1)
                  apply simp_all
               apply (simp add: valid_tm_next_move le_Suc(1) [OF 8 15 16])
               apply (subst M'_def)
               apply (subst (asm) (2) M'_def)
               apply simp
              apply (rule 17)
             apply (subst nth_ctape_cstep_Shift_Right1)
                  apply simp_all
            using 20 apply argo
              apply (rule 6)
             apply (cases "k' = 0")
              apply simp
            using le_Suc(11) [OF 8 _ 6 _ _ 15 16, of 1] 24 apply simp
             apply (cases "cell_index (Abs_TM M') w 3 k' = min_cell_index (Abs_TM M') w 3 (k' - Suc 0)")
              apply simp_all
             apply (cases k')
              apply simp_all
             apply (smt (verit, best) min_cell_Suc_uneq_m1 min_cell_index_le_cell_index)
            apply (subst (asm) cell_index.simps(4))
             apply (simp add: cotm_heads_steps_congruence cotm_steps_congruences(1))
            apply (subst (asm) nth_ctape_cstep_No_Shift2)
                apply simp_all
              apply (simp add: valid_tm_next_move le_Suc(1) [OF 8 15 16])
              apply (subst M'_def)
              apply (subst (asm) (2) M'_def)
              apply simp
             apply (rule 17)
            unfolding valid_tm_next_write [OF valid_M'] le_Suc(1) [OF 8 15 16] apply (subst (asm) M'_def)
            using 6 by simp
        next
          case False
          have 4: "min_cell_index (Abs_TM M') w 3 (k - Suc 0) = min_cell_index M w 0 (k - Suc 0)"
            apply (rule min_cell_index_eq_from_cell_index_eqs [where k=k])
             apply (frule le_Suc(10))
            using False unfolding TM.cis_final_def [symmetric]
                apply (metis cis_final_csteps_stay_eq cis_final_sub_imp)
               apply simp_all
            using * apply simp
            using ** by simp
          show ?thesis using a4 apply (subst csteps_untouched_cells_head2_left)
                apply simp
            using False [folded TM.cis_final_def] using cis_final_sub_imp apply blast
            unfolding nth_ctape_0 [symmetric] using Suc(11) [OF 0 False _ _ * **, of 0] apply simp
              apply (rule ccontr)
              apply (subst (asm) Suc(10) [OF _ * **, symmetric])
            using TM.cis_final_def False [folded TM.cis_final_def] cis_final_sub_imp apply blast
            unfolding 4 [symmetric] apply (smt (verit) a1 max_cell_index_ge_0)
             apply (rule 0)
            apply (subst TM.cinitial_config_def)
            by (simp add: TM_abbrevs.cinput_tape_def empty_ctape_def)
        qed
      qed
      have 2: "(hd (tl (cheads ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w)))) #
               tl (tl (tl (tl (cheads ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w))))))) ! i =
               chead (ctapes ((TM.cstep M ^^ k) (TM.cinitial_config M w)) ! i)" if "i > 0" and "i < TM.tape_count M"
        for i :: nat
        using that apply (simp add: nth_tl)
        using Suc(2) [of "Suc (Suc (Suc i))", OF _ _ * **] by simp
      show "original_hds (cheads ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w)))
            (take k (map Some w) @ take (k - length w) [None]) (nat (cell_index (Abs_TM M') w 3 k)) =
            cheads ((TM.cstep M ^^ k) (TM.cinitial_config M w))"
        apply (rule nth_equalityI')
         apply (simp add: original_hds_def)
        apply simp
      proof -
        fix i :: nat
        assume a1: "i < TM.tape_count M" and
               a2: "length (original_hds (cheads ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w)))
                    (take k (map Some w) @ take (k - length w) [None]) (nat (cell_index (Abs_TM M') w 3 k))) =
                    TM.TM.tape_count M"
        show "original_hds (cheads ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w)))
              (take k (map Some w) @ take (k - length w) [None]) (nat (cell_index (Abs_TM M') w 3 k)) ! i =
              chead (ctapes ((TM.cstep M ^^ k) (TM.cinitial_config M w)) ! i)"
          apply (cases "i = 0")
          using 1 apply simp
          unfolding original_hds_def using 2 [of i] a1 by auto
      qed
    qed
    {
      case 1
      hence *: "k \<le> n" and **: "k \<le> Suc (length w)" by simp_all
      have [simp]: "cstate ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w)) \<notin>
                    TM.TM.final_states (Abs_TM M')"
        unfolding Suc(1) [OF * **] valid_tm_final_states [OF valid_M'] apply (subst (2) M'_def)
      proof simp
        have 1: "take k (map Some w) @ take (k - length w) [None] \<noteq> [] \<Longrightarrow>
                 last (take k (map Some w) @ take (k - length w) [None]) \<noteq> None" apply auto
          unfolding last_append apply auto
            apply (rule exI [where x="w ! (k - 1)"])
            apply auto
            apply (simp add: last_conv_nth min.commute)
          using 1(2) apply simp
          using 1(2) by simp
        show "(cstate ((TM.cstep M ^^ k) (TM.cinitial_config M w)),
              take k (map Some w) @ take (k - length w) [None], nat (cell_index (Abs_TM M') w 3 k), False)
              \<notin> final_states" unfolding final_states_def apply (rule notI)
          apply (drule IntD2)
          using 1 apply simp
          using * "1.prems"(2) by fastforce
      qed
      have 2: "min (length w) k + min (Suc 0) (k - length w) \<le> n"
        using "1.prems"(1) by linarith
      have 3: "nat (cell_index M w 0 k) \<le> n" using cell_index_abs_bound [of M w 0 k] * by linarith
      have 4: "cheads ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w)) ! 3 =
               chead (ctapes ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w)) ! 3)"
        apply (subst nth_map)
        by simp_all
      have ***: "None \<up> (k - length w) = take (k - length w) [None]"
        apply (rule nth_equalityI)
        using 1 by simp_all
      have 5: "cstate ((TM.cstep M ^^ k) (TM.cinitial_config M w)) \<notin> TM.TM.final_states M \<Longrightarrow>
               cstate ((TM.cstep M ^^ (k - 1)) (TM.cinitial_config M w)) \<notin> TM.TM.final_states M"
        apply auto
        unfolding TM.cis_final_def [symmetric] using cis_final_sub_imp by blast
      show ?case apply simp
        apply (subst (1 2) TM.cstep_def)
        apply auto
        unfolding TM.cstep_not_final_def Let_def apply simp_all
        unfolding valid_tm_next_state [OF valid_M'] Suc(1) [OF * **] apply (subst M'_def)
         apply auto
              apply (rule nth_equalityI)
               apply simp
        using "1.prems"(2) apply force
        using 1 apply (auto simp add: nth_append)[1]
        unfolding Suc(4) [of 0, unfolded nth_ctape_0, OF * **] apply simp
        unfolding Suc(9) [OF * **] apply (subst TM.cinitial_config_def)
        unfolding TM_abbrevs.cinput_tape_def apply auto[1]
               apply (cases "k = 0")
                apply (simp add: nth_ctape_0)
        using hd_conv_nth apply blast
               apply (subst nth_ctape_pos)
                apply simp
               apply simp
               apply (subst prepend_list_nth_less)
                apply simp
               apply simp
               apply (smt (verit, best) Nitpick.size_list_simp(2) Suc_less_eq Suc_nat_eq_nat_zadd1
            le_eq_less_or_eq less_Suc_eq_le nat_int nth_tl of_nat_0_less_iff)
        using 1 apply simp
              apply (subst TM.cinitial_config_def)
        unfolding TM_abbrevs.cinput_tape_def apply auto[1]
              apply (cases "k = 0")
               apply simp
              apply (subst nth_ctape_pos)
               apply simp
              apply simp
              apply (subst prepend_list_nth_ge)
               apply simp
              apply simp
             apply (subst cell_index.simps(4))
              apply (fold cotm_steps_congruences(1))[1]
        unfolding valid_tm_next_move [OF valid_M'] Suc(1) [OF * **] apply (subst M'_def)
              apply simp
             apply standard
        using cell_index_abs_bound [of "Abs_TM M'" w 3 k] "1.prems"(1) apply linarith
        using * diff_is_0_eq[of k "length w"] min_def[of "length w" k] apply force
        using 1 apply fastforce+
        apply (subst M'_def)
        apply (frule 5)
        apply (auto simp add: Suc(10) [OF _ * **] 2)
                          apply (simp_all add: 3)
        using original_hds_spec [OF * **] Suc(10) [OF _ * **] apply simp
                     apply (rule nth_equalityI)
                      apply simp
        using "1.prems"(2) apply force
        using 1 apply (auto simp add: nth_append)[1]
        unfolding Suc(4) [OF * **, of 0, unfolded nth_ctape_0, simplified, unfolded Suc(9) [OF * **]]
                      apply (subst nth_ctape_cinit_conf_w [of k w, simplified])
                       apply simp
                      apply simp
        using less_Suc_eq apply blast
                     apply (subst nth_ctape_cinit_conf_ge [of w k])
                      apply simp
                     apply standard
                    apply (cases "TM.TM.next_move M (cstate ((TM.cstep M ^^ k) (TM.cinitial_config M w)))
                      (original_hds (cheads ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w)))
                      (take k (map Some w) @ take (k - length w) [None]) (nat (cell_index M w 0 k))) 0")
                      apply simp_all[3]
        using original_hds_spec [OF * **] Suc(10) [OF _ * **] apply simp
                      apply (subst cell_index.simps(2))
        unfolding valid_tm_next_move [OF valid_M'] cotm_steps_congruences(1) [symmetric]
          cotm_heads_steps_congruence [symmetric] Suc(1) [OF * **] apply (subst M'_def)
                       apply simp
                      apply simp
                     apply (subst cell_index.simps(3))
        unfolding valid_tm_next_move [OF valid_M'] cotm_steps_congruences(1) [symmetric]
          cotm_heads_steps_congruence [symmetric] Suc(1) [OF * **] apply (subst M'_def)
                      apply simp
        using * ** Suc(10) 5 apply presburger
        unfolding Suc(10) [OF _ * **, simplified] using Suc(8) [OF _ * **, THEN iffD1, THEN conjunct1] apply linarith
                    apply (subst cell_index.simps(4))
        unfolding valid_tm_next_move [OF valid_M'] cotm_steps_congruences(1) [symmetric]
          cotm_heads_steps_congruence [symmetric] Suc(1) [OF * **] apply (subst M'_def)
                     apply simp
        using * ** Suc(10) 5 apply presburger
        using * ** Suc(10) 5 apply presburger
        using Suc(10) [OF _ * **] 5 original_hds_spec [OF * **] apply presburger
                     apply (rule nth_equalityI)
        using "1.prems"(2) apply force
        using 1 apply (auto simp add: nth_append)[1]
                      apply (auto simp add: TM.cinitial_config_def TM_abbrevs.cinput_tape_def empty_ctape_def)[1]
                      apply (cases "k = 0")
                       apply simp
                      apply simp
                      apply (subst nth_ctape_pos)
                       apply simp
                      apply simp
                      apply (subst prepend_list_nth_less)
                       apply simp
                      apply simp
                      apply (metis Suc_le_D diff_Suc_1 int_eq_iff le_less_Suc_eq less_eq_Suc_le linorder_not_less
            list.collapse nat_diff_distrib' nth_Cons_Suc of_nat_1)
                     apply (simp add: nth_ctape_cinit_conf_ge)
                    apply (cases "TM.TM.next_move M (cstate ((TM.cstep M ^^ k) (TM.cinitial_config M w)))
                                  (original_hds (cheads ((TM.cstep (Abs_TM M') ^^ k)
                                  (TM.cinitial_config (Abs_TM M') w)))
                                  (take k (map Some w) @ take (k - length w) [None])
                                  (nat (cell_index M w 0 k))) 0")
                      apply auto[3]
                   apply (subst cell_index.simps(2))
        unfolding valid_tm_next_move [OF valid_M'] cotm_steps_congruences(1) [symmetric]
          cotm_heads_steps_congruence [symmetric] using Suc(1) [OF * **] original_hds_spec [OF * **] apply (subst M'_def)
                       apply simp
                       apply (metis Suc(10) [OF _ * **] 5)
                      apply (simp add: Suc(10) [OF _ * **])
                     apply (subst cell_index.simps(3))
        unfolding valid_tm_next_move [OF valid_M'] cotm_steps_congruences(1) [symmetric] Suc(1) [OF * **]
                      apply (subst M'_def)
                      apply simp
                      apply (simp add: Suc(10) [OF _ * **] cotm_heads_steps_congruence)
        unfolding Suc(10) [OF _ * **, simplified] apply (drule 21 [THEN conjunct1, THEN iffD1, simplified, OF exI,
            folded cotm_heads_steps_congruence, of k w, unfolded 4])
        unfolding Suc(8) [OF _ * **] apply simp
                    apply (drule 21 [THEN conjunct1, THEN iffD1, simplified, OF exI,
            folded cotm_heads_steps_congruence, of k w, unfolded 4])
        unfolding Suc(8) [OF _ * **] apply simp
                    apply (subst cell_index.simps(4))
        unfolding valid_tm_next_move [OF valid_M'] cotm_steps_congruences(1) [symmetric] Suc(1) [OF * **]
                     apply (subst M'_def)
                     apply (simp add: Suc(10) [OF _ * **] cotm_heads_steps_congruence)
        using Suc(10) [OF _ * **] 5 apply presburger
        using original_hds_spec [OF * **] apply auto[1]
                  apply (cases w)
                   apply simp_all[2]
                   apply (simp add: TM.cinitial_config_def TM_abbrevs.cinput_tape_def empty_ctape_def)
                  apply (simp add: TM.cinitial_config_def TM_abbrevs.cinput_tape_def)
                  apply (cases "TM.TM.next_move M (cstate (TM.cinitial_config M w))
                                (original_hds (cheads (TM.cinitial_config (Abs_TM M') w)) [] 0) 0")
                   apply auto[3]
                   apply (subst cell_index.simps(2))
        unfolding cotm_steps_congruences(1) [symmetric] cotm_heads_steps_congruence [symmetric]
        using Suc(1) [OF * **] apply simp
        unfolding valid_tm_next_move [OF valid_M'] apply (subst M'_def)
                    apply simp
                   apply simp
                  apply (subst cell_index.simps(3))
        unfolding cotm_steps_congruences(1) [symmetric] cotm_heads_steps_congruence [symmetric]
        using Suc(1) [OF * **] apply simp
        unfolding valid_tm_next_move [OF valid_M'] apply (subst M'_def)
                   apply simp
                  apply simp
                 apply (subst cell_index.simps(4))
        unfolding cotm_steps_congruences(1) [symmetric] cotm_heads_steps_congruence [symmetric]
        using Suc(1) [OF * **] apply simp
        unfolding valid_tm_next_move [OF valid_M'] apply (subst M'_def)
                  apply simp
                 apply simp
        using original_hds_spec [OF * **] apply auto[1]
               apply (simp add: TM.cinitial_config_def TM_abbrevs.cinput_tape_def empty_ctape_def)
                 apply (cases "TM.TM.next_move M (cstate (TM.cinitial_config M w))
                               (original_hds (cheads (TM.cinitial_config (Abs_TM M') w)) [] 0) 0")
                   apply auto[3]
                   apply (subst cell_index.simps(2))
        unfolding cotm_steps_congruences(1) [symmetric] cotm_heads_steps_congruence [symmetric]
        using Suc(1) [OF * **] apply simp
        unfolding valid_tm_next_move [OF valid_M'] apply (subst M'_def)
                    apply simp
                   apply simp
                  apply (subst cell_index.simps(3))
        unfolding cotm_steps_congruences(1) [symmetric] cotm_heads_steps_congruence [symmetric]
        using Suc(1) [OF * **] apply simp
        unfolding valid_tm_next_move [OF valid_M'] apply (subst M'_def)
                   apply simp
                  apply simp
                 apply (subst cell_index.simps(4))
        unfolding cotm_steps_congruences(1) [symmetric] cotm_heads_steps_congruence [symmetric]
        using Suc(1) [OF * **] apply simp
        unfolding valid_tm_next_move [OF valid_M'] apply (subst M'_def)
                  apply simp
                 apply simp
        using Suc(10) [OF _ * **] original_hds_spec [OF * **] apply force
            apply (rule nth_equalityI)
             apply simp
        using "1.prems"(2) apply force
        using 1 apply (auto simp add: nth_append)[1]
             apply (subst TM.cinitial_config_def)
        unfolding TM_abbrevs.cinput_tape_def apply simp
             apply (subst nth_ctape_pos)
              apply simp
             apply simp
             apply (subst prepend_list_nth_less)
              apply simp
             apply simp
             apply (metis diff_Suc_1 le_less_Suc_eq[of k] linorder_not_less[of _ k] list.collapse[of w]
            nat_diff_distrib'[of "int _" "1"] nat_int not0_implies_Suc
            nth_Cons_Suc[of "hd w" "tl w" "nat (int _ - 1)"] of_nat_0_le_iff of_nat_1)
            apply (simp add: nth_ctape_cinit_conf_ge)
           apply (cases "TM.TM.next_move M (cstate ((TM.cstep M ^^ k) (TM.cinitial_config M w)))
                         (original_hds (cheads ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w)))
                         (take k (map Some w) @ take (k - length w) [None]) 0) 0")
             apply auto[3]
             apply (subst cell_index.simps(2))
        unfolding cotm_heads_steps_congruence [symmetric] cotm_steps_congruences(1) [symmetric]
          Suc(1) [OF * **] valid_tm_next_move [OF valid_M'] apply (subst M'_def)
              apply simp
              apply (simp add: Suc(10) [OF _ * **])
        using Suc(10) [OF _ * **] 5 apply linarith
            apply (subst cell_index.simps(3))
        unfolding cotm_steps_congruences(1) [symmetric] cotm_heads_steps_congruence [symmetric]
          Suc(1) [OF * **] valid_tm_next_move [OF valid_M'] apply (subst M'_def)
             apply simp
             apply (simp add: Suc(10) [OF _ * **])
        unfolding Suc(10) [OF _ * **, simplified] 
        using Suc(8) [OF _ * **, THEN arg_cong, of Not, THEN iffD1, simplified, THEN mp] apply fastforce
           apply (subst cell_index.simps(4))
        unfolding cotm_steps_congruences(1) [symmetric] cotm_heads_steps_congruence [symmetric]
          Suc(1) [OF * **] valid_tm_next_move [OF valid_M'] apply (subst M'_def)
            apply simp
            apply (simp add: Suc(10) [OF _ * **])
           apply (metis Suc(10) [OF _ * **] linorder_not_less 5)
        using "1.prems"(2) by blast+
    next
      case 2
      hence *: "k \<le> n" and **: "k \<le> Suc (length w)" by simp_all
      have [simp]: "cstate ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w)) \<notin>
                    TM.TM.final_states (Abs_TM M')"
        unfolding Suc(1) [OF * **] valid_tm_final_states [OF valid_M'] apply (subst (2) M'_def)
      proof simp
        have 1: "take k (map Some w) @ take (k - length w) [None] \<noteq> [] \<Longrightarrow>
                 last (take k (map Some w) @ take (k - length w) [None]) \<noteq> None" apply auto
          unfolding last_append apply auto
            apply (rule exI [where x="w ! (k - 1)"])
            apply auto
            apply (simp add: last_conv_nth min.commute)
          using 2(4) apply simp
          using 2(4) by simp
        show "(cstate ((TM.cstep M ^^ k) (TM.cinitial_config M w)),
              take k (map Some w) @ take (k - length w) [None], nat (cell_index (Abs_TM M') w 3 k), False)
              \<notin> final_states" unfolding final_states_def apply (rule notI)
          apply (drule IntD2)
          using 2 apply auto
        proof -
          assume a1: "0 < k" and a2: "w \<noteq> []" and a3: "last (take k (map Some w)) = None"
          have "last (take k (map Some w)) = Some (w ! (min k (length w - 1)))"
            using 1 "2.prems"(4) a1 a2 a3 by auto
          thus False using a3 by simp
        qed
      qed
      have ***: "None \<up> (k - length w) = take (k - length w) [None]"
        apply (rule nth_equalityI)
        using 2 by simp_all
      show ?case apply simp
      proof (rule nth_ctape_inject)
        fix j :: int
        show "nth_ctape (ctapes (TM.cstep (Abs_TM M') ((TM.cstep (Abs_TM M') ^^ k)
              (TM.cinitial_config (Abs_TM M') w))) ! i) j =
              nth_ctape (ctapes (TM.cstep M ((TM.cstep M ^^ k) (TM.cinitial_config M w))) ! (i - 3)) j"
          apply (cases "TM.TM.next_move (Abs_TM M') (cstate ((TM.cstep (Abs_TM M') ^^ k)
                        (TM.cinitial_config (Abs_TM M') w)))
                        (cheads ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w))) i")
            apply (cases "j = 1")
             apply simp
             apply (subst nth_ctape_cstep_Shift_Left2)
                 apply assumption
                apply simp
               apply simp
          using "2.prems"(2) 5 apply argo+
          unfolding Suc(1) [OF * **] apply (subst nth_ctape_cstep_Shift_Left2)
          unfolding valid_tm_next_move [OF valid_M'] apply (subst (asm) M'_def)
                 apply simp
          using original_hds_spec [OF * **] Suc(10) [OF _ * **]
                 apply (metis diff_is_0_eq head_move.distinct(1,3) linorder_not_less)
                apply (subst (asm) M'_def)
                apply simp
          using head_move.distinct(1,3) apply argo
               apply simp
               apply (metis (no_types, lifting) "2.prems"(2) M'_def TM.at_least_one_tape
              bot_nat_0.not_eq_extremum less_diff_conv2 nat_less_le simps(1) valid_M' valid_tm_tape_count
              zero_less_diff)
              apply (metis (no_types, lifting) "2.prems"(2) M'_def TM.at_least_one_tape
              bot_nat_0.not_eq_extremum less_diff_conv2 nat_less_le simps(1) valid_M' valid_tm_tape_count
              zero_less_diff)
          unfolding valid_tm_next_write [OF valid_M'] apply (subst M'_def)
          using 2 apply auto[1]
              apply (subst (asm) M'_def)
              apply simp
          using original_hds_spec [OF * **] Suc(10) [OF _ * **] apply simp
            apply (subst (1 2) nth_ctape_cstep_Shift_Left1)
                     apply simp_all
                   apply (subst (asm) M'_def)
                   apply simp
          using original_hds_spec [OF * **] Suc(10) [OF _ * **]
                   apply (metis diff_is_0_eq head_move.distinct(1,3) linorder_not_less)
                  apply (subst (asm) M'_def)
                  apply simp
          using head_move.distinct(1,3) apply argo
                 apply (metis "2.prems"(2) 5 TM.at_least_one_tape diff_is_0_eq less_diff_conv2
              linorder_not_less nat_less_le)
                apply (metis "2.prems"(2) 5 TM.at_least_one_tape diff_is_0_eq less_diff_conv2
              linorder_not_less nat_less_le)
               apply (simp add: valid_tm_next_move Suc(1) [OF * **])
          using "2.prems"(2) 5 apply argo
          using "2.prems"(2) 5 apply argo
          unfolding Suc(2) [OF 2(1, 2) * **] apply standard
           apply (cases "j = -1")
            apply simp
            apply (subst (1 2) nth_ctape_cstep_Shift_Right2)
                    apply simp_all
                   apply (subst (asm) M'_def)
          using 2 apply simp
                   apply (cases "cstate ((TM.cstep M ^^ k) (TM.cinitial_config M w)) \<in> TM.TM.final_states M")
                    apply simp
                   apply simp
          using original_hds_spec [OF * **] Suc(10) [OF _ * **] apply simp
                  apply (subst (asm) M'_def)
          using 2 apply auto
             apply (subst (asm) M'_def)
             apply simp
             apply (cases "cstate ((TM.cstep M ^^ k) (TM.cinitial_config M w)) \<in> TM.TM.final_states M")
              apply simp
             apply simp
          unfolding valid_tm_next_move [OF valid_M'] Suc(1) [OF * **] apply (subst M'_def)
             apply simp
          unfolding valid_tm_next_write [OF valid_M'] apply (subst M'_def)
            apply auto
             apply (subst (asm) M'_def)
             apply simp
          using original_hds_spec [OF * **] Suc(10) [OF _ * **] apply simp
           apply (subst (1 2) nth_ctape_cstep_Shift_Right1)
                    apply simp_all
              apply (subst (asm) M'_def)
              apply simp
              apply (cases "cstate ((TM.cstep M ^^ k) (TM.cinitial_config M w)) \<in> TM.TM.final_states M")
               apply simp
              apply simp
          using original_hds_spec [OF * **] Suc(10) [OF _ * **] apply simp
             apply (subst (asm) M'_def)
             apply auto
          unfolding valid_tm_next_move [OF valid_M'] Suc(1) [OF * **] apply simp
          unfolding Suc(2) [OF 2(1, 2) * **] apply standard
          apply (cases "cstate ((TM.cstep M ^^ k) (TM.cinitial_config M w)) \<in> TM.TM.final_states M")
           apply (subst (1 2) TM.cstep_def)
           apply (simp add: TM.cstep_not_final_def Let_def)
           apply (subst nth_map2)
             apply (metis "2.prems"(2) TM.next_actions_simps(2))
            apply simp
          unfolding TM.ctape_action_def TM.next_actions_def TM.next_writes_def TM.next_moves_def apply simp
          unfolding Suc(1) [OF * **] valid_tm_next_move [OF valid_M'] apply simp
          unfolding valid_tm_next_write [OF valid_M'] apply (subst M'_def)
           apply (simp add: TM_abbrevs.ctape_write_def)
          unfolding Suc(2) [OF 2(1, 2) * **] apply standard
          apply (cases "j = 0")
           apply simp
           apply (subst (1 2) nth_ctape_cstep_No_Shift2)
                   apply simp_all
              apply (subst (asm) M'_def)
          using 2 apply auto
              apply (cases "cstate ((TM.cstep M ^^ k) (TM.cinitial_config M w)) \<in> TM.TM.final_states M")
          using original_hds_spec [OF * **] Suc(10) [OF _ * **] apply simp_all
          unfolding valid_tm_next_move [OF valid_M'] Suc(1) [OF * **] apply simp
           apply (subst (asm) M'_def)
           apply simp
          unfolding valid_tm_next_write [OF valid_M'] apply (subst M'_def)
           apply simp
          apply (subst (1 2) nth_ctape_cstep_No_Shift1)
                   apply simp_all
            apply (subst (asm) M'_def)
            apply simp
          unfolding valid_tm_next_move [OF valid_M'] Suc(1) [OF * **] apply simp
          unfolding Suc(2) [OF 2(1, 2) * **] ..
      qed
    next
      case 3
      hence *: "k \<le> n" and **: "k \<le> Suc (length w)" by simp_all
      have 1 [simp]: "cstate ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w)) \<notin>
                      TM.TM.final_states (Abs_TM M')"
        unfolding Suc(1) [OF * **] valid_tm_final_states [OF valid_M'] apply (subst (2) M'_def)
      proof simp
        have 1: "take k (map Some w) @ take (k - length w) [None] \<noteq> [] \<Longrightarrow>
                 last (take k (map Some w) @ take (k - length w) [None]) \<noteq> None" apply auto
          unfolding last_append apply auto
            apply (rule exI [where x="w ! (k - 1)"])
            apply auto
            apply (simp add: last_conv_nth min.commute)
          using 3(4) apply simp
          using 3(4) by simp
        show "(cstate ((TM.cstep M ^^ k) (TM.cinitial_config M w)),
              take k (map Some w) @ take (k - length w) [None], nat (cell_index (Abs_TM M') w 3 k), False)
              \<notin> final_states" unfolding final_states_def apply (rule notI)
          apply (drule IntD2)
          using 3 apply auto
        proof -
          assume a1: "0 < k" and a2: "w \<noteq> []" and a3: "last (take k (map Some w)) = None"
          have "last (take k (map Some w)) = Some (w ! (min k (length w - 1)))"
            using 1 "3.prems"(4) a1 a2 a3 by auto
          thus False using a3 by simp
        qed
      qed
      show ?case using 3(1, 2) apply simp
        apply (cases "TM.TM.next_move (Abs_TM M') (cstate ((TM.cstep (Abs_TM M') ^^ k)
                      (TM.cinitial_config (Abs_TM M') w)))
                      (cheads ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w))) 3")
          apply (cases "i = 1")
           apply simp
           apply (rule ccontr)
           apply (subst (asm) nth_ctape_cstep_Shift_Left2)
               apply assumption
              apply simp_all
        unfolding valid_tm_next_write [OF valid_M'] Suc(1) [OF * **] apply (subst (asm) M'_def)
        using 3 apply simp
           apply (cases "k = 0 \<or> w = []")
            apply auto
             apply (subst (asm) nth_ctape_cstep_Shift_Left1)
                  apply simp_all
        using Suc(1) [OF * **] apply simp
        using 1 apply simp
             apply (subst (asm) TM.cinitial_config_def)
        unfolding TM_abbrevs.cinput_tape_def apply simp
            apply (subst (asm) nth_ctape_cstep_Shift_Left1)
                 apply simp_all
        using Suc(1) [OF * **] apply simp
        using 1 apply simp
            apply (subst (asm) TM.cinitial_config_def)
        unfolding TM_abbrevs.cinput_tape_def apply simp
           apply (subst (asm) nth_ctape_cstep_Shift_Left2)
               apply simp_all
        unfolding Suc(1) [OF * **] apply simp
           apply (subst (asm) nth_ctape_cstep_Shift_Left1)
                apply simp_all
        unfolding Suc(1) [OF * **] apply simp
           apply (subst (asm) nth_ctape_0 [symmetric])
           apply (drule (1) Suc(3) [OF _ _ * **])
           apply simp
          apply (subst (asm) nth_ctape_cstep_Shift_Left1)
        unfolding Suc(1) [OF * **] apply simp_all
        using 1 Suc(1) [OF * **] apply fastforce
          apply (cases "j = 1")
           apply simp_all
           apply (subst (asm) nth_ctape_cstep_Shift_Left2)
               apply simp_all
            apply (simp add: Suc(1) [OF * **])
        unfolding valid_tm_next_write [OF valid_M'] Suc(1) [OF * **] apply (subst (asm) (3) M'_def)
        using 3 apply simp
           apply (cases "k = 0 \<or> w = []")
            apply auto
             apply (subst (asm) nth_ctape_cstep_Shift_Left2)
                 apply simp_all
        using Suc(1) [OF * **] apply fastforce
        using 1 apply simp
             apply (subst (asm) TM.cinitial_config_def)
        unfolding TM_abbrevs.cinput_tape_def apply simp
            apply (subst (asm) TM.cinitial_config_def)
        unfolding TM_abbrevs.cinput_tape_def apply simp
           apply (subst (asm) nth_ctape_0 [symmetric])
           apply (drule (1) Suc(3) [OF _ _ * **])
           apply simp
          apply (subst (asm) nth_ctape_cstep_Shift_Left1)
               apply simp_all
        unfolding Suc(1) [OF * **] apply simp
          apply (drule (1) Suc(3) [OF _ _ * **])
          apply simp
         apply (cases "i = -1")
          apply simp
          apply (rule ccontr)
          apply (subst (asm) nth_ctape_cstep_Shift_Right2)
              apply simp_all
        unfolding Suc(1) [OF * **] apply simp
          apply (subst (asm) nth_ctape_cstep_Shift_Right1)
               apply simp_all
        unfolding Suc(1) [OF * **] apply simp
        unfolding valid_tm_next_write [OF valid_M'] apply (subst (asm) M'_def)
        using 3 apply simp
          apply (cases "k = 0 \<or> w = []")
           apply auto
            apply (subst (asm) TM.cinitial_config_def)
            apply simp
           apply (subst (asm) TM.cinitial_config_def)
           apply simp
          apply (subst (asm) nth_ctape_0 [symmetric])
          apply (drule (1) Suc(3) [OF _ _ * **])
          apply simp
         apply (subst (asm) nth_ctape_cstep_Shift_Right1)
              apply simp_all
        unfolding Suc(1) [OF * **] apply simp
         apply (cases "j = -1")
          apply simp
          apply (subst (asm) nth_ctape_cstep_Shift_Right2)
              apply simp_all
        unfolding Suc(1) [OF * **] apply simp
        unfolding valid_tm_next_write [OF valid_M'] apply (subst (asm) (3) M'_def)
        using 3 apply simp
          apply (cases "k = 0 \<or> w = []")
           apply auto
            apply (simp add: TM.cinitial_config_def)
           apply (simp add: TM.cinitial_config_def)
          apply (subst (asm) nth_ctape_0 [symmetric])
          apply (drule (1) Suc(3) [OF _ _ * **])
          apply simp
         apply (subst (asm) nth_ctape_cstep_Shift_Right1)
              apply simp_all
        unfolding Suc(1) [OF * **] apply simp
         apply (drule (1) Suc(3) [OF _ _ * **])
         apply simp
        apply (rule ccontr)
        apply (cases "i = 0")
         apply simp
         apply (subst (asm) nth_ctape_cstep_No_Shift2)
             apply simp_all
        unfolding Suc(1) [OF * **] apply simp
         apply (subst (asm) nth_ctape_cstep_No_Shift1)
              apply simp_all
        unfolding Suc(1) [OF * **] apply simp
        unfolding valid_tm_next_write [OF valid_M'] Suc(1) [OF * **] apply (subst (asm) M'_def)
        using 3 apply simp
         apply (cases "k = 0 \<or> w = []")
          apply auto
           apply (simp add: TM.cinitial_config_def)
          apply (simp add: TM.cinitial_config_def)
         apply (subst (asm) nth_ctape_0 [symmetric])
         apply (drule (1) Suc(3) [OF _ _ * **])
         apply simp
        apply (subst (asm) nth_ctape_cstep_No_Shift1)
             apply simp_all
        unfolding Suc(1) [OF * **] apply simp
        apply (cases "j = 0")
         apply simp
         apply (subst (asm) nth_ctape_cstep_No_Shift2)
             apply simp_all
        unfolding Suc(1) [OF * **] apply simp
        unfolding valid_tm_next_write [OF valid_M'] Suc(1) [OF * **] apply (subst (asm) (3) M'_def)
        using 3 apply simp
         apply (cases "k = 0 \<or> w = []")
          apply auto
           apply (simp add: TM.cinitial_config_def)
          apply (simp add: TM.cinitial_config_def)
         apply (subst (asm) nth_ctape_0 [symmetric])
        apply (drule (1) Suc(3) [OF _ _ * **])
         apply simp
        apply (subst (asm) nth_ctape_cstep_No_Shift1)
             apply simp_all
        unfolding Suc(1) [OF * **] apply simp
        apply (drule (1) Suc(3) [OF _ _ * **])
        by simp
    next
      case 4
      hence *: "k \<le> n" and **: "k \<le> Suc (length w)" by simp_all
      have 1 [simp]: "cstate ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w)) \<notin>
                      TM.TM.final_states (Abs_TM M')"
        unfolding Suc(1) [OF * **] valid_tm_final_states [OF valid_M'] apply (subst (2) M'_def)
      proof simp
        have 1: "take k (map Some w) @ take (k - length w) [None] \<noteq> [] \<Longrightarrow>
                 last (take k (map Some w) @ take (k - length w) [None]) \<noteq> None" apply auto
          unfolding last_append apply auto
            apply (rule exI [where x="w ! (k - 1)"])
            apply auto
            apply (simp add: last_conv_nth min.commute)
          using 4(2) apply simp
          using 4(2) by simp
        show "(cstate ((TM.cstep M ^^ k) (TM.cinitial_config M w)),
              take k (map Some w) @ take (k - length w) [None], nat (cell_index (Abs_TM M') w 3 k), False)
              \<notin> final_states" unfolding final_states_def apply (rule notI)
          apply (drule IntD2)
          using 4 apply auto
        proof -
          assume a1: "0 < k" and a2: "w \<noteq> []" and a3: "last (take k (map Some w)) = None"
          have "last (take k (map Some w)) = Some (w ! (min k (length w - 1)))"
            using 1 "4.prems"(2) a1 a2 a3 by auto
          thus False using a3 by simp
        qed
      qed
      show ?case apply simp
        apply (cases "TM.TM.next_move (Abs_TM M') (cstate ((TM.cstep (Abs_TM M') ^^ k)
                      (TM.cinitial_config (Abs_TM M') w)))
                      (cheads ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w))) 0")
        apply (subst cell_index.simps(2))
           apply (simp add: cotm_heads_steps_congruence cotm_steps_congruences(1))
          apply (cases "i = 1")
           apply simp
           apply (subst nth_ctape_cstep_Shift_Left2)
        using 4 apply simp_all
        unfolding Suc(1) [OF * **] apply simp
        unfolding valid_tm_next_write [OF valid_M'] apply (subst M'_def)
           apply simp
        using Suc(4)[of "0"] nth_ctape_0[of "ctapes ((TM.cstep (Abs_TM M') ^^ k)
          (TM.cinitial_config (Abs_TM M') w)) ! 0"] apply force
          apply (subst nth_ctape_cstep_Shift_Left1)
               apply simp_all
        unfolding Suc(1) [OF * **] apply simp
        unfolding Suc(4) [OF * **] apply (metis (no_types, lifting) add.commute add_diff_eq)
         apply (subst cell_index.simps(3))
          apply (simp add: cotm_heads_steps_congruence cotm_steps_congruences(1))
        unfolding Suc(1) [OF * **, unfolded cotm_steps_congruences(1)] apply simp
         apply (cases "i = -1")
          apply simp
          apply (subst nth_ctape_cstep_Shift_Right2)
              apply simp_all
        unfolding Suc(1) [OF * **] apply simp
        unfolding valid_tm_next_write [OF valid_M'] apply (subst M'_def)
          apply simp
          apply (rule Suc(4) [OF * **, of 0, unfolded nth_ctape_0, simplified])
         apply (subst nth_ctape_cstep_Shift_Right1)
              apply simp_all
        unfolding Suc(1) [OF * **] apply simp
        unfolding Suc(4) [OF * **] apply (smt (verit, ccfv_SIG))
        apply (subst cell_index.simps(4))
         apply (simp add: cotm_heads_steps_congruence cotm_steps_congruences(1))
         apply (simp add: Suc(1) [OF * **, unfolded cotm_steps_congruences(1)])
        apply (cases "i = 0")
         apply simp
         apply (subst nth_ctape_cstep_No_Shift2)
             apply simp_all
        unfolding Suc(1) [OF * **] apply simp
        unfolding valid_tm_next_write [OF valid_M'] apply (subst M'_def)
         apply simp
         apply (subst nth_ctape_0 [symmetric])
        unfolding Suc(4) [OF  * **] apply simp
        apply (subst nth_ctape_cstep_No_Shift1)
             apply simp_all
        unfolding Suc(1) [OF * **] apply simp
        by (rule Suc(4) [OF * **])
    next
      case 5
      hence *: "k \<le> n" and **: "k \<le> Suc (length w)" by simp_all
      have 1 [simp]: "cstate ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w)) \<notin>
                      TM.TM.final_states (Abs_TM M')"
        unfolding Suc(1) [OF * **] valid_tm_final_states [OF valid_M'] apply (subst (2) M'_def)
      proof simp
        have 1: "take k (map Some w) @ take (k - length w) [None] \<noteq> [] \<Longrightarrow>
                 last (take k (map Some w) @ take (k - length w) [None]) \<noteq> None" apply auto
          unfolding last_append apply auto
            apply (rule exI [where x="w ! (k - 1)"])
            apply auto
            apply (simp add: last_conv_nth min.commute)
          using 5(3) apply simp
          using 5(3) by simp
        show "(cstate ((TM.cstep M ^^ k) (TM.cinitial_config M w)),
              take k (map Some w) @ take (k - length w) [None], nat (cell_index (Abs_TM M') w 3 k), False)
              \<notin> final_states" unfolding final_states_def apply (rule notI)
          apply (drule IntD2)
          using 5 apply auto
        proof -
          assume a1: "0 < k" and a2: "w \<noteq> []" and a3: "last (take k (map Some w)) = None"
          have "last (take k (map Some w)) = Some (w ! (min k (length w - 1)))"
            using 1 "5.prems"(3) a1 a2 a3 by auto
          thus False using a3 by simp
        qed
      qed
      have ***: "None \<up> (k - length w) = take (k - length w) [None]"
        apply (rule nth_equalityI)
        using 5 by simp_all
      show ?case using 5(1) apply auto
      proof -
        fix y :: 's
        assume a1: "nth_ctape (ctapes (TM.cstep (Abs_TM M') ((TM.cstep (Abs_TM M') ^^ k)
                    (TM.cinitial_config (Abs_TM M') w))) ! 2) i = Some y"
        thus "nth_ctape (ctapes (TM.cstep (Abs_TM M') ((TM.cstep (Abs_TM M') ^^ k)
              (TM.cinitial_config (Abs_TM M') w))) ! Suc 0) i =
              nth_ctape (ctapes (TM.cstep M ((TM.cstep M ^^ k) (TM.cinitial_config M w))) ! 0) i"
          apply (cases "TM.TM.next_move (Abs_TM M') (cstate ((TM.cstep (Abs_TM M') ^^ k)
                        (TM.cinitial_config (Abs_TM M') w)))
                        (cheads ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w))) (Suc 0)")
            apply (cases "i = 1")
             apply simp
             apply (subst (1 2) nth_ctape_cstep_Shift_Left2)
          using 5 apply simp_all
          unfolding valid_tm_next_move [OF valid_M'] Suc(1) [OF * **] apply (subst (asm) (4) M'_def)
               apply simp
               apply (cases "cstate ((TM.cstep M ^^ k) (TM.cinitial_config M w)) \<in> TM.TM.final_states M")
                apply simp
               apply simp
          using original_hds_spec [OF * **] Suc(10) [OF _ * **] apply simp
              apply (subst (asm) (4) M'_def)
              apply auto
          unfolding valid_tm_next_write [OF valid_M'] apply (subst M'_def)
             apply auto
              apply (subst (asm) (4) M'_def)
              apply simp
          using original_hds_spec [OF * **] Suc(10) [OF _ * **] apply simp
            apply (subst (1 2) nth_ctape_cstep_Shift_Left1)
                     apply simp_all
               apply (subst (asm) (4) M'_def)
               apply simp
               apply (cases "cstate ((TM.cstep M ^^ k) (TM.cinitial_config M w)) \<in> TM.TM.final_states M")
                apply simp
          using original_hds_spec [OF * **] Suc(10) [OF _ * **] apply simp
              apply (subst (asm) (4) M'_def)
              apply simp
              apply (cases "cstate ((TM.cstep M ^^ k) (TM.cinitial_config M w)) \<in> TM.TM.final_states M")
               apply simp
          using original_hds_spec [OF * **] Suc(10) [OF _ * **] apply simp
          unfolding valid_tm_next_move [OF valid_M'] Suc(1) [OF * **] apply simp
            apply (subst (asm) nth_ctape_cstep_Shift_Left1)
                 apply simp_all
          unfolding valid_tm_next_move [OF valid_M'] Suc(1) [OF * **] apply simp
             apply (subst M'_def)
             apply (subst (asm) M'_def)
             apply simp
            apply (erule Suc(5) [OF _ * **, simplified, OF exI])
           apply (cases "i = -1")
            apply simp
            apply (subst (1 2) nth_ctape_cstep_Shift_Right2)
                    apply simp_all
               apply (subst (asm) (4) M'_def)
               apply simp
               apply (cases "cstate ((TM.cstep M ^^ k) (TM.cinitial_config M w)) \<in> TM.TM.final_states M")
                apply simp
          using original_hds_spec [OF * **] Suc(10) [OF _ * **] apply simp
              apply (subst (asm) (4) M'_def)
              apply auto
          unfolding valid_tm_next_move [OF valid_M'] Suc(1) [OF * **] apply simp
          unfolding valid_tm_next_write [OF valid_M'] apply (subst M'_def)
            apply auto
             apply (subst (asm) (4) M'_def)
             apply simp
          using original_hds_spec [OF * **] Suc(10) [OF _ * **] apply simp
           apply (subst (1 2) nth_ctape_cstep_Shift_Right1)
                    apply simp_all
              apply (subst (asm) (4) M'_def)
              apply simp
              apply (cases "cstate ((TM.cstep M ^^ k) (TM.cinitial_config M w)) \<in> TM.TM.final_states M")
               apply simp
          using original_hds_spec [OF * **] Suc(10) [OF _ * **] apply simp
             apply (subst (asm) (4) M'_def)
             apply auto
          unfolding valid_tm_next_move [OF valid_M'] Suc(1) [OF * **] apply simp
           apply (subst (asm) nth_ctape_cstep_Shift_Right1)
          unfolding valid_tm_next_move [OF valid_M'] Suc(1) [OF * **] apply (subst M'_def)
                apply (subst (asm) M'_def)
                apply simp
               apply (subst (asm) M'_def)
               apply auto
            apply (cases "cstate ((TM.cstep M ^^ k) (TM.cinitial_config M w)) \<in> TM.TM.final_states M")
             apply simp
          using original_hds_spec [OF * **] Suc(10) [OF _ * **] apply simp
          using 1 Suc(1) [OF * **] apply simp
           apply (erule Suc(5) [OF _ * **, simplified, OF exI])
          apply (cases "cstate ((TM.cstep M ^^ k) (TM.cinitial_config M w)) \<in> TM.TM.final_states M")
           apply (subst (2) TM.cstep_def)
           apply simp
           apply (cases "i = 0")
            apply simp
            apply (subst nth_ctape_cstep_No_Shift2)
                apply simp_all
          unfolding valid_tm_next_move [OF valid_M'] Suc(1) [OF * **] apply simp
          unfolding valid_tm_next_write [OF valid_M'] apply (subst M'_def)
            apply simp
            apply (subst (asm) nth_ctape_cstep_No_Shift2)
                apply simp_all
          unfolding valid_tm_next_move [OF valid_M'] Suc(1) [OF * **] apply (subst M'_def)
             apply (subst (asm) M'_def)
             apply simp
          unfolding valid_tm_next_write [OF valid_M'] Suc(1) [OF * **] apply (subst (asm) M'_def)
            apply simp
            apply (subst (asm) nth_ctape_0 [symmetric])
            apply (subst nth_ctape_0 [symmetric])
            apply (erule Suc(5) [OF _ * **, simplified, OF exI])
           apply (subst nth_ctape_cstep_No_Shift1)
                apply simp_all
          unfolding valid_tm_next_move [OF valid_M'] Suc(1) [OF * **] apply simp
           apply (subst (asm) nth_ctape_cstep_No_Shift1)
                apply simp_all
          unfolding valid_tm_next_move [OF valid_M'] Suc(1) [OF * **] apply (subst M'_def)
            apply (subst (asm) M'_def)
            apply simp
           apply (erule Suc(5) [OF _ * **, simplified, OF exI])
          apply (cases "i = 0")
           apply simp
           apply (subst (1 2) nth_ctape_cstep_No_Shift2)
                   apply simp_all
             apply (subst (asm) (4) M'_def)
          using original_hds_spec [OF * **] Suc(10) [OF _ * **] apply simp
          unfolding valid_tm_next_move [OF valid_M'] Suc(1) [OF * **] apply simp
          unfolding valid_tm_next_write [OF valid_M'] Suc(1) [OF * **] apply (subst M'_def)
          using original_hds_spec [OF * **] Suc(10) [OF _ * **] apply simp
          apply (subst (1 2) nth_ctape_cstep_No_Shift1)
                   apply simp_all
            apply (subst (asm) (4) M'_def)
          using original_hds_spec [OF * **] Suc(10) [OF _ * **] apply simp
          unfolding valid_tm_next_move [OF valid_M'] Suc(1) [OF * **] apply simp
          apply (subst (asm) nth_ctape_cstep_No_Shift1)
               apply simp_all
          unfolding valid_tm_next_move [OF valid_M'] Suc(1) [OF * **] apply (subst M'_def)
           apply (subst (asm) M'_def)
           apply simp
          by (rule Suc(5) [OF _ * **, simplified, OF exI])
      qed
    next
      case 6
      hence *: "k \<le> n" and **: "k \<le> Suc (length w)" by simp_all
      have 1 [simp]: "cstate ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w)) \<notin>
                      TM.TM.final_states (Abs_TM M')"
        unfolding Suc(1) [OF * **] valid_tm_final_states [OF valid_M'] apply (subst (2) M'_def)
      proof simp
        have 1: "take k (map Some w) @ take (k - length w) [None] \<noteq> [] \<Longrightarrow>
                 last (take k (map Some w) @ take (k - length w) [None]) \<noteq> None" apply auto
          unfolding last_append apply auto
            apply (rule exI [where x="w ! (k - 1)"])
            apply auto
            apply (simp add: last_conv_nth min.commute)
          using 6(3) apply simp
          using 6(3) by simp
        show "(cstate ((TM.cstep M ^^ k) (TM.cinitial_config M w)),
              take k (map Some w) @ take (k - length w) [None], nat (cell_index (Abs_TM M') w 3 k), False)
              \<notin> final_states" unfolding final_states_def apply (rule notI)
          apply (drule IntD2)
          using 6 apply auto
        proof -
          assume a1: "0 < k" and a2: "w \<noteq> []" and a3: "last (take k (map Some w)) = None"
          have "last (take k (map Some w)) = Some (w ! (min k (length w - 1)))"
            using 1 "6.prems"(3) a1 a2 a3 by auto
          thus False using a3 by simp
        qed
      qed
      show ?case apply simp
        apply (cases "TM.TM.next_move (Abs_TM M') (state ((TM.step (Abs_TM M') ^^ k)
                      (TM.initial_config (Abs_TM M') w)))
                      (heads ((TM.step (Abs_TM M') ^^ k) (TM.initial_config (Abs_TM M') w))) 3")
        unfolding cell_index.simps unfolding cotm_heads_steps_congruence [symmetric]
          cotm_steps_congruences(1) [symmetric] apply (cases "- (cell_index (Abs_TM M') w 3 k - 1) = 1")
           apply simp
           apply (subst nth_ctape_cstep_Shift_Left2)
               apply assumption
              apply (auto simp add: valid_tm_next_move Suc(1) [OF * **])[1]
              apply (subst (asm) M'_def)
              apply simp
        unfolding valid_tm_final_states [OF valid_M']
        using * 1 "6.prems"(3) Suc(1) \<open>TM.TM.final_states (Abs_TM M') = TM_record.final_states M'\<close>
              apply force
             apply simp
            apply simp
        unfolding valid_tm_next_write [OF valid_M'] Suc(1) [OF * **] apply (subst M'_def)
        using 6 apply auto[1]
           apply (smt (verit, best) * ** Suc(6) nth_ctape_0)
          apply (subst nth_ctape_cstep_Shift_Left1)
               apply simp_all
           apply (simp add: Suc(1) [OF * **])
        using * ** Suc(6) cell_index.simps(1) apply blast
         apply (cases "- (cell_index (Abs_TM M') w 3 k + 1) = -1")
          apply simp
          apply (subst nth_ctape_cstep_Shift_Right2)
              apply simp_all
           apply (simp add: Suc(1) [OF * **])
        unfolding valid_tm_next_write [OF valid_M'] Suc(1) [OF * **] apply (subst M'_def)
          using 6 apply auto[1]
            apply (metis * ** Suc(6) ab_group_add_class.ab_diff_conv_add_uminus add_0
              cancel_comm_monoid_add_class.diff_cancel nth_ctape_0)
           apply (subst nth_ctape_cstep_Shift_Right1)
                apply simp_all
            apply (simp add: Suc(1) [OF * **])
          using * ** Suc(6) apply fastforce
          apply (cases "- cell_index (Abs_TM M') w 3 k = 0")
           apply simp
           apply (subst nth_ctape_cstep_No_Shift2)
               apply simp_all
            apply (simp add: Suc(1) [OF * **])
          unfolding valid_tm_next_write [OF valid_M'] Suc(1) [OF * **] apply (subst M'_def)
           using 6 apply auto[1]
            apply (smt (verit, best) * ** Suc(6) nth_ctape_0)
           apply (subst nth_ctape_cstep_No_Shift1)
                apply simp_all
            apply (simp add: Suc(1) [OF * **])
           using * ** Suc(6) by fastforce
    next
      case 7
      hence *: "k \<le> n" and **: "k \<le> Suc (length w)" by simp_all
      have 1 [simp]: "cstate ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w)) \<notin>
                      TM.TM.final_states (Abs_TM M')"
        unfolding Suc(1) [OF * **] valid_tm_final_states [OF valid_M'] apply (subst (2) M'_def)
      proof simp
        have 1: "take k (map Some w) @ take (k - length w) [None] \<noteq> [] \<Longrightarrow>
                 last (take k (map Some w) @ take (k - length w) [None]) \<noteq> None" apply auto
          unfolding last_append apply auto
            apply (rule exI [where x="w ! (k - 1)"])
            apply auto
            apply (simp add: last_conv_nth min.commute)
          using 7(5) apply simp
          using 7(5) by simp
        show "(cstate ((TM.cstep M ^^ k) (TM.cinitial_config M w)),
              take k (map Some w) @ take (k - length w) [None], nat (cell_index (Abs_TM M') w 3 k), False)
              \<notin> final_states" unfolding final_states_def apply (rule notI)
          apply (drule IntD2)
          using 7 apply auto
        proof -
          assume a1: "0 < k" and a2: "w \<noteq> []" and a3: "last (take k (map Some w)) = None"
          have "last (take k (map Some w)) = Some (w ! (min k (length w - 1)))"
            using 1 "7.prems"(5) a1 a2 a3 by auto
          thus False using a3 by simp
        qed
      qed
      show ?case
        apply (cases "k' = Suc k")
         apply simp
      proof -
        assume a1: "k' \<noteq> Suc k"
        hence ***: "k' \<le> k" using 7(2) by auto
        note 2 = Suc(7) [OF 7(1) *** 7(3) * **]
        have 3: "cstate ((TM.cstep M ^^ k) (TM.cinitial_config M w)) \<in> TM.TM.final_states M"
          using 7(3) unfolding TM.cis_final_def [symmetric] using ***
          by (metis cis_final_sub_imp diff_diff_cancel)
        show "tl (ctapes ((TM.cstep (Abs_TM M') ^^ Suc k) (TM.cinitial_config (Abs_TM M') w))) =
              tl (ctapes ((TM.cstep (Abs_TM M') ^^ k') (TM.cinitial_config (Abs_TM M') w)))"
          unfolding 2 [symmetric] apply simp
          apply (rule nth_equalityI)
           apply simp_all
          apply (subst (1 2) nth_tl)
            apply simp_all
        proof (rule nth_ctape_inject)
          fix i :: nat and j :: int
          assume a2: "i < Suc (Suc (TM.TM.tape_count M))"
          show "nth_ctape (ctapes (TM.cstep (Abs_TM M') ((TM.cstep (Abs_TM M') ^^ k)
                (TM.cinitial_config (Abs_TM M') w))) ! Suc i) j =
                nth_ctape (ctapes ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w)) ! Suc i) j"
            apply (cases "j = 0")
             apply simp
             apply (subst nth_ctape_cstep_No_Shift2)
            using a2 apply simp_all
            unfolding valid_tm_next_move [OF valid_M'] Suc(1) [OF * **] apply (subst M'_def)
            using 3 apply simp
            unfolding valid_tm_next_write [OF valid_M'] apply (subst M'_def)
            using 2 apply simp
            using 7 *** apply (auto simp add: nth_ctape_0 [symmetric])
            using 3 apply simp_all
            apply (subst nth_ctape_cstep_No_Shift1)
                 apply simp_all
            unfolding valid_tm_next_move [OF valid_M'] Suc(1) [OF * **] apply (subst M'_def)
            by simp
        qed
      qed
    next
      case 8
      hence *: "k \<le> n" and **: "k \<le> Suc (length w)" by simp_all
      have 1 [simp]: "cstate ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w)) \<notin>
                      TM.TM.final_states (Abs_TM M')"
        unfolding Suc(1) [OF * **] valid_tm_final_states [OF valid_M'] apply (subst (2) M'_def)
      proof simp
        have 1: "take k (map Some w) @ take (k - length w) [None] \<noteq> [] \<Longrightarrow>
                 last (take k (map Some w) @ take (k - length w) [None]) \<noteq> None" apply auto
          unfolding last_append apply auto
            apply (rule exI [where x="w ! (k - 1)"])
            apply auto
            apply (simp add: last_conv_nth min.commute)
          using 8(3) apply simp
          using 8(3) by simp
        show "(cstate ((TM.cstep M ^^ k) (TM.cinitial_config M w)),
              take k (map Some w) @ take (k - length w) [None], nat (cell_index (Abs_TM M') w 3 k), False)
              \<notin> final_states" unfolding final_states_def apply (rule notI)
          apply (drule IntD2)
          using 8 apply auto
        proof -
          assume a1: "0 < k" and a2: "w \<noteq> []" and a3: "last (take k (map Some w)) = None"
          have "last (take k (map Some w)) = Some (w ! (min k (length w - 1)))"
            using 1 "8.prems"(3) a1 a2 a3 by auto
          thus False using a3 by simp
        qed
      qed
      have 2: "cstate ((TM.cstep M ^^ k) (TM.cinitial_config M w)) \<notin> TM.TM.final_states M"
        using 8(1) apply auto
        apply (subst (asm) TM.cstep_def)
        by simp
      have ***: "None \<up> (k - length w) = take (k - length w) [None]"
        using 8(3) by simp
      have 3: "TM.TM.next_move (Abs_TM M') (cstate ((TM.cstep (Abs_TM M') ^^ k)
               (TM.cinitial_config (Abs_TM M') w)))
               (cheads ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w))) 3 =
               TM.TM.next_move M (state ((TM.step M ^^ k) (TM.initial_config M w)))
               (heads ((TM.step M ^^ k) (TM.initial_config M w))) 0"
        unfolding valid_tm_next_move [OF valid_M'] Suc(1) [OF * **] apply (subst M'_def)
        using 2 apply simp
        unfolding original_hds_spec [OF * **] cotm_steps_congruences(1)
        unfolding cotm_heads_steps_congruence ..
      have 5: "cstate ((TM.cstep M ^^ (k - 1)) (TM.cinitial_config M w)) \<notin> TM.TM.final_states M"
        using 2 unfolding TM.cis_final_def [symmetric] using cis_final_sub_imp by blast
      show ?case
        apply (cases "k = 0")
      proof auto
        assume a1: "chead (ctapes (TM.cstep (Abs_TM M') (TM.cinitial_config (Abs_TM M') w)) ! 3) =
                    Some extra_sym" and a2: "k = 0"
        have 3: "TM.TM.next_move M (cstate ((TM.cstep M ^^ 0) (TM.cinitial_config M w)))
                 (cheads ((TM.cstep M ^^ 0) (TM.cinitial_config M w))) 0 = No_Shift"
          apply (cases "TM.TM.next_move M (cstate ((TM.cstep M ^^ 0) (TM.cinitial_config M w)))
                        (cheads ((TM.cstep M ^^ 0) (TM.cinitial_config M w))) 0")
            apply simp_all
          using a1 unfolding nth_ctape_0 [symmetric] apply (subst (asm) nth_ctape_cstep_Shift_Left1)
                apply simp_all
             apply (metis (no_types, lifting) ext 3 a2 cinit_conf_state_init_conf
              cotm_heads_steps_congruence funpow_0 nth_ctape_0)
          using a2 1 apply simp
           apply (simp add: nth_ctape_cinit_non_input)
          using a1 unfolding nth_ctape_0 [symmetric] apply (subst (asm) nth_ctape_cstep_Shift_Right1)
               apply simp_all
            apply (metis (no_types, lifting) ext 3 a2 cinit_conf_state_init_conf
              cotm_heads_steps_congruence funpow_0 nth_ctape_0)
          using a2 1 apply simp
          by (simp add: nth_ctape_cinit_non_input)
        show "cell_index M w 0 (Suc 0) = 0"
          apply (subst cell_index.simps(4))
          using 3 apply simp_all
          by (simp add: cinit_conf_heads_init_conf cinit_conf_state_init_conf)
      next
        assume a1: "cell_index M w 0 (Suc 0) = 0" and a2: "k = 0"
        have 4: "TM.TM.next_move M (cstate ((TM.cstep M ^^ 0) (TM.cinitial_config M w)))
                 (cheads ((TM.cstep M ^^ 0) (TM.cinitial_config M w))) 0 = No_Shift"
          apply (cases "TM.TM.next_move M (cstate ((TM.cstep M ^^ 0) (TM.cinitial_config M w)))
                        (cheads ((TM.cstep M ^^ 0) (TM.cinitial_config M w))) 0")
            apply simp_all
          using a1 apply (subst (asm) cell_index.simps(2))
            apply simp_all
           apply (simp add: cinit_conf_heads_init_conf cinit_conf_state_init_conf)
          using a1 apply (subst (asm) cell_index.simps(3))
           apply simp_all
          by (simp add: cinit_conf_heads_init_conf cinit_conf_state_init_conf)
        show "chead (ctapes (TM.cstep (Abs_TM M') (TM.cinitial_config (Abs_TM M') w)) ! 3) = Some extra_sym"
          unfolding nth_ctape_0 [symmetric] apply (subst nth_ctape_cstep_No_Shift2)
              apply simp_all
            apply (metis 3 4 a2 cotm_heads_steps_congruence funpow_0 cotm_steps_congruences(1))
          using 1 a2 apply simp
          unfolding valid_tm_next_write [OF valid_M'] TM.cinitial_config_def
          apply (simp add: valid_tm_initial_state)
          unfolding M'_def init_state_def by simp
      next
        assume a1: "0 < k" and
               a2: "chead (ctapes (TM.cstep (Abs_TM M') ((TM.cstep (Abs_TM M') ^^ k)
                    (TM.cinitial_config (Abs_TM M') w))) ! 3) = Some extra_sym"
        show "cell_index M w 0 (Suc k) = 0" using a2
          apply (cases "TM.TM.next_move M (cstate ((TM.cstep M ^^ k) (TM.cinitial_config M w)))
                        (cheads ((TM.cstep M ^^ k) (TM.cinitial_config M w))) 0")
          unfolding nth_ctape_0 [symmetric] apply (subst (asm) nth_ctape_cstep_Shift_Left1)
                 apply simp_all
             apply (metis (no_types, lifting) ext 3 cotm_heads_steps_congruence
              cotm_steps_congruences(1) nth_ctape_0)
            apply (subst cell_index.simps(2))
             apply (simp add: cotm_heads_steps_congruence cotm_steps_congruences(1) nth_ctape_0)
            apply simp
          using Suc(6) [OF a1 * **, unfolded Suc(10) [OF 5 * **]] Suc(3) [of "- cell_index M w 0 k" "-1",
              OF _ _ * **] apply linarith
           apply (subst (asm) nth_ctape_cstep_Shift_Right1)
                apply simp_all
            apply (metis (no_types, lifting) ext 3 cotm_heads_steps_congruence
              cotm_steps_congruences(1) nth_ctape_0)
           apply (subst cell_index.simps(3))
            apply (simp add: cotm_heads_steps_congruence cotm_steps_congruences(1) nth_ctape_0)
          using Suc(6) [OF a1 * **, unfolded Suc(10) [OF 5 * **]] Suc(3) [of "- cell_index M w 0 k" 1,
              OF _ _ * **] apply linarith
          apply (subst (asm) nth_ctape_cstep_No_Shift2)
              apply simp_all
           apply (metis (no_types, lifting) ext 3 cotm_heads_steps_congruence
              cotm_steps_congruences(1) nth_ctape_0)
          apply (subst cell_index.simps(4))
           apply (simp add: cotm_heads_steps_congruence cotm_steps_congruences(1) nth_ctape_0)
          unfolding Suc(1) [OF * **] valid_tm_next_write [OF valid_M'] apply (subst (asm) M'_def)
          using 8 a1 apply simp
          apply (cases "w = []")
           apply simp_all
          using * ** 2 Suc(8) by blast
      next
        assume a1: "0 < k" and
               a2: "cell_index M w 0 (Suc k) = 0"
        show "chead (ctapes (TM.cstep (Abs_TM M') ((TM.cstep (Abs_TM M') ^^ k)
              (TM.cinitial_config (Abs_TM M') w))) ! 3) = Some extra_sym" using a2
          apply (cases "TM.TM.next_move M (cstate ((TM.cstep M ^^ k) (TM.cinitial_config M w)))
                        (cheads ((TM.cstep M ^^ k) (TM.cinitial_config M w))) 0")
          unfolding nth_ctape_0 [symmetric] apply (subst nth_ctape_cstep_Shift_Left1)
                 apply simp_all
             apply (metis (no_types, lifting) ext 3 cotm_heads_steps_congruence
              cotm_steps_congruences(1) nth_ctape_0)
            apply (subst (asm) cell_index.simps(2))
             apply (simp add: cotm_heads_steps_congruence cotm_steps_congruences(1) nth_ctape_0)
            apply simp
          using Suc(6) [OF a1 * **, unfolded Suc(10) [OF 5 * **]] apply argo
           apply (subst nth_ctape_cstep_Shift_Right1)
                apply simp_all
            apply (metis (no_types, lifting) ext 3 cotm_heads_steps_congruence
              cotm_steps_congruences(1) nth_ctape_0)
          apply (subst (asm) cell_index.simps(3))
            apply (simp add: cotm_heads_steps_congruence cotm_steps_congruences(1) nth_ctape_0)
          using Suc(6) [OF a1 * **, unfolded Suc(10) [OF 5 * **]]
           apply (metis (no_types, lifting) ab_group_add_class.ab_diff_conv_add_uminus add.commute
              add.right_neutral add_diff_cancel_right')
          apply (subst nth_ctape_cstep_No_Shift2)
              apply simp_all
           apply (metis (no_types, lifting) ext 3 cotm_heads_steps_congruence
              cotm_steps_congruences(1) nth_ctape_0)
          apply (subst (asm) cell_index.simps(4))
           apply (simp add: cotm_heads_steps_congruence cotm_steps_congruences(1) nth_ctape_0)
          using Suc(6) [OF a1 * **, unfolded Suc(10) [OF 5 * **]] apply simp
          unfolding nth_ctape_0 valid_tm_next_write [OF valid_M'] Suc(1) [OF * **] apply (subst M'_def)
          by simp
      qed
    next
      case 9
      hence *: "k \<le> n" and **: "k \<le> Suc (length w)" by simp_all
      have 1 [simp]: "cstate ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w)) \<notin>
                      TM.TM.final_states (Abs_TM M')"
        unfolding Suc(1) [OF * **] valid_tm_final_states [OF valid_M'] apply (subst (2) M'_def)
      proof simp
        have 1: "take k (map Some w) @ take (k - length w) [None] \<noteq> [] \<Longrightarrow>
                 last (take k (map Some w) @ take (k - length w) [None]) \<noteq> None" apply auto
          unfolding last_append apply auto
            apply (rule exI [where x="w ! (k - 1)"])
            apply auto
            apply (simp add: last_conv_nth min.commute)
          using 9(2) apply simp
          using 9(2) by simp
        show "(cstate ((TM.cstep M ^^ k) (TM.cinitial_config M w)),
              take k (map Some w) @ take (k - length w) [None], nat (cell_index (Abs_TM M') w 3 k), False)
              \<notin> final_states" unfolding final_states_def apply (rule notI)
          apply (drule IntD2)
          using 9 apply auto
        proof -
          assume a1: "0 < k" and a2: "w \<noteq> []" and a3: "last (take k (map Some w)) = None"
          have "last (take k (map Some w)) = Some (w ! (min k (length w - 1)))"
            using 1 "9.prems"(2) a1 a2 a3 by auto
          thus False using a3 by simp
        qed
      qed
      show ?case apply (subst cell_index.simps(3))
        unfolding valid_tm_next_move [OF valid_M'] Suc(1) [OF * **, unfolded cotm_steps_congruences(1)]
         apply (subst M'_def)
        using 9 apply simp
        apply simp
        using Suc(9) [OF * **] .
    next
      case 10
      hence *: "k \<le> n" and **: "k \<le> Suc (length w)" by simp_all
      have 1 [simp]: "cstate ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w)) \<notin>
                      TM.TM.final_states (Abs_TM M')"
        unfolding Suc(1) [OF * **] valid_tm_final_states [OF valid_M'] apply (subst (2) M'_def)
      proof simp
        have 1: "take k (map Some w) @ take (k - length w) [None] \<noteq> [] \<Longrightarrow>
                 last (take k (map Some w) @ take (k - length w) [None]) \<noteq> None" apply auto
          unfolding last_append apply auto
            apply (rule exI [where x="w ! (k - 1)"])
            apply auto
            apply (simp add: last_conv_nth min.commute)
          using 10(3) apply simp
          using 10(3) by simp
        show "(cstate ((TM.cstep M ^^ k) (TM.cinitial_config M w)),
              take k (map Some w) @ take (k - length w) [None], nat (cell_index (Abs_TM M') w 3 k), False)
              \<notin> final_states" unfolding final_states_def apply (rule notI)
          apply (drule IntD2)
          using 10 apply auto
        proof -
          assume a1: "0 < k" and a2: "w \<noteq> []" and a3: "last (take k (map Some w)) = None"
          have "last (take k (map Some w)) = Some (w ! (min k (length w - 1)))"
            using 1 "10.prems"(3) a1 a2 a3 by auto
          thus False using a3 by simp
        qed
      qed
      have 2: "cstate ((TM.cstep M ^^ k) (TM.cinitial_config M w)) \<notin> TM.TM.final_states M"
        using 10(1) by simp
      have ***: "None \<up> (k - length w) = take (k - length w) [None]"
        using 10(3) by simp
      have 3: "TM.TM.next_move (Abs_TM M') (cstate ((TM.cstep (Abs_TM M') ^^ k)
               (TM.cinitial_config (Abs_TM M') w)))
               (cheads ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w))) 3 =
               TM.TM.next_move M (state ((TM.step M ^^ k) (TM.initial_config M w)))
               (heads ((TM.step M ^^ k) (TM.initial_config M w))) 0"
        unfolding valid_tm_next_move [OF valid_M'] Suc(1) [OF * **] apply (subst M'_def)
        using 2 apply simp
        unfolding original_hds_spec [OF * **] cotm_steps_congruences(1)
        unfolding cotm_heads_steps_congruence ..
      have 4: "cstate ((TM.cstep M ^^ (k - 1)) (TM.cinitial_config M w)) \<notin> TM.TM.final_states M"
        using 2 unfolding TM.cis_final_def [symmetric] using cis_final_sub_imp by blast
      show ?case apply (rule cell_index_eq_next_moves_eq)
         apply (rule Suc(10) [OF 4 * **])
        using 3 unfolding cotm_steps_congruences(1) cotm_heads_steps_congruence .
    next
      case 11
      hence *: "k \<le> n" and **: "k \<le> Suc (length w)" by simp_all
      have 1 [simp]: "cstate ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w)) \<notin>
                      TM.TM.final_states (Abs_TM M')"
        unfolding Suc(1) [OF * **] valid_tm_final_states [OF valid_M'] apply (subst (2) M'_def)
      proof simp
        have 1: "take k (map Some w) @ take (k - length w) [None] \<noteq> [] \<Longrightarrow>
                 last (take k (map Some w) @ take (k - length w) [None]) \<noteq> None" apply auto
          unfolding last_append apply auto
            apply (rule exI [where x="w ! (k - 1)"])
            apply auto
            apply (simp add: last_conv_nth min.commute)
          using 11(6) apply simp
          using 11(6) by simp
        show "(cstate ((TM.cstep M ^^ k) (TM.cinitial_config M w)),
              take k (map Some w) @ take (k - length w) [None], nat (cell_index (Abs_TM M') w 3 k), False)
              \<notin> final_states" unfolding final_states_def apply (rule notI)
          apply (drule IntD2)
          using 11 apply auto
        proof -
          assume a1: "0 < k" and a2: "w \<noteq> []" and a3: "last (take k (map Some w)) = None"
          have "last (take k (map Some w)) = Some (w ! (min k (length w - 1)))"
            using 1 "11.prems"(6) a1 a2 a3 by auto
          thus False using a3 by simp
        qed
      qed
      have 2: "cstate ((TM.cstep M ^^ k) (TM.cinitial_config M w)) \<notin> TM.TM.final_states M"
        using 11(2) apply auto
        apply (subst (asm) TM.cstep_def)
        by simp
      show ?case apply (cases "k = 0")
        using 11 apply simp
         apply (cases "TM.TM.next_move (Abs_TM M') (cstate (TM.cinitial_config (Abs_TM M') w))
                       (cheads (TM.cinitial_config (Abs_TM M') w)) 2")
           apply (subst (asm) cell_index.simps(2))
        using Suc(1) [OF * **] apply simp
            apply (simp add: valid_tm_next_move)
            apply (subst (asm) M'_def)
            apply (subst M'_def)
        unfolding init_state_def using 2 apply auto
             apply (simp add: TM.cinitial_config_def)
            apply (simp add: cinit_conf_heads_init_conf cinit_conf_state_init_conf init_state_def)
           apply (subst nth_ctape_cstep_Shift_Left2)
               apply simp_all
        using 1 apply simp
        unfolding valid_tm_next_write [OF valid_M'] using Suc(1) [OF * **] apply simp
           apply (subst M'_def)
           apply simp
          apply (subst (asm) cell_index.simps(3))
        using Suc(1) [OF * **] apply (simp add: valid_tm_next_move)
           apply (subst (asm) M'_def)
           apply (subst M'_def)
        unfolding init_state_def apply auto
            apply (subst (asm) (4) TM.cinitial_config_def)
            apply simp
           apply (simp add: cinit_conf_heads_init_conf cinit_conf_state_init_conf init_state_def)
          apply (subst cell_index.simps(3))
        using Suc(1) [OF * **] apply (simp add: valid_tm_next_move)
           apply (subst (asm) M'_def)
           apply (subst M'_def)
        unfolding init_state_def apply auto
            apply (subst (asm) (4) TM.cinitial_config_def)
            apply simp
           apply (simp add: cinit_conf_heads_init_conf cinit_conf_state_init_conf init_state_def)
          apply (subst nth_ctape_cstep_Shift_Right2)
              apply simp_all
        using 1 apply simp
        unfolding valid_tm_next_write [OF valid_M'] using Suc(1) [OF * **] apply simp
          apply (subst M'_def)
          apply simp
         apply (subst (asm) cell_index.simps(4))
        using Suc(1) [OF * **] apply (simp add: valid_tm_next_move)
          apply (subst (asm) M'_def)
          apply (subst M'_def)
        unfolding init_state_def apply auto
          apply (simp add: cinit_conf_heads_init_conf cinit_conf_state_init_conf init_state_def)
         apply (subst cell_index.simps(4))
        using Suc(1) [OF * **] apply (simp add: valid_tm_next_move)
          apply (subst (asm) M'_def)
          apply (subst M'_def)
        unfolding init_state_def apply auto
          apply (simp add: cinit_conf_heads_init_conf cinit_conf_state_init_conf init_state_def)
         apply (subst nth_ctape_cstep_No_Shift2)
             apply simp_all
        using 1 apply simp
        unfolding valid_tm_next_write [OF valid_M'] using Suc(1) [OF * **] apply simp
         apply (subst M'_def)
         apply simp
        apply (cases "TM.TM.next_move (Abs_TM M') (cstate ((TM.cstep (Abs_TM M') ^^ k)
                      (TM.cinitial_config (Abs_TM M') w)))
                      (cheads ((TM.cstep (Abs_TM M') ^^ k) (TM.cinitial_config (Abs_TM M') w))) 2")
          apply (cases "i = 1")
           apply simp
           apply (subst nth_ctape_cstep_Shift_Left2)
               apply simp_all
        unfolding valid_tm_next_write [OF valid_M'] apply (simp add: Suc(1) [OF * **])
           apply (subst M'_def)
           apply simp
          apply (subst nth_ctape_cstep_Shift_Left1)
               apply simp_all
        using 11(3, 4) [simplified] apply (subst (asm) (1 2) cell_index.simps(2))
            apply (simp add: valid_tm_next_move cotm_heads_steps_congruence [symmetric]
            cotm_steps_congruences(1) [symmetric] Suc(1) [OF * **])
            apply (subst M'_def)
            apply (subst (asm) M'_def)
            apply simp
           apply (simp add: valid_tm_next_move cotm_heads_steps_congruence [symmetric]
            cotm_steps_congruences(1) [symmetric] Suc(1) [OF * **])
           apply (subst M'_def)
           apply (subst (asm) (3) M'_def)
           apply simp
          apply (cases "max_cell_index (Abs_TM M') w 3 k = max_cell_index (Abs_TM M') w 3 (k - 1)")
           apply (cases "min_cell_index (Abs_TM M') w 3 k = min_cell_index (Abs_TM M') w 3 (k - 1)")
        using Suc(11) [OF _ 2 _ _ * **, of "i - 1"] apply force
        using min_cell_Suc_uneq_m1 [of "Abs_TM M'" w 3 "k - 1"] apply simp
        using min_cell_index_Suc_lt_impl_eq_cell_index_Suc [of "Abs_TM M'" w 3 "k - 1"] apply simp
           apply (simp add: Suc(11) [OF _ 2 _ _ * **, of "i - 1"])
          apply (cases "min_cell_index (Abs_TM M') w 3 k = min_cell_index (Abs_TM M') w 3 (k - 1)")
           apply simp
        using max_cell_Suc_uneq_p1 [of "Abs_TM M'" w 3 "k - 1"] apply simp
        using max_cell_index_Suc_gt_impl_eq_cell_index_Suc [of "Abs_TM M'" w 3 "k - 1"] apply simp
        using Suc(11) [OF _ 2 _ _ * **, of "i - 1"] apply simp
        using min_cell_Suc_uneq_m1 [of "Abs_TM M'" w 3 "k - 1"] max_cell_Suc_uneq_p1 [of "Abs_TM M'" w 3 "k - 1"]
        using max_cell_index_Suc_gt_impl_eq_cell_index_Suc [of "Abs_TM M'" w 3 "k - 1"]
              min_cell_index_Suc_lt_impl_eq_cell_index_Suc [of "Abs_TM M'" w 3 "k - 1"] apply simp
         apply (cases "i = -1")
          apply simp
          apply (subst nth_ctape_cstep_Shift_Right2)
              apply simp_all
        unfolding valid_tm_next_write [OF valid_M'] apply (simp add: Suc(1) [OF * **])
          apply (subst M'_def)
          apply simp
         apply (subst nth_ctape_cstep_Shift_Right1)
              apply simp_all
        using 11(3, 4) [simplified] apply (subst (asm) (1 2) cell_index.simps(3))
           apply (simp add: valid_tm_next_move cotm_heads_steps_congruence [symmetric]
            cotm_steps_congruences(1) [symmetric] Suc(1) [OF * **])
           apply (subst M'_def)
           apply (subst (asm) M'_def)
           apply simp
          apply (simp add: valid_tm_next_move cotm_heads_steps_congruence [symmetric]
            cotm_steps_congruences(1) [symmetric] Suc(1) [OF * **])
        apply (subst M'_def)
          apply (subst (asm) (3) M'_def)
          apply simp
         apply (cases "max_cell_index (Abs_TM M') w 3 k = max_cell_index (Abs_TM M') w 3 (k - 1)")
          apply (cases "min_cell_index (Abs_TM M') w 3 k = min_cell_index (Abs_TM M') w 3 (k - 1)")
        using Suc(11) [OF _ 2 _ _ * **, of "i + 1"] apply force
        using min_cell_Suc_uneq_m1 [of "Abs_TM M'" w 3 "k - 1"] apply simp
        using min_cell_index_Suc_lt_impl_eq_cell_index_Suc [of "Abs_TM M'" w 3 "k - 1"] apply simp
          apply (simp add: Suc(11) [OF _ 2 _ _ * **, of "i + 1"])
         apply (cases "min_cell_index (Abs_TM M') w 3 k = min_cell_index (Abs_TM M') w 3 (k - 1)")
          apply simp
        using max_cell_Suc_uneq_p1 [of "Abs_TM M'" w 3 "k - 1"] apply simp
        using max_cell_index_Suc_gt_impl_eq_cell_index_Suc [of "Abs_TM M'" w 3 "k - 1"] apply simp
        using Suc(11) [OF _ 2 _ _ * **, of "i + 1"] apply simp
        using min_cell_Suc_uneq_m1 [of "Abs_TM M'" w 3 "k - 1"] max_cell_Suc_uneq_p1 [of "Abs_TM M'" w 3 "k - 1"]
        using max_cell_index_Suc_gt_impl_eq_cell_index_Suc [of "Abs_TM M'" w 3 "k - 1"]
              min_cell_index_Suc_lt_impl_eq_cell_index_Suc [of "Abs_TM M'" w 3 "k - 1"] apply simp
        apply (cases "i = 0")
         apply simp
         apply (subst nth_ctape_cstep_No_Shift2)
             apply simp_all
        unfolding valid_tm_next_write [OF valid_M'] apply (simp add: Suc(1) [OF * **])
         apply (subst M'_def)
         apply simp
        apply (subst nth_ctape_cstep_No_Shift1)
             apply simp_all
        using 11(3, 4) [simplified] apply (subst (asm) (1 2) cell_index.simps(4))
          apply (simp add: valid_tm_next_move cotm_heads_steps_congruence [symmetric]
            cotm_steps_congruences(1) [symmetric] Suc(1) [OF * **])
          apply (subst M'_def)
          apply (subst (asm) M'_def)
        apply simp
         apply (simp add: valid_tm_next_move cotm_heads_steps_congruence [symmetric]
            cotm_steps_congruences(1) [symmetric] Suc(1) [OF * **])
         apply (subst M'_def)
         apply (subst (asm) (3) M'_def)
         apply simp
        apply (cases "max_cell_index (Abs_TM M') w 3 k = max_cell_index (Abs_TM M') w 3 (k - 1)")
         apply (cases "min_cell_index (Abs_TM M') w 3 k = min_cell_index (Abs_TM M') w 3 (k - 1)")
        using Suc(11) [OF _ 2 _ _ * **, of i] apply force
        using min_cell_Suc_uneq_m1 [of "Abs_TM M'" w 3 "k - 1"] apply simp
        using min_cell_index_Suc_lt_impl_eq_cell_index_Suc [of "Abs_TM M'" w 3 "k - 1"] apply simp
         apply (simp add: Suc(11) [OF _ 2 _ _ * **, of i])
        apply (cases "min_cell_index (Abs_TM M') w 3 k = min_cell_index (Abs_TM M') w 3 (k - 1)")
        apply simp
        using max_cell_Suc_uneq_p1 [of "Abs_TM M'" w 3 "k - 1"] apply simp
        using max_cell_index_Suc_gt_impl_eq_cell_index_Suc [of "Abs_TM M'" w 3 "k - 1"] apply simp
        using Suc(11) [OF _ 2 _ _ * **, of i] apply simp
        using min_cell_Suc_uneq_m1 [of "Abs_TM M'" w 3 "k - 1"] max_cell_Suc_uneq_p1 [of "Abs_TM M'" w 3 "k - 1"]
        using max_cell_index_Suc_gt_impl_eq_cell_index_Suc [of "Abs_TM M'" w 3 "k - 1"]
              min_cell_index_Suc_lt_impl_eq_cell_index_Suc [of "Abs_TM M'" w 3 "k - 1"] by simp
    }
  qed
  have f201: "cstate (TM.csteps (Abs_TM M') k (TM.cinitial_config (Abs_TM M') w)) =
              (cstate (TM.csteps M k (TM.cinitial_config M w)), take (Suc n) (map Some w @ [None]),
              nat (cell_index (Abs_TM M') w 3 k), False)" and
       f202: "\<And>i. i \<ge> 4 \<Longrightarrow> i < TM.tape_count (Abs_TM M') \<Longrightarrow>
              ctapes (TM.csteps (Abs_TM M') k (TM.cinitial_config (Abs_TM M') w)) ! i =
              ctapes (TM.csteps M k (TM.cinitial_config M w)) ! (i - 3)" and
       f203: "\<And>i j. nth_ctape (ctapes (TM.csteps (Abs_TM M') k
              (TM.cinitial_config (Abs_TM M') w)) ! 3) i = Some extra_sym \<Longrightarrow>
              nth_ctape (ctapes (TM.csteps (Abs_TM M') k
              (TM.cinitial_config (Abs_TM M') w)) ! 3) j = Some extra_sym \<Longrightarrow> i = j" and
       f204: "\<And>i. nth_ctape (ctapes (TM.csteps (Abs_TM M') k
              (TM.cinitial_config (Abs_TM M') w)) ! 0) i =
              nth_ctape (ctapes (TM.cinitial_config (Abs_TM M') w) ! 0) (i + n)" and
       f205: "\<And>i. nth_ctape (ctapes (TM.csteps (Abs_TM M') k
              (TM.cinitial_config (Abs_TM M') w)) ! 2) i \<noteq> None \<Longrightarrow> nth_ctape (ctapes (TM.csteps (Abs_TM M') k
              (TM.cinitial_config (Abs_TM M') w)) ! 1) i = nth_ctape (ctapes (TM.csteps M k
              (TM.cinitial_config M w)) ! 0) i" and
       f206: "k > 0 \<Longrightarrow> nth_ctape (ctapes (TM.csteps (Abs_TM M') k
              (TM.cinitial_config (Abs_TM M') w)) ! 3) (-cell_index (Abs_TM M') w 3 k) = Some extra_sym" and
       f207: "\<And>k'. k' > 0 \<Longrightarrow> k' \<le> k \<Longrightarrow> cstate (TM.csteps M k' (TM.cinitial_config M w)) \<in> TM.final_states M \<Longrightarrow>
              tl (ctapes (TM.csteps (Abs_TM M') k (TM.cinitial_config (Abs_TM M') w))) =
              tl (ctapes (TM.csteps (Abs_TM M') k' (TM.cinitial_config (Abs_TM M') w)))" and
       f208: "cstate (TM.csteps M k (TM.cinitial_config M w)) \<notin> TM.final_states M \<Longrightarrow>
              chead (ctapes (TM.csteps (Abs_TM M') k (TM.cinitial_config (Abs_TM M') w)) ! 3) = Some extra_sym \<longleftrightarrow>
              cell_index M w 0 k = 0 \<and> k > 0" and
       f209: "cell_index (Abs_TM M') w 0 k = Suc n" and
       f210: "cstate ((TM.cstep M ^^ (k - 1)) (TM.cinitial_config M w)) \<notin> TM.TM.final_states M \<Longrightarrow>
              cell_index (Abs_TM M') w 3 k = cell_index M w 0 k" and
       f211: "\<And>i. 0 < k \<Longrightarrow> cstate ((TM.cstep M ^^ k) (TM.cinitial_config M w)) \<notin> TM.TM.final_states M \<Longrightarrow>
              i \<le> max_cell_index (Abs_TM M') w 3 (k - 1) - cell_index (Abs_TM M') w 3 k \<Longrightarrow>
              i \<ge> min_cell_index (Abs_TM M') w 3 (k - 1) - cell_index (Abs_TM M') w 3 k \<Longrightarrow>
              nth_ctape (ctapes (TM.csteps (Abs_TM M') k (TM.cinitial_config (Abs_TM M') w)) ! 2) i = Some extra_sym"
       if "k \<ge> Suc n" and "length w \<ge> n" and "\<And>k'. k' \<le> k \<Longrightarrow> cell_index (Abs_TM M') w 3 k' \<le> n" and
         "set w \<subseteq> TM.symbols M"
       for k :: nat and w :: "'s list" using that
  proof (induction k rule: full_nat_induct_at_least)
    case k
    have original_hds_correct: "original_hds (cheads ((TM.cstep (Abs_TM M') ^^ n) (TM.cinitial_config (Abs_TM M') w)))
                                (take n (map Some w)) (nat (cell_index (Abs_TM M') w 3 n)) =
                                cheads ((TM.cstep M ^^ n) (TM.cinitial_config M w))"
      if "n \<le> length w" and "\<And>k'. k' \<le> Suc n \<Longrightarrow> cell_index (Abs_TM M') w 3 k' \<le> int n" and "set w \<subseteq> TM.TM.symbols M"
      apply (rule nth_equalityI')
       apply (simp add: original_hds_def)
      apply simp
    proof -
      fix i :: nat
      assume a1: "i < TM.tape_count M"
      show "original_hds (cheads ((TM.cstep (Abs_TM M') ^^ n) (TM.cinitial_config (Abs_TM M') w))) (take n (map Some w))
            (nat (cell_index (Abs_TM M') w 3 n)) ! i = chead (ctapes ((TM.cstep M ^^ n) (TM.cinitial_config M w)) ! i)"
      proof (cases i)
        case 0
        show ?thesis unfolding 0 original_hds_def apply auto
          unfolding nth_ctape_0 [symmetric]
        proof -
          fix y :: 's
          assume a1: "nth_ctape (ctapes ((TM.cstep (Abs_TM M') ^^ n) (TM.cinitial_config (Abs_TM M') w)) ! 2) 0 =
                      Some y"
          show "hd (tl (map (\<lambda>ct. nth_ctape ct 0) (ctapes ((TM.cstep (Abs_TM M') ^^ n)
                (TM.cinitial_config (Abs_TM M') w))))) =
                nth_ctape (ctapes ((TM.cstep M ^^ n) (TM.cinitial_config M w)) ! 0) 0"
            apply (subst zeroth_is_head [symmetric])
             apply auto
             apply (drule arg_cong [where f=length])
             apply simp
            apply (subst nth_tl)
             apply simp
            apply (subst nth_map)
             apply simp
            apply (rule f105 [OF le_refl, of w 0, simplified, OF _ exI, OF _ a1])
            using that(1) by simp
          thus "hd (tl (map (\<lambda>ct. nth_ctape ct 0) (ctapes ((TM.cstep (Abs_TM M') ^^ n)
                (TM.cinitial_config (Abs_TM M') w))))) =
                nth_ctape (ctapes ((TM.cstep M ^^ n) (TM.cinitial_config M w)) ! 0) 0" .
          thus "hd (tl (map (\<lambda>ct. nth_ctape ct 0) (ctapes ((TM.cstep (Abs_TM M') ^^ n)
                (TM.cinitial_config (Abs_TM M') w))))) =
                nth_ctape (ctapes ((TM.cstep M ^^ n) (TM.cinitial_config M w)) ! 0) 0" .
          thus "hd (tl (map (\<lambda>ct. nth_ctape ct 0) (ctapes ((TM.cstep (Abs_TM M') ^^ n)
                (TM.cinitial_config (Abs_TM M') w))))) =
                nth_ctape (ctapes ((TM.cstep M ^^ n) (TM.cinitial_config M w)) ! 0) 0" .
          thus "hd (tl (map (\<lambda>ct. nth_ctape ct 0) (ctapes ((TM.cstep (Abs_TM M') ^^ n)
                (TM.cinitial_config (Abs_TM M') w))))) =
                nth_ctape (ctapes ((TM.cstep M ^^ n) (TM.cinitial_config M w)) ! 0) 0" .
          thus "hd (tl (map (\<lambda>ct. nth_ctape ct 0) (ctapes ((TM.cstep (Abs_TM M') ^^ n)
                (TM.cinitial_config (Abs_TM M') w))))) =
                nth_ctape (ctapes ((TM.cstep M ^^ n) (TM.cinitial_config M w)) ! 0) 0" .
        next
          assume a1: "0 < cell_index (Abs_TM M') w 3 n" and
                 a2: "min (length w) n \<le> nat (cell_index (Abs_TM M') w 3 n)" and
                 a3: "nth_ctape (ctapes ((TM.cstep (Abs_TM M') ^^ n)
                      (TM.cinitial_config (Abs_TM M') w)) ! 2) 0 = None"
          have 1: "min (length w) n = n" using that(1) by simp
          have 2: "cell_index (Abs_TM M') w 3 n = n"
            using a2 unfolding 1 using cell_index_abs_bound [of "Abs_TM M'" w 3 n] by simp
          have 3: "cell_index (Abs_TM M') w 3 (n - 1) = n - 1"
            using 2 cell_index_eq_steps_all_lower_eq diff_le_self by blast
          have 4: "TM.next_move (Abs_TM M') (cstate (TM.csteps (Abs_TM M') (n - 1) (TM.cinitial_config (Abs_TM M') w)))
                   (cheads (TM.csteps (Abs_TM M') (n - 1) (TM.cinitial_config (Abs_TM M') w))) 3 = Shift_Right"
            apply (cases n)
            using n_gt_0 apply simp
            apply (cases "TM.next_move (Abs_TM M') (cstate (TM.csteps (Abs_TM M') (n - 1)
                          (TM.cinitial_config (Abs_TM M') w)))
                          (cheads (TM.csteps (Abs_TM M') (n - 1) (TM.cinitial_config (Abs_TM M') w))) 3")
              using 2 3 apply simp_all
               apply (subst (asm) cell_index.simps(2))
                apply (simp add: cotm_heads_steps_congruence cotm_steps_congruences(1))
               apply simp
              apply (subst (asm) cell_index.simps(4))
               apply (simp add: cotm_heads_steps_congruence cotm_steps_congruences(1))
              by simp
          have 5: "\<not>TM.cis_final M (TM.csteps M (n - 1) (TM.cinitial_config M w))"
            apply standard
            unfolding TM.cis_final_def using 4 unfolding valid_tm_next_move [OF valid_M']
            apply (subst (asm) f101)
              apply simp
            using that(1) apply simp
            apply (subst (asm) M'_def)
            by simp
          note f110 [OF le_refl _ 5 [unfolded TM.cis_final_def]]
          hence 6: "cell_index M w 0 n = n" using 2 that(1) by simp
          have 7: "cell_index M w 0 (n - 1) = n - 1"
            using 6 cell_index_eq_steps_all_lower_eq diff_le_self by blast
          have 8: "max_cell_index M w 0 (n - 1) = n - 1" using 7 cell_index_eq_k_is_max by blast
          show "hd (map (\<lambda>ct. nth_ctape ct 0) (ctapes ((TM.cstep (Abs_TM M') ^^ n)
                (TM.cinitial_config (Abs_TM M') w)))) =
                nth_ctape (ctapes ((TM.cstep M ^^ n) (TM.cinitial_config M w)) ! 0) 0"
            apply (subst hd_map)
             apply auto
             apply (drule arg_cong [where f=length])
             apply simp
            apply (subst zeroth_is_head [symmetric])
             apply auto
             apply (drule arg_cong [where f=length])
             apply simp
            apply (subst f104 [OF le_refl, of w 0])
            using that(1) apply simp
            apply simp
            apply (subst f109 [OF le_refl, of w])
            using that(1) apply simp
            apply (subst csteps_untouched_cells_head2_right [of 0 M n w, OF _ 5 _ n_gt_0, folded nth_ctape_0])
              apply simp
            using 6 8 n_gt_0 apply simp
            unfolding 6 apply simp
            unfolding TM.cinitial_config_def TM_abbrevs.cinput_tape_def apply auto
            unfolding empty_ctape_def apply simp
            apply (subst nth_ctape_pos)
            using n_gt_0 apply simp_all
            by (simp add: nat_diff_distrib')
        next
          assume a1: "0 < cell_index (Abs_TM M') w 3 n" and
                 a2: "\<not> min (length w) n \<le> nat (cell_index (Abs_TM M') w 3 n)" and
                 a3: "nth_ctape (ctapes ((TM.cstep (Abs_TM M') ^^ n) (TM.cinitial_config (Abs_TM M') w)) ! 2) 0 = None"
          have 1: "cstate (TM.cinitial_config M w) \<notin> TM.final_states M"
          proof
            assume a4: "cstate (TM.cinitial_config M w) \<in> TM.TM.final_states M"
            have 1: "TM.next_move (Abs_TM M') (cstate (TM.csteps (Abs_TM M') k'
                     (TM.cinitial_config (Abs_TM M') w)))
                     (cheads (TM.csteps (Abs_TM M') k' (TM.cinitial_config (Abs_TM M') w))) 3 = No_Shift"
              if "k' \<le> n" for k' :: nat
              apply (subst f101)
                apply fact
              using \<open>n \<le> length w\<close> that apply simp
              unfolding valid_tm_next_move [OF valid_M'] apply (subst M'_def)
              using a4 apply auto
              by (metis TM.cis_final_def cis_final_sub_imp diff_self_eq_0 funpow_0)
            have 2: "k' \<le> n \<Longrightarrow> cell_index (Abs_TM M') w 3 k' = 0" for k' :: nat
              apply (induction k')
               apply simp
              apply (subst cell_index.simps(4))
              using 1 apply (simp add: cotm_heads_steps_congruence cotm_steps_congruences(1))
              by fastforce
            show False using 2 [OF le_refl] a1 by simp
          qed
          show "Some (w ! nat (cell_index (Abs_TM M') w 3 n)) =
                nth_ctape (ctapes ((TM.cstep M ^^ n) (TM.cinitial_config M w)) ! 0) 0"
          proof (cases "cstate (TM.csteps M n (TM.cinitial_config M w)) \<in> TM.TM.final_states M")
            case True
            define k' :: nat where "k' \<equiv> (LEAST k'. cstate (TM.csteps M k' (TM.cinitial_config M w)) \<in>
                                          TM.TM.final_states M)"
            note 2 = LeastI [of "\<lambda>k'. cstate (TM.csteps M k' (TM.cinitial_config M w)) \<in> TM.TM.final_states M",
                OF True, folded k'_def]
            have 3: "k' > 0"
              apply (rule ccontr)
              apply simp
              using 1 2 by simp
            have 4: "cstate ((TM.cstep M ^^ (k' - 1)) (TM.cinitial_config M w)) \<notin> TM.TM.final_states M"
              using 3 2 by (metis diff_diff_cancel k'_def less_one linorder_not_less not_less_Least zero_less_diff)
            define k'' :: nat where "k'' \<equiv> k' - 1"
            have 5: "k' = Suc k''" unfolding k''_def using 3 by simp
            note 6 = 4 [folded k''_def]
            note 7 = 2 [unfolded 5]
            have 8: "k' \<le> n" using True 2
                Least_le [of "\<lambda>k'. cstate (TM.csteps M k' (TM.cinitial_config M w)) \<in> TM.TM.final_states M", OF True]
              unfolding k'_def by simp
            have 9: "k'' < n" using 8 unfolding 5 by simp
            have 10: "k'' \<ge> k' \<Longrightarrow> k'' \<le> n \<Longrightarrow> cell_index (Abs_TM M') w 3 k'' = cell_index (Abs_TM M') w 3 k'"
              for k'' :: nat
            proof (induction k'' rule: nat_induct_at_least)
              case base
              show ?case ..
            next
              case (Suc k'')
              hence 1: "k'' \<le> n" by simp
              show ?case unfolding Suc(2) [OF 1, symmetric]
                apply (subst cell_index.simps(4))
                unfolding cotm_steps_congruences(1) [symmetric] cotm_heads_steps_congruence [symmetric]
                 apply (subst f101)
                   apply fact
                using 1 that(1) apply simp
                unfolding valid_tm_next_move [OF valid_M'] apply (subst M'_def)
                 apply auto
                apply (erule notE)
                using 2 unfolding TM.cis_final_def [symmetric] using 1 by (metis Suc.hyps cis_final_csteps_stay_eq)
            qed
            have 11: "ctapes ((TM.cstep M ^^ n) (TM.cinitial_config M w)) ! 0 =
                      ctapes ((TM.cstep M ^^ k') (TM.cinitial_config M w)) ! 0"
              using 2 8 unfolding TM.cis_final_def [symmetric] by (simp add: cis_final_csteps_stay_eq)
            have 12: "k'' \<ge> k' \<Longrightarrow> k'' \<le> n \<Longrightarrow> nth_ctape (ctapes ((TM.cstep (Abs_TM M') ^^ k'')
                      (TM.cinitial_config (Abs_TM M') w)) ! 2) 0 =
                      nth_ctape (ctapes ((TM.cstep (Abs_TM M') ^^ k') (TM.cinitial_config (Abs_TM M') w)) ! 2) 0"
              for k'' :: nat
            proof (induction k'' rule: nat_induct_at_least)
              case base
              show ?case ..
            next
              case (Suc k'')
              hence 1: "k'' \<le> n" by simp
              show ?case unfolding Suc(2) [OF 1, symmetric]
                apply simp
                apply (subst nth_ctape_cstep_No_Shift2)
                    apply simp_all
                unfolding valid_tm_next_move [OF valid_M'] apply (subst f101)
                    apply fact
                using that(1) 1 apply simp
                  apply (subst M'_def)
                  apply auto
                using 2 Suc(1) unfolding TM.cis_final_def [symmetric] apply (simp add: cis_final_csteps_stay_eq)
                unfolding TM.cis_final_def apply (subst (asm) f101)
                   apply fact
                using that(1) 1 apply simp
                unfolding valid_tm_final_states [OF valid_M'] apply (subst (asm) (2) M'_def)
                 apply simp
                unfolding final_states_def states_def using 1 that(1) apply auto
                unfolding take_map apply (subst (asm) last_map)
                  apply simp_all
                unfolding valid_tm_next_write [OF valid_M'] apply (subst f101)
                  apply (rule 1)
                 apply simp
                apply (subst M'_def)
                apply auto
                unfolding nth_ctape_0 [symmetric] apply standard
                apply (erule notE)
                using 2 unfolding TM.cis_final_def [symmetric] using Suc(1) by (simp add: cis_final_csteps_stay_eq)
            qed
            note 13 = 12 [OF 8 le_refl, unfolded a3, symmetric]
            have 14: "cstate ((TM.cstep (Abs_TM M') ^^ k'') (TM.cinitial_config (Abs_TM M') w)) \<notin>
                      TM.TM.final_states (Abs_TM M')"
              apply (subst f101)
              using 9 apply simp
              using 9 that(1) apply simp
              unfolding valid_tm_final_states [OF valid_M'] apply (subst (2) M'_def)
              apply simp
              unfolding final_states_def states_def using 9 that(1) apply auto
              apply (rule ccontr)
              unfolding take_map apply (subst (asm) last_map)
              by simp_all
            have 15: "\<And>n. max_cell_index (Abs_TM M') w 3 (k'' - Suc 0) -
                      cell_index (Abs_TM M') w 3 k'' = - 1 - int n \<Longrightarrow> n = 0"
              by (smt (verit, ccfv_SIG) Suc_diff_1 diff_Suc_1' diff_is_0_eq less_eq_Suc_le max_cell_index_Suc2
                  max_cell_index_ge_cell_index not_less_eq_eq of_nat_0_less_iff)
            have 16: "0 < k'' \<Longrightarrow> min (length w) k'' + min (Suc 0) (k'' - length w) \<le>
                      nat (cell_index (Abs_TM M') w 3 k'') \<Longrightarrow>
                      hd (map (\<lambda>ct. nth_ctape ct 0) (ctapes ((TM.cstep (Abs_TM M') ^^ k'')
                      (TM.cinitial_config (Abs_TM M') w)))) # tl (tl (tl (tl (map (\<lambda>ct. nth_ctape ct 0)
                      (ctapes ((TM.cstep (Abs_TM M') ^^ k'') (TM.cinitial_config (Abs_TM M') w))))))) =
                      map (\<lambda>ct. nth_ctape ct 0) (ctapes ((TM.cstep M ^^ k'') (TM.cinitial_config M w)))"
              apply (rule nth_equalityI)
               apply simp_all
              unfolding nth_Cons' apply auto
               apply (subst hd_map)
                apply auto
                apply (drule arg_cong [where f=length])
                apply simp
               apply (subst zeroth_is_head [symmetric])
                apply auto
                apply (drule arg_cong [where f=length])
                apply simp
              using 9 that(1) apply simp
              using cell_index_abs_bound [of "Abs_TM M'" w 3 k''] apply simp
               apply (cases "cell_index (Abs_TM M') w 3 k'' \<ge> int k''")
                apply simp_all
              unfolding nth_ctape_0 apply (subst csteps_untouched_cells_head)
                   apply simp_all
              using 14 TM.cis_final_def cis_final_sub_imp apply blast
                apply (subst f109)
                  apply simp_all
               apply (subst csteps_untouched_cells_head)
                   apply simp_all
              using 6 unfolding TM.cis_final_def [symmetric] using cis_final_sub_imp apply blast
                apply (subst f110 [symmetric])
                   apply simp_all
              using 6 unfolding TM.cis_final_def [symmetric] using cis_final_sub_imp apply blast
               apply (simp add: TM.cinitial_config_def)
              apply (simp add: nth_tl)
              apply (subst f102)
              using 9 that(1) by simp_all
            have 17: "max_cell_index (Abs_TM M') w 3 (k'' - Suc 0) = max_cell_index M w 0 (k'' - Suc 0)"
              unfolding max_cell_index_def apply (rule arg_cong [where f=Max]) apply auto
            proof -
              fix n' :: nat
              assume a1: "n' \<le> k'' - Suc 0"
              show "\<exists>na\<le>k'' - Suc 0. cell_index M w 0 na = cell_index (Abs_TM M') w 3 n'"
                apply (rule exI [where x=n'])
                apply (rule conjI)
                 apply fact
                apply (rule f110 [symmetric])
                using a1 9 apply simp
                using a1 9 that(1) apply simp
                using a1 6 unfolding TM.cis_final_def [symmetric] by (metis cis_final_csteps_stay_eq cis_final_sub_imp)
              show "\<exists>na\<le>k'' - Suc 0. cell_index (Abs_TM M') w 3 na = cell_index M w 0 n'"
                apply (rule exI [where x=n'])
                apply (rule conjI)
                 apply fact
                apply (rule f110)
                using a1 9 apply simp
                using a1 9 that(1) apply simp
                using a1 6 unfolding TM.cis_final_def [symmetric] by (metis cis_final_csteps_stay_eq cis_final_sub_imp)
            qed
            have 18: "0 < k'' \<Longrightarrow> \<not> min (length w) k'' + min (Suc 0) (k'' - length w) \<le>
                      nat (cell_index (Abs_TM M') w 3 k'') \<Longrightarrow> 0 < cell_index (Abs_TM M') w 3 k'' \<Longrightarrow>
                      nth_ctape (ctapes ((TM.cstep (Abs_TM M') ^^ k'')
                      (TM.cinitial_config (Abs_TM M') w)) ! 2) 0 = None \<Longrightarrow>
                      (take k'' (map Some w) @ take (k'' - length w) [None]) ! nat (cell_index (Abs_TM M') w 3 k'') #
                      tl (tl (tl (tl (map (\<lambda>ct. nth_ctape ct 0)
                      (ctapes ((TM.cstep (Abs_TM M') ^^ k'') (TM.cinitial_config (Abs_TM M') w))))))) =
                      map (\<lambda>ct. nth_ctape ct 0) (ctapes ((TM.cstep M ^^ k'') (TM.cinitial_config M w)))"
              apply (rule nth_equalityI)
               apply simp_all
              unfolding nth_Cons' apply auto
              unfolding nth_ctape_0 apply (subst csteps_untouched_cells_head2_right)
                   apply simp_all
              using 6 unfolding TM.cis_final_def [symmetric] using cis_final_sub_imp apply blast
                apply (rule ccontr)
                apply (subst (asm) f111 [of "k''" w 0, unfolded nth_ctape_0])
              using 9 that(1) apply simp_all
                  apply (rule 6)
                 apply (subst f110)
                    apply simp_all
              using 6 unfolding TM.cis_final_def [symmetric] using cis_final_sub_imp apply blast
              unfolding 17 apply simp 
                apply (meson linorder_not_less min_cell_index_le_0 nle_le order_trans)
               apply (auto simp add: TM.cinitial_config_def TM_abbrevs.cinput_tape_def)[1]
               apply (subst prepend_list_nth_less)
                apply simp_all
                apply (smt (verit, del_insts) One_nat_def cell_index_abs_bound int_nat_eq int_ops(6)
                  of_nat_1 of_nat_le_iff of_nat_less_iff)
               apply (subst nth_map)
                apply simp
                apply (smt (verit, del_insts) One_nat_def cell_index_abs_bound int_nat_eq int_ops(6)
                  of_nat_1 of_nat_le_iff of_nat_less_iff)
               apply (subst nth_tl)
                apply simp
                apply (smt (verit, del_insts) One_nat_def cell_index_abs_bound int_nat_eq int_ops(6)
                  of_nat_1 of_nat_le_iff of_nat_less_iff)
               apply (subst f110 [symmetric])
                  apply simp_all
              using 6 unfolding TM.cis_final_def [symmetric] using cis_final_sub_imp apply blast 
              apply (simp add: nth_tl)
              apply (subst f102)
              by simp_all
            have 19: "\<And>y. nth_ctape (ctapes ((TM.cstep (Abs_TM M') ^^ k'')
                      (TM.cinitial_config (Abs_TM M') w)) ! 3) 0 = Some y \<Longrightarrow>
                      nth_ctape (ctapes ((TM.cstep (Abs_TM M') ^^ k'') (TM.cinitial_config (Abs_TM M') w)) ! 3) 0 =
                      Some extra_sym"
              unfolding nth_ctape_0
              by (drule 21 [THEN conjunct1, folded cotm_heads_steps_congruence, THEN iffD1, simplified, of k'' w,
                  OF exI])
            have 20: "min_cell_index (Abs_TM M') w 3 (k'' - Suc 0) = min_cell_index M w 0 (k'' - Suc 0)"
              unfolding min_cell_index_def apply (rule arg_cong [where f=Min]) apply auto
            proof -
              fix n' :: nat
              assume a1: "n' \<le> k'' - Suc 0"
              show "\<exists>na\<le>k'' - Suc 0. cell_index M w 0 na = cell_index (Abs_TM M') w 3 n'"
                apply (rule exI [where x=n'])
                apply (rule conjI)
                 apply fact
                apply (rule f110 [symmetric])
                using a1 9 apply simp
                using a1 9 that(1) apply simp
                using a1 6 unfolding TM.cis_final_def [symmetric] by (metis cis_final_csteps_stay_eq cis_final_sub_imp)
              show "\<exists>na\<le>k'' - Suc 0. cell_index (Abs_TM M') w 3 na = cell_index M w 0 n'"
                apply (rule exI [where x=n'])
                apply (rule conjI)
                 apply fact
                apply (rule f110)
                using a1 9 apply simp
                using a1 9 that(1) apply simp
                using a1 6 unfolding TM.cis_final_def [symmetric] by (metis cis_final_csteps_stay_eq cis_final_sub_imp)
            qed
            have 21: "0 < k'' \<Longrightarrow> cstate ((TM.cstep M ^^ k'') (TM.cinitial_config M w)) \<notin> TM.TM.final_states M \<Longrightarrow>
                      nth_ctape (ctapes ((TM.cstep (Abs_TM M') ^^ k'')
                      (TM.cinitial_config (Abs_TM M') w)) ! 2) 0 = None \<Longrightarrow> \<not> 0 < cell_index (Abs_TM M') w 3 k'' \<Longrightarrow>
                      nth_ctape (ctapes ((TM.cstep (Abs_TM M') ^^ k'')
                      (TM.cinitial_config (Abs_TM M') w)) ! 3) 0 = None \<Longrightarrow>
                      None # tl (tl (tl (tl (map (\<lambda>ct. nth_ctape ct 0)
                      (ctapes ((TM.cstep (Abs_TM M') ^^ k'') (TM.cinitial_config (Abs_TM M') w))))))) =
                      map (\<lambda>ct. nth_ctape ct 0) (ctapes ((TM.cstep M ^^ k'') (TM.cinitial_config M w)))"
              apply (rule nth_equalityI)
               apply simp_all
              unfolding nth_Cons' apply auto
              unfolding nth_ctape_0 apply (subst csteps_untouched_cells_head2_left)
                   apply simp_all
              unfolding TM.cis_final_def [symmetric]
              using cis_final_sub_imp apply blast
                apply (rule ccontr)
                apply (subst (asm) f111 [of k'' w 0, unfolded nth_ctape_0])
              using 9 that(1) apply simp_all
              unfolding TM.cis_final_def [symmetric] apply assumption
                 apply (smt (verit) max_cell_index_ge_0)
                apply (subst f110)
                   apply simp_all
              unfolding TM.cis_final_def [symmetric] using cis_final_sub_imp apply blast
              unfolding 20 apply simp
               apply (subst TM.cinitial_config_def)
               apply (auto simp add: TM_abbrevs.cinput_tape_def)
              apply (simp add: nth_tl)
              apply (subst f102)
              by simp_all
            have 22: "nth_ctape (ctapes ((TM.cstep (Abs_TM M') ^^ k'')
                      (TM.cinitial_config (Abs_TM M') w)) ! 2) 0 = Some y \<Longrightarrow> 0 < k'' \<Longrightarrow>
                      hd (tl (map (\<lambda>ct. nth_ctape ct 0) (ctapes ((TM.cstep (Abs_TM M') ^^ k'')
                      (TM.cinitial_config (Abs_TM M') w))))) # tl (tl (tl (tl (map (\<lambda>ct. nth_ctape ct 0)
                      (ctapes ((TM.cstep (Abs_TM M') ^^ k'') (TM.cinitial_config (Abs_TM M') w))))))) =
                      map (\<lambda>ct. nth_ctape ct 0) (ctapes ((TM.cstep M ^^ k'') (TM.cinitial_config M w)))"
              for y :: 's
              apply (rule nth_equalityI)
               apply simp_all
              unfolding nth_Cons' apply auto
              using f105 [of k'' w 0, symmetric] 9 that(1) apply simp
               apply (subst map_tl [symmetric])
               apply (subst hd_map)
                apply auto
                apply (drule arg_cong [where f=length])
                apply simp
               apply (subst zeroth_is_head [symmetric])
                apply auto
                apply (drule arg_cong [where f=length])
                apply simp
               apply (subst nth_tl)
                apply simp_all
              apply (simp add: nth_tl)
              apply (subst f102)
              using 9 that(1) by simp_all
            have 23: "max_cell_index (Abs_TM M') w 3 k'' = max_cell_index M w 0 k''"
              unfolding max_cell_index_def apply (rule arg_cong [where f=Max]) apply auto
            proof -
              fix n' :: nat
              assume a1: "n' \<le> k''"
              show "\<exists>na\<le>k''. cell_index M w 0 na = cell_index (Abs_TM M') w 3 n'"
                apply (rule exI [where x=n'])
                apply (rule conjI)
                 apply fact
                apply (rule f110 [symmetric])
                using a1 9 apply simp
                using a1 9 that(1) apply simp
                using a1 6 unfolding TM.cis_final_def [symmetric] by (metis cis_final_csteps_stay_eq cis_final_sub_imp)
              show "\<exists>na\<le>k''. cell_index (Abs_TM M') w 3 na = cell_index M w 0 n'"
                apply (rule exI [where x=n'])
                apply (rule conjI)
                 apply fact
                apply (rule f110)
                using a1 9 apply simp
                using a1 9 that(1) apply simp
                using a1 6 unfolding TM.cis_final_def [symmetric] by (metis cis_final_csteps_stay_eq cis_final_sub_imp)
            qed
            show ?thesis using 13 unfolding 10 [OF 8 le_refl] 11 5
              apply (cases "TM.TM.next_move (Abs_TM M') (cstate ((TM.cstep (Abs_TM M') ^^ k'')
                            (TM.cinitial_config (Abs_TM M') w)))
                            (cheads ((TM.cstep (Abs_TM M') ^^ k'') (TM.cinitial_config (Abs_TM M') w))) 3")
                apply (subst cell_index.simps(2))
                 apply (simp add: cotm_heads_steps_congruence cotm_steps_congruences(1))
                apply simp
                apply (subst (asm) nth_ctape_cstep_Shift_Left1)
                     apply simp_all
                  apply (simp add: valid_tm_next_move)
                  apply (subst f101)
              using 9 apply simp
              using 9 that(1) apply simp
                  apply (subst (asm) f101)
              using 9 apply simp
              using 9 that(1) apply simp
                  apply (subst M'_def)
                  apply (subst (asm) M'_def)
                  apply simp
                 apply (rule 14)
                apply (subst (asm) f111 [of k'' w "-1"])
              using 9 apply simp
              using 9 that(1) apply simp
              apply (smt (verit, del_insts) 5 \<open>cell_index (Abs_TM M') w 3 n = cell_index (Abs_TM M') w 3 k'\<close> a1
                  bot_nat_0.not_eq_extremum cell_index.simps(1,2) cotm_heads_steps_congruence
                  cotm_steps_congruences(1))
                   apply (rule 6)
                  apply (cases "max_cell_index (Abs_TM M') w 3 (k'' - 1) = max_cell_index (Abs_TM M') w 3 k''")
                   apply simp
                   apply (meson diff_ge_0_iff_ge le_minus_one_simps(1) max_cell_index_ge_cell_index order_trans)
                  apply (cases k'')
                   apply simp_all
                 apply (smt (verit, best) max_cell_index_Suc2 max_cell_index_ge_cell_index)
                apply (cases k'')
                 apply simp
                 apply (smt (verit, del_insts) 5 \<open>cell_index (Abs_TM M') w 3 n = cell_index (Abs_TM M') w 3 k'\<close>
                  a1 cell_index.simps(1,2) cotm_heads_steps_congruence cotm_steps_congruences(1) funpow_0)
              using a1 [unfolded 10 [OF 8 le_refl], unfolded 5] apply (subst (asm) cell_index.simps(2))
                 apply (metis cotm_heads_steps_congruence cotm_steps_congruences(1))
                apply simp
                apply (metis diff_mono linorder_not_le min_cell_index_le_0 not_less_iff_gr_or_eq
                  verit_minus_simplify(3))
               apply (subst (asm) nth_ctape_cstep_Shift_Right1)
                    apply simp_all
                 apply (simp add: valid_tm_next_move)
                 apply (subst f101)
              using 9 apply simp
              using 9 that(1) apply simp
                 apply (subst (asm) f101)
              using 9 apply simp
              using 9 that(1) apply simp
                 apply (subst M'_def)
                 apply (subst (asm) M'_def)
                 apply simp
                apply (rule 14)
               apply (subst cell_index.simps(3))
                apply (simp add: cotm_heads_steps_congruence cotm_steps_congruences(1))
               apply (cases "k'' = 0")
                apply simp
                apply (subst nth_ctape_cstep_Shift_Right1)
                     apply simp_all
                  apply (simp add: valid_tm_next_move)
                  apply (subst (asm) f101 [of 0, simplified])
                  apply (subst (asm) (2) M'_def)
              using 6 apply simp
              unfolding original_hds_def apply (cases "cheads (TM.cinitial_config (Abs_TM M') w) ! 2 = None")
                   apply simp_all
                   apply (subst (asm) (3 4) TM.cinitial_config_def)
                   apply (subst (2) TM.cinitial_config_def)
              unfolding TM_abbrevs.cinput_tape_def apply auto
                  apply (subst (asm) (6) TM.cinitial_config_def)
              unfolding TM_abbrevs.cinput_tape_def apply (simp add: empty_ctape_def)
              using 1 apply meson
                apply (subst TM.cinitial_config_def)
              unfolding TM_abbrevs.cinput_tape_def apply auto
              using n_gt_0 that(1) apply fastforce
                apply (subst nth_ctape_pos)
                 apply (simp_all del: zeroth_clist_is_chd)
                apply (subst prepend_list_nth_less)
                 apply simp
              using a1 a2 apply linarith
                apply (subst nth_map)
                 apply simp
              using a1 a2 apply linarith
                apply (subst nth_tl)
                 apply simp
              using a1 a2 apply linarith
                apply standard
               apply (subst nth_ctape_cstep_Shift_Right1)
                    apply simp_all
                 apply (simp add: valid_tm_next_move)
                 apply (subst (asm) f101)
              using 9 apply simp
              using 9 that(1) apply simp
                 apply (subst (asm) (3) M'_def)
              using 6 apply simp
              unfolding original_hds_def
                 apply (cases "cheads ((TM.cstep (Abs_TM M') ^^ k'') (TM.cinitial_config (Abs_TM M') w)) ! 2 = None")
                  apply simp_all
              unfolding nth_ctape_0 [symmetric]
                  apply (cases "min (length w) k'' + min (Suc 0) (k'' - length w) \<le>
                                nat (cell_index (Abs_TM M') w 3 k'')")
                   apply simp_all
              unfolding 16 apply assumption
                  apply (cases "0 < cell_index (Abs_TM M') w 3 k'' \<or> cell_index (Abs_TM M') w 3 k'' \<le> 0 \<and>
                                (\<exists>y. nth_ctape (ctapes ((TM.cstep (Abs_TM M') ^^ k'')
                                (TM.cinitial_config (Abs_TM M') w)) ! 3) 0 = Some y)")
                   apply auto
              unfolding 18 apply assumption
              using f106 [of k'' w] f103 [of k'' w 0 "- cell_index (Abs_TM M') w 3 k''"] 9 that(1) apply simp
                   apply (frule 19)
                   apply simp
                   apply (subst (asm) (2) f111)
                         apply simp_all
              using max_cell_index_ge_0 apply blast
              using min_cell_index_le_0 apply blast
              unfolding 21 apply assumption
              unfolding 22 apply assumption
              using 6 apply simp
              using a1 [unfolded 10 [OF 8 le_refl] 5] apply (subst (asm) cell_index.simps(3))
                apply (simp add: cotm_heads_steps_congruence cotm_steps_congruences(1) nth_ctape_0)
               apply simp
               apply (subst nth_ctape_pos)
                apply simp
               apply (cases "cell_index (Abs_TM M') w 3 k'' = 0")
                apply (subst csteps_untouched_cells_right2)
                    apply simp_all
              using 6 unfolding TM.cis_final_def [symmetric] using cis_final_sub_imp apply blast
              apply (smt (verit, best) 17 5 6 8 One_nat_def Suc_diff_1
                  \<open>cell_index (Abs_TM M') w 3 n = cell_index (Abs_TM M') w 3 k'\<close> a1 f110 f111 k''_def
                  le_eq_less_or_eq less_eq_Suc_le max_cell_index_Suc_gt_impl_eq_cell_index
                  max_cell_index_Suc_gt_impl_eq_cell_index_Suc max_cell_index_ge_cell_index
                  min_cell_index_le_0 option.distinct(1) order_trans that(1))
                 apply (subst f110 [symmetric])
              using 9 apply simp
              using 9 that(1) apply simp
              using 6 unfolding TM.cis_final_def [symmetric] using cis_final_sub_imp apply blast
                 apply simp
                apply (subst f110 [symmetric])
              using 9 apply simp
              using 9 that(1) apply simp
              using 6 unfolding TM.cis_final_def [symmetric] using cis_final_sub_imp apply blast
                apply (auto simp add: TM.cinitial_config_def TM_abbrevs.cinput_tape_def)[1]
              using n_gt_0 that(1) apply auto[1]
                apply (simp flip: zeroth_clist_is_chd)
                apply (cases "length w = 1")
              using 9 that(1) apply linarith
                apply (subst prepend_list_nth_less)
                 apply simp_all
              using 5 8 that(1) apply linarith
                apply (subst nth_map)
                 apply simp
              using 5 8 that(1) apply linarith
                apply (subst nth_tl)
                 apply simp_all
              using 5 8 that(1) apply linarith
               apply (simp flip: zeroth_clist_is_chd)
               apply (subst csteps_untouched_cells_right2)
                   apply simp_all
              using 6 unfolding TM.cis_final_def [symmetric] using cis_final_sub_imp apply blast
              unfolding 23 [symmetric] apply (subst f110 [symmetric])
              using 9 apply simp
              using 9 that(1) apply simp
              using 6 unfolding TM.cis_final_def [symmetric] using cis_final_sub_imp apply blast
                 apply (smt (verit, best) 6 9 Suc_diff_1 f111 max_cell_index_Suc_gt_impl_eq_cell_index_Suc
                  min_cell_index_le_0 nat_less_le not_less_eq_eq of_nat_le_iff option.distinct(1) that(1))
                apply (subst f110 [symmetric])
              using 9 apply simp
              using 9 that(1) apply simp
              using 6 unfolding TM.cis_final_def [symmetric] using cis_final_sub_imp apply blast
                apply assumption
               apply (subst TM.cinitial_config_def)
               apply (auto simp add: TM_abbrevs.cinput_tape_def)
                apply (metis list.size(3) n_gt_0 linorder_not_less that(1))
               apply (subst prepend_list_nth_less)
                apply simp_all
                apply (subst f110 [symmetric])
              using 9 apply simp
              using 9 that(1) apply simp
              using 6 unfolding TM.cis_final_def [symmetric] using cis_final_sub_imp apply blast
              using a2 [unfolded 10 [OF 8 le_refl] 5] apply (subst (asm) cell_index.simps(3))
                 apply (simp add: cotm_heads_steps_congruence cotm_steps_congruences(1) nth_ctape_0)
                apply simp
               apply (subst nth_map)
              using a2 [unfolded 10 [OF 8 le_refl] 5] apply (subst (asm) cell_index.simps(3))
                 apply (simp add: cotm_heads_steps_congruence cotm_steps_congruences(1) nth_ctape_0)
                apply (subst f110 [symmetric])
              using 9 apply simp
              using 9 that(1) apply simp
              using 6 unfolding TM.cis_final_def [symmetric] using cis_final_sub_imp apply blast
                apply simp
               apply (subst nth_tl)
              using a2 [unfolded 10 [OF 8 le_refl] 5] apply (subst (asm) cell_index.simps(3))
                 apply (simp add: cotm_heads_steps_congruence cotm_steps_congruences(1) nth_ctape_0)
                apply (subst f110 [symmetric])
              using 9 apply simp
              using 9 that(1) apply simp
              using 6 unfolding TM.cis_final_def [symmetric] using cis_final_sub_imp apply blast
                apply simp
               apply (subst f110 [symmetric])
              using 9 apply simp
              using 9 that(1) apply simp
              using 6 unfolding TM.cis_final_def [symmetric] using cis_final_sub_imp apply blast
               apply (smt (verit, best) Suc_nat_eq_nat_zadd1)
              apply (subst (asm) nth_ctape_cstep_No_Shift2)
                  apply simp_all
                apply (simp add: valid_tm_next_move)
              using f101 [of k'' w] 9 that(1) apply simp
              apply (subst M'_def)
                apply (subst (asm) M'_def)
              using 6 apply (simp add: nth_ctape_0)
               apply (rule 14)
              unfolding valid_tm_next_write [OF valid_M'] using 9 that(1) f101 [of k'' w] apply simp
              apply (subst (asm) M'_def)
              using 6 by simp
            next
              case False
              have 3: "max_cell_index (Abs_TM M') w 3 (n - 1) = max_cell_index M w 0 (n - 1)"
                unfolding max_cell_index_def apply (rule arg_cong [where f=Max])
              proof auto
                fix n' :: nat
                assume a1: "n' \<le> n - Suc 0"
                show "\<exists>nb\<le>n - Suc 0. cell_index M w 0 nb = cell_index (Abs_TM M') w 3 n'"
                  apply (rule exI [where x=n'])
                  apply (rule conjI)
                   apply fact
                  apply (rule f110 [symmetric])
                  using a1 apply simp
                  using a1 that(1) apply simp
                  using False unfolding TM.cis_final_def [symmetric]
                  by (metis a1 cis_final_csteps_stay_eq cis_final_sub_imp)
                show "\<exists>nb\<le>n - Suc 0. cell_index (Abs_TM M') w 3 nb = cell_index M w 0 n'"
                  apply (rule exI [where x=n'])
                  apply (rule conjI)
                   apply fact
                  apply (rule f110)
                  using a1 apply simp
                  using a1 that(1) apply simp
                  using False unfolding TM.cis_final_def [symmetric]
                  by (metis a1 cis_final_csteps_stay_eq cis_final_sub_imp)
              qed
              show ?thesis unfolding nth_ctape_0 apply (subst csteps_untouched_cells_head2_right)
                    apply simp
                using False unfolding TM.cis_final_def [symmetric] using n_gt_0 cis_final_sub_imp apply blast
                  apply (rule ccontr)
                using a3 apply (subst (asm) f111)
                        apply (rule le_refl)
                using that(1) apply simp
                      apply (rule n_gt_0)
                     apply (rule False)
                unfolding 3 apply (subst f110)
                       apply (rule le_refl)
                using that(1) apply simp
                using False unfolding TM.cis_final_def [symmetric] using cis_final_sub_imp apply blast
                    apply fastforce
                using a1 apply (smt (verit, ccfv_SIG) min_cell_index_le_0)
                  apply simp
                 apply (rule n_gt_0)
                apply (auto simp add: TM.cinitial_config_def TM_abbrevs.cinput_tape_def)
                using n_gt_0 that(1) apply fastforce
                apply (subst f110 [symmetric])
                   apply (rule le_refl)
                using that(1) apply simp
                using False unfolding TM.cis_final_def [symmetric] using cis_final_sub_imp apply blast
                apply (subst prepend_list_nth_less)
                using a2 apply (simp add: a1 less_diff_conv)
                apply (subst nth_map)
                using a2 apply (simp add: a1 less_diff_conv)
                apply (subst nth_tl)
                using a2 apply (simp add: a1 less_diff_conv)
                using a1 by simp
          qed
        next
          fix y :: 's
          assume a1: "min (length w) n = 0"            
          have False using n_gt_0 a1 by (simp add: that(1))
          thus "hd (map (\<lambda>ct. nth_ctape ct 0) (ctapes ((TM.cstep (Abs_TM M') ^^ n)
                (TM.cinitial_config (Abs_TM M') w)))) =
                nth_ctape (ctapes ((TM.cstep M ^^ n) (TM.cinitial_config M w)) ! 0) 0" ..
        next
          fix y :: 's
          assume a1: "cell_index (Abs_TM M') w 3 n \<le> 0" and
                 a2: "nth_ctape (ctapes ((TM.cstep (Abs_TM M') ^^ n) (TM.cinitial_config (Abs_TM M') w)) ! 3) 0 =
                      Some y" and
                 a3: "w \<noteq> []" and
                 a4: "nth_ctape (ctapes ((TM.cstep (Abs_TM M') ^^ n) (TM.cinitial_config (Abs_TM M') w)) ! 2) 0 = None"
          have 0 [simp]: "y = extra_sym"
            using 21 [THEN conjunct1, THEN iffD1, folded cotm_heads_steps_congruence, simplified, OF exI,
                folded nth_ctape_0, OF a2, unfolded a2] by simp
          have 1: "cell_index (Abs_TM M') w 3 n = 0"
            using f103 [OF le_refl _ a2 [unfolded 0] f106 [OF le_refl _ n_gt_0]] that(1) by simp
          have 2: "cstate ((TM.cstep M ^^ n) (TM.cinitial_config M w)) \<in> TM.TM.final_states M"
            apply (rule ccontr)
            using a4 apply (subst (asm) f111 [OF le_refl _ n_gt_0, of w 0])
            using that(1) apply simp
               apply assumption
            unfolding 1 apply simp_all
             apply (simp add: max_cell_index_ge_0)
            using min_cell_index_le_0 by blast
          show "Some (w ! 0) = nth_ctape (ctapes ((TM.cstep M ^^ n) (TM.cinitial_config M w)) ! 0) 0"
          proof (cases "cstate (TM.cinitial_config M w) \<in> TM.final_states M")
            case True
            hence 3: "(TM.cstep M ^^ n) (TM.cinitial_config M w) = TM.cinitial_config M w"
              by (simp add: TM.cstep_def funpow_fixpoint)
            show ?thesis unfolding 3 unfolding TM.cinitial_config_def TM_abbrevs.cinput_tape_def
              using a3 apply (simp add: nth_ctape_0)
              by (simp add: hd_conv_nth)
          next
            case False
            define n' :: nat where
              "n' \<equiv> (LEAST n'. cstate ((TM.cstep M ^^ n') (TM.cinitial_config M w)) \<in> TM.TM.final_states M)"
            note 3 = LeastI [of "\<lambda>n'. cstate ((TM.cstep M ^^ n') (TM.cinitial_config M w)) \<in> TM.TM.final_states M",
                OF 2, folded n'_def]
            have 4: "n' > 0"
              apply (rule ccontr)
              apply simp
              using 3 False by simp
            then obtain n'' :: nat where n'_altdef: "n' = Suc n''" by (rule lessE)
            note 5 = Least_le [of "\<lambda>n'. cstate ((TM.cstep M ^^ n') (TM.cinitial_config M w)) \<in> TM.TM.final_states M",
                OF 2, folded n'_def]
            have 6: "(TM.cstep M ^^ n) (TM.cinitial_config M w) = (TM.cstep M ^^ n') (TM.cinitial_config M w)"
              using 3 5 TM.cis_final_def cis_final_csteps_stay_eq by blast
            have 7: "n' \<le> n2 \<Longrightarrow> n2 \<le> n \<Longrightarrow> cell_index (Abs_TM M') w 3 n' = cell_index (Abs_TM M') w 3 n2" for n2 :: nat
            proof (induction n2 rule: nat_induct_at_least)
              case base
              show ?case ..
            next
              case (Suc n2)
              have *: "n2 \<le> n" using Suc(3) by simp
              show ?case unfolding Suc(2) [OF *] apply (subst cell_index.simps(4))
                unfolding cotm_steps_congruences(1) [symmetric] cotm_heads_steps_congruence [symmetric]
                unfolding valid_tm_next_move [OF valid_M'] apply (subst f101 [OF *, of w])
                using * that(1) apply simp
                 apply (subst M'_def)
                 apply auto
                using 3 Suc(1) by (simp add: TM.cis_final_def cis_final_csteps_stay_eq)
            qed
            have 8: "n2 \<ge> n' \<Longrightarrow> n2 \<le> n \<Longrightarrow> nth_ctape (ctapes ((TM.cstep (Abs_TM M') ^^ n2)
                     (TM.cinitial_config (Abs_TM M') w)) ! 2) 0 =
                     nth_ctape (ctapes ((TM.cstep (Abs_TM M') ^^ n') (TM.cinitial_config (Abs_TM M') w)) ! 2) 0"
              for n2 :: nat
            proof (induction n2 rule: nat_induct_at_least)
              case base
              show ?case ..
            next
              case (Suc n2)
              have *: "n2 \<le> n" using Suc(3) by simp
              show ?case apply simp
                apply (subst nth_ctape_cstep_No_Shift2)
                    apply simp_all
                unfolding valid_tm_next_move [OF valid_M'] valid_tm_next_write [OF valid_M']
                  apply (subst f101 [OF *, of w])
                using * that(1) apply simp
                  apply (subst M'_def)
                  apply auto
                using Suc(1) 3 apply (simp add: TM.cis_final_def cis_final_csteps_stay_eq)
                 apply (subst (asm) f101 [OF *, of w])
                using * that(1) apply simp
                unfolding valid_tm_final_states [OF valid_M'] apply (subst (asm) (2) M'_def)
                 apply simp
                unfolding final_states_def states_def using that(1) * apply auto
                unfolding take_map apply (subst (asm) last_map)
                  apply auto
                apply (subst f101 [OF *, of w])
                using * that(1) apply simp
                apply (subst M'_def)
                using Suc(1) 4 apply (auto simp add: nth_ctape_0 [symmetric])
                 apply (erule Suc(2))
                by (metis 3 TM.cis_final_def cis_final_csteps_stay_eq)
            qed
            have 9: "cstate ((TM.cstep M ^^ n'') (TM.cinitial_config M w)) \<notin> TM.TM.final_states M"
              apply standard
              using 3 [unfolded n'_altdef] by (metis lessI n'_altdef n'_def not_less_Least)
            have 10: "cstate ((TM.cstep (Abs_TM M') ^^ n') (TM.cinitial_config (Abs_TM M') w)) \<notin>
                      TM.TM.final_states (Abs_TM M')"
              apply (subst f101 [OF 5, of w])
              using that(1) 5 apply simp
              unfolding valid_tm_final_states [OF valid_M'] apply (subst (2) M'_def)
              apply simp
              unfolding final_states_def states_def using 5 that(1) apply auto
              apply (rule ccontr)
              unfolding take_map apply (subst (asm) last_map)
              by auto
            have 11: "cstate ((TM.cstep (Abs_TM M') ^^ n'') (TM.cinitial_config (Abs_TM M') w)) \<notin>
                      TM.TM.final_states (Abs_TM M')"
              using 10 [unfolded n'_altdef, simplified] apply auto
              by (simp add: TM.cstep_def)
            have 12: "n'' < n"
              using 5 unfolding n'_altdef by simp
            have 13: "nth_ctape (ctapes ((TM.cstep (Abs_TM M') ^^ n'') (TM.cinitial_config (Abs_TM M') w)) ! 2) 0 =
                      Some y \<Longrightarrow> (hd (tl (map (\<lambda>ct. nth_ctape ct 0) (ctapes ((TM.cstep (Abs_TM M') ^^ n'')
                      (TM.cinitial_config (Abs_TM M') w))))) # tl (tl (tl (tl (map (\<lambda>ct. nth_ctape ct 0)
                      (ctapes ((TM.cstep (Abs_TM M') ^^ n'') (TM.cinitial_config (Abs_TM M') w)))))))) =
                      map (\<lambda>ct. nth_ctape ct 0) (ctapes ((TM.cstep M ^^ n'') (TM.cinitial_config M w)))" for y :: 's
              apply (rule nth_equalityI)
              apply simp_all
              unfolding nth_Cons' apply auto
               apply (subst zeroth_is_head [symmetric])
                apply standard
                apply (drule arg_cong [where f=length])
              apply simp
               apply (subst nth_tl)
                apply simp
               apply (subst nth_map)
                apply simp
              using f105 [of n'' w 0] 12 that(1) apply simp
              apply (simp add: nth_tl)
              apply (subst f102)
              using 12 that(1) by simp_all
            have 14: "chead (ctapes ((TM.cstep (Abs_TM M') ^^ n'') (TM.cinitial_config (Abs_TM M') w)) ! 2) = None \<Longrightarrow>
                      n'' \<le> nat (cell_index (Abs_TM M') w 3 n'') \<Longrightarrow>
                      hd (cheads ((TM.cstep (Abs_TM M') ^^ n'') (TM.cinitial_config (Abs_TM M') w))) #
                      tl (tl (tl (tl (cheads ((TM.cstep (Abs_TM M') ^^ n'') (TM.cinitial_config (Abs_TM M') w)))))) =
                      cheads ((TM.cstep M ^^ n'') (TM.cinitial_config M w))"
              apply (rule nth_equalityI)
               apply simp_all
              unfolding nth_Cons' apply auto
               apply (subst hd_map)
                apply standard
                apply (drule arg_cong [where f=length])
                apply simp
               apply (subst zeroth_is_head [symmetric])
                apply standard
                apply (drule arg_cong [where f=length])
                apply simp
              apply (subst (asm) f110)
              using 12 that(1) apply simp_all
              using 9 TM.cis_final_def cis_final_sub_imp apply blast
               apply (subst f104 [of n'' w 0, unfolded nth_ctape_0])
                 apply simp_all
               apply (cases n'')
                apply simp
              using a3 apply (simp add: TM.cinitial_config_def TM_abbrevs.cinput_tape_def nth_ctape_0)
              unfolding nth_ctape_0 [symmetric]
               apply (subst csteps_untouched_cells_head2_right [where k=n'', of 0 M w, folded nth_ctape_0])
                   apply simp_all
                 apply (metis 9 TM.cis_final_def cis_final_csteps_stay_eq suc_is_ge)
              using cell_index_abs_bound [of M w 0 "n'' - 1"] apply simp
                apply (smt (verit, best) int_nat_eq max_cell_index_bound of_nat_Suc of_nat_le_iff)
              using a3 apply (simp add: TM.cinitial_config_def TM_abbrevs.cinput_tape_def)
               apply (subst nth_ctape_pos)
                apply simp_all
              using f109 [of n'' w] apply simp_all
               apply (cases "cell_index M w 0 n'' = n''")
                apply simp_all
                apply (metis One_nat_def diff_Suc_1 nat_int of_nat_Suc)
               apply (smt (verit, del_insts) cell_index_abs_bound int_nat_eq of_nat_Suc of_nat_le_iff)
              apply (simp add: nth_tl)
              apply (subst f102)
              by simp_all
            show ?thesis using 1 [folded 7 [OF 5 le_refl]] a4 [unfolded 8 [OF 5 le_refl]] unfolding n'_altdef
              6 apply simp
              apply (subst (asm) f110 [OF 5, of w, unfolded n'_altdef, simplified])
              using n'_altdef 5 that(1) apply simp
               apply (rule 9)
              apply (cases "TM.TM.next_move M (cstate ((TM.cstep M ^^ n'') (TM.cinitial_config M w)))
                            (cheads ((TM.cstep M ^^ n'') (TM.cinitial_config M w))) 0")
                apply (subst (asm) cell_index.simps(2))
                 apply (simp add: cotm_heads_steps_congruence cotm_steps_congruences(1))
                apply simp
                apply (subst (asm) nth_ctape_cstep_Shift_Left1)
                     apply simp_all
              unfolding valid_tm_next_move [OF valid_M'] apply (subst f101)
              using 12 apply simp
              using 12 that(1) apply simp
                  apply (subst M'_def)
              using 9 apply simp
              using f110 [of n'' w] 12 that(1) apply simp
              unfolding original_hds_def apply (auto simp add: 13 [unfolded nth_ctape_0] 14) sorry
          qed
        next
          assume a1: "min (length w) n = 0"
          have 1: "length w = 0" using a1 n_gt_0 by presburger
          have False using that(1) unfolding 1 using n_gt_0 by simp
          thus "hd (map (\<lambda>ct. nth_ctape ct 0) (ctapes ((TM.cstep (Abs_TM M') ^^ n)
                (TM.cinitial_config (Abs_TM M') w)))) =
                nth_ctape (ctapes ((TM.cstep M ^^ n) (TM.cinitial_config M w)) ! 0) 0" ..
        next
          assume a1: "\<not> 0 < cell_index (Abs_TM M') w 3 n" and
                 a2: "nth_ctape (ctapes ((TM.cstep (Abs_TM M') ^^ n)
                      (TM.cinitial_config (Abs_TM M') w)) ! 3) 0 = None" and
                 a3: "w \<noteq> []" and
                 a4: "nth_ctape (ctapes ((TM.cstep (Abs_TM M') ^^ n) (TM.cinitial_config (Abs_TM M') w)) ! 2) 0 = None"
          have 1: "cell_index (Abs_TM M') w 3 n \<noteq> 0"
            apply standard
            using f106 [OF le_refl _ n_gt_0, of w] that(1) a2 by simp
          have 2: "cell_index (Abs_TM M') w 3 n < 0" using a1 1 by simp
          have 3: "cstate (TM.cinitial_config M w) \<notin> TM.TM.final_states M"
          proof
            assume a1: "cstate (TM.cinitial_config M w) \<in> TM.TM.final_states M"
            have 3: "TM.next_move (Abs_TM M') (cstate (TM.csteps (Abs_TM M') n'
                     (TM.cinitial_config (Abs_TM M') w))) (cheads (TM.csteps (Abs_TM M') n'
                     (TM.cinitial_config (Abs_TM M') w))) 3 = No_Shift" if "n' \<le> n" for n' :: nat
              unfolding valid_tm_next_move [OF valid_M'] apply (subst f101)
                apply fact
              using that(1) \<open>n \<le> length w\<close> apply simp
              apply (subst M'_def)
              apply auto
              using a1 by (metis TM.cis_final_def cis_final_sub_imp diff_self_eq_0 funpow_0)
            have 4: "cell_index (Abs_TM M') w 3 n' = 0" if "n' \<le> n" for n' :: nat using that
            proof (induction n')
              case 0
              then show ?case by simp
            next
              case (Suc n')
              then show ?case apply simp
                apply (subst cell_index.simps(4))
                using 3 [of n'] by (metis cotm_heads_steps_congruence cotm_steps_congruences(1)
                    less_eq_Suc_le nat_less_le)
            qed
            show False using 2 4 [OF le_refl] by simp
          qed
          show "None = nth_ctape (ctapes ((TM.cstep M ^^ n) (TM.cinitial_config M w)) ! 0) 0"
          proof (cases "cstate (TM.csteps M n (TM.cinitial_config M w)) \<in> TM.final_states M")
            case True
            define n' :: nat where
              "n' \<equiv> (LEAST n'. cstate ((TM.cstep M ^^ n') (TM.cinitial_config M w)) \<in> TM.TM.final_states M)"
            note 4 = LeastI [of "\<lambda>n. cstate ((TM.cstep M ^^ n) (TM.cinitial_config M w)) \<in> TM.TM.final_states M",
                OF True, folded n'_def]
            note 5 = Least_le [of "\<lambda>n. cstate ((TM.cstep M ^^ n) (TM.cinitial_config M w)) \<in> TM.TM.final_states M",
                OF True, folded n'_def]
            have 6: "n' > 0"
              apply (rule ccontr)
              using 3 4 by simp
            then obtain n'' :: nat where n'_altdef: "n' = Suc n''" by (rule lessE)
            have 7: "n'' < n" using 5 unfolding n'_altdef by simp
            have 8: "cstate ((TM.cstep M ^^ n'') (TM.cinitial_config M w)) \<notin> TM.TM.final_states M"
              by (metis lessI n'_altdef n'_def not_less_Least)
            have 9: "(TM.cstep M ^^ n) (TM.cinitial_config M w) = (TM.cstep M ^^ n') (TM.cinitial_config M w)"
              using True 4 unfolding TM.cis_final_def [symmetric]
              using 5 cis_final_csteps_stay_eq by blast
            have 10: "n' - 1 = n''" unfolding n'_altdef by simp
            show ?thesis unfolding 9 n'_altdef sorry
          next
            case False
            have 4: "min_cell_index (Abs_TM M') w 3 (n - Suc 0) = min_cell_index M w 0 (n - Suc 0)"
              unfolding min_cell_index_def apply (rule arg_cong [where f=Min])
            proof auto
              fix n' :: nat
              assume a1: "n' \<le> n - Suc 0"
              show "\<exists>nb\<le>n - Suc 0. cell_index M w 0 nb = cell_index (Abs_TM M') w 3 n'"
                apply (rule exI [where x=n'])
                apply (rule conjI)
                 apply fact
                apply (rule f110 [of n' w, symmetric])
                using a1 apply simp
                using a1 that(1) apply simp
                using False unfolding TM.cis_final_def [symmetric] using a1
                by (metis cis_final_csteps_stay_eq cis_final_sub_imp)
              show "\<exists>nb\<le>n - Suc 0. cell_index (Abs_TM M') w 3 nb = cell_index M w 0 n'"
                apply (rule exI [where x=n'])
                apply (rule conjI)
                 apply fact
                apply (rule f110 [of n' w])
                using a1 apply simp
                using a1 that(1) apply simp
                using False unfolding TM.cis_final_def [symmetric] using a1
                by (metis cis_final_csteps_stay_eq cis_final_sub_imp)
            qed
            show ?thesis unfolding nth_ctape_0 apply (subst csteps_untouched_cells_head2_left)
                  apply simp
              using False unfolding TM.cis_final_def [symmetric] using cis_final_sub_imp apply blast
                apply (rule ccontr)
              using a4 apply (subst (asm) f111 [OF le_refl, of w 0, OF _ n_gt_0 False])
              using that(1) apply simp
              using 2 apply (smt (verit, ccfv_SIG) max_cell_index_ge_0)
                 apply simp
                 apply (subst f110 [OF le_refl])
              using that(1) apply simp
              using False unfolding TM.cis_final_def [symmetric] using cis_final_sub_imp apply blast
              unfolding 4 apply simp
                apply simp
               apply fact
              using a3 by (simp add: TM.cinitial_config_def TM_abbrevs.cinput_tape_def)
          qed
        qed
      next
        case (Suc i')
        have 1: "tl (tl (tl (tl (cheads ((TM.cstep (Abs_TM M') ^^ n) (TM.cinitial_config (Abs_TM M') w)))))) ! i' =
                 chead (ctapes ((TM.cstep M ^^ n) (TM.cinitial_config M w)) ! Suc i')"
          using a1 Suc apply (simp add: nth_tl)
          using f102 [OF le_refl, of w "Suc (Suc (Suc (Suc i')))"] a1 that(1) by simp
        show ?thesis unfolding original_hds_def Suc using 1 by simp
      qed
    qed
    {
      case 1
      have [simp]: "cstate ((TM.cstep (Abs_TM M') ^^ n) (TM.cinitial_config (Abs_TM M') w)) \<notin>
                    TM.TM.final_states (Abs_TM M')"
        apply (subst f101 [OF le_refl])
        using 1(1) apply simp
        unfolding valid_tm_final_states [OF valid_M'] apply (subst (2) M'_def)
        apply simp
        unfolding final_states_def using 1(1) apply auto
        unfolding take_map apply (subst (asm) last_map)
        by auto
      show ?case apply simp
        apply (subst (1 2) TM.cstep_def)
        apply auto
        unfolding TM.cstep_not_final_def Let_def apply simp_all
        unfolding valid_tm_next_state [OF valid_M'] apply (subst f101 [OF le_refl])
        using 1(1) apply simp
         apply (subst M'_def)
        using 1(1) apply auto
           apply (rule nth_equalityI)
            apply simp_all
        unfolding nth_append apply auto
        using f104 [OF le_refl, of w 0, unfolded nth_ctape_0, simplified] apply simp
        using f109 [OF le_refl, of w] apply simp
            apply (subst nth_ctape_pos)
        using n_gt_0 apply simp
            apply (subst TM.cinitial_config_def)
        unfolding TM_abbrevs.cinput_tape_def apply auto
            apply (subst prepend_list_nth_less)
             apply simp_all
        using n_gt_0 apply linarith
            apply (subst nth_map)
             apply auto
        using n_gt_0 apply linarith
            apply (smt (verit, best) Nitpick.size_list_simp(2) Suc_less_eq Suc_nat_eq_nat_zadd1 less_Suc_eq n_gt_0
            nat_int nth_tl of_nat_0_less_iff)
        using f104 [OF le_refl, of w 0, unfolded nth_ctape_0, simplified] apply simp
        using f109 [OF le_refl, of w] apply simp
           apply (subst nth_ctape_pos)
        using n_gt_0 apply simp
           apply (subst TM.cinitial_config_def)
        unfolding TM_abbrevs.cinput_tape_def apply (auto simp add: empty_ctape_def)
           apply (subst prepend_list_nth_ge)
        using n_gt_0 apply simp_all
          apply (subst cell_index.simps(4))
        unfolding cotm_steps_congruences(1) [symmetric] cotm_heads_steps_congruence [symmetric]
          valid_tm_next_move [OF valid_M'] apply (subst f101 [OF le_refl])
        using 1(1) apply simp
           apply (subst M'_def)
           apply simp
          apply standard
        using 1(2) [of n] apply simp
        apply (subst f101 [OF le_refl])
        using 1(1) apply simp
        apply (subst M'_def)
        using 1(1, 3) apply auto sorry
    next
      case 2
      then show ?case sorry
    next                                                    
      case 3
      then show ?case sorry
    next
      case 4
      then show ?case sorry
    next
      case 5
      then show ?case sorry
    next
      case 6
      then show ?case sorry
    next
      case 7
      then show ?case sorry
    next
      case 8
      then show ?case sorry
    next
      case 9
      then show ?case sorry
    next
      case 10
      then show ?case sorry
    next
      case 11
      then show ?case sorry
    }
  next
    case (le_Suc k)
    {
      case 1
      then show ?case sorry
    next
      case 2
      then show ?case sorry
    next
      case 3
      then show ?case sorry
    next
      case 4
      then show ?case sorry
    next
      case 5
      then show ?case sorry
    next
      case 6
      then show ?case sorry
    next
      case 7
      then show ?case sorry
    next
      case 8
      then show ?case sorry
    next
      case 9
      then show ?case sorry
    next
      case 10
      then show ?case sorry
    next
      case 11
      then show ?case sorry
    }
  qed
  have "alphabet L \<subseteq> TM.TM.symbols (Abs_TM M')"
    using M'_def \<open>alphabet L \<subseteq> TM.TM.symbols M\<close> valid_tm_symbols by force
  moreover have tb: "TM.time_bounded_word (Abs_TM M') (tcomp (\<lambda>x. real (T x))) w"
    if "set w \<subseteq> alphabet L" for w :: "'s list"
  proof (cases "length w \<ge> n")
    case True
    have "TM.time_bounded_word (Abs_TM M') T w" sorry
    then show ?thesis by (rule TM.time_bounded_word_tcompI)
  next
    case False
    have "TM.time_bounded_word (Abs_TM M') (\<lambda>n. Suc n) w"
      unfolding TM.time_bounded_word_def TM.run_def TM.is_final_def cotm_steps_congruences(1) [symmetric]
      apply (subst f101 [of "Suc (length w)", OF _ le_refl])
      using False apply simp
      unfolding valid_tm_final_states [OF valid_M'] apply (subst (2) M'_def)
      apply simp
      unfolding final_states_def states_def apply auto
      using that unfolding cotm_steps_congruences(1) [of "Suc (length w)", simplified]
         apply (subst TM.step_def)
         apply auto
         apply (rule TM.next_state_valid)
           apply (meson TM_steps_valid_stateI \<open>alphabet L \<subseteq> TM.TM.symbols M\<close> order_trans)
          apply (simp add: TM.run_tapes_len)
         apply (meson TM_steps_valid_headsI \<open>alphabet L \<subseteq> TM.TM.symbols M\<close> order_trans)
      using False apply simp
      using that \<open>alphabet L \<subseteq> TM.TM.symbols M\<close> apply blast
      using cell_index_abs_bound [of "Abs_TM M'" w 3 "Suc (length w)"] False by simp
    then show ?thesis by (metis Suc_eq_plus1 TM.time_bounded_word_mono tcomp_min)
  qed
  moreover have "TM_decider.decides_word (Abs_TM M') L w" if "set w \<subseteq> alphabet L" for w :: "'s list"
  proof (cases "length w \<ge> n")
    case True
    show ?thesis unfolding TM_decider.decides_def apply auto
    proof -
      show "TM_decider.accepts (Abs_TM M') w" if "w \<in>\<^sub>L L" sorry
      thus "TM_decider.rejects (Abs_TM M') w \<Longrightarrow> w \<in>\<^sub>L L \<Longrightarrow> False"
        using tb [OF that] TM_decider.acc_not_rej by blast
      show "TM_decider.rejects (Abs_TM M') w" if "w \<notin> words L" sorry
      thus "TM_decider.accepts (Abs_TM M') w \<Longrightarrow> w \<in>\<^sub>L L" using tb [OF that] TM_decider.acc_not_rej by blast
    qed
  next
    case False
    show ?thesis unfolding TM_decider.decides_def apply auto
    proof -
      have *: "(LEAST n. TM.is_final (Abs_TM M') ((TM.step (Abs_TM M') ^^ n) (TM.initial_config (Abs_TM M') w))) =
               Suc (length w)"
        apply (rule Least_nat_monoI)
          apply simp_all
        unfolding TM.is_final_def cotm_steps_congruences(1) [of "Suc (length w)", simplified, symmetric]
          cotm_steps_congruences(1) [symmetric]
        using f101 [of "Suc (length w)", OF _ le_refl] False apply simp_all
        unfolding valid_tm_final_states [OF valid_M'] apply (subst (2) M'_def)
         apply simp
        unfolding final_states_def states_def apply auto
           apply (simp add: cotm_steps_congruences(1) [of "Suc (length w)", simplified])
           apply (subst TM.step_def)
           apply auto
           apply (rule TM.next_state_valid)
             apply (meson TM_steps_valid_stateI \<open>alphabet L \<subseteq> TM.TM.symbols M\<close> order_trans that)
          apply (simp add: TM.run_tapes_len)
           apply (meson TM_steps_valid_headsI \<open>alphabet L \<subseteq> TM.TM.symbols M\<close> order_trans that)
        using False apply simp
      using that \<open>alphabet L \<subseteq> TM.TM.symbols M\<close> apply blast
      using cell_index_abs_bound [of "Abs_TM M'" w 3 "Suc (length w)"] False apply simp
      apply (subst (asm) (7) M'_def)
      apply simp
      unfolding final_states_def apply auto
      using f101 [of "length w", of w] apply simp_all
      apply (subst (asm) last_map)
      by simp_all
      show "TM_decider.accepts (Abs_TM M') w" if "w \<in>\<^sub>L L"
        unfolding TM_decider.accepts_def TM_decider.acc_def TM.compute_def TM.compute_config_def * apply auto
        unfolding cotm_steps_congruences(1) [of "Suc (length w)", simplified, symmetric]
        using f101 [of "Suc (length w)", OF _ le_refl] False apply simp_all
        unfolding valid_tm_final_states [OF valid_M'] apply (subst (2) M'_def)
         apply simp
        unfolding final_states_def states_def apply auto
           apply (simp add: cotm_steps_congruences(1) [of "Suc (length w)", simplified] cotm_steps_congruences(1))
           apply (subst TM.step_def)
           apply auto
           apply (rule TM.next_state_valid)
             apply (meson TM_steps_valid_stateI \<open>alphabet L \<subseteq> TM.TM.symbols M\<close> order_trans \<open>set w \<subseteq> alphabet L\<close>)
          apply (simp add: TM.run_tapes_len)
           apply (meson TM_steps_valid_headsI \<open>alphabet L \<subseteq> TM.TM.symbols M\<close> order_trans \<open>set w \<subseteq> alphabet L\<close>)
        using False apply simp
      using that \<open>alphabet L \<subseteq> TM.TM.symbols M\<close> apply blast
      using cell_index_abs_bound [of "Abs_TM M'" w 3 "Suc (length w)"] False apply simp
      unfolding valid_tm_label [OF valid_M'] apply (subst M'_def)
      using that by simp
      thus "TM_decider.rejects (Abs_TM M') w \<Longrightarrow> w \<in>\<^sub>L L \<Longrightarrow> False"
        using tb [OF that] TM_decider.acc_not_rej by blast
      show "TM_decider.rejects (Abs_TM M') w" if "w \<notin> words L"
        unfolding TM_decider.rejects_def TM_decider.rej_def TM.compute_def TM.compute_config_def * apply auto
        unfolding cotm_steps_congruences(1) [of "Suc (length w)", simplified, symmetric]
        using f101 [of "Suc (length w)", OF _ le_refl] False apply simp_all
        unfolding valid_tm_final_states [OF valid_M'] apply (subst (2) M'_def)
         apply simp
        unfolding final_states_def states_def apply auto
           apply (simp add: cotm_steps_congruences(1) [of "Suc (length w)", simplified] cotm_steps_congruences(1))
           apply (subst TM.step_def)
           apply auto
           apply (rule TM.next_state_valid)
             apply (meson TM_steps_valid_stateI \<open>alphabet L \<subseteq> TM.TM.symbols M\<close> order_trans \<open>set w \<subseteq> alphabet L\<close>)
          apply (simp add: TM.run_tapes_len)
           apply (meson TM_steps_valid_headsI \<open>alphabet L \<subseteq> TM.TM.symbols M\<close> order_trans \<open>set w \<subseteq> alphabet L\<close>)
        using False apply simp
      using \<open>set w \<subseteq> alphabet L\<close> \<open>alphabet L \<subseteq> TM.TM.symbols M\<close> apply blast
      using cell_index_abs_bound [of "Abs_TM M'" w 3 "Suc (length w)"] False apply simp
      unfolding valid_tm_label [OF valid_M'] apply (subst (asm) M'_def)
      using that by simp
      thus "TM_decider.accepts (Abs_TM M') w \<Longrightarrow> w \<in>\<^sub>L L" using tb [OF that] TM_decider.acc_not_rej by blast
    qed
  qed
  ultimately have *: "alphabet L \<subseteq> TM.TM.symbols (Abs_TM M') \<and>
                      (\<forall>x\<in>(alphabet L)*. TM_decider.decides_word (Abs_TM M') L x) \<and>
                      (\<forall>w. set w \<subseteq> alphabet L \<longrightarrow>
                      TM.time_bounded_word (Abs_TM M') (tcomp (\<lambda>x. real (T x))) w)" by simp
  have "L \<in> typed_DTIME TYPE('q \<times> 's option list \<times> nat \<times> bool) (tcomp (\<lambda>x. real (T x)))"
    unfolding in_dtime_tb_words_language_alphabet_iff
    apply standard
    apply standard
     apply standard
      apply (fact \<open>alphabet L \<subseteq> TM.TM.symbols (Abs_TM M')\<close>)
    using * by simp_all
  thus "L \<in> DTIME (tcomp (\<lambda>x. real (T x)))" by (rule typed_DTIME_impl_DTIME)
  qed
qed

lemma (in TM_decider) DTIME_aeI:
  assumes valid_alphabet: "alphabet L \<subseteq> \<Sigma>"
    and "\<forall>\<^sub>\<infinity>w\<in>(alphabet L)*. decides_word L w \<and> time_bounded_word T w"
  shows "L \<in> DTIME (tcomp T)" using DTIME_ae_tcomp assms by blast

lemma (in TM_decider) DTIME_aeI':
  assumes valid_alphabet: "alphabet L \<subseteq> \<Sigma>"
    and [intro]: "\<And>w. n \<le> length w \<Longrightarrow> w \<in> (alphabet L)* \<Longrightarrow> decides_word L w"
    and [intro]: "\<And>w. n \<le> length w \<Longrightarrow> w \<in> (alphabet L)* \<Longrightarrow> time_bounded_word T w"
  shows "L \<in> DTIME (tcomp T)"
  apply (rule DTIME_aeI)
   apply (fact valid_alphabet)
  apply (rule ae_word_lengthI)
  using valid_alphabet apply (simp add: finite_subset)
  by blast

lemma DTIME_mono_ae:
  fixes L :: "'s lang"
  assumes "L \<in> DTIME t"
    and Tt: "\<forall>\<^sub>\<infinity>n. T n \<ge> t n"
  shows "L \<in> DTIME (tcomp T)"
proof (insert assms(1), erule in_dtimeE, rule TM_decider.DTIME_aeI, auto)
  fix M :: "('a, 's) TM_decider"
  assume a1: "\<forall>w. set w \<subseteq> TM.TM.symbols M \<longrightarrow> TM.time_bounded_word M t w" and
         a2: "alphabet L \<subseteq> TM.TM.symbols M" and
         a3: "\<forall>x\<in>(alphabet L)*. TM_decider.decides_word M L x"
  obtain n\<^sub>0 :: nat where "\<And>n::nat. n \<ge> n\<^sub>0 \<Longrightarrow> T n \<ge> t n" using Tt by auto
  hence 1: "\<And>w. set w \<subseteq> TM.TM.symbols M \<Longrightarrow> length w \<ge> n\<^sub>0 \<Longrightarrow>
         TM.time_bounded_word M T w" using a1 TM.time_bounded_word_mono by blast
  show "\<forall>\<^sub>\<infinity>x. set x \<subseteq> alphabet L \<longrightarrow> TM.time_bounded_word M T x"
    apply (rule Alm_all_finite_listI)
     apply (rule 1)
    using a2 finite_subset by auto
qed



subsubsection\<open>Linear Speed-Up\<close>

text\<open>From @{cite \<open>ch.~12.2\<close> hopcroftAutomata1979}:

 ``\<^bold>\<open>Theorem 12.3\<close>  If \<open>L\<close> is accepted by a \<open>k\<close>-tape \<open>T(n)\<close> time-bounded Turing machine
  \<open>M\<^sub>1\<close>, then \<open>L\<close> is accepted by a \<open>k\<close>-tape \<open>cT(n)\<close> time-bounded TM \<open>M\<^sub>2\<close> for any \<open>c > 0\<close>,
  provided that \<open>k > 1\<close> and \<open>inf\<^sub>n\<^sub>\<rightarrow>\<^sub>\<infinity> T(n)/n = \<infinity>\<close>.''\<close>

(* TODO (!) check for consistency (fix types!) *)
(*lemma linear_time_speed_up:
  fixes T :: "nat \<Rightarrow> nat" and c :: real
  assumes "c > 0"
  \<comment> \<open>This assumption is stronger than the \<open>lim inf\<close> required by @{cite hopcroftAutomata1979}, but simpler to define in Isabelle.\<close>
    and "superlinear T"
    and "TM_decider.decides M1 L"
    and "TM.time_bounded M1 T"
  obtains M2 where "TM_decider.decides M2 L" and "TM.time_bounded M2 (tcomp (\<lambda>n. c * T n))"
  sorry*)

(* This can't work due to typing issues - since M2 works over a different alphabet than M1, the symbols are not necessarily
   type-compatible. Idea: define a function that has as input a TM and as output a TM that "behaves" the same, but works
   over a different set of symbols that can be concatinated. *)
(*lemma linear_time_speed_up:
  fixes T :: "nat \<Rightarrow> nat" and c :: real and M1 :: "(nat, 'a, bool) TM"
  assumes "c > 0"
  \<comment> \<open>This assumption is stronger than the \<open>lim inf\<close> required by @{cite hopcroftAutomata1979}, but simpler to define in Isabelle.\<close>
    and "superlinear T"
    and "TM_decider.decides M1 L"
    and "TM.time_bounded M1 T"
  shows "\<exists>M2::(nat, 'a list) TM_decider. TM_decider.decides M2 (ext_lang L) \<and> TM.time_bounded M2 (tcomp (\<lambda>n. c * T n))"
proof -
  let ?k = "TM.tape_count M1"
  obtain m :: nat where "m * c \<ge> 16"
    by (meson assms(1) ex_less_of_nat_mult nless_le)
  define M2_symbols :: "'a list set" where
    "M2_symbols \<equiv> {l. (length l = 1 \<or> length l = m) \<and> (\<forall>s\<in>set l. s\<in>TM.symbols M1)}"
  obtain max_state :: nat where "max_state \<in> TM.states M1 \<and> (\<forall>s\<in>TM.states M1. s \<le> max_state)"
    by (metis TM.state_axioms(1) TM.state_axioms(2) finite_has_maximal2 nat_le_linear)
  define M2_start_state :: nat where "M2_start_state \<equiv> Suc max_state"
  
  thus ?thesis sorry
qed*)

lemma linear_time_speed_up2:
  fixes T :: "nat \<Rightarrow> nat" and M1 :: "(nat, 'a, bool) TM"
  assumes "superlinear T"
    and "TM_decider.decides M1 L"
    and "TM.time_bounded_symbols M1 (tcomp T)"
  shows "\<exists>M2::(nat, 'a) TM_decider. TM_decider.decides M2 L \<and>
         TM.time_bounded_symbols M2 (tcomp (\<lambda>n. T n div 2))"
proof -
  define tape_count :: nat where "tape_count \<equiv> Suc ((TM.tape_count M1) * 32)"
  hence tape_count_gt_0: "tape_count > 0" by simp
  have 1: "\<And>C::nat. \<exists>n\<^sub>0::nat. \<forall>n\<ge>n\<^sub>0. C * n \<le> T n"
    using assms(1) [unfolded superlinear_def, folded atomize_all, simplified] by auto
  have "\<And>C::nat. \<exists>n\<^sub>0::nat. \<forall>n\<ge>n\<^sub>0. real C \<le> real (T n) / n"
  proof -
    fix C :: nat
    obtain n\<^sub>0 :: nat where "\<And>n::nat. n \<ge> n\<^sub>0 \<Longrightarrow> C * n \<le> T n" using 1 by blast
    hence "\<And>n::nat. n \<ge> n\<^sub>0 \<Longrightarrow> real C * n \<le> real (T n)"
      by (metis of_nat_mono of_nat_mult)
    hence "\<And>n::nat. n \<ge> Suc n\<^sub>0 \<Longrightarrow> real C \<le> real (T n) / real n"
      by (simp add: pos_le_divide_eq)
    thus "\<exists>n\<^sub>0. \<forall>n\<ge>n\<^sub>0. real C \<le> real (T n) / real n" by auto
  qed
  then obtain n\<^sub>d :: nat where n\<^sub>d_def: "\<And>n::nat. n \<ge> n\<^sub>d \<Longrightarrow> real (T n) / n \<ge> 65 / 8"
    by (meson order_trans real_arch_simple)
  show ?thesis sorry
qed

lemma linear_time_speed_up_c:
  fixes T :: "nat \<Rightarrow> nat" and c :: real and M1 :: "(nat, 'a, bool) TM"
  assumes "superlinear T"
    and "c > 0"
    and "TM_decider.decides M1 L"
    and "TM.time_bounded_symbols M1 T"
  shows "\<exists>M2::(nat, 'a) TM_decider. TM_decider.decides M2 L \<and>
         TM.time_bounded_symbols M2 (tcomp (\<lambda>n. c * T n))"
proof -
  have 1: "\<And>p::nat. \<exists>M2::(nat, 'a) TM_decider. TM_decider.decides M2 L \<and>
        TM.time_bounded_symbols M2 (tcomp (\<lambda>n. T n div (2 ^ p)))"
  proof -
    fix p :: nat
    show "\<exists>M2::(nat, 'a) TM_decider. (alphabet L \<subseteq> TM.TM.symbols M2 \<and>
          (\<forall>w\<in>(alphabet L)*. TM_decider.decides_word M2 L w)) \<and>
          (\<forall>w. set w \<subseteq> TM.TM.symbols M2 \<longrightarrow>
                   TM.time_bounded_word M2 (tcomp (\<lambda>x. real (T x div 2 ^ p))) w)"
      apply (induction p)
      apply simp
      apply (meson TM.time_bounded_word_mono assms(3) assms(4) max.cobounded2)
    proof (erule exE, erule conjE, erule conjE)
      fix p :: nat and M2 :: "(nat, 'a) TM_decider"
      assume a1: "\<forall>w. set w \<subseteq> TM.TM.symbols M2 \<longrightarrow>
           TM.time_bounded_word M2 (tcomp (\<lambda>x. real (T x div 2 ^ p))) w" and
             a2: "alphabet L \<subseteq> TM.TM.symbols M2" and
             a3: "\<forall>w\<in>(alphabet L)*. TM_decider.decides_word M2 L w"
      have "\<exists>M2::(nat, 'a) TM_decider. (alphabet L \<subseteq> TM.TM.symbols M2 \<and>
             (\<forall>w\<in>(alphabet L)*. TM_decider.decides_word M2 L w)) \<and>
            (\<forall>w. set w \<subseteq> TM.TM.symbols M2 \<longrightarrow>
           TM.time_bounded_word M2 (tcomp (\<lambda>x. real (T x div 2 ^ p div 2))) w)"
        apply (rule linear_time_speed_up2)
          apply (rule superlinear_div_nat [THEN iffD2])
           apply auto
           apply (fact assms(1))
        using a1 a2 a3 by auto
      moreover have "\<And>n::nat. n div 2 ^ p div 2 = n div 2 ^ Suc p"
        by (metis div_mult2_eq power_Suc2)
      ultimately show "\<exists>M2::(nat, 'a) TM_decider. (alphabet L \<subseteq> TM.TM.symbols M2 \<and>
             (\<forall>w\<in>(alphabet L)*. TM_decider.decides_word M2 L w)) \<and>
            (\<forall>w. set w \<subseteq> TM.TM.symbols M2 \<longrightarrow>
                 TM.time_bounded_word M2 (tcomp (\<lambda>x. real (T x div 2 ^ Suc p))) w)"
        by simp
    qed
  qed
  then obtain M :: "(nat, 'a) TM_decider" where
    M_alphabet: "alphabet L \<subseteq> TM.TM.symbols M" and
    M_dec: "\<forall>w\<in>(alphabet L)*. TM_decider.decides_word M L w" and
    M_tb: "TM.time_bounded_symbols M (tcomp (\<lambda>n. T n div (2 ^ nat \<lceil>1 / c\<rceil>)))" by blast
  have 2: "\<And>n::nat. (real n) / (1 / c) = c * (real n)" by simp
  have "\<And>n::nat. n div (1 / c) \<le> (real n) / (1 / c)" by simp
  hence 3: "\<And>n::nat. n div \<lceil>1 / c\<rceil> \<le> (real n) / (1 / c)"
    by (smt (verit, ccfv_SIG) assms(2) ceiling_eq_iff divide_eq_0_iff
        floor_divide_of_int_eq frac_le le_floor_iff of_int_of_nat_eq of_nat_0_le_iff
        zero_le_divide_1_iff)
  have 4: "\<And>n::nat. real (n div 2 ^ nat \<lceil>1 / c\<rceil>) \<le> real (n div nat \<lceil>1 / c\<rceil>)"
    by (metis Groups.mult_ac(2) assms(2) 2 div_by_0 div_le_mono2
        mult.left_neutral nle_le not_less of_nat_0 of_nat_0_le_iff of_nat_1
        of_nat_ceiling of_nat_le_iff self_le_ge2_pow zero_le_divide_1_iff)
  have "TM.time_bounded_symbols M (tcomp (\<lambda>n. c * T n))"
    apply (rule TM.time_bounded_symbols_mono)
     apply (fact M_tb)
    apply (rule tcomp_nat_mono)
    using 2 3 4
    by (smt (verit, ccfv_SIG) assms(2) ceiling_of_int
        linordered_euclidean_semiring_class.of_nat_div of_int_of_nat_eq
        of_nat_int_ceiling zero_le_divide_1_iff)
  thus ?thesis using M_alphabet M_dec by auto
qed

corollary DTIME_speed_up:
  fixes T :: "nat \<Rightarrow> nat" and c :: real
    and L::"'s lang"
  assumes "L \<in> DTIME T"
    and "superlinear T"
    and "c > 0"
  shows "L \<in> DTIME (tcomp (\<lambda>n. c * T n))"
proof -
  from \<open>L \<in> DTIME T\<close> obtain M1 :: "(nat, 's) TM_decider"
    where M1_dec: "TM_decider.decides M1 L" and
          M1_tb: "TM.time_bounded_symbols M1 T" ..
  hence M1_sym: "alphabet L \<subseteq> TM.symbols M1" by simp
  then obtain M2 :: "(nat, 's) TM_decider"
    where "TM_decider.decides M2 L" and
          "TM.time_bounded_symbols M2 (tcomp (\<lambda>n. c * T n))"
    using linear_time_speed_up_c [OF assms(2) assms(3), where L=L]
      M1_dec M1_tb M1_sym by metis
  thus ?thesis by auto
qed


(*lemma speed_up_rev_helper:
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
qed*)

(*lemma speed_up_rev_helper':
  fixes n :: nat and c d :: real
  defines "d \<equiv> 1/(2*c)"
  assumes "c \<ge> 1"
  shows "nat \<lceil>d * nat \<lceil>c * n\<rceil>\<rceil> \<le> n"
proof -
  from \<open>c \<ge> 1\<close> have "c * n \<ge> 0" by simp
  then have *: "real (nat \<lceil>c * n\<rceil>) = real_of_int \<lceil>c * n\<rceil>" by simp
  from speed_up_rev_helper[OF \<open>c \<ge> 1\<close>] show ?thesis unfolding * d_def .
qed*)

(*lemma DTIME_speed_up_rev:
  fixes T :: "nat \<Rightarrow> nat" and c :: real
  defines "T' \<equiv> tcomp (\<lambda>n. c * T n)"
  assumes "L \<in> DTIME T'"
    and "superlinear T"
    and "c > 0"
  shows "L \<in> DTIME (tcomp T)"
proof (cases "c \<ge> 1")
  assume "\<not> c \<ge> 1"
  then have "c \<le> 1" by simp

  define T'' where "T'' \<equiv> tcomp (\<lambda>n. 1 * real (T' n))"
  have "T'' = T'" unfolding T''_def T'_def mult_1 tcomp_tcomp ..

  from \<open>superlinear T\<close> and \<open>c > 0\<close> have "superlinear T'" unfolding T'_def by simp
  with \<open>L \<in> DTIME T'\<close>
  have "L \<in> DTIME T''" unfolding T''_def by (rule DTIME_speed_up) simp
  then show "L \<in> DTIME (tcomp T)" unfolding \<open>T'' = T'\<close> and T'_def
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

  from \<open>L \<in> DTIME T'\<close> and \<open>superlinear T'\<close> and \<open>d > 0\<close>
  have "L \<in> DTIME T''" unfolding T''_def by (rule DTIME_speed_up)
  then show "L \<in> DTIME (tcomp T)"
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
qed*)

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

lemma ex_readonly_input_tm: "L \<in> DTIME T \<Longrightarrow>
      \<exists>tm::(nat, 'a) TM_decider. TM_decider.decides tm L \<and>
      TM.time_bounded_symbols tm (\<lambda>n. T n + n) \<and>
      (\<forall>w\<in>(TM.symbols tm)*. hd (tapes (trim_tapes (TM.steps tm (T (length w) + length w)
      (TM.initial_config tm w)))) = hd (tapes (TM.initial_config tm w)))"
proof (erule in_dtimeE, erule conjE, fold atomize_all atomize_imp atomize_ball, simp)
  fix M :: "(nat, 'a) TM_decider"
  assume a1: "alphabet L \<subseteq> TM.TM.symbols M" and
         a2: "\<And>w. set w \<subseteq> TM.TM.symbols M \<Longrightarrow> TM.time_bounded_word M T w" and
         a3: "\<And>x. set x \<subseteq> alphabet L \<Longrightarrow> TM_decider.decides_word M L x"
  define tape_count :: nat where "tape_count \<equiv> TM.tape_count M + 3"
  define states :: "(nat \<times> bool \<times> bool \<times> bool) set" where
    "states \<equiv> TM.states M \<times> UNIV \<times> UNIV \<times> UNIV"
  define final_states :: "(nat \<times> bool \<times> bool \<times> bool) set" where
    "final_states \<equiv> {(s, _, _, b). s \<in> TM.final_states M \<and> b \<or>
                     TM.initial_state M \<in> TM.final_states M \<and> s \<in> TM.states M}"
  define init_state :: "nat \<times> bool \<times> bool \<times> bool" where
    "init_state \<equiv> (TM.initial_state M, False, False, False)"
  have states_final: "finite states" unfolding states_def by simp
  have final_states_subset: "final_states \<subseteq> states"
    unfolding final_states_def states_def by auto
  have init_state_in_states: "init_state \<in> states"
    unfolding init_state_def states_def by simp
  obtain marker_sym :: 'a where marker_sym_is_sym: "marker_sym \<in> TM.symbols M" by fastforce
  define M_tapes :: "'a tape list \<Rightarrow> 'a tape list" where
    "\<And>t. M_tapes t \<equiv> t ! (TM.tape_count M) # take (TM.tape_count M - 1) (tl t)"
  define M_hds :: "'a option list \<Rightarrow> 'a option list" where
    "\<And>hds. M_hds hds \<equiv> hds ! (TM.tape_count M) # take (TM.tape_count M - 1) (tl hds)"
      (* TODO: Continue from here! Define the TM and prove its validity and properties *)
  define M' :: "(nat \<times> bool \<times> bool \<times> bool, 'a, bool) TM_record" where
    "M' \<equiv> TM tape_count (TM.symbols M) states init_state final_states
          (\<lambda>(s, _, _, _). TM.label M s)
          (\<lambda>(s, b1, b2, b3) hds. let s' = TM.next_state M s (M_hds hds);
                                     b1' = if \<not>b2 \<and> hds ! (tape_count - 2) \<noteq> None then
                                             undefined else b1;
                                     b2' = if hds ! 0 = None then True else b2;
                                     b3' = undefined
                                      in (s', b1', b2', b3'))
          (\<lambda>(s, b1, b2, b3) hds k. undefined)
          (\<lambda>(s, b1, b2, b3) hds k. undefined)"
  have M'_valid [intro, simp]: "valid_TM M'" sorry
  obtain f :: "(nat \<times> bool \<times> bool \<times> bool) \<Rightarrow> nat" where
    f_inj: "inj_on f (TM.states (Abs_TM M'))" by blast
  define tm :: "(nat, 'a, bool) TM_record" where "tm \<equiv> map_states_tmrec f (Abs_TM M')"
  have tm_valid [intro, simp]: "valid_TM tm"
    by (simp add: f_inj map_states_tmrec_valid tm_def)
  have *: "TM.symbols (Abs_TM tm) = TM.symbols (Abs_TM M')"
    unfolding valid_tm_symbols [OF tm_valid]
    unfolding tm_def map_states_tmrec_def [OF f_inj] by simp
  have "alphabet L \<subseteq> TM.TM.symbols (Abs_TM M')" sorry
  hence "alphabet L \<subseteq> TM.symbols (Abs_TM tm)" by (simp only: *)
  moreover have "\<And>w. set w \<subseteq> alphabet L \<Longrightarrow> TM_decider.decides_word (Abs_TM M') L w" sorry
  hence "\<And>w. set w \<subseteq> alphabet L \<Longrightarrow> TM_decider.decides_word (Abs_TM tm) L w"
    using map_states_tmrec_decides_iff [OF f_inj, of L]
    by (simp add: \<open>alphabet L \<subseteq> TM.TM.symbols (Abs_TM M')\<close> tm_def)
  moreover have "\<And>w. set w \<subseteq> TM.TM.symbols (Abs_TM M') \<Longrightarrow>
                 TM.time_bounded_word (Abs_TM M') (\<lambda>n. T n + n) w" sorry
  hence "set w \<subseteq> TM.TM.symbols (Abs_TM tm) \<Longrightarrow>
         TM.time_bounded_word (Abs_TM tm) (\<lambda>n. T n + n) w" for w :: "'a list"
    unfolding TM.time_bounded_word_def using map_states_tmrec_run(1) [OF f_inj,
        of w "T (length w) + length w"] unfolding * apply auto
    by (metis (no_types, lifting) TM.final_run_compute TM.halts_compute TM_config.expand
        f_inj map_states_tmrec_comp_state map_states_tmrec_comp_tapes
        map_states_tmrec_halts_iff map_states_tmrec_run_tapes tm_def)
  moreover have "\<And>w. set w \<subseteq> TM.symbols (Abs_TM M') \<Longrightarrow> hd (tapes (trim_tapes
        ((TM.step (Abs_TM M') ^^ (T (length w) + length w))
        (TM.initial_config (Abs_TM M') w)))) = hd (tapes (TM.initial_config (Abs_TM M') w))"
    sorry
  hence "set w \<subseteq> TM.symbols (Abs_TM tm) \<Longrightarrow> hd (tapes (trim_tapes
        ((TM.step (Abs_TM tm) ^^ (T (length w) + length w))
        (TM.initial_config (Abs_TM tm) w)))) = hd (tapes (TM.initial_config (Abs_TM tm) w))"
    for w :: "'a list"
    unfolding * using map_states_tmrec_run(2) [OF f_inj, of w "T (length w) + length w"]
    by (simp add: TM.initial_config_def TM.run_def tm_def trim_tapes_def)
  ultimately show "\<exists>tm :: (nat, 'a) TM_decider. alphabet L \<subseteq> TM.TM.symbols tm \<and>
                   (\<forall>x\<in>(alphabet L)*. TM_decider.decides_word tm L x) \<and>
                   (\<forall>w. set w \<subseteq> TM.TM.symbols tm \<longrightarrow>
                   TM.time_bounded_word tm (\<lambda>n. T n + n) w) \<and>
                   (\<forall>w\<in>(TM.TM.symbols tm)*. hd (tapes (trim_tapes
                   ((TM.step tm ^^ (T (length w) + length w)) (TM.initial_config tm w)))) =
                   hd (tapes (TM.initial_config tm w)))" by blast
qed

lemma DTIME_int:
  fixes L\<^sub>1 L\<^sub>2 :: "'s lang"
  assumes "L\<^sub>1 \<in> DTIME(T\<^sub>1)"
    and "L\<^sub>2 \<in> DTIME(T\<^sub>2)"
  shows "L\<^sub>1 \<inter>\<^sub>L L\<^sub>2 \<in> DTIME(\<lambda>n. max (T\<^sub>1 n) (T\<^sub>2 n))"
proof -
  have "\<And>T\<^sub>1 T\<^sub>2 L\<^sub>1 L\<^sub>2. T\<^sub>1 \<le> T\<^sub>2 \<Longrightarrow> L\<^sub>1 \<in> DTIME(T\<^sub>1) \<Longrightarrow> L\<^sub>2 \<in> DTIME(T\<^sub>2) \<Longrightarrow>
        L\<^sub>1 \<inter>\<^sub>L L\<^sub>2 \<in> DTIME(T\<^sub>2)"
  proof -
    fix T\<^sub>1 T\<^sub>2 :: "nat \<Rightarrow> nat" and L\<^sub>1 L\<^sub>2 :: "'b lang" (* new type parameter 'b! *)
    assume a1: "T\<^sub>1 \<le> T\<^sub>2" and a2: "L\<^sub>1 \<in> DTIME T\<^sub>1" and a2: "L\<^sub>2 \<in> DTIME T\<^sub>2"
    show "L\<^sub>1 \<inter>\<^sub>L L\<^sub>2 \<in> DTIME T\<^sub>2"
    proof (cases "superlinear T\<^sub>1")
      case True
      then have superlinear_T\<^sub>2: "superlinear T\<^sub>2"
        using a1 by (simp add: le_fun_def superlinear_ae_mono)

      then show ?thesis sorry
    next
      case False
      then show ?thesis sorry
    qed
  qed
  thus ?thesis using assms
    by (metis (no_types, lifting) dual_order.eq_iff in_dtime_mono max.cobounded1
        max.cobounded2)
qed

lemma DTIME_compl_helper: "L \<in> DTIME t \<Longrightarrow> -L \<in> DTIME t"
proof -
  assume "L \<in> DTIME t"
  then obtain tm :: "(nat, 'a) TM_decider" where tm_def: "TM_decider.decides tm L \<and>
                                                  TM.time_bounded_symbols tm t"
    unfolding typed_DTIME_def by blast
  have 1: "TM.TM.final_states (Abs_TM (compl_TM tm)) = TM.TM.final_states tm"
    unfolding compl_TM_def using compl_TM_valid
    by (simp add: valid_TM_I valid_tm_final_states)
  have 2: "TM.TM.symbols (Abs_TM (compl_TM tm)) = TM.TM.symbols tm"
    unfolding compl_TM_def using compl_TM_valid
    by (metis compl_TM_def select_convs(2) valid_tm_symbols)
  have "TM.time_bounded_symbols (Abs_TM (compl_TM tm)) t" unfolding TM.time_bounded_word_def
      compl_TM_run TM.is_final_def 1 using 2 TM.time_bounded_wordD tm_def by blast
  moreover have "TM_decider.decides (Abs_TM (compl_TM tm)) (-L)" unfolding
      TM_decider.decides_def compl_alphabet 2
    by (metis TM_decider.decides_def compl_TM_accepts compl_TM_rejects
        compl_word tm_def)
  ultimately show ?thesis using typed_DTIME_def by force
qed

lemma DTIME_compl: "-L \<in> DTIME T \<longleftrightarrow> L \<in> DTIME T"
proof (rule sym, rule, erule DTIME_compl_helper)
  have "- L \<in> DTIME T \<Longrightarrow> -(-L) \<in> DTIME T" by (rule DTIME_compl_helper)
  thus "- L \<in> DTIME T \<Longrightarrow> L \<in> DTIME T" by simp
qed

subsection\<open>Reductions\<close> (* currently broken *) 

(* Reduceability of languages with time constraints *)
definition dtime_reducible :: "(nat \<Rightarrow> nat) \<Rightarrow> 'a lang \<Rightarrow> 'a lang \<Rightarrow> bool" where
  "dtime_reducible T L1 L2 \<equiv> \<exists>M::(nat, 'a, unit) TM. (\<forall>wi::'a list \<in> (alphabet L1)*.
                              \<exists>wo::'a list \<in> (alphabet L2)*. TM.computes_word M wi wo \<and>
                              (\<forall>wo::'a list \<in> (alphabet L2)*. TM.computes_word M wi wo \<longrightarrow>
                              (wi \<in>\<^sub>L L1 \<longleftrightarrow> wo \<in>\<^sub>L L2))) \<and>
                              ((\<exists>l::nat. \<forall>wi::'a list \<in> (alphabet L1)*. length wi \<ge> l \<longrightarrow>
                              (\<forall>wo::'a list \<in> (alphabet L2)*. TM.computes_word M wi wo \<longrightarrow>
                              TM.is_final M (TM.run M (T (length wi)) wi))))"

definition poly_reducible :: "'a lang \<Rightarrow> 'a lang \<Rightarrow> bool" (infix "\<le>\<^sub>p" 50) where
  "poly_reducible L1 L2 \<equiv> \<exists>k::nat. dtime_reducible (\<lambda>n. n^k) L1 L2"

lemma dtime_reducibleE: assumes "dtime_reducible T L1 L2"
  obtains M :: "(nat, 'a, unit) TM" and l :: nat where
    "\<And>wi. set wi \<subseteq> alphabet L1 \<Longrightarrow> \<exists>wo\<in>(alphabet L2)*. TM.computes_word M wi wo" and
    "\<And>wi wo. set wi \<subseteq> alphabet L1 \<Longrightarrow> set wo \<subseteq> alphabet L2 \<Longrightarrow>
     TM.computes_word M wi wo \<Longrightarrow> (wi \<in>\<^sub>L L1 \<longleftrightarrow> wo \<in>\<^sub>L L2)" and
    "\<And>wi wo. set wi \<subseteq> alphabet L1 \<Longrightarrow> length wi \<ge> l \<Longrightarrow> TM.is_final M (TM.run M (T (length wi)) wi)"
proof
  fix wi :: "'a list"
  assume a1: "set wi \<subseteq> alphabet L1"
  define M :: "(nat, 'a, unit) TM" where "M \<equiv> (SOME M. (\<forall>wi::'a list \<in> (alphabet L1)*.
                              \<exists>wo::'a list \<in> (alphabet L2)*. TM.computes_word M wi wo \<and>
                              (\<forall>wo::'a list \<in> (alphabet L2)*. TM.computes_word M wi wo \<longrightarrow>
                              (wi \<in>\<^sub>L L1 \<longleftrightarrow> wo \<in>\<^sub>L L2))) \<and>
                              ((\<exists>l::nat. \<forall>wi::'a list \<in> (alphabet L1)*. length wi \<ge> l \<longrightarrow>
                              (\<forall>wo::'a list \<in> (alphabet L2)*. TM.computes_word M wi wo \<longrightarrow>
                              TM.is_final M (TM.run M (T (length wi)) wi)))))"
  note M_characteristic = someI_ex [OF assms [unfolded dtime_reducible_def], folded M_def]
  show output_exists: "\<exists>wo\<in>(alphabet L2)*. TM.computes_word M wi wo"
    using M_characteristic a1 by blast
  fix wo :: "'a list"
  show "wi \<in>\<^sub>L L1 \<longleftrightarrow> wo \<in>\<^sub>L L2" if a2: "set wo \<subseteq> alphabet L2" and a3: "TM.computes_word M wi wo"
    using M_characteristic [THEN conjunct1, THEN bspec, simplified, OF a1, THEN conjunct2] a2 a3 by blast
  define l :: nat where "l \<equiv> (SOME l. \<forall>wi\<in>(alphabet L1)*. l \<le> length wi \<longrightarrow>
                              (\<forall>wo\<in>(alphabet L2)*. TM.computes_word M wi wo \<longrightarrow>
                              TM.is_final M (TM.run M (T (length wi)) wi)))"
  note l_characteristic = someI_ex [OF M_characteristic [THEN conjunct2], folded l_def]
  assume a4: "l \<le> length wi"
  show "TM.is_final M (TM.run M (T (length wi)) wi)"
    using l_characteristic [THEN bspec, simplified, OF a1, THEN mp, OF a4, THEN mp, OF output_exists] .
qed

lemma dtime_reducibleE': assumes "dtime_reducible T L1 L2"
  obtains M :: "(nat, 'a, unit) TM" and l :: nat and f :: "'a list \<Rightarrow> 'a list" where
    "\<And>wi. set wi \<subseteq> alphabet L1 \<Longrightarrow> set (f wi) \<subseteq> alphabet L2" and
    "\<And>wi. set wi \<subseteq> alphabet L1 \<Longrightarrow> TM.computes_word M wi (f wi)" and
    "\<And>wi wo. set wi \<subseteq> alphabet L1 \<Longrightarrow> (wi \<in>\<^sub>L L1 \<longleftrightarrow> (f wi) \<in>\<^sub>L L2)" and
    "\<And>wi wo. set wi \<subseteq> alphabet L1 \<Longrightarrow> length wi \<ge> l \<Longrightarrow> TM.is_final M (TM.run M (T (length wi)) wi)"
proof
  fix wi :: "'a list"
  assume a1: "set wi \<subseteq> alphabet L1"
  define M :: "(nat, 'a, unit) TM" where "M \<equiv> (SOME M. (\<forall>wi::'a list \<in> (alphabet L1)*.
                              \<exists>wo::'a list \<in> (alphabet L2)*. TM.computes_word M wi wo \<and>
                              (\<forall>wo::'a list \<in> (alphabet L2)*. TM.computes_word M wi wo \<longrightarrow>
                              (wi \<in>\<^sub>L L1 \<longleftrightarrow> wo \<in>\<^sub>L L2))) \<and>
                              ((\<exists>l::nat. \<forall>wi::'a list \<in> (alphabet L1)*. length wi \<ge> l \<longrightarrow>
                              (\<forall>wo::'a list \<in> (alphabet L2)*. TM.computes_word M wi wo \<longrightarrow>
                              TM.is_final M (TM.run M (T (length wi)) wi)))))"
  note M_characteristic = someI_ex [OF assms [unfolded dtime_reducible_def], folded M_def]
  define f :: "'a list \<Rightarrow> 'a list" where
    "\<And>w. f w \<equiv> if set w \<subseteq> alphabet L1 then (SOME wo. TM.computes_word M w wo) else undefined"
  have f_characteristic: "set w \<subseteq> alphabet L1 \<Longrightarrow> TM.computes_word M w (f w)" for w :: "'a list"
    unfolding f_def apply simp
    apply (rule someI_ex)
    apply (drule M_characteristic [THEN conjunct1, THEN bspec, simplified])
    by fast
  show "TM.computes_word M wi (f wi)"
    apply (rule f_characteristic)
    by fact
  obtain wo :: "'a list" where M_comp_wi_wo: "TM.computes_word M wi wo" and wo_alphabet: "set wo \<subseteq> alphabet L2"
    using M_characteristic [THEN conjunct1, THEN bspec, simplified, OF a1, THEN conjunct1] by fast
  have wo_is_fwi: "f wi = wo"
    using f_characteristic [OF a1] M_comp_wi_wo by (rule computes_word_unique)
  show "set (f wi) \<subseteq> alphabet L2"
    unfolding wo_is_fwi by fact
  show "wi \<in>\<^sub>L L1 \<longleftrightarrow> f wi \<in>\<^sub>L L2"
    unfolding wo_is_fwi using M_characteristic [THEN conjunct1, THEN bspec, simplified, OF a1, THEN conjunct2,
        THEN bspec, simplified, OF wo_alphabet, THEN mp, OF M_comp_wi_wo] .
  define l :: nat where "l \<equiv> (SOME l. \<forall>wi\<in>(alphabet L1)*. l \<le> length wi \<longrightarrow>
                              (\<forall>wo\<in>(alphabet L2)*. TM.computes_word M wi wo \<longrightarrow>
                              TM.is_final M (TM.run M (T (length wi)) wi)))"
  note l_characteristic = someI_ex [OF M_characteristic [THEN conjunct2], folded l_def]
  assume a2: "l \<le> length wi"
  show "TM.is_final M (TM.run M (T (length wi)) wi)"
    using l_characteristic [THEN bspec, simplified, OF a1, THEN mp, OF a2, THEN mp, OF bexI, OF M_comp_wi_wo, simplified,
        OF wo_alphabet] .
qed

(*lemma dtime_reducible_id: "dtime_reducible (\<lambda>n. 1) L L"
  apply (unfold dtime_reducible_def)
proof -
  define tm :: "(nat, 'a) TM_decider" where "tm \<equiv> Abs_TM (halting_TM_rec 0 {(SOME x. True)} True)"
  have "\<forall>wi wo. TM.computes_word tm wi wo \<longrightarrow> (wi \<in>\<^sub>L L) = (wo \<in>\<^sub>L L) \<and> TM.is_final tm (TM.run tm 1 wi)"
    (is "?P tm")
  proof auto
    fix wi wo :: "'a list"
    assume "TM.computes_word tm wi wo" and "wi \<in>\<^sub>L L"
    have "TM.initial_state tm = (0::nat)" unfolding tm_def halting_TM_rec_def using halting_TM_valid
      by (metis finite.emptyI finite_insert halting_TM_rec_def insert_not_empty select_convs(4)
          valid_tm_initial_state)
    moreover have "0\<in>TM.final_states tm" unfolding tm_def halting_TM_rec_def using halting_TM_valid
      by (smt (verit) finite.emptyI finite.insertI insert_not_empty insert_subset less_numeral_extra(1)
          select_convs(5) singletonI singleton_insert_inj_eq' valid_TM_I valid_tm_final_states)
    ultimately have "\<And>c. state c = 0 \<Longrightarrow> TM.is_final tm c" unfolding tm_def halting_TM_rec_def TM.is_final_def
      using halting_TM_valid by simp
    moreover have "TM.tape_count tm = 1" unfolding tm_def halting_TM_rec_def using halting_TM_valid
      by (metis finite.emptyI finite_insert halting_TM_rec_def insert_not_empty select_convs(1) valid_tm_tape_count)
    ultimately have "wi = wo" using \<open>TM.computes_word tm wi wo\<close> halting_TM_valid apply (unfold TM.computes_word_def)
      apply auto unfolding TM.has_output_def sorry (* Is clearly true. ;-) *)
    thus "wo \<in>\<^sub>L L" using \<open>wi \<in>\<^sub>L L\<close> by simp
  next
    fix wi wo :: "'a list"
    assume "TM.computes_word tm wi wo" and "wo \<in>\<^sub>L L"
    thus "wi \<in>\<^sub>L L" sorry
  next
    fix wi wo :: "'a list"
    assume "TM.computes_word tm wi wo"
    have "TM.initial_state tm = (0::nat)" unfolding tm_def halting_TM_rec_def using halting_TM_valid
      by (metis finite.emptyI finite_insert halting_TM_rec_def insert_not_empty select_convs(4)
          valid_tm_initial_state)
    moreover have "0\<in>TM.final_states tm" unfolding tm_def halting_TM_rec_def using halting_TM_valid
      by (smt (verit) finite.emptyI finite.insertI insert_not_empty insert_subset less_numeral_extra(1)
          select_convs(5) singletonI singleton_insert_inj_eq' valid_TM_I valid_tm_final_states)
    ultimately have "\<And>c. state c = 0 \<Longrightarrow> TM.is_final tm c" unfolding tm_def halting_TM_rec_def TM.is_final_def
      using halting_TM_valid by simp
    thus "TM.is_final tm (TM.run tm (Suc 0) wi)" unfolding TM.run_def TM.initial_config_def
      using \<open>TM.TM.initial_state tm = 0\<close> by force
  qed
  thus "\<exists>tm::(nat, 'a) TM_decider. ?P tm" by auto
qed

lemma dtime_reducibleI [intro]:
  fixes tm :: "(nat, 'a) TM_decider" and l1 l2 :: "'a lang" and t :: "nat \<Rightarrow> nat"
  assumes "\<And>wi wo. TM.computes_word tm wi wo \<Longrightarrow> wi \<in>\<^sub>L l1 \<longleftrightarrow> wo \<in>\<^sub>L l2" and
          "\<And>wi wo. TM.computes_word tm wi wo \<Longrightarrow> TM.time_bounded_word tm t wi"
  shows "dtime_reducible t l1 l2"
proof (unfold dtime_reducible_def)
  have "\<forall>wi wo.
            TM.computes_word tm wi wo \<longrightarrow> (wi \<in>\<^sub>L l1) = (wo \<in>\<^sub>L l2) \<and> TM.is_final tm (TM.run tm (t (length wi)) wi)"
    using assms unfolding TM.time_bounded_word_def by simp
  thus "\<exists>tm::(nat, 'a) TM_decider. \<forall>wi wo.
            TM.computes_word tm wi wo \<longrightarrow> (wi \<in>\<^sub>L l1) = (wo \<in>\<^sub>L l2) \<and> TM.is_final tm (TM.run tm (t (length wi)) wi)"
    by auto
qed*)

lemma poly_reducibleI [intro]:
  fixes tm :: "(nat, 'a, unit) TM" and l1 l2 :: "'a lang" and k l :: nat
  assumes "\<And>wi. set wi \<subseteq> alphabet l1 \<Longrightarrow> \<exists>wo. set wo \<subseteq> alphabet l2 \<and> TM.computes_word tm wi wo"
          "\<And>wi wo. set wi \<subseteq> alphabet l1 \<Longrightarrow> set wo \<subseteq> alphabet l2 \<Longrightarrow>
           TM.computes_word tm wi wo \<Longrightarrow> wi \<in>\<^sub>L l1 \<longleftrightarrow> wo \<in>\<^sub>L l2" and
          "\<And>wi wo. length wi \<ge> l \<Longrightarrow> set wi \<subseteq> alphabet l1 \<Longrightarrow> set wo \<subseteq> alphabet l2 \<Longrightarrow>
           TM.computes_word tm wi wo \<Longrightarrow> TM.time_bounded_word tm (\<lambda>n. n^k) wi"
  shows "l1 \<le>\<^sub>p l2"
proof (unfold poly_reducible_def, unfold dtime_reducible_def)
  have "(\<forall>wi\<in>(alphabet l1)*. (\<exists>wo. set wo \<subseteq> alphabet l2 \<and> TM.computes_word tm wi wo) \<and>
         (\<forall>wo\<in>(alphabet l2)*. TM.computes_word tm wi wo \<longrightarrow> (wi \<in>\<^sub>L l1) = (wo \<in>\<^sub>L l2))) \<and>
         (\<exists>l. \<forall>wi\<in>(alphabet l1)*. l \<le> length wi \<longrightarrow> (\<forall>wo\<in>(alphabet l2)*.
         TM.computes_word tm wi wo \<longrightarrow> TM.is_final tm (TM.run tm (length wi ^ k) wi)))"
    apply auto
       apply (erule assms(1))
    using assms(2) apply simp
    using assms(2) apply simp
    apply (rule exI [where x=l])
    apply auto
    using assms(3) unfolding TM.time_bounded_word_def .
  hence 1: "\<exists>tm::(nat, 'a, unit) TM. (\<forall>wi\<in>(alphabet l1)*. (\<exists>wo. set wo \<subseteq> alphabet l2 \<and> TM.computes_word tm wi wo) \<and>
            (\<forall>wo\<in>(alphabet l2)*. TM.computes_word tm wi wo \<longrightarrow> (wi \<in>\<^sub>L l1) = (wo \<in>\<^sub>L l2))) \<and>
            (\<exists>l. \<forall>wi\<in>(alphabet l1)*. l \<le> length wi \<longrightarrow> (\<forall>wo\<in>(alphabet l2)*.
            TM.computes_word tm wi wo \<longrightarrow> TM.is_final tm (TM.run tm (length wi ^ k) wi)))"
    by blast
  show "\<exists>k::nat. \<exists>tm::(nat, 'a, unit) TM. (\<forall>wi\<in>(alphabet l1)*. \<exists>wo\<in>(alphabet l2)*. TM.computes_word tm wi wo \<and>
        (\<forall>wo\<in>(alphabet l2)*. TM.computes_word tm wi wo \<longrightarrow> (wi \<in>\<^sub>L l1) = (wo \<in>\<^sub>L l2))) \<and>
        (\<exists>l. \<forall>wi\<in>(alphabet l1)*. l \<le> length wi \<longrightarrow> (\<forall>wo\<in>(alphabet l2)*.
        TM.computes_word tm wi wo \<longrightarrow> TM.is_final tm (TM.run tm (length wi ^ k) wi)))"
    apply (rule exI [where x=k])
    using 1 by auto blast
qed

definition DTIME_hard :: "'a lang \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> 'a set \<Rightarrow> bool" where
  "DTIME_hard L t a \<equiv> \<forall>l\<in>DTIME t. alphabet l = a \<longrightarrow> l \<le>\<^sub>p L"

lemma DTIME_hardI [intro]: "(\<And>l. l \<in> DTIME t \<Longrightarrow> alphabet l = a \<Longrightarrow> l \<le>\<^sub>p L) \<Longrightarrow>
                    DTIME_hard L t a"
  unfolding DTIME_hard_def by blast

lemma DTIME_hardD [dest]: "DTIME_hard L t a \<Longrightarrow> l \<in> DTIME t \<Longrightarrow>
                           alphabet l = a \<Longrightarrow> l \<le>\<^sub>p L"
  unfolding DTIME_hard_def by blast

lemma add_const_prefix:
  fixes syms :: "'s set" and p :: "'s list"
  assumes syms_finite: "finite syms" and syms_not_empty: "syms \<noteq> {}"
  shows "\<exists>tm::(nat, 's) TM_decider. (\<forall>w\<in>syms*. TM.computes_word tm w (p@w)) \<and>
                         TM.time_bounded tm (\<lambda>_. Suc (length p)) \<and>
                         TM.tape_count tm = 1 \<and> TM.symbols tm = syms \<union> set p"
proof (cases p, rule exI)
  case Nil
  define p_tm0 :: "(nat, 's, bool) TM_record" where
    "p_tm0 \<equiv> TM 1 syms {0} 0 {0} (\<lambda>n. True)
          (\<lambda>state sym. 0)
          (\<lambda>state sym k. sym ! k)
          (\<lambda>state sym k. No_Shift)"
  have valid0: "valid_TM p_tm0"
    by (standard, unfold p_tm0_def, (auto simp add: assms))
  have k_1: "TM.tape_count (Abs_TM p_tm0) = 1"
    using p_tm0_def valid0 valid_tm_tape_count by fastforce
  have "\<And>w. w \<in> syms* \<Longrightarrow> TM.computes_word (Abs_TM p_tm0) w ([] @ w)"
  proof (rule TM.computes_wordI, unfold TM.halts_altdef, rule exI [where x=0])
    fix w :: "'s list"
    have "TM.is_final (Abs_TM p_tm0) (TM.initial_config (Abs_TM p_tm0) w)"
      unfolding p_tm0_def TM.initial_config_def
      using p_tm0_def valid0 valid_tm_final_states valid_tm_initial_state by fastforce
    thus "TM.is_final (Abs_TM p_tm0) (TM.run (Abs_TM p_tm0) 0 w)"
      unfolding TM.run_def by simp
  next
    fix w :: "'s list"
    assume "w \<in> syms*"
    hence "w \<noteq> [] \<Longrightarrow> w ! 0 \<in> syms" by auto
    show "TM.has_output (TM.compute (Abs_TM p_tm0) w) ([] @ w)"
      apply (rule TM.has_outputI) unfolding TM_abbrevs.input_tape_def
    proof auto
      show "last (tapes (TM.compute (Abs_TM p_tm0) [])) = Tape [] None []"
        by (metis TM.compute_altdef TM.final_steps TM.init_conf_last(1)
            TM.init_conf_state TM.run_def TM_abbrevs.input_tape.simps(1) is_finalI
            k_1 p_tm0_def select_convs(4) select_convs(5) singletonI valid0
            valid_tm_final_states valid_tm_initial_state)
    next
      assume "w \<noteq> []"
      thus "last (tapes (TM.compute (Abs_TM p_tm0) w)) =
            Tape [] (Some (hd w)) (map Some (tl w))"
        by (metis TM.compute_altdef TM.final_steps TM.init_conf_last(1)
            TM.init_conf_state TM.run_def TM_abbrevs.input_tape.simps(2) is_finalI k_1
            list.collapse p_tm0_def select_convs(4) select_convs(5) singletonI valid0
            valid_tm_final_states valid_tm_initial_state)
    qed
  qed
  moreover have "\<And>w. TM.time_bounded_word (Abs_TM p_tm0) (\<lambda>_. 0) w"
    apply (rule TM.time_bounded_wordI) unfolding TM.run_def
  proof (standard, auto)
    have "\<And>w. state (TM.initial_config (Abs_TM p_tm0) w) = 0"
      by (metis TM.init_conf_state p_tm0_def select_convs(4) valid0
          valid_tm_initial_state)
    moreover have "TM.TM.final_states (Abs_TM p_tm0) = {0}"
      by (metis p_tm0_def select_convs(5) valid0 valid_tm_final_states)
    ultimately show "\<And>w. state (TM.initial_config (Abs_TM p_tm0) w) \<in>
                     TM.TM.final_states (Abs_TM p_tm0)" by simp
  qed
  hence "\<And>w. TM.time_bounded_word (Abs_TM p_tm0) (\<lambda>_. 1) w"
    using TM.time_bounded_word_mono by blast
  moreover have "TM.symbols (Abs_TM p_tm0) = syms \<union> set p"
    unfolding valid_tm_symbols [OF valid0] unfolding p_tm0_def Nil by simp
  ultimately show "(\<forall>w\<in>syms*. TM.computes_word (Abs_TM p_tm0) w (p @ w)) \<and>
    (\<forall>w. TM.time_bounded_word (Abs_TM p_tm0) (\<lambda>_. Suc (length p)) w) \<and>
    TM.tape_count (Abs_TM p_tm0) = 1 \<and> TM.symbols (Abs_TM p_tm0) = syms \<union> set p"
    using Nil p_tm0_def by (metis One_nat_def k_1 list.size(3))
next
  case (Cons a list)
  define p_tm :: "'s list \<Rightarrow> (nat, 's, bool) TM_record" where
    "\<And>p. p_tm p \<equiv> TM 1 (set p \<union> syms)
          ({0..Suc (Suc (length p * 2))}) 0
          {Suc (length p), Suc (Suc (length p * 2))} (\<lambda>n. True)
          (\<lambda>state sym. if state = 0 \<and> sym ! 0 = None then Suc (Suc (length p)) else
            if state = Suc (length p) \<or> state = Suc (Suc (length p * 2)) then state
            else Suc state)
          (\<lambda>state sym k. if state = 0 then sym ! k else
            if state \<le> (Suc (length p)) then Some (p ! (length p - state)) else
            Some (p ! ((Suc (length p * 2)) - state)))
          (\<lambda>state sym k. if (state = 0 \<and> sym ! k = None) \<or> state = length p \<or>
                         state = Suc (length p * 2) then No_Shift
                         else Shift_Left)"
  have get0: "\<And>a l. (a#l) ! 0 = a" by simp
  have getSub: "\<And>a l n. n < length (a#l) \<Longrightarrow>
                (a#l) ! (length (a#l) - n) = l ! (length l - n)" by simp
  have valid_s: "\<And>s. s \<noteq> [] \<Longrightarrow> valid_TM (p_tm s)"
  proof (standard, unfold p_tm_def, (auto simp add: assms))
    fix s :: "'s list" and q :: nat and hds :: "'s option list"
    assume "s \<noteq> []" and "q \<le> Suc (Suc (length s * 2))" and "length hds = Suc 0"
    and "set hds \<subseteq> options (set s \<union> syms)" and q_not_le_sucls: "\<not> q \<le> Suc (length s)"
    and "s ! (Suc (length s * 2) - q) \<notin> syms"
    hence "(Suc (length s * 2)) - (Suc (Suc (length s))) < length s" by simp
    hence "(Suc (length s * 2)) - q < length s" using q_not_le_sucls by simp
    thus "s ! (Suc (length s * 2) - q) \<in> set s" by simp
  qed
  hence p_valid: "valid_TM (p_tm p)" using local.Cons by blast
  have states_mono_s: "\<And>p s hds. p \<noteq> [] \<Longrightarrow> TM.next_state (Abs_TM (p_tm p)) s hds \<ge> s"
    using p_tm_def valid_s valid_tm_next_state by fastforce
  hence states_mono: "\<And>s hds. TM.next_state (Abs_TM (p_tm p)) s hds \<ge> s"
    using Cons by blast
  have states_strict_mono: "\<And>s hds. s \<notin> TM.F (Abs_TM (p_tm p)) \<Longrightarrow>
                            TM.next_state (Abs_TM (p_tm p)) s hds > s"
    using less_Suc_eq_0_disj n_not_Suc_n p_tm_def select_convs(5) select_convs(7)
      states_mono p_valid valid_tm_final_states valid_tm_next_state by fastforce
  have initial_config_state: "\<And>w. state (TM.initial_config (Abs_TM (p_tm p)) w) = 0"
    by (smt (verit) TM.init_conf_state p_tm_def select_convs(4) p_valid
        valid_tm_initial_state)
  hence p_initial_state: "TM.initial_state (Abs_TM (p_tm p)) = 0"
    by (simp add: TM.init_conf_state)
  have initial_state_s: "\<And>p. p \<noteq> [] \<Longrightarrow> TM.initial_state (Abs_TM (p_tm p)) = 0"
    using p_tm_def valid_s valid_tm_initial_state by fastforce
  have p_final_states: "TM.final_states (Abs_TM (p_tm p)) =
                        {Suc (length p), Suc (Suc (length p * 2))}"
    using p_tm_def p_valid valid_tm_final_states by force
  have state_step_f_s: "\<And>p c. p \<noteq> [] \<Longrightarrow> state c \<notin> TM.F (Abs_TM (p_tm p)) \<Longrightarrow>
        state c \<noteq> TM.initial_state (Abs_TM (p_tm p)) \<Longrightarrow>
        state (TM.step (Abs_TM (p_tm p)) c) = Suc (state c)"
    by (smt (verit, best) TM.step_def TM.step_not_final_simps(1) insertCI p_tm_def
        select_convs(4) select_convs(5) select_convs(7) valid_s valid_tm_final_states
        valid_tm_initial_state valid_tm_next_state)
  hence state_step_s: "\<And>p c. p \<noteq> [] \<Longrightarrow> state c \<noteq> 0 \<Longrightarrow> state c \<noteq> Suc (length p) \<Longrightarrow>
              state c \<noteq> Suc (Suc (length p * 2)) \<Longrightarrow>
         state (TM.step (Abs_TM (p_tm p)) c) = Suc (state c)" unfolding p_initial_state
    p_final_states
    by (metis (no_types, lifting) insert_iff p_tm_def select_convs(4) select_convs(5)
        singletonD valid_s valid_tm_final_states valid_tm_initial_state)
  hence p_state_step: "\<And>c. state c \<noteq> 0 \<Longrightarrow> state c \<noteq> Suc (length p) \<Longrightarrow>
              state c \<noteq> Suc (Suc (length p * 2)) \<Longrightarrow>
         state (TM.step (Abs_TM (p_tm p)) c) = Suc (state c)" using local.Cons by blast
  have state_step_s2: "\<And>p c. p \<noteq> [] \<Longrightarrow> heads c ! 0 \<noteq> None \<Longrightarrow>
                       state c \<noteq> Suc (length p) \<Longrightarrow>
                       state c \<noteq> Suc (Suc (length p * 2)) \<Longrightarrow>
                       state (TM.step (Abs_TM (p_tm p)) c) = Suc (state c)"
    by (smt (verit, ccfv_threshold) TM.step_def TM.step_not_final_simps(1) empty_iff
        insert_iff p_tm_def select_convs(5) select_convs(7) valid_s
        valid_tm_final_states valid_tm_next_state)
  have state_steps_empty_s: "\<And>p c n. p \<noteq> [] \<Longrightarrow> state c > Suc (length p) \<Longrightarrow>
                             state c + n < Suc (Suc (length p * 2)) \<Longrightarrow>
                             state ((TM.step (Abs_TM (p_tm p)) ^^ n) c) = state c + n"
  proof -
    fix n :: nat
    show "\<And>p c.
       p \<noteq> [] \<Longrightarrow>
       Suc (length p) < state c \<Longrightarrow>
       state c + n < Suc (Suc (length p * 2)) \<Longrightarrow>
       state ((TM.step (Abs_TM (p_tm p)) ^^ n) c) = state c + n"
      apply (induction n)
    proof auto
      fix n :: nat and p :: "'s list" and c :: "(nat, 's) TM_config"
      assume step_n_IH: "\<And>p c. p \<noteq> [] \<Longrightarrow>
               Suc (length p) < state c \<Longrightarrow>
               state c + n < Suc (Suc (length p * 2)) \<Longrightarrow>
               state ((TM.step (Abs_TM (p_tm p)) ^^ n) c) = state c + n" and
             p_not_empty: "p \<noteq> []" and suc_lp_c: "Suc (length p) < state c" and
             state_c_n_IS: "state c + n < Suc (length p * 2)"
      have "state ((TM.step (Abs_TM (p_tm p)) ^^ n) c) = state c + n"
        using step_n_IH [OF p_not_empty suc_lp_c] state_c_n_IS by simp
      thus "state (TM.step (Abs_TM (p_tm p)) ((TM.step (Abs_TM (p_tm p)) ^^ n) c)) =
            Suc (state c + n)"
        using p_not_empty state_c_n_IS state_step_s suc_lp_c by auto
    qed
  qed
  have state_steps_mono_s: "\<And>p c n. p \<noteq> [] \<Longrightarrow>
         state ((TM.step (Abs_TM (p_tm p)) ^^ n) c) \<ge> state c"
  proof -
    fix n::nat
    show "\<And>p c. p \<noteq> [] \<Longrightarrow> state c \<le> state ((TM.step (Abs_TM (p_tm p)) ^^ n) c)"
      apply (induction n) apply auto
      by (metis TM.step_def bot_nat_0.extremum_uniqueI initial_state_s nat_le_linear
          not_less_eq_eq state_step_f_s)
  qed
  have tape_count_1: "\<And>p. p \<noteq> [] \<Longrightarrow> TM.TM.tape_count (Abs_TM (p_tm p)) = 1"
    using p_tm_def valid_s valid_tm_tape_count by fastforce
  have state0_step_empty_s: "\<And>p c. p \<noteq> [] \<Longrightarrow>
                     state c = TM.initial_state (Abs_TM (p_tm p)) \<Longrightarrow>
                     heads c = [None] \<Longrightarrow>
                     state (TM.step (Abs_TM (p_tm p)) c) = Suc (Suc (length p))"
    unfolding TM.step_def apply auto
     apply (metis (no_types, lifting) insert_iff nat.simps(3) p_tm_def select_convs(4)
        select_convs(5) singletonD valid_s valid_tm_final_states valid_tm_initial_state)
    using p_tm_def valid_s valid_tm_initial_state valid_tm_next_state by fastforce
  hence state0_step_empty: "\<And>c. state c = TM.initial_state (Abs_TM (p_tm p)) \<Longrightarrow>
                     heads c = [None] \<Longrightarrow>
                     state (TM.step (Abs_TM (p_tm p)) c) = Suc (Suc (length p))"
    using Cons by simp
  have state0_step_non_empty: "\<And>p c. p \<noteq> [] \<Longrightarrow>
                     state c = TM.initial_state (Abs_TM (p_tm p)) \<Longrightarrow>
                     \<exists>s. heads c = [Some s] \<Longrightarrow>
                     state (TM.step (Abs_TM (p_tm p)) c) = Suc (state c)"
    unfolding TM.step_def apply auto
     apply (metis (no_types, lifting) insert_iff nat.simps(3) p_tm_def select_convs(4)
        select_convs(5) singletonD valid_s valid_tm_final_states valid_tm_initial_state)
    unfolding p_initial_state using p_tm_def valid_s valid_tm_next_state
      initial_state_s by fastforce
  hence state0_step_non_empty: "\<And>c. state c = TM.initial_state (Abs_TM (p_tm p)) \<Longrightarrow>
                     \<exists>s. heads c = [Some s] \<Longrightarrow>
                     state (TM.step (Abs_TM (p_tm p)) c) = Suc (state c)"
    using Cons by simp
  have initial_state_not_final_s: "\<And>p. p \<noteq> [] \<Longrightarrow>
        TM.initial_state (Abs_TM (p_tm p)) \<notin> TM.final_states (Abs_TM (p_tm p))"
    by (metis (no_types, lifting) initial_state_s insert_iff nat.simps(3) p_tm_def
        select_convs(5) singletonD valid_s valid_tm_final_states)
  have steps_non0_plus_le_s: "\<And>p c n. p \<noteq> [] \<Longrightarrow> state c \<noteq> 0 \<Longrightarrow>
              state ((TM.step (Abs_TM (p_tm p)) ^^ n) c) \<le> n + (state c)"
  proof -
    fix n :: nat
    show "\<And>p c. p \<noteq> [] \<Longrightarrow> state c \<noteq> 0 \<Longrightarrow>
          state ((TM.step (Abs_TM (p_tm p)) ^^ n) c) \<le> n + (state c)"
      apply (induction n) apply auto
      by (metis TM.step_def add_le_cancel_left initial_state_s leD le_SucI plus_1_eq_Suc
          state_step_f_s state_steps_mono_s)
  qed
  have steps_non_empty_plus_le_s: "\<And>p n w. p \<noteq> [] \<Longrightarrow> w \<noteq> [] \<Longrightarrow>
              state ((TM.step (Abs_TM (p_tm p)) ^^ n)
              (TM.initial_config (Abs_TM (p_tm p)) w)) \<le> n"
  proof -
    fix n :: nat
    show "\<And>p w. p \<noteq> [] \<Longrightarrow> w \<noteq> [] \<Longrightarrow>
       state ((TM.step (Abs_TM (p_tm p)) ^^ n) (TM.initial_config (Abs_TM (p_tm p)) w))
       \<le> n" apply (induction n)
      apply auto
       apply (simp add: TM.init_conf_state initial_state_s)
    proof -
      fix n :: nat and p w :: "'s list"
      assume steps_IH: "\<And>p w. p \<noteq> [] \<Longrightarrow> w \<noteq> [] \<Longrightarrow>
               state ((TM.step (Abs_TM (p_tm p)) ^^ n)
               (TM.initial_config (Abs_TM (p_tm p)) w)) \<le> n" and "p \<noteq> []" and
             "w \<noteq> []"
      have finals: "TM.final_states (Abs_TM (p_tm p)) =
                    {Suc (length p), Suc (Suc (length p * 2))}"
        by (metis (no_types, lifting) \<open>p \<noteq> []\<close> p_tm_def select_convs(5) valid_s
            valid_tm_final_states)
      have initial: "state (TM.initial_config (Abs_TM (p_tm p)) w) = 0"
        by (simp add: TM.init_conf_state \<open>p \<noteq> []\<close> initial_state_s)
      have heads0: "n = 0 \<Longrightarrow> heads ((TM.step (Abs_TM (p_tm p)) ^^ n)
            (TM.initial_config (Abs_TM (p_tm p)) w)) \<noteq> [None]"
        by (metis TM.initial_config_heads_0 \<open>w \<noteq> []\<close> funpow_0 not_None_eq nth_Cons_0)
      have "state ((TM.step (Abs_TM (p_tm p)) ^^ n)
            (TM.initial_config (Abs_TM (p_tm p)) w)) \<in>
            TM.final_states (Abs_TM (p_tm p)) \<Longrightarrow> state (TM.step (Abs_TM (p_tm p))
            ((TM.step (Abs_TM (p_tm p)) ^^ n) (TM.initial_config (Abs_TM (p_tm p)) w)))
            \<le> n" by (simp add: \<open>p \<noteq> []\<close> \<open>w \<noteq> []\<close> is_finalI steps_IH)
        moreover have "state ((TM.step (Abs_TM (p_tm p)) ^^ n)
            (TM.initial_config (Abs_TM (p_tm p)) w)) \<notin>
            TM.final_states (Abs_TM (p_tm p)) \<Longrightarrow> state (TM.step (Abs_TM (p_tm p))
            ((TM.step (Abs_TM (p_tm p)) ^^ n) (TM.initial_config (Abs_TM (p_tm p)) w)))
            \<le> Suc n" apply (subst (1) TM.step_def) unfolding finals apply auto
          apply (cases n) apply auto unfolding initial apply auto
           apply (smt (verit, best) Orderings.order_eq_iff TM.initial_config_heads_0
              \<open>p \<noteq> []\<close> \<open>w \<noteq> []\<close> nat.simps(3) option.distinct(1) p_tm_def
              select_convs(7) valid_s valid_tm_next_state)
          by (smt (z3) TM.step_def TM.step_not_final_simps(1) \<open>p \<noteq> []\<close> p_tm_def
              \<open>w \<noteq> []\<close> funpow.simps(2) initial_state_not_final_s initial_state_s
              less_Suc_eq_0_disj less_Suc_eq_le o_apply old.nat.distinct(1)
              select_convs(7) steps_IH valid_s valid_tm_next_state)
      ultimately show "state (TM.step (Abs_TM (p_tm p))
            ((TM.step (Abs_TM (p_tm p)) ^^ n) (TM.initial_config (Abs_TM (p_tm p)) w)))
            \<le> Suc n" by linarith
    qed
  qed
  have steps_non_empty_plus_eq_s: "\<And>p n w. p \<noteq> [] \<Longrightarrow> w \<noteq> [] \<Longrightarrow> n \<le> Suc (length p)
              \<Longrightarrow> state ((TM.step (Abs_TM (p_tm p)) ^^ n)
              (TM.initial_config (Abs_TM (p_tm p)) w)) = n"
  proof -
    fix p w :: "'s list" and n :: nat
    show "p \<noteq> [] \<Longrightarrow> w \<noteq> [] \<Longrightarrow> n \<le> Suc (length p) \<Longrightarrow>
       state ((TM.step (Abs_TM (p_tm p)) ^^ n) (TM.initial_config (Abs_TM (p_tm p)) w))
       = n" apply (induction n) apply auto
       apply (simp add: TM.init_conf_state initial_state_s)
      using state_step_s2
      by (smt (verit, ccfv_SIG) TM.initial_config_heads_0 add.commute
          add_cancel_right_right add_le_cancel_left bot_nat_0.extremum_uniqueI funpow_0
          le_Suc_eq less_Suc_eq_le mult_2_right nat_less_le option.distinct(1)
          state_step_s)
  qed
  have state_0_iff: "\<And>s n w. s \<noteq> [] \<Longrightarrow>
                     n = 0 \<longleftrightarrow> state ((TM.step (Abs_TM (p_tm s)) ^^ n)
                     (TM.initial_config (Abs_TM (p_tm s)) w)) = 0"
     apply (auto simp add: TM.init_conf_state initial_state_s)
  proof -
    fix s w :: "'s list" and n :: nat
    assume s_not_empty: "s \<noteq> []" and
  state_0: "state ((TM.step (Abs_TM (p_tm s)) ^^ n)
            (TM.initial_config (Abs_TM (p_tm s)) w)) = 0"
    have init_state: "state (TM.initial_config (Abs_TM (p_tm s)) w) = 0"
      by (simp add: TM.init_conf_state \<open>s \<noteq> []\<close> initial_state_s)
    have "w \<noteq> [] \<Longrightarrow> state ((TM.step (Abs_TM (p_tm s)) ^^ 1)
          (TM.initial_config (Abs_TM (p_tm s)) w)) = 1"
      apply auto unfolding TM.step_def apply auto
       apply (simp add: TM.init_conf_state \<open>s \<noteq> []\<close> initial_state_not_final_s)
      unfolding init_state
      by (smt (verit, ccfv_SIG) TM.initial_config_heads_0 \<open>s \<noteq> []\<close> nat.simps(3)
          option.distinct(1) p_tm_def select_convs(7) valid_s valid_tm_next_state)
    moreover have "w = [] \<Longrightarrow> state ((TM.step (Abs_TM (p_tm s)) ^^ 1)
          (TM.initial_config (Abs_TM (p_tm s)) w)) = Suc (Suc (length s))"
    proof -
      assume "w = []"
      hence "heads (TM.initial_config (Abs_TM (p_tm s)) w) = [None]"
        by (simp add: TM.one_tape_initial_config TM_abbrevs.input_tape.simps(1)
            s_not_empty tape_count_1)
      thus "state ((TM.step (Abs_TM (p_tm s)) ^^ 1)
          (TM.initial_config (Abs_TM (p_tm s)) w)) = Suc (Suc (length s))"
        by (simp add: TM.init_conf_state s_not_empty state0_step_empty_s)
    qed
    moreover have "\<And>n1 n2. n1 \<ge> n2 \<Longrightarrow> state ((TM.step (Abs_TM (p_tm s)) ^^ n1)
          (TM.initial_config (Abs_TM (p_tm s)) w)) \<ge>
          state ((TM.step (Abs_TM (p_tm s)) ^^ n2)
          (TM.initial_config (Abs_TM (p_tm s)) w))"
      by (metis TM.steps_plus less_eqE s_not_empty state_steps_mono_s)
    ultimately show "n = 0" using s_not_empty state_0
      by (metis One_nat_def bot_nat_0.extremum le_antisym not_less_eq_eq)
  qed
  have next_write_s: "\<And>s st hds k. s \<noteq> [] \<Longrightarrow>
                      TM.next_write (Abs_TM (p_tm s)) st hds k =
                      (if st = 0 then hds ! k else
            if st \<le> (Suc (length s)) then Some (s ! (length s - st)) else
            Some (s ! ((Suc (length s * 2)) - st)))" unfolding p_tm_def
    using valid_s by (simp add: p_tm_def valid_tm_next_write)
  have no_shift_right_s: "\<And>s st hds k. s \<noteq> [] \<Longrightarrow>
                          TM.next_move (Abs_TM (p_tm s)) st hds k \<noteq> Shift_Right"
    by (smt (verit) head_move.simps(1) head_move.simps(6) p_tm_def select_convs(9)
        valid_s valid_tm_next_move)
  have shift_left_before_end_s: "\<And>s hds k. length s > 1 \<Longrightarrow>
                                 TM.next_move (Abs_TM (p_tm s)) (length s * 2) hds k =
                                 Shift_Left"
    by (smt (verit, ccfv_threshold) Suc_1 length_0_conv less_imp_le_nat mult_is_0
        mult_numeral_1_right n_not_Suc_n nat.simps(3) nat_mult_eq_cancel_disj
        not_one_le_zero numeral_eq_iff p_tm_def select_convs(9) semiring_norm(85)
        valid_s valid_tm_next_move)
  have tb: "\<And>p w. p \<noteq> [] \<Longrightarrow>
            TM.time_bounded_word (Abs_TM (p_tm p)) (\<lambda>_. Suc (length p)) w"
    apply (rule TM.time_bounded_wordI) unfolding TM.run_def
  proof
    fix p w :: "'s list"
    assume "p \<noteq> []"
    hence valid: "valid_TM (p_tm p)" using local.Cons valid_s by blast
    have p_final_states: "\<And>s. s \<in> TM.TM.final_states (Abs_TM (p_tm p)) \<longleftrightarrow>
              s = Suc (length p) \<or> s = Suc (Suc (length p * 2))"
      using p_tm_def valid valid_tm_final_states by force
    have "w = [] \<Longrightarrow> state
          ((TM.step (Abs_TM (p_tm p)) ^^ Suc (length p))
            (TM.initial_config (Abs_TM (p_tm p)) w)) = Suc (Suc (length p * 2))"
    proof auto
      have empty_init_conf: "heads (TM.initial_config (Abs_TM (p_tm p)) []) = [None]"
        by (metis (no_types, lifting) TM.one_tape_initial_config
            TM_abbrevs.input_tape.simps(1) TM_config.sel(2) list.simps(8)
            list.simps(9) p_tm_def select_convs(1) tape.sel(2) valid
            valid_tm_tape_count)
      have "state (TM.step (Abs_TM (p_tm p)) (TM.initial_config (Abs_TM (p_tm p)) [])) =
            Suc (Suc (length p))" unfolding TM.step_def apply auto
         apply (metis (no_types, lifting) TM.init_conf_state nat.simps(3)
            p_final_states p_tm_def select_convs(4) valid valid_tm_initial_state)
        unfolding initial_config_state empty_init_conf
        using p_tm_def valid valid_tm_next_state
        by (smt (verit) TM.init_conf_state get0 select_convs(4) select_convs(7)
            valid_tm_initial_state)
      moreover have "\<And>n. n \<le> length p \<Longrightarrow> state ((TM.step (Abs_TM (p_tm p)) ^^ n)
         (TM.step (Abs_TM (p_tm p)) (TM.initial_config (Abs_TM (p_tm p)) []))) =
          Suc (Suc (length p)) + n"
      proof -
        fix n :: nat
        show "n \<le> length p \<Longrightarrow> state ((TM.step (Abs_TM (p_tm p)) ^^ n)
            (TM.step (Abs_TM (p_tm p)) (TM.initial_config (Abs_TM (p_tm p)) []))) =
          Suc (Suc (length p)) + n"
        proof (induct n)
          case 0
          then show ?case apply auto by (rule calculation)
        next
          case IH: (Suc n)
          hence "n \<le> length p" by simp
          hence refined_IH: "state ((TM.step (Abs_TM (p_tm p)) ^^ n)
              (TM.step (Abs_TM (p_tm p)) (TM.initial_config (Abs_TM (p_tm p)) []))) =
              Suc (Suc (length p)) + n" using IH by simp
          have "Suc (Suc (length p)) + n \<notin> TM.final_states (Abs_TM (p_tm p))"
            using IH.prems p_final_states by auto
          then show ?case using refined_IH
            by (simp add: \<open>p \<noteq> []\<close> p_final_states state_step_s)
        qed
      qed
      ultimately have "state ((TM.step (Abs_TM (p_tm p)) ^^ length p)
         (TM.step (Abs_TM (p_tm p)) (TM.initial_config (Abs_TM (p_tm p)) []))) =
          Suc (Suc (length p * 2))" by simp
      thus "state (TM.step (Abs_TM (p_tm p)) ((TM.step (Abs_TM (p_tm p)) ^^ length p)
         (TM.initial_config (Abs_TM (p_tm p)) []))) = Suc (Suc (length p * 2))"
        by (simp add: funpow_swap1)
    qed
    moreover have "w \<noteq> [] \<Longrightarrow> state
          ((TM.step (Abs_TM (p_tm p)) ^^ Suc (length p))
            (TM.initial_config (Abs_TM (p_tm p)) w)) = Suc (length p)"
    proof auto
      assume "w \<noteq> []"
      hence heads_init_conf_some: "\<exists>s. heads (TM.initial_config (Abs_TM (p_tm p)) w) =
                                   [Some s]"
        by (smt (verit, best) TM.initial_config_heads_0 TM.one_tape_initial_config
            TM_config.sel(2) get0 list.map_disc_iff list.simps(9) p_tm_def
            select_convs(1) valid valid_tm_tape_count)
      hence w_step: "state (TM.step (Abs_TM (p_tm p))
              (TM.initial_config (Abs_TM (p_tm p)) w)) = 1"
        by (smt (verit) One_nat_def TM.init_conf_state TM.step_def
            TM.step_not_final_simps(1) \<open>p \<noteq> []\<close> get0 initial_state_s nat.simps(3)
            option.distinct(1) p_final_states p_tm_def select_convs(7) valid
            valid_tm_next_state)
      moreover have "\<And>n. n \<le> length p \<Longrightarrow> state ((TM.step (Abs_TM (p_tm p)) ^^ n)
         (TM.step (Abs_TM (p_tm p)) (TM.initial_config (Abs_TM (p_tm p)) w))) =
         1 + n"
      proof -
        fix n::nat
        show "n \<le> length p \<Longrightarrow> state ((TM.step (Abs_TM (p_tm p)) ^^ n)
         (TM.step (Abs_TM (p_tm p)) (TM.initial_config (Abs_TM (p_tm p)) w))) =
         1 + n"
        proof (induct n)
          case 0
          then show ?case using w_step by simp
        next
          case (Suc n)
          hence "n \<le> length p" by simp
          hence "state
           ((TM.step (Abs_TM (p_tm p)) ^^ n)
             (TM.step (Abs_TM (p_tm p)) (TM.initial_config (Abs_TM (p_tm p)) w))) =
          1 + n" using Suc by simp
          then show ?case using Suc.prems state_step_s \<open>p \<noteq> []\<close> by auto
        qed
      qed
      ultimately show "w \<noteq> [] \<Longrightarrow> state (TM.step (Abs_TM (p_tm p))
      ((TM.step (Abs_TM (p_tm p)) ^^ length p)
      (TM.initial_config (Abs_TM (p_tm p)) w))) = Suc (length p)"
        by (simp add: funpow_swap1)
    qed
    ultimately show "state
          ((TM.step (Abs_TM (p_tm p)) ^^ Suc (length p))
            (TM.initial_config (Abs_TM (p_tm p)) w))
         \<in> TM.TM.final_states (Abs_TM (p_tm p))" unfolding p_final_states by auto
  qed
  moreover have cw: "\<And>w. w \<in> syms* \<Longrightarrow> TM.computes_word (Abs_TM (p_tm p)) w (p @ w)"
  proof (rule TM.computes_wordI)
    show "\<And>w. w \<in> syms* \<Longrightarrow> TM.halts (Abs_TM (p_tm p)) w"
      using tb TM.time_bounded_altdef2 Cons by blast
  next
    fix w :: "'s list"
    assume "w \<in> syms*"
    hence w_in_syms: "set w \<subseteq> syms" by simp
    have halts: "\<And>p w. p \<noteq> [] \<Longrightarrow> TM.halts (Abs_TM (p_tm p)) w" using tb
      by (meson TM.time_bounded_altdef2)
    show "TM.has_output (TM.compute (Abs_TM (p_tm p)) w) (p @ w)"
      apply (rule TM.has_outputI)
    proof (cases w)
      case Nil
      then show "last (tapes (TM.compute (Abs_TM (p_tm p)) w)) =
                 TM_abbrevs.input_tape (p @ w)"
        apply auto
      proof (induct p rule: list_length_induct' [of 1], (simp_all add: local.Cons))
        fix l::"'s list"
        assume "length l = Suc 0"
        then obtain x::'s where x_def: "l = [x]" by (metis length_1_ex_iff)
        have final_states_x: "TM.TM.final_states (Abs_TM (p_tm [x])) = {2, 4}"
            by (smt (verit, del_insts) One_nat_def \<open>length l = Suc 0\<close> add.commute
                add_Suc_right list.distinct(1) mult.right_neutral mult_Suc_right
                num_double numeral_2_eq_2 numeral_times_numeral p_tm_def select_convs(5)
                valid_s valid_tm_final_states x_def)
        have tape_count_x: "TM.TM.tape_count (Abs_TM (p_tm [x])) = 1"
          by (metis (no_types, lifting) list.distinct(1) p_tm_def select_convs(1)
              valid_s valid_tm_tape_count)
        have state_0: "state (TM.initial_config (Abs_TM (p_tm [x])) []) = 0"
          by (metis (no_types, lifting) TM.init_conf_state list.distinct(1)
              p_tm_def select_convs(4) valid_s valid_tm_initial_state)
        have tapes_0: "tapes (TM.initial_config (Abs_TM (p_tm [x])) []) =
                       [Tape [] None []]"
          by (metis (no_types, lifting) TM.one_tape_initial_config
              TM_abbrevs.input_tape.simps(1) TM_config.sel(2) list.distinct(1) p_tm_def
              select_convs(1) valid_s valid_tm_tape_count)
        have state_3: "state (TM.step (Abs_TM (p_tm [x]))
              (TM.initial_config (Abs_TM (p_tm [x])) [])) = 3"
          unfolding TM.step_def state_0
        proof auto
          assume "0 \<in> TM.TM.final_states (Abs_TM (p_tm [x]))"
          moreover have "TM.TM.final_states (Abs_TM (p_tm [x])) = {2, 4}"
            by (rule final_states_x)
          ultimately have "False" by simp
          thus "state (TM.initial_config (Abs_TM (p_tm [x])) []) = 3" ..
        next
          assume "0 \<notin> TM.TM.final_states (Abs_TM (p_tm [x]))"
          thus "TM.TM.next_state (Abs_TM (p_tm [x]))
                (state (TM.initial_config (Abs_TM (p_tm [x])) []))
                (heads (TM.initial_config (Abs_TM (p_tm [x])) [])) = 3"
            unfolding state_0 tapes_0 head_def apply simp
            by (smt (verit, ccfv_SIG) p_tm_def length_1_ex_iff list.discI nth_Cons_0
                numeral_3_eq_3 select_convs(7) valid_s valid_tm_next_state)
        qed
        have next_no_shift: "TM.TM.next_move (Abs_TM (p_tm [x])) 0 [None] 0 = No_Shift"
            by (smt (verit) get0 list.distinct(1) p_tm_def select_convs(9) valid_s
                valid_tm_next_move)
          have next_write_x: "TM.TM.next_write (Abs_TM (p_tm [x])) 0 [None] 0 = None"
            by (smt (verit) p_tm_def get0 list.distinct(1) select_convs(8) valid_s
                valid_tm_next_write)
        have tapes_3: "tapes (TM.step (Abs_TM (p_tm [x]))
              (TM.initial_config (Abs_TM (p_tm [x])) [])) = [Tape [] None []]"
          unfolding TM.step_def apply auto
          unfolding state_0 final_states_x tapes_0 TM.next_actions_def
           TM.next_writes_def TM.next_moves_def tape_count_x TM_abbrevs.tape_action_def
           apply auto unfolding next_no_shift next_write_x
            by (simp add: TM_abbrevs.tape_shift.simps(5) TM_abbrevs.tape_write_simps)
        have next_state_3:  "TM.TM.next_state (Abs_TM (p_tm [x])) 0 [None] = 3"
          by (smt (verit, ccfv_threshold) p_tm_def length_1_ex_iff list.discI
              nth_Cons_0 numeral_3_eq_3 select_convs(7) valid_s valid_tm_next_state)
        have tape_write_0: "TM_abbrevs.tape_write None (Tape [] None []) =
                            Tape [] None []"
            by (simp add: TM_abbrevs.tape_write_simps)
          have tape_shift_0: "\<And>t. TM_abbrevs.tape_shift No_Shift t = t"
            by (simp add: TM_abbrevs.tape_shift.simps(5))
        have state_4: "state ((TM.step (Abs_TM (p_tm [x])) ^^ (Suc 1))
              (TM.initial_config (Abs_TM (p_tm [x])) [])) = 4" apply auto
          unfolding TM.step_def apply auto
          unfolding state_0 tapes_0 final_states_x apply (auto simp add: next_state_3)
          unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_writes_def
            TM.next_moves_def tape_count_x apply auto
          unfolding next_no_shift next_write_x tape_write_0 tape_shift_0 apply auto
            by (smt (verit, del_insts) One_nat_def Suc_1 Suc_eq_plus1 \<open>length l = Suc 0\<close>
                add_Suc_right list.distinct(1) mult.right_neutral mult_Suc_right
                numeral_3_eq_3 numeral_Bit0 p_tm_def select_convs(7) valid_s
                valid_tm_next_state x_def zero_neq_numeral)
        have tapes_4: "tapes ((TM.step (Abs_TM (p_tm [x])) ^^ 2)
              (TM.initial_config (Abs_TM (p_tm [x])) [])) = [Tape [] (Some x) []]"
          unfolding TM.step_def numeral_2_eq_2 apply auto
          unfolding state_0 tapes_0 final_states_x apply auto
          unfolding next_state_3 apply auto
          unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_writes_def
          tape_count_x TM.next_moves_def apply auto
          unfolding next_no_shift next_write_x tape_write_0 tape_shift_0 apply auto
        proof -
          have next_move: "TM.TM.next_move (Abs_TM (p_tm [x])) 3 [None] 0 = No_Shift"
            by (smt (verit, del_insts) One_nat_def Suc_1 \<open>length l = Suc 0\<close>
                list.distinct(1) mult_1 numeral_3_eq_3 p_tm_def select_convs(9) valid_s
                valid_tm_next_move x_def)
          have next_write: "TM.TM.next_write (Abs_TM (p_tm [x])) 3 [None] 0 = Some x"
            by (smt (verit, del_insts) Suc3_eq_add_3 Suc_1 Suc_n_not_le_n
                \<open>length l = Suc 0\<close> add_Suc_shift add_diff_cancel_left' get0
                list.distinct(1) mult_Suc mult_is_0 numeral_3_eq_3 p_tm_def
                plus_1_eq_Suc select_convs(8) valid_s valid_tm_next_write x_def
                zero_neq_numeral)
          show "TM_abbrevs.tape_shift (TM.TM.next_move (Abs_TM (p_tm [x])) 3 [None] 0)
     (TM_abbrevs.tape_write (TM.TM.next_write (Abs_TM (p_tm [x])) 3 [None] 0)
       (Tape [] None [])) = Tape [] (Some x) []" unfolding next_move next_write
            by (simp add: TM_abbrevs.tape_write_simps tape_shift_0)
        qed
        have final_state_x_4: "4 \<in> TM.final_states (Abs_TM (p_tm [x]))"
          by (simp add: final_states_x)
        have "tapes (TM.compute (Abs_TM (p_tm l)) []) = [TM_abbrevs.input_tape l]"
          unfolding x_def TM.compute_def TM.compute_config_def TM.initial_config_def
            tape_count_x TM_abbrevs.input_tape_def
        proof auto
          have init_state: "TM.TM.initial_state (Abs_TM (p_tm [x])) = 0"
            by (metis TM.init_conf_state state_0)
          have least_steps: "(LEAST n.
           TM.is_final (Abs_TM (p_tm [x]))
            ((TM.step (Abs_TM (p_tm [x])) ^^ n) (TM_config 0 [Tape [] None []]))) =
             2"
          proof -
            have "\<not>TM.is_final (Abs_TM (p_tm [x]))
            ((TM.step (Abs_TM (p_tm [x])) ^^ 0) (TM_config 0 [Tape [] None []]))"
              by (metis TM.step_final TM_config.collapse funpow_0 state_0 state_3
                  tapes_0 zero_neq_numeral)
            moreover have "\<not>TM.is_final (Abs_TM (p_tm [x]))
            ((TM.step (Abs_TM (p_tm [x])) ^^ 1) (TM_config 0 [Tape [] None []]))"
              apply auto
              by (metis One_nat_def Suc_1 TM_config.collapse add_Suc_shift
                  final_states_x insertE is_finalD n_not_Suc_n numeral_3_eq_3
                  numeral_Bit0 plus_1_eq_Suc singletonD state_0 state_3 tapes_0)
            ultimately have "\<And>n. n \<le> 1 \<Longrightarrow> \<not>TM.is_final (Abs_TM (p_tm [x]))
            ((TM.step (Abs_TM (p_tm [x])) ^^ n) (TM_config 0 [Tape [] None []]))"
              using TM.final_mono by blast
            moreover have "TM.is_final (Abs_TM (p_tm [x]))
            ((TM.step (Abs_TM (p_tm [x])) ^^ 2) (TM_config 0 [Tape [] None []]))"
              by (metis Suc_1 TM_config.collapse final_state_x_4 is_finalI state_0
                  state_4 tapes_0)
            ultimately show "(LEAST n. TM.is_final (Abs_TM (p_tm [x]))
         ((TM.step (Abs_TM (p_tm [x])) ^^ n) (TM_config 0 [Tape [] None []]))) = 2"
              by (metis Least_le Suc_1 TM.config_time_def TM.steps_conf_time le_Suc_eq)
          qed
          show "tapes ((TM.step (Abs_TM (p_tm [x])) ^^ (LEAST n.
           TM.is_final (Abs_TM (p_tm [x]))
            ((TM.step (Abs_TM (p_tm [x])) ^^ n)
              (TM_config (TM.TM.initial_state (Abs_TM (p_tm [x]))) [Tape [] None []]))))
       (TM_config (TM.TM.initial_state (Abs_TM (p_tm [x]))) [Tape [] None []])) =
    [Tape [] (Some x) []]" unfolding init_state least_steps 
            using tapes_4 unfolding numeral_2_eq_2
            by (metis TM_config.collapse state_0 tapes_0)
        qed
        thus "last (tapes (TM.compute (Abs_TM (p_tm l)) [])) =
                   TM_abbrevs.input_tape l" by simp
      next
        fix a::'s and l::"'s list"
        assume last_IH: "last (tapes (TM.compute (Abs_TM (p_tm l)) [])) =
                TM_abbrevs.input_tape l" and "l \<noteq> []"
        hence "length l \<ge> Suc 0" by simp
        hence "tapes (TM.compute (Abs_TM (p_tm l)) []) = [TM_abbrevs.input_tape l]"
          using tape_count_1 length_1_ex_iff last_IH
          by (metis One_nat_def Orderings.order_eq_iff TM.compute_altdef TM.run_def
              TM.run_tapes_len last_ConsL less_Suc_eq list.size(3) not_le_imp_less
              order_less_imp_not_less)
        also have "... = [Tape [] (Some (hd l)) (map Some (tl l))]"
          unfolding TM_abbrevs.input_tape_def using \<open>Suc 0 \<le> length l\<close> by auto
        finally have tapes_l: "tapes (TM.compute (Abs_TM (p_tm l)) []) =
                      [Tape [] (Some (hd l)) (map Some (tl l))]" .
        have p_tm_l_valid: "valid_TM (p_tm l)"
          by (metis Suc_n_not_le_n \<open>Suc 0 \<le> length l\<close> list.size(3) valid_s)
        have final_states_l: "TM.final_states (Abs_TM (p_tm l)) =
                              {Suc (length l), Suc (Suc (length l * 2))}"
          by (smt (verit, best) p_tm_def p_tm_l_valid select_convs(5)
              valid_tm_final_states)
        have initial_state_l: "TM.initial_state (Abs_TM (p_tm l)) = 0"
          using p_tm_def p_tm_l_valid valid_tm_initial_state by fastforce
        have initial_config_state_l: "state (TM.initial_config (Abs_TM (p_tm l)) []) =
                                      0"
          by (simp add: TM.init_conf_state initial_state_l)
        have initial_config_state_al: "state (TM.initial_config
                                       (Abs_TM (p_tm (a#l))) []) = 0"
          by (simp add: TM.init_conf_state initial_state_s)
        have compute_final: "TM.is_final (Abs_TM (p_tm l))
                             (TM.compute (Abs_TM (p_tm l)) [])"
          using halts \<open>Suc 0 \<le> length l\<close> Suc_le_lessD by blast
        have initial_tapes_l: "tapes (TM.initial_config (Abs_TM (p_tm l)) []) =
                               [Tape [] None []]"
          by (metis Suc_le_lessD TM.one_tape_initial_config
              TM_abbrevs.input_tape.simps(1) TM_config.sel(2) \<open>Suc 0 \<le> length l\<close>
              length_greater_0_conv tape_count_1)
        have initial_tapes_al: "tapes (TM.initial_config (Abs_TM (p_tm (a#l))) []) =
                                [Tape [] None []]"
          by (simp add: TM.initial_config_def TM_abbrevs.input_tape.simps(1)
              tape_count_1)
        have final_state_l: "state (TM.compute (Abs_TM (p_tm l)) []) =
                              Suc (Suc (length l * 2))" using compute_final
          apply standard unfolding final_states_l
        proof auto
          assume "state (TM.compute (Abs_TM (p_tm l)) []) = Suc (length l)"
          moreover have state_1_l: "state (TM.step (Abs_TM (p_tm l))
                         (TM.initial_config (Abs_TM (p_tm l)) [])) =
                         Suc (Suc (length l))"
            by (metis Cons_eq_map_conv \<open>Suc 0 \<le> length l\<close> initial_config_state_l
                initial_state_l initial_tapes_l length_Suc0_not_empty list.simps(8)
                state0_step_empty_s tape.sel(2))
          moreover have not_final: "Suc (Suc (length l)) \<notin>
                                    TM.final_states (Abs_TM (p_tm l))"
            by (metis One_nat_def Suc_eq_plus1 \<open>Suc 0 \<le> length l\<close> add_less_cancel_left
                final_states_l insert_iff leD lessI mult.right_neutral mult_Suc_right
                n_not_Suc_n numeral_2_eq_2 plus_1_eq_Suc singletonD)
          moreover have "state ((TM.step (Abs_TM (p_tm l)) ^^ (Suc n))
                         (TM.initial_config (Abs_TM (p_tm l)) [])) \<ge>
                         Suc (Suc (length l))" for n::nat
            apply (induction n) using state_1_l apply auto
            by (metis TM.step_def \<open>Suc 0 \<le> length l\<close> state_step_f_s initial_state_l
                le_Suc_eq less_eq_Suc_le less_nat_zero_code list.size(3))
          ultimately show "False" apply auto
            by (metis Suc_n_not_le_n TM.compute_altdef TM.run_def TM.step_final
                compute_final)
        qed
        have valid_al: "valid_TM (p_tm (a#l))" by (simp add: valid_s)
        have final_states_al: "TM.final_states (Abs_TM (p_tm (a#l))) =
                           {Suc (Suc (length l)), Suc (Suc (Suc (Suc (length l * 2))))}"
          by (smt (verit, ccfv_threshold) One_nat_def add_Suc length_Cons mult_Suc
              numeral_2_eq_2 p_tm_def plus_1_eq_Suc select_convs(5) valid_al
              valid_tm_final_states)
        have sucl_steps_final: "TM.is_final (Abs_TM (p_tm l))
                         ((TM.step (Abs_TM (p_tm l)) ^^ (Suc (length l)))
                         (TM.initial_config (Abs_TM (p_tm l)) []))"
          by (metis Suc_le_eq TM.run_def TM.time_bounded_word_def \<open>Suc 0 \<le> length l\<close>
              length_greater_0_conv tb)
        have heads_l: "heads (TM.initial_config (Abs_TM (p_tm l)) []) = [None]"
                by (simp add: initial_tapes_l)
        have state_step_1_l: "state (TM.step (Abs_TM (p_tm l))
                    (TM.initial_config (Abs_TM (p_tm l)) [])) = Suc (Suc (length l))"
                unfolding TM.step_def initial_config_state_l final_states_l apply auto
                unfolding initial_config_state_l heads_l
                using p_tm_def p_tm_l_valid valid_tm_next_state by force
        have states_l_al: "\<And>n. n > 0 \<Longrightarrow> n \<le> Suc (length l) \<Longrightarrow>
                         Suc (state ((TM.step (Abs_TM (p_tm l)) ^^ n)
                         (TM.initial_config (Abs_TM (p_tm l)) []))) =
                         state ((TM.step (Abs_TM (p_tm (a#l))) ^^ n)
                         (TM.initial_config (Abs_TM (p_tm (a#l))) []))"
        proof -
          fix n::nat
          show "n > 0 \<Longrightarrow> n \<le> Suc (length l) \<Longrightarrow>
                Suc (state ((TM.step (Abs_TM (p_tm l)) ^^ n)
                (TM.initial_config (Abs_TM (p_tm l)) []))) =
                state ((TM.step (Abs_TM (p_tm (a#l))) ^^ n)
                (TM.initial_config (Abs_TM (p_tm (a#l))) []))"
            apply (induction n rule: nat_induct_non_zero) apply auto
            using state0_step_empty_s
             apply (smt (verit) Suc_n_not_le_n TM.initial_config_def \<open>Suc 0 \<le> length l\<close>
                get0 initial_config_state_l initial_state_s initial_tapes_l
                length_1_ex_iff length_Cons length_map list.distinct(1) list.simps(9)
                tape.sel(2) tape_count_1)
          proof -
            fix n::nat
            assume "0 < n" and IH: "Suc (state ((TM.step (Abs_TM (p_tm l)) ^^ n)
                 (TM.initial_config (Abs_TM (p_tm l)) []))) = state
                  ((TM.step (Abs_TM (p_tm (a # l))) ^^ n)
                  (TM.initial_config (Abs_TM (p_tm (a # l))) []))" and
           "n \<le> length l"
            moreover from this have n_not_final_l:
                  "n \<notin> TM.final_states (Abs_TM (p_tm l))" and
                  n_not_final_al: "n \<notin> TM.final_states (Abs_TM (p_tm (a#l)))"
              by (simp_all add: final_states_l final_states_al)
            moreover have n_not_initial_l: "n \<noteq> TM.initial_state (Abs_TM (p_tm l))"
                     and  n_not_initial_al: "n \<noteq> TM.initial_state (Abs_TM (p_tm (a#l)))"
              by (simp_all add: calculation(1) initial_state_l initial_state_s)
            have "state
               (TM.step (Abs_TM (p_tm l))
                 ((TM.step (Abs_TM (p_tm l)) ^^ n)
                   (TM.initial_config (Abs_TM (p_tm l)) []))) =
                 Suc (state ((TM.step (Abs_TM (p_tm l)) ^^ n)
                 (TM.initial_config (Abs_TM (p_tm l)) [])))" and
                            "state
          (TM.step (Abs_TM (p_tm (a # l)))
            ((TM.step (Abs_TM (p_tm (a # l))) ^^ n)
              (TM.initial_config (Abs_TM (p_tm (a # l))) []))) =
                             Suc (state
                  ((TM.step (Abs_TM (p_tm (a # l))) ^^ n)
                  (TM.initial_config (Abs_TM (p_tm (a # l))) [])))"
               apply (rule state_step_f_s)
                 apply (rule \<open>Suc 0 \<le> length l\<close> [unfolded length_Suc0_not_empty])
            proof -
              obtain nm1 :: nat where nm1_def: "Suc nm1 = n" using \<open>0 < n\<close>
                by (rule nat_gr0_obtain_prev)
              have nm1ltlengthl: "nm1 < length l" using \<open>n \<le> length l\<close> nm1_def by simp
              have state_ge: "state ((TM.step (Abs_TM (p_tm l)) ^^ (Suc nm1))
                     (TM.initial_config (Abs_TM (p_tm l)) [])) \<ge> Suc (Suc (length l))"
                unfolding state_step_1_l [symmetric]
                apply (simp add: funpow_swap1)
                apply (rule state_steps_mono_s [where p2=l])
                using \<open>Suc 0 \<le> length l\<close> by auto
              show "state ((TM.step (Abs_TM (p_tm l)) ^^ n)
                    (TM.initial_config (Abs_TM (p_tm l)) []))
                    \<notin> TM.TM.final_states (Abs_TM (p_tm l))" unfolding final_states_l
                nm1_def
              proof -
                have "state ((TM.step (Abs_TM (p_tm l)) ^^ n)
                      (TM.initial_config (Abs_TM (p_tm l)) [])) \<noteq> Suc (length l)"
                  using state_ge unfolding nm1_def by simp
                moreover have "state ((TM.step (Abs_TM (p_tm l)) ^^ n)
                      (TM.initial_config (Abs_TM (p_tm l)) [])) <
                      Suc (Suc (length l * 2))" unfolding nm1_def [symmetric]
                  using steps_non0_plus_le_s [where p2=l and
                c2="TM.step (Abs_TM (p_tm l)) (TM.initial_config (Abs_TM (p_tm l)) [])"
                and n2=nm1, unfolded state_step_1_l, simplified] \<open>length l \<ge> Suc 0\<close>
                  nm1ltlengthl apply auto
                  by (smt (z3) Groups.add_ac(2) Suc_le_lessD \<open>Suc 0 \<le> length l\<close>
                      add_le_cancel_left funpow_swap1 leD le_add1 length_Suc0_not_empty
                      mult_Suc_right not_less_eq_eq numeral_2_eq_2 order_less_le_trans)
                ultimately show "state ((TM.step (Abs_TM (p_tm l)) ^^ n)
                                 (TM.initial_config (Abs_TM (p_tm l)) []))
                                 \<notin> {Suc (length l), Suc (Suc (length l * 2))}" by simp
              qed
              show "state ((TM.step (Abs_TM (p_tm l)) ^^ n)
                    (TM.initial_config (Abs_TM (p_tm l)) [])) \<noteq>
                    TM.TM.initial_state (Abs_TM (p_tm l))" unfolding nm1_def [symmetric]
                initial_state_l apply auto
                by (metis \<open>Suc 0 \<le> length l\<close> funpow_swap1 gr0I le_zero_eq
                    length_greater_0_conv nat.simps(3) state_step_1_l
                    state_steps_mono_s)
              show "state
                    (TM.step (Abs_TM (p_tm (a # l)))
                    ((TM.step (Abs_TM (p_tm (a # l))) ^^ n)
                    (TM.initial_config (Abs_TM (p_tm (a # l))) []))) =
                    Suc (state
                    ((TM.step (Abs_TM (p_tm (a # l))) ^^ n)
                    (TM.initial_config (Abs_TM (p_tm (a # l))) [])))"
                apply (rule state_step_f_s)
                apply simp
                proof -
                  have heads_al: "heads (TM.initial_config (Abs_TM (p_tm (a#l))) []) =
                                  [None]"
                    by (simp add: initial_tapes_al)
                  have state_step_1_al: "state (TM.step (Abs_TM (p_tm (a#l)))
                    (TM.initial_config (Abs_TM (p_tm (a#l))) [])) =
                    Suc (Suc (Suc (length l)))"
                    unfolding TM.step_def initial_config_state_al final_states_al
                    apply auto unfolding initial_config_state_al heads_al
                using p_tm_def valid_al valid_tm_next_state by force
              have "state ((TM.step (Abs_TM (p_tm (a#l))) ^^ (Suc nm1))
                     (TM.initial_config (Abs_TM (p_tm (a#l))) [])) \<ge>
                    Suc (Suc (Suc (length l)))"
                unfolding state_step_1_al [symmetric]
                apply (simp add: funpow_swap1)
                apply (rule state_steps_mono_s [where p2="a#l"])
                by simp
              thus "state ((TM.step (Abs_TM (p_tm (a#l))) ^^ n)
                    (TM.initial_config (Abs_TM (p_tm (a#l))) []))
                    \<notin> TM.TM.final_states (Abs_TM (p_tm (a#l)))"
                unfolding final_states_al
                nm1_def apply auto using steps_non0_plus_le_s
                  [where p2="a#l" and n2=nm1 and
                    c2="TM.step (Abs_TM (p_tm (a#l)))
                    (TM.initial_config (Abs_TM (p_tm (a#l))) [])", simplified]
                unfolding state_step_1_al
              proof auto
                have "state ((TM.step (Abs_TM (p_tm (a # l))) ^^ n)
                      (TM.initial_config (Abs_TM (p_tm (a # l))) [])) =
                      state ((TM.step (Abs_TM (p_tm (a # l))) ^^ nm1)
                      (TM.step (Abs_TM (p_tm (a # l)))
                      (TM.initial_config (Abs_TM (p_tm (a # l))) [])))"
                  unfolding nm1_def [symmetric] by (simp add: funpow_swap1)
                moreover have "Suc (Suc (Suc (Suc (length l * 2)))) >
                               Suc (Suc (Suc (nm1 + length l)))"
                  by (simp add: less_SucI nm1ltlengthl)
                ultimately show "state ((TM.step (Abs_TM (p_tm (a # l))) ^^ n)
                                 (TM.initial_config (Abs_TM (p_tm (a # l))) [])) =
                                 Suc (Suc (Suc (Suc (length l * 2)))) \<Longrightarrow> state
                                 ((TM.step (Abs_TM (p_tm (a # l))) ^^ nm1)
       (TM.step (Abs_TM (p_tm (a # l))) (TM.initial_config (Abs_TM (p_tm (a # l))) [])))
    \<le> Suc (Suc (Suc (nm1 + length l))) \<Longrightarrow> False" by simp
              qed
              show "state
                    ((TM.step (Abs_TM (p_tm (a # l))) ^^ n)
                    (TM.initial_config (Abs_TM (p_tm (a # l))) [])) \<noteq>
                    TM.TM.initial_state (Abs_TM (p_tm (a # l)))"
                unfolding nm1_def [symmetric] apply auto
                by (metis TM.init_conf_state funpow_swap1 initial_config_state_al
                    le_zero_eq list.distinct(1) nat.simps(3) state_step_1_al
                    state_steps_mono_s)
            qed
            qed
            thus "Suc (state
               (TM.step (Abs_TM (p_tm l))
                 ((TM.step (Abs_TM (p_tm l)) ^^ n)
                   (TM.initial_config (Abs_TM (p_tm l)) [])))) =
         state
          (TM.step (Abs_TM (p_tm (a # l)))
            ((TM.step (Abs_TM (p_tm (a # l))) ^^ n)
              (TM.initial_config (Abs_TM (p_tm (a # l))) [])))" using IH by auto
          qed
        qed
        have tapes_l_al: "\<And>n. n < length l \<Longrightarrow> tapes ((TM.step (Abs_TM (p_tm l)) ^^ n)
                         (TM.initial_config (Abs_TM (p_tm l)) [])) =
                         tapes ((TM.step (Abs_TM (p_tm (a#l))) ^^ n)
                         (TM.initial_config (Abs_TM (p_tm (a#l))) []))"
        proof -
          fix n :: nat
          show "n < length l \<Longrightarrow> tapes ((TM.step (Abs_TM (p_tm l)) ^^ n)
                (TM.initial_config (Abs_TM (p_tm l)) [])) =
                tapes ((TM.step (Abs_TM (p_tm (a#l))) ^^ n)
                (TM.initial_config (Abs_TM (p_tm (a#l))) []))" apply (induction n)
            apply auto
            using initial_tapes_al initial_tapes_l apply presburger
          proof -
            fix n :: nat
            assume tapes_IH: "tapes
          ((TM.step (Abs_TM (p_tm l)) ^^ n) (TM.initial_config (Abs_TM (p_tm l)) [])) =
          tapes ((TM.step (Abs_TM (p_tm (a # l))) ^^ n)
          (TM.initial_config (Abs_TM (p_tm (a # l))) []))" and "Suc n < length l"
            hence states_step_sucn: "Suc (state ((TM.step (Abs_TM (p_tm l)) ^^ (Suc n))
                  (TM.initial_config (Abs_TM (p_tm l)) []))) =
                  state ((TM.step (Abs_TM (p_tm (a # l))) ^^ (Suc n))
                  (TM.initial_config (Abs_TM (p_tm (a # l))) []))"
              by (meson gr0_conv_Suc le_SucI less_or_eq_imp_le states_l_al)
            have states_step_n_g0: "n > 0 \<Longrightarrow>
                  Suc (state ((TM.step (Abs_TM (p_tm l)) ^^ n)
                  (TM.initial_config (Abs_TM (p_tm l)) []))) =
                  state ((TM.step (Abs_TM (p_tm (a # l))) ^^ n)
                  (TM.initial_config (Abs_TM (p_tm (a # l))) []))"
              using \<open>Suc n < length l\<close> states_l_al by auto
            have states_step_n_0: "n = 0 \<Longrightarrow> state ((TM.step (Abs_TM (p_tm l)) ^^ n)
                  (TM.initial_config (Abs_TM (p_tm l)) [])) =
                  state ((TM.step (Abs_TM (p_tm (a # l))) ^^ n)
                  (TM.initial_config (Abs_TM (p_tm (a # l))) []))"
              by (simp add: initial_config_state_al initial_config_state_l)
            have next_write_l_al: "\<And>hds s k. s > Suc (length l) \<Longrightarrow>
                  s < Suc (length l * 2) \<Longrightarrow>
                  TM.next_write (Abs_TM (p_tm l)) s hds k =
                  TM.next_write (Abs_TM (p_tm (a#l))) (Suc s) hds k"
            proof -
              fix hds and s k
              assume "Suc (length l) < s" and "s < Suc (length l * 2)"
              have "TM.TM.next_write (Abs_TM (p_tm l)) s hds k =
                    Some (l ! (Suc (length l * 2) - s))"
                by (metis \<open>Suc (length l) < s\<close> \<open>Suc 0 \<le> length l\<close>
                    bot_nat_0.extremum_strict leD length_Suc0_not_empty next_write_s)
              moreover have "TM.TM.next_write (Abs_TM (p_tm (a # l))) (Suc s) hds k =
                             Some ((a#l) ! (Suc (length (a#l) * 2) - (Suc s)))"
                using \<open>Suc (length l) < s\<close> next_write_s by auto
              ultimately show "TM.TM.next_write (Abs_TM (p_tm l)) s hds k =
                    TM.TM.next_write (Abs_TM (p_tm (a # l))) (Suc s) hds k"
                using \<open>s < Suc (length l * 2)\<close> by auto
            qed
            have next_write_l_al_0: "\<And>hds k.
                  TM.next_write (Abs_TM (p_tm l)) 0 hds k =
                  TM.next_write (Abs_TM (p_tm (a#l))) 0 hds k"
              using \<open>Suc 0 \<le> length l\<close> next_write_s by auto
            have next_move_l_al: "\<And>hds s k. s > Suc (length l) \<Longrightarrow>  
                           s < Suc (length l * 2) \<Longrightarrow>
                           TM.next_move (Abs_TM (p_tm l)) s hds k =
                           TM.next_move (Abs_TM (p_tm (a#l))) (Suc s) hds k"
            proof -
              fix hds :: "'s option list" and s k :: nat
              assume "Suc (length l) < s" and "s < Suc (length l * 2)"
              hence "TM.TM.next_move (Abs_TM (p_tm l)) s hds k = Shift_Left"
                using p_tm_def p_tm_l_valid valid_tm_next_move by force
              moreover have "TM.TM.next_move (Abs_TM (p_tm (a # l))) (Suc s) hds k =
                             Shift_Left"
                using \<open>Suc (length l) < s\<close> \<open>s < Suc (length l * 2)\<close> p_tm_def valid_al
                  valid_tm_next_move by force
              ultimately show "TM.TM.next_move (Abs_TM (p_tm l)) s hds k =
                    TM.TM.next_move (Abs_TM (p_tm (a # l))) (Suc s) hds k"
                by simp
            qed
            have next_move_l_al_0: "\<And>hds k.
                           TM.next_move (Abs_TM (p_tm l)) 0 hds k =
                           TM.next_move (Abs_TM (p_tm (a#l))) 0 hds k"
              by (smt (verit) Suc_le_lessD \<open>Suc 0 \<le> length l\<close> length_Cons
                  less_numeral_extra(3) nat.simps(3) p_tm_def p_tm_l_valid
                  select_convs(9) valid_al valid_tm_next_move)
            have heads_l_al: "heads ((TM.step (Abs_TM (p_tm l)) ^^ n)
                              (TM.initial_config (Abs_TM (p_tm l)) [])) =
                              heads ((TM.step (Abs_TM (p_tm (a # l))) ^^ n)
                              (TM.initial_config (Abs_TM (p_tm (a # l))) []))"
              using tapes_IH by simp
            show "tapes (TM.step (Abs_TM (p_tm l))
            ((TM.step (Abs_TM (p_tm l)) ^^ n)
            (TM.initial_config (Abs_TM (p_tm l)) []))) = tapes
            (TM.step (Abs_TM (p_tm (a # l))) ((TM.step (Abs_TM (p_tm (a # l))) ^^ n)
            (TM.initial_config (Abs_TM (p_tm (a # l))) [])))"
              apply (rule same_tps_shift_write)
                   apply (rule tapes_IH)
                  apply (cases n)
                   apply (simp add: initial_config_state_al initial_config_state_l
                  initial_tapes_al initial_tapes_l next_write_l_al_0)
              unfolding n_gt_0_eq_Suc_nat [symmetric] heads_l_al
                  apply (rule states_step_n_g0 [THEN subst])
              apply assumption
                  apply (rule next_write_l_al)
              using state_steps_mono_s
                [where p2=l and n2="n - 1" and c2="TM.step (Abs_TM (p_tm l))
                  (TM.initial_config (Abs_TM (p_tm l)) [])", OF \<open>length l \<ge> Suc 0\<close>
                  [unfolded length_Suc0_not_empty], unfolded state_step_1_l]
                   apply (metis One_nat_def Suc_pred funpow.simps(2) funpow_swap1
                  less_eq_Suc_le o_apply) using steps_non0_plus_le_s
                    [OF \<open>length l \<ge> Suc 0\<close> [unfolded length_Suc0_not_empty]]
                  apply (smt (z3) Suc_pred \<open>Suc n < length l\<close> add.commute add_Suc_right
                  add_le_cancel_left funpow.simps(2) funpow_swap1 leD le_SucI
                  less_eq_Suc_le mult_Suc_right mult_numeral_1_right not_less_eq
                  numeral_1_eq_Suc_0 numeral_2_eq_2 o_apply order_less_le_trans
                  state_step_1_l)
                 apply (cases n)
                  apply (simp add: initial_config_state_al initial_config_state_l
                  next_move_l_al_0)
                 unfolding n_gt_0_eq_Suc_nat [symmetric] heads_l_al
                 apply (rule states_step_n_g0 [THEN subst])
                     apply assumption
                    apply (rule next_move_l_al)
                 using state_steps_mono_s
                [where p2=l and n2="n - 1" and c2="TM.step (Abs_TM (p_tm l))
                  (TM.initial_config (Abs_TM (p_tm l)) [])", OF \<open>length l \<ge> Suc 0\<close>
                  [unfolded length_Suc0_not_empty], unfolded state_step_1_l]
                   apply (metis One_nat_def Suc_pred funpow.simps(2) funpow_swap1
                  less_eq_Suc_le o_apply) using steps_non0_plus_le_s
                    [OF \<open>length l \<ge> Suc 0\<close> [unfolded length_Suc0_not_empty]]
                  apply (smt (z3) Suc_pred \<open>Suc n < length l\<close> add.commute add_Suc_right
                  add_le_cancel_left funpow.simps(2) funpow_swap1 leD le_SucI
                  less_eq_Suc_le mult_Suc_right mult_numeral_1_right not_less_eq
                  numeral_1_eq_Suc_0 numeral_2_eq_2 o_apply order_less_le_trans
                  state_step_1_l)
               proof -
                 have "\<not>TM.is_final (Abs_TM (p_tm l))
            ((TM.step (Abs_TM (p_tm l)) ^^ n) (TM.initial_config (Abs_TM (p_tm l)) []))"
                   unfolding TM.is_final_def final_states_l apply auto
                    apply (cases n)
                     apply (simp add: initial_config_state_l)
                    apply (metis One_nat_def
                       state_steps_mono_s
                [where p2=l and n2="n - 1" and c2="TM.step (Abs_TM (p_tm l))
                  (TM.initial_config (Abs_TM (p_tm l)) [])", OF \<open>length l \<ge> Suc 0\<close>
                  [unfolded length_Suc0_not_empty], unfolded state_step_1_l]
                diff_Suc_1' funpow.simps(2) funpow_swap1 lessI less_eq_Suc_le
                not_less_eq_eq o_apply)
                 proof -
                   assume a1: "state ((TM.step (Abs_TM (p_tm l)) ^^ n) (TM.initial_config (Abs_TM (p_tm l)) [])) = Suc (Suc (length l * 2))"
                   have f2: "\<forall>n na. ((n::nat) < na) = (n \<le> na \<and> n \<noteq> na)"
                     using nat_less_le by argo
                   then have f3: "Suc n \<le> length l \<and> Suc n \<noteq> length l"
                     using \<open>Suc n < length l\<close> by presburger
                   then have f4: "Suc (state ((TM.step (Abs_TM (p_tm l)) ^^ Suc n) (TM.initial_config (Abs_TM (p_tm l)) []))) = state ((TM.step (Abs_TM (p_tm (a # l))) ^^ Suc n) (TM.initial_config (Abs_TM (p_tm (a # l))) []))"
                     using f2 le_imp_less_Suc states_l_al zero_less_Suc by presburger
                   have f5: "state (TM.compute (Abs_TM (p_tm l)) []) \<in> TM.TM.final_states (Abs_TM (p_tm l))"
                     using compute_final by blast
                   then have f6: "(TM.step (Abs_TM (p_tm l)) ^^ Suc n) (TM.initial_config (Abs_TM (p_tm l)) []) = (TM.step (Abs_TM (p_tm l)) ^^ n) (TM.initial_config (Abs_TM (p_tm l)) [])"
                     using a1 by (simp add: TM.step_def final_state_l)
                   have f7: "length l * Suc 0 = length l"
                     by simp
                   have f8: "length l + length l * Suc 0 = length l * 2"
                     by presburger
                   have f9: "Suc (state ((TM.step (Abs_TM (p_tm l)) ^^ n) (TM.initial_config (Abs_TM (p_tm l)) []))) < Suc (Suc (Suc (length l)) + Suc (length l))"
                     using a1 by linarith
                   have "(TM.step (Abs_TM (p_tm l)) ^^ Suc (Suc n)) (TM.initial_config (Abs_TM (p_tm l)) []) = (TM.step (Abs_TM (p_tm l)) ^^ Suc n) (TM.initial_config (Abs_TM (p_tm l)) [])"
                     using f5 a1 by (simp add: TM.step_def final_state_l)
                   then have "state (TM.step (Abs_TM (p_tm (a # l))) ((TM.step (Abs_TM (p_tm (a # l))) ^^ n) (TM.initial_config (Abs_TM (p_tm (a # l))) []))) = Suc (length (a # l)) \<or> state (TM.step (Abs_TM (p_tm (a # l))) ((TM.step (Abs_TM (p_tm (a # l))) ^^ n) (TM.initial_config (Abs_TM (p_tm (a # l))) []))) = Suc (Suc (length (a # l) * 2))"
                     using f9 f8 f7 f6 f3 f2 a1 by (smt (z3) add.commute add_Suc_right funpow.simps(2) le_imp_less_Suc length_Cons length_Suc0_not_empty less_eq_Suc_le o_apply state_step_s states_l_al zero_less_Suc)
                   then show False
                     using f6 f4 a1 by simp
                 qed
                 moreover have "\<not>TM.is_final (Abs_TM (p_tm (a # l)))
                                ((TM.step (Abs_TM (p_tm (a # l))) ^^ n)
                                (TM.initial_config (Abs_TM (p_tm (a # l))) []))"
                  unfolding TM.is_final_def final_states_al apply auto
                  apply (cases n)
                     apply (simp add: initial_config_state_al)
                  using calculation final_states_l states_step_n_g0 apply fastforce
                  apply (cases n)
                  apply (simp add: initial_config_state_al)
                  using steps_non0_plus_le_s [OF \<open>l \<noteq> []\<close>]
                  by (smt (verit) Suc_le_lessD TM.step_def state_steps_mono_s
                [where p2=l and n2="n - 1" and c2="TM.step (Abs_TM (p_tm l))
                  (TM.initial_config (Abs_TM (p_tm l)) [])", OF \<open>length l \<ge> Suc 0\<close>
                  [unfolded length_Suc0_not_empty], unfolded state_step_1_l]
                \<open>Suc n < length l\<close> \<open>l \<noteq> []\<close> add_Suc_shift add_cancel_right_right
                add_left_imp_eq compute_final diff_Suc_1' final_state_l funpow.simps(2)
                funpow_swap1 initial_state_l is_finalD le_antisym length_Cons
                less_Suc_eq list.distinct(1) mult_2_right nat_less_le o_apply
                plus_1_eq_Suc state_step_1_l state_step_f_s state_step_s states_l_al
                zero_less_Suc)
                 ultimately show "TM.is_final (Abs_TM (p_tm l))
     ((TM.step (Abs_TM (p_tm l)) ^^ n) (TM.initial_config (Abs_TM (p_tm l)) [])) =
    TM.is_final (Abs_TM (p_tm (a # l)))
     ((TM.step (Abs_TM (p_tm (a # l))) ^^ n)
       (TM.initial_config (Abs_TM (p_tm (a # l))) []))" by simp
               next
                 show "TM.TM.tape_count (Abs_TM (p_tm l)) =
                       TM.TM.tape_count (Abs_TM (p_tm (a # l)))"
                   using \<open>Suc 0 \<le> length l\<close> tape_count_1 by auto
               next
                 show "TM.TM.tape_count (Abs_TM (p_tm l)) = length
                       (tapes ((TM.step (Abs_TM (p_tm l)) ^^ n)
                       (TM.initial_config (Abs_TM (p_tm l)) [])))"
                   by (simp add: TM.run_tapes_len)
               qed
          qed
        qed
        hence heads_l_al: "\<And>n. n < length l \<Longrightarrow> heads ((TM.step (Abs_TM (p_tm l)) ^^ n)
                         (TM.initial_config (Abs_TM (p_tm l)) [])) =
                         heads ((TM.step (Abs_TM (p_tm (a#l))) ^^ n)
                         (TM.initial_config (Abs_TM (p_tm (a#l))) []))" by simp
        have initial_configs_eq: "TM.initial_config (Abs_TM (p_tm l)) [] =
              TM.initial_config (Abs_TM (p_tm (a#l))) []"
          unfolding TM.initial_config_def tape_count_1 [OF \<open>l \<noteq> []\<close>]
          tape_count_1 [OF list.distinct(2)] initial_state_s [OF list.distinct(2)]
          initial_state_l ..
        obtain lm1 :: "'s option list" where lm1_def: "length l = Suc (length lm1)"
          using \<open>length l \<ge> Suc 0\<close>
          by (metis Suc_n_not_le_n length_replicate old.nat.exhaust)
        have tapes_step_length_l: "tapes ((TM.step (Abs_TM (p_tm l)) ^^ (length l))
              (TM.initial_config (Abs_TM (p_tm l)) [])) =
              tapes ((TM.step (Abs_TM (p_tm (a#l))) ^^ (length l))
              (TM.initial_config (Abs_TM (p_tm (a#l))) []))"
          unfolding initial_configs_eq lm1_def apply auto
          apply (rule same_tps_shift_write)
          using lm1_def tapes_l_al apply (simp add: initial_configs_eq)
          apply (cases lm1) apply simp
               apply (simp add: \<open>l \<noteq> []\<close> initial_config_state_al next_write_s)
              apply (insert lm1_def [THEN suc_is_ge])
              apply (rule states_l_al [THEN subst]) apply simp
               apply simp
        proof -
          fix k :: nat and b :: "'s option" and list :: "'s option list"
          assume lm1_cons: "lm1 = b # list" and "length lm1 \<le> length l"
          have state_l_lm1: "state ((TM.step (Abs_TM (p_tm l)) ^^ length lm1)
                (TM.initial_config (Abs_TM (p_tm (a # l))) [])) = length l * 2"
            unfolding lm1_cons apply auto unfolding funpow_swap1
          proof -
            have list_lm2: "length list = length l - 2"
              using lm1_def lm1_cons by simp
            have "state (TM.step (Abs_TM (p_tm l))
                  (TM.initial_config (Abs_TM (p_tm (a # l))) [])) =
                  Suc (Suc (length l))"
              using initial_configs_eq state_step_1_l by presburger
            thus "state ((TM.step (Abs_TM (p_tm l)) ^^ length list)
                  (TM.step (Abs_TM (p_tm l))
                  (TM.initial_config (Abs_TM (p_tm (a # l))) []))) = length l * 2"
              using state_steps_empty_s by (simp add: \<open>l \<noteq> []\<close> lm1_cons lm1_def)
          qed
          have "\<And>hds k. TM.TM.next_write (Abs_TM (p_tm l)) (length l * 2) hds k =
                Some (l ! (Suc (length l * 2) - length l * 2))"
            by (simp add: \<open>l \<noteq> []\<close> lm1_cons lm1_def next_write_s)
          hence next_write_l: "\<And>hds k. TM.TM.next_write (Abs_TM (p_tm l))
                               (length l * 2) hds k = Some (l ! 1)" by simp
          have "\<And>hds k. TM.TM.next_write (Abs_TM (p_tm (a#l))) (Suc (length l * 2))
                hds k = Some ((a#l) ! (Suc (length (a#l) * 2) - Suc (length l * 2)))"
            by (simp add: lm1_cons lm1_def next_write_s)
          hence next_write_al: "\<And>hds k. TM.TM.next_write (Abs_TM (p_tm (a#l)))
                (Suc (length l * 2)) hds k = Some ((a#l) ! 2)" by simp
          show "TM.TM.next_write (Abs_TM (p_tm l))
                (state ((TM.step (Abs_TM (p_tm l)) ^^ length lm1)
                (TM.initial_config (Abs_TM (p_tm (a # l))) [])))
                (heads ((TM.step (Abs_TM (p_tm l)) ^^ length lm1)
                (TM.initial_config (Abs_TM (p_tm (a # l))) []))) k =
                TM.TM.next_write (Abs_TM (p_tm (a # l)))
                (Suc (state ((TM.step (Abs_TM (p_tm l)) ^^ length lm1)
                (TM.initial_config (Abs_TM (p_tm l)) []))))
                (heads ((TM.step (Abs_TM (p_tm (a # l))) ^^ length lm1)
                (TM.initial_config (Abs_TM (p_tm (a # l))) []))) k"
            unfolding state_l_lm1 initial_configs_eq next_write_l next_write_al by simp
        next
          fix k :: nat
          assume "length lm1 \<le> length l"
          show "TM.TM.next_move (Abs_TM (p_tm l))
                (state ((TM.step (Abs_TM (p_tm l)) ^^ length lm1)
                (TM.initial_config (Abs_TM (p_tm (a # l))) [])))
                (heads ((TM.step (Abs_TM (p_tm l)) ^^ length lm1)
                (TM.initial_config (Abs_TM (p_tm (a # l))) []))) k =
                TM.TM.next_move (Abs_TM (p_tm (a # l)))
                (state ((TM.step (Abs_TM (p_tm (a # l))) ^^ length lm1)
                (TM.initial_config (Abs_TM (p_tm (a # l))) [])))
                (heads ((TM.step (Abs_TM (p_tm (a # l))) ^^ length lm1)
                (TM.initial_config (Abs_TM (p_tm (a # l))) []))) k" apply (cases lm1)
            apply simp
             apply (smt (verit, best) initial_config_state_al length_Cons lm1_def
                nat.simps(3) p_tm_def p_tm_l_valid select_convs(9) valid_al
                valid_tm_next_move)
          proof -
            fix b :: "'s option" and list :: "'s option list"
            assume lm1_cons: "lm1 = b # list"
            have state_l_lm1: "state ((TM.step (Abs_TM (p_tm l)) ^^ length lm1)
                (TM.initial_config (Abs_TM (p_tm (a # l))) [])) = length l * 2"
            unfolding lm1_cons apply auto unfolding funpow_swap1
            proof -
              have list_lm2: "length list = length l - 2"
                using lm1_def lm1_cons by simp
              have "state (TM.step (Abs_TM (p_tm l))
                  (TM.initial_config (Abs_TM (p_tm (a # l))) [])) =
                  Suc (Suc (length l))"
                using initial_configs_eq state_step_1_l by presburger
              thus "state ((TM.step (Abs_TM (p_tm l)) ^^ length list)
                  (TM.step (Abs_TM (p_tm l))
                  (TM.initial_config (Abs_TM (p_tm (a # l))) []))) = length l * 2"
                using state_steps_empty_s by (simp add: \<open>l \<noteq> []\<close> lm1_cons lm1_def)
            qed
            have state_al_lm1: "state ((TM.step (Abs_TM (p_tm (a # l))) ^^ length lm1)
                                (TM.initial_config (Abs_TM (p_tm (a # l))) [])) =
                                Suc (length l * 2)"
              by (metis \<open>length lm1 \<le> length l\<close> initial_configs_eq le_Suc_eq
                  length_greater_0_conv list.discI lm1_cons state_l_lm1 states_l_al)
            have next_move_l: "\<And>hds k. TM.TM.next_move (Abs_TM (p_tm l))
                               (length l * 2) hds k = Shift_Left"
              using \<open>Suc 0 \<le> length l\<close> p_tm_def p_tm_l_valid valid_tm_next_move
              by fastforce
            have next_move_al: "\<And>hds k. TM.TM.next_move (Abs_TM (p_tm (a#l)))
                                (Suc (length l * 2)) hds k = Shift_Left"
              using \<open>Suc 0 \<le> length l\<close> p_tm_def valid_al valid_tm_next_move by fastforce
            show "TM.TM.next_move (Abs_TM (p_tm l))
                  (state ((TM.step (Abs_TM (p_tm l)) ^^ length lm1)
                  (TM.initial_config (Abs_TM (p_tm (a # l))) [])))
                  (heads ((TM.step (Abs_TM (p_tm l)) ^^ length lm1)
                  (TM.initial_config (Abs_TM (p_tm (a # l))) []))) k =
                  TM.TM.next_move (Abs_TM (p_tm (a # l)))
                  (state ((TM.step (Abs_TM (p_tm (a # l))) ^^ length lm1)
                  (TM.initial_config (Abs_TM (p_tm (a # l))) [])))
                  (heads ((TM.step (Abs_TM (p_tm (a # l))) ^^ length lm1)
                  (TM.initial_config (Abs_TM (p_tm (a # l))) []))) k"
              unfolding state_l_lm1 state_al_lm1 next_move_l next_move_al ..
          qed
        next
          assume "length lm1 \<le> length l"
          have "\<not>TM.is_final (Abs_TM (p_tm l))
                ((TM.step (Abs_TM (p_tm l)) ^^ length lm1)
                (TM.initial_config (Abs_TM (p_tm (a # l))) []))"
            unfolding TM.is_final_def final_states_l
            by (smt (verit, best) Suc_eq_plus1 TM.step_final \<open>l \<noteq> []\<close> add_Suc_shift
                final_states_l funpow_swap1 group_cancel.add1 initial_configs_eq insertE
                is_finalI le_add1 less_Suc_eq linorder_not_less lm1_def mult_2_right
                singleton_iff state_step_1_l state_steps_empty_s)
          moreover have "\<not>TM.is_final (Abs_TM (p_tm (a # l)))
                         ((TM.step (Abs_TM (p_tm (a # l))) ^^ length lm1)
                         (TM.initial_config (Abs_TM (p_tm (a # l))) []))"
            unfolding TM.is_final_def final_states_al
            by (smt (verit, ccfv_threshold) TM.final_le_steps \<open>length lm1 \<le> length l\<close>
                calculation diff_Suc_1' final_states_al funpow_0 initial_config_state_l
                initial_configs_eq is_finalD is_finalI le_Suc_eq nat_less_le states_l_al
                sucl_steps_final zero_less_Suc)
          ultimately show "TM.is_final (Abs_TM (p_tm l))
                           ((TM.step (Abs_TM (p_tm l)) ^^ length lm1)
                           (TM.initial_config (Abs_TM (p_tm (a # l))) [])) =
                           TM.is_final (Abs_TM (p_tm (a # l)))
                           ((TM.step (Abs_TM (p_tm (a # l))) ^^ length lm1)
                           (TM.initial_config (Abs_TM (p_tm (a # l))) []))" by simp
        next
          show "TM.TM.tape_count (Abs_TM (p_tm l)) =
                TM.TM.tape_count (Abs_TM (p_tm (a # l)))"
            by (simp add: \<open>l \<noteq> []\<close> tape_count_1)
        next
          show "TM.TM.tape_count (Abs_TM (p_tm l)) =
                length (tapes ((TM.step (Abs_TM (p_tm l)) ^^ length lm1)
                (TM.initial_config (Abs_TM (p_tm (a # l))) [])))"
            by (metis TM.run_tapes_len initial_configs_eq)
        qed
        hence tapes_l_al_length_l: "\<And>n. n \<le> length l \<Longrightarrow>
                         tapes ((TM.step (Abs_TM (p_tm l)) ^^ n)
                         (TM.initial_config (Abs_TM (p_tm l)) [])) =
                         tapes ((TM.step (Abs_TM (p_tm (a#l))) ^^ n)
                         (TM.initial_config (Abs_TM (p_tm (a#l))) []))"
          using tapes_l_al nat_less_le by blast
        have state_suc_l: "state ((TM.step (Abs_TM (p_tm (a#l))) ^^ (Suc (length l)))
              (TM.initial_config (Abs_TM (p_tm (a#l))) [])) =
              Suc (Suc (Suc (length l * 2)))" using states_l_al [of "Suc (length l)"]
          sucl_steps_final final_state_l apply auto
          unfolding TM.compute_altdef TM.run_def
          by (smt (verit, ccfv_threshold) TM.compute_altdef TM.final_steps_rev
              TM.run_def compute_final funpow.simps(2) o_apply)
        have tapes_l_finished: "tapes ((TM.step (Abs_TM (p_tm l)) ^^ (Suc (length l)))
              (TM.initial_config (Abs_TM (p_tm l)) [])) =
              [Tape [] (Some (hd l)) (map Some (tl l))]"
            by (metis TM.compute_altdef TM.final_le_steps TM.run_def compute_final
                nat_le_linear sucl_steps_final tapes_l)
        have al_steps_sucl: "(TM.step (Abs_TM (p_tm (a#l))) ^^ (Suc (length l)))
              (TM.initial_config (Abs_TM (p_tm (a#l))) []) =
              TM_config (Suc (Suc (Suc (length l * 2))))
              [Tape [] None (map Some l)]"
        proof -
          have "tapes ((TM.step (Abs_TM (p_tm l)) ^^ (Suc (length l)))
              (TM.initial_config (Abs_TM (p_tm l)) [])) =
              [Tape [] (Some (hd l)) (map Some (tl l))]"
            by (metis TM.compute_altdef TM.final_le_steps TM.run_def compute_final
                nat_le_linear sucl_steps_final tapes_l)
          moreover have "map (TM_abbrevs.tape_shift Shift_Left)
                (tapes ((TM.step (Abs_TM (p_tm l)) ^^ (Suc (length l)))
                (TM.initial_config (Abs_TM (p_tm l)) []))) =
                tapes ((TM.step (Abs_TM (p_tm (a#l))) ^^ (Suc (length l)))
                (TM.initial_config (Abs_TM (p_tm (a#l))) []))"
            apply (rule sym)
            unfolding initial_configs_eq [symmetric]
            apply auto
            apply (rule tps_same_write_left_no_shift)
            using initial_configs_eq tapes_step_length_l apply argo
          proof -
            fix k :: nat
            have state_step_al: "state (TM.step (Abs_TM (p_tm (a # l)))
                    (TM.initial_config (Abs_TM (p_tm l)) [])) =
                    Suc (Suc (length (a#l)))"
                unfolding initial_configs_eq using state0_step_empty_s
                by (metis TM.init_conf_state heads_l initial_configs_eq
                    list.distinct(1))
            have state_stepsl_al: "state ((TM.step (Abs_TM (p_tm (a # l))) ^^ length l)
                 (TM.initial_config (Abs_TM (p_tm l)) [])) = length (a#l) * 2"
              unfolding lm1_def apply auto unfolding funpow_swap1
              by (simp add: lm1_def state_step_al state_steps_empty_s)
            have state_stepsl_l: "state ((TM.step (Abs_TM (p_tm l)) ^^ length l)
                 (TM.initial_config (Abs_TM (p_tm l)) [])) = length (a#l) * 2 - 1"
              by (metis One_nat_def Suc_le_lessD \<open>Suc 0 \<le> length l\<close> diff_Suc_1'
                  initial_configs_eq le_add2 plus_1_eq_Suc state_stepsl_al states_l_al)
            have next_write_al: "\<And>hds k. TM.TM.next_write (Abs_TM (p_tm (a # l)))
                                 (Suc (Suc (length l * 2))) hds k =
                                 Some ((a#l) ! (Suc (length (a#l) * 2) -
                                 Suc (Suc (length l * 2))))"
              using \<open>Suc 0 \<le> length l\<close> next_write_s by auto
            have next_write_l: "\<And>hds k. TM.TM.next_write (Abs_TM (p_tm l))
                                 (Suc (length l * 2)) hds k =
                                 Some (l ! (Suc (length l * 2) -
                                 Suc (length l * 2)))"
              by (simp add: \<open>l \<noteq> []\<close> next_write_s)
            show "TM.TM.next_write (Abs_TM (p_tm (a # l)))
          (state
            ((TM.step (Abs_TM (p_tm (a # l))) ^^ length l)
              (TM.initial_config (Abs_TM (p_tm l)) [])))
          (heads
            ((TM.step (Abs_TM (p_tm (a # l))) ^^ length l)
              (TM.initial_config (Abs_TM (p_tm l)) [])))
          k =
         TM.TM.next_write (Abs_TM (p_tm l))
          (state
            ((TM.step (Abs_TM (p_tm l)) ^^ length l)
              (TM.initial_config (Abs_TM (p_tm l)) [])))
          (heads
            ((TM.step (Abs_TM (p_tm l)) ^^ length l)
              (TM.initial_config (Abs_TM (p_tm l)) [])))
          k" unfolding state_stepsl_al state_stepsl_l apply auto
              unfolding next_write_l next_write_al by simp
          next
            fix k :: nat
            have state_step_al: "state (TM.step (Abs_TM (p_tm (a # l)))
                    (TM.initial_config (Abs_TM (p_tm l)) [])) =
                    Suc (Suc (length (a#l)))"
                unfolding initial_configs_eq using state0_step_empty_s
                by (metis TM.init_conf_state heads_l initial_configs_eq
                    list.distinct(1))
            have state_stepsl_al: "state ((TM.step (Abs_TM (p_tm (a # l))) ^^ length l)
                 (TM.initial_config (Abs_TM (p_tm l)) [])) = length (a#l) * 2"
              unfolding lm1_def apply auto unfolding funpow_swap1
              by (simp add: lm1_def state_step_al state_steps_empty_s)
            show "TM.TM.next_move (Abs_TM (p_tm (a # l)))
          (state ((TM.step (Abs_TM (p_tm (a # l))) ^^ length l)
              (TM.initial_config (Abs_TM (p_tm l)) [])))
           (heads ((TM.step (Abs_TM (p_tm (a # l))) ^^ length l)
              (TM.initial_config (Abs_TM (p_tm l)) []))) k = Shift_Left"
              unfolding state_stepsl_al
              by (metis length_Cons less_add_Suc1 lm1_def plus_1_eq_Suc
                  shift_left_before_end_s)
          next
            fix k :: nat
            have state_step_al: "state (TM.step (Abs_TM (p_tm (a # l)))
                    (TM.initial_config (Abs_TM (p_tm l)) [])) =
                    Suc (Suc (length (a#l)))"
                unfolding initial_configs_eq using state0_step_empty_s
                by (metis TM.init_conf_state heads_l initial_configs_eq
                    list.distinct(1))
            have state_stepsl_al: "state ((TM.step (Abs_TM (p_tm (a # l))) ^^ length l)
                 (TM.initial_config (Abs_TM (p_tm l)) [])) = length (a#l) * 2"
              unfolding lm1_def apply auto unfolding funpow_swap1
              by (simp add: lm1_def state_step_al state_steps_empty_s)
            have state_stepsl_l: "state ((TM.step (Abs_TM (p_tm l)) ^^ length l)
                 (TM.initial_config (Abs_TM (p_tm l)) [])) = length (a#l) * 2 - 1"
              by (metis One_nat_def Suc_le_lessD \<open>Suc 0 \<le> length l\<close> diff_Suc_1'
                  initial_configs_eq le_add2 plus_1_eq_Suc state_stepsl_al states_l_al)
            show "TM.TM.next_move (Abs_TM (p_tm l))
          (state
            ((TM.step (Abs_TM (p_tm l)) ^^ length l)
              (TM.initial_config (Abs_TM (p_tm l)) [])))
          (heads
            ((TM.step (Abs_TM (p_tm l)) ^^ length l)
              (TM.initial_config (Abs_TM (p_tm l)) [])))
          k =
         No_Shift" unfolding state_stepsl_l apply auto
              using p_tm_def p_tm_l_valid valid_tm_next_move by force
          next
            show "\<not> TM.is_final (Abs_TM (p_tm (a # l)))
                  ((TM.step (Abs_TM (p_tm (a # l))) ^^ length l)
                  (TM.initial_config (Abs_TM (p_tm l)) []))"
              unfolding TM.is_final_def final_states_al apply auto
               apply (metis Suc_n_not_le_n TM.final_mono TM.final_steps_rev diff_Suc_1'
                  final_states_al initial_configs_eq insertI1 is_finalI le_add2
                  mult_2_right plus_1_eq_Suc state_suc_l)
              by (metis TM.final_mono TM.final_steps_rev final_states_al
                  initial_configs_eq insert_iff is_finalI le_add2 n_not_Suc_n
                  plus_1_eq_Suc state_suc_l)
          next
            show "\<not> TM.is_final (Abs_TM (p_tm l))
                  ((TM.step (Abs_TM (p_tm l)) ^^ length l)
                  (TM.initial_config (Abs_TM (p_tm l)) []))"
              unfolding TM.is_final_def final_states_l apply auto
               apply (metis Suc_n_not_le_n TM.final_steps_rev final_states_l insertI1
                  is_finalI le_add2 mult_2_right not_less_eq_eq state_suc_l states_l_al
                  sucl_steps_final zero_less_Suc)
              unfolding lm1_def apply auto unfolding funpow_swap1
              by (simp add: \<open>l \<noteq> []\<close> lm1_def state_step_1_l state_steps_empty_s)
          next
            show "TM.TM.tape_count (Abs_TM (p_tm (a # l))) =
                  TM.TM.tape_count (Abs_TM (p_tm l))"
              by (simp add: \<open>l \<noteq> []\<close> tape_count_1)
          next
            show "TM.TM.tape_count (Abs_TM (p_tm (a # l))) =
                  length (tapes ((TM.step (Abs_TM (p_tm (a # l))) ^^ length l)
                  (TM.initial_config (Abs_TM (p_tm l)) [])))"
              by (simp add: TM.run_tapes_len initial_configs_eq)
          qed
          moreover have "map (TM_abbrevs.tape_shift Shift_Left)
                         [Tape [] (Some (hd l)) (map Some (tl l))] =
                         [Tape [] None (map Some l)]" apply auto
            by (metis TM_abbrevs.tape_shift.simps(1) \<open>l \<noteq> []\<close> list.exhaust_sel
                list.simps(9))
          ultimately have "tapes ((TM.step (Abs_TM (p_tm (a#l))) ^^ (Suc (length l)))
                (TM.initial_config (Abs_TM (p_tm (a#l))) [])) =
                [Tape [] None (map Some l)]" by simp
          thus "(TM.step (Abs_TM (p_tm (a#l))) ^^ (Suc (length l)))
                (TM.initial_config (Abs_TM (p_tm (a#l))) []) =
                TM_config (Suc (Suc (Suc (length l * 2))))
                [Tape [] None (map Some l)]" by (metis TM_config.collapse state_suc_l)
        qed
        have "(TM.step (Abs_TM (p_tm (a#l))) ^^ (Suc (Suc (length l))))
              (TM.initial_config (Abs_TM (p_tm (a#l))) []) =
              TM_config (Suc (Suc (Suc (Suc (length l * 2)))))
              [Tape [] (Some a) (map Some l)]"
        proof -
          have steps_suc_suc: "(TM.step (Abs_TM (p_tm (a#l))) ^^ (Suc (Suc (length l))))
                (TM.initial_config (Abs_TM (p_tm (a#l))) []) =
                TM.step (Abs_TM (p_tm (a#l)))
                ((TM.step (Abs_TM (p_tm (a#l))) ^^ (Suc (length l)))
                (TM.initial_config (Abs_TM (p_tm (a#l))) []))" by simp
          have "a#l \<noteq> []" by simp
          have last_no_move: "TM.TM.next_move (Abs_TM (p_tm (a # l)))
                              (Suc (Suc (Suc (length l * 2)))) [None] 0 = No_Shift"
            using p_tm_def valid_al valid_tm_next_move by fastforce
          have last_write_a: "TM.TM.next_write (Abs_TM (p_tm (a # l)))
                              (Suc (Suc (Suc (length l * 2)))) [None] 0 = Some a"
            by (simp add: next_write_s)
          show "(TM.step (Abs_TM (p_tm (a#l))) ^^ (Suc (Suc (length l))))
              (TM.initial_config (Abs_TM (p_tm (a#l))) []) =
              TM_config (Suc (Suc (Suc (Suc (length l * 2)))))
              [Tape [] (Some a) (map Some l)]" unfolding steps_suc_suc al_steps_sucl
            TM.step_def apply auto
             apply (simp add: final_states_al n_not_Suc_n)
            unfolding TM.step_not_final_def Let_def apply auto
            using p_tm_def valid_al valid_tm_next_state apply fastforce
            unfolding TM.next_actions_def TM.next_writes_def TM.next_moves_def
              tape_count_1 [OF \<open>a#l \<noteq> []\<close>] apply auto
            unfolding TM_abbrevs.tape_action_def apply auto
            unfolding last_no_move last_write_a
            by (simp add: TM_abbrevs.tape_shift.simps(5) TM_abbrevs.tape_write_simps)
        qed
        hence "tapes (TM.compute (Abs_TM (p_tm (a # l))) []) =
              [Tape [] (Some a) (map Some l)]" unfolding TM.compute_def
          TM.compute_config_def TM.is_final_def final_states_al
          by (smt (verit, best) LeastI_ex TM.final_run_compute TM.is_final_def
              TM.run_def TM.time_bounded_word_def TM_config.sel(2) final_states_al
              length_Cons list.distinct(1) tb)
        hence "tapes (TM.compute (Abs_TM (p_tm (a # l))) []) =
              [TM_abbrevs.input_tape (a # l)]"
          unfolding TM_abbrevs.input_tape_def by simp
        then show "last (tapes (TM.compute (Abs_TM (p_tm (a # l))) [])) =
                   TM_abbrevs.input_tape (a # l)" by simp
      qed
    next
      case cons_w: (Cons a list)
      show "last (tapes (TM.compute (Abs_TM (p_tm p)) w)) =
                 TM_abbrevs.input_tape (p @ w)"
      proof (induct p rule: list_length_induct' [of "Suc 0"], (simp_all add: local.Cons))
        fix l :: "'s list"
        assume "length l = Suc 0"
        then obtain x :: 's where x_def: "l = [x]" using length_1_hd_iff by metis
        have compute_eq: "TM.compute (Abs_TM (p_tm [x])) w =
              (TM.step (Abs_TM (p_tm [x])) ^^ 2)
              (TM.initial_config (Abs_TM (p_tm [x])) w)"
          unfolding TM.compute_altdef TM.run_def TM.time_def TM.config_time_def
          using tb [of "[x]", simplified]
          by (metis (no_types, lifting) LeastI_ex TM.final_steps_rev TM.run_def
              TM.time_bounded_word_def numeral_2_eq_2)
        have init_config: "TM.initial_config (Abs_TM (p_tm [x])) w =
              TM_config 0 [Tape [] (Some a) (map Some list)]"
          by (simp add: TM.one_tape_initial_config TM_abbrevs.input_tape.simps(2)
              cons_w initial_state_s tape_count_1)
        have final_states_x: "TM.final_states (Abs_TM (p_tm [x])) = {2, 4}"
          by (metis (no_types, lifting) One_nat_def \<open>length l = Suc 0\<close> p_tm_def
              add_2_eq_Suc' mult_2_right not_Cons_self2 numeral_2_eq_2 numeral_Bit0
              plus_1_eq_Suc select_convs(5) valid_s valid_tm_final_states x_def)
        have tape_count_x: "TM.TM.tape_count (Abs_TM (p_tm [x])) = 1"
          by (simp add: tape_count_1)
        have one_step_config: "TM.step (Abs_TM (p_tm [x]))
                               (TM.initial_config (Abs_TM (p_tm [x])) w) =
                               TM_config 1 [Tape [] None (map Some w)]"
          unfolding init_config TM.step_def final_states_x apply auto
          unfolding TM.step_not_final_def Let_def apply auto
           apply (smt (verit, ccfv_threshold) get0 list.distinct(1) nat.simps(3)
              option.distinct(1) p_tm_def select_convs(7) valid_s valid_tm_next_state)
          unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_writes_def
            TM.next_moves_def tape_count_x cons_w apply auto
          by (smt (verit, del_insts) TM_abbrevs.tape_shift.simps(1)
              TM_abbrevs.tape_write_id \<open>length l = Suc 0\<close> get0 nat.simps(3) next_write_s
              not_Cons_self2 option.distinct(1) p_tm_def select_convs(9) tape.sel(2)
              valid_s valid_tm_next_move x_def)
        have two_step_config: "TM.step (Abs_TM (p_tm [x])) (TM.step (Abs_TM (p_tm [x]))
                               (TM.initial_config (Abs_TM (p_tm [x])) w)) =
                               TM_config 2 [Tape [] (Some x) (map Some w)]"
          unfolding one_step_config
          unfolding TM.step_def final_states_x apply auto
          unfolding TM.step_not_final_def Let_def apply auto
           apply (smt (verit, del_insts) One_nat_def Suc_n_not_le_n \<open>length l = Suc 0\<close>
              add_Suc_shift le_add2 length_0_conv mult.right_neutral mult_Suc_right
              numeral_2_eq_2 p_tm_def select_convs(7) valid_s valid_tm_next_state x_def)
          unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_writes_def
            TM.next_moves_def tape_count_x apply auto
        proof -
          have next_move_x: "TM.TM.next_move (Abs_TM (p_tm [x])) (Suc 0) [None] 0 =
                             No_Shift"
            by (smt (verit, ccfv_threshold) \<open>length l = Suc 0\<close> list.distinct(1) p_tm_def
                select_convs(9) valid_s valid_tm_next_move x_def)
          have next_write_x: "TM.TM.next_write (Abs_TM (p_tm [x])) (Suc 0) [None] 0 =
                              Some x" by (simp add: next_write_s)
          show "TM_abbrevs.tape_shift (TM.TM.next_move (Abs_TM (p_tm [x]))
                (Suc 0) [None] 0)
          (TM_abbrevs.tape_write (TM.TM.next_write (Abs_TM (p_tm [x])) (Suc 0) [None] 0)
                (Tape [] None (map Some w))) = Tape [] (Some x) (map Some w)"
            unfolding next_move_x next_write_x
            by (simp add: TM_abbrevs.tape_shift.simps(5) TM_abbrevs.tape_write_def)
        qed
        show "last (tapes (TM.compute (Abs_TM (p_tm l)) w)) =
              TM_abbrevs.input_tape (l @ w)"
          unfolding x_def compute_eq apply auto
          by (simp add: TM_abbrevs.input_tape.simps(2) numeral_2_eq_2 two_step_config)
      next
        fix b :: 's and l :: "'s list"
        assume "l \<noteq> []" and tapes_IH: "last (tapes (TM.compute (Abs_TM (p_tm l)) w)) =
           TM_abbrevs.input_tape (l @ w)"
        have initial_config_l: "TM.initial_config (Abs_TM (p_tm l)) w =
                                TM_config 0 [Tape [] (Some a) (map Some list)]"
          unfolding cons_w
          by (simp add: TM.one_tape_initial_config TM_abbrevs.input_tape.simps(2)
              \<open>l \<noteq> []\<close> initial_state_s tape_count_1)
        have initial_config_bl: "TM.initial_config (Abs_TM (p_tm (b#l))) w =
                                TM_config 0 [Tape [] (Some a) (map Some list)]"
          by (simp add: TM.one_tape_initial_config TM_abbrevs.input_tape.simps(2)
              cons_w initial_state_s tape_count_1)
        have initial_configs_eq: "TM.initial_config (Abs_TM (p_tm l)) w =
                                  TM.initial_config (Abs_TM (p_tm (b#l))) w"
          unfolding initial_config_l initial_config_bl ..
        have final_states_l: "TM.final_states (Abs_TM (p_tm l)) = {Suc (length l),
                              Suc (Suc (length l * 2))}"
          by (smt (verit, best) \<open>l \<noteq> []\<close> p_tm_def select_convs(5) valid_s
              valid_tm_final_states)
        have final_states_bl: "TM.final_states (Abs_TM (p_tm (b#l))) =
                               {Suc (Suc (length l)),
                               Suc (Suc (Suc (Suc (length l * 2))))}"
          by (metis (no_types, lifting) One_nat_def add_Suc_shift length_Cons
              list.distinct(1) mult_Suc numeral_2_eq_2 p_tm_def plus_1_eq_Suc
              select_convs(5) valid_s valid_tm_final_states)
        have valid_l: "valid_TM (p_tm l)"
          by (simp add: \<open>l \<noteq> []\<close> valid_s)
        have valid_bl: "valid_TM (p_tm (b#l))" by (simp add: valid_s)
        have steps_eq_states_l: "\<And>n. n \<le> Suc (length l) \<Longrightarrow>
                               state ((TM.step (Abs_TM (p_tm l)) ^^ n)
                               (TM.initial_config (Abs_TM (p_tm l)) w)) = n"
          by (simp add: \<open>l \<noteq> []\<close> cons_w steps_non_empty_plus_eq_s)
        have steps_eq_states_bl: "\<And>n. n \<le> Suc (length (b#l)) \<Longrightarrow>
                               state ((TM.step (Abs_TM (p_tm (b#l))) ^^ n)
                               (TM.initial_config (Abs_TM (p_tm (b#l))) w)) = n"
          by (simp add: cons_w steps_non_empty_plus_eq_s)
        have states_l_bl: "\<And>n. n \<le> Suc (length l) \<Longrightarrow>
                           state ((TM.step (Abs_TM (p_tm l)) ^^ n)
                           (TM.initial_config (Abs_TM (p_tm l)) w)) =
                           state ((TM.step (Abs_TM (p_tm (b#l))) ^^ n)
                           (TM.initial_config (Abs_TM (p_tm (b#l))) w))"
        proof -
          fix n :: nat
          show "n \<le> Suc (length l) \<Longrightarrow>
         state ((TM.step (Abs_TM (p_tm l)) ^^ n)
         (TM.initial_config (Abs_TM (p_tm l)) w)) =
         state ((TM.step (Abs_TM (p_tm (b#l))) ^^ n)
         (TM.initial_config (Abs_TM (p_tm (b#l))) w))" apply (induction n)
             apply auto unfolding initial_configs_eq apply simp
          proof -
            fix n :: nat
            assume states_IH: "state ((TM.step (Abs_TM (p_tm l)) ^^ n)
                    (TM.initial_config (Abs_TM (p_tm (b # l))) w)) =
                    state ((TM.step (Abs_TM (p_tm (b # l))) ^^ n)
                    (TM.initial_config (Abs_TM (p_tm (b # l))) w))" and
                    "n \<le> length l"
            show "state (TM.step (Abs_TM (p_tm l))
                  ((TM.step (Abs_TM (p_tm l)) ^^ n)
                  (TM.initial_config (Abs_TM (p_tm (b # l))) w))) =
                  state (TM.step (Abs_TM (p_tm (b # l)))
                  ((TM.step (Abs_TM (p_tm (b # l))) ^^ n)
                  (TM.initial_config (Abs_TM (p_tm (b # l))) w)))" unfolding cons_w
              apply (subst (1 2) TM.step_def) apply auto
              unfolding states_IH [unfolded cons_w, symmetric] apply auto
              unfolding final_states_l final_states_bl apply auto
              using steps_non_empty_plus_le_s
                  apply (metis \<open>l \<noteq> []\<close> \<open>n \<le> length l\<close> cons_w initial_configs_eq
                  list.distinct(1) not_less_eq_eq)
              apply (metis (no_types, opaque_lifting) \<open>n \<le> length l\<close> cons_w
                  initial_configs_eq le_add2 le_trans mult_2_right mult_Suc
                  mult_numeral_1_right neq_Nil_conv not_less_eq_eq
                  steps_non_empty_plus_le_s)
                apply (metis \<open>n \<le> length l\<close> cons_w initial_configs_eq list.distinct(1)
                  nat_le_linear not_less_eq_eq steps_non_empty_plus_le_s)
               apply (smt (verit, best) \<open>l \<noteq> []\<close> \<open>n \<le> length l\<close> cons_w
                  initial_configs_eq le_SucI le_add2 le_trans list.distinct(1)
                  mult_2_right not_less_eq_eq steps_non_empty_plus_le_s)
              unfolding initial_config_bl [unfolded cons_w]
            proof -
              have next_state_l: "\<And>st hds. TM.TM.next_state (Abs_TM (p_tm l))
                    st hds = (if st = 0 \<and> hds ! 0 = None then Suc (Suc (length l)) else
                    if st = Suc (length l) \<or> st = Suc (Suc (length l * 2)) then st
                    else Suc st)"
                using p_tm_def valid_l valid_tm_next_state by fastforce
              assume state_not_final_1: "state ((TM.step (Abs_TM (p_tm l)) ^^ n)
                     (TM_config 0 [Tape [] (Some a) (map Some list)])) \<noteq> Suc (length l)"
              and state_not_final_2:"state ((TM.step (Abs_TM (p_tm l)) ^^ n)
                   (TM_config 0 [Tape [] (Some a) (map Some list)])) \<noteq>
                   Suc (Suc (length l * 2))" and
                   state_not_final_3: "state ((TM.step (Abs_TM (p_tm l)) ^^ n)
                    (TM_config 0 [Tape [] (Some a) (map Some list)])) \<noteq>
                    Suc (Suc (length l))" and
                   state_not_final_4: "state ((TM.step (Abs_TM (p_tm l)) ^^ n)
                    (TM_config 0 [Tape [] (Some a) (map Some list)])) \<noteq>
                    Suc (Suc (Suc (Suc (length l * 2))))"
              moreover have "n = 0 \<Longrightarrow> heads ((TM.step (Abs_TM (p_tm l)) ^^ n)
                    (TM_config 0 [Tape [] (Some a) (map Some list)])) ! 0 \<noteq> None"
                by simp
              moreover have state_l_0_iff: "state ((TM.step (Abs_TM (p_tm l)) ^^ n)
                    (TM_config 0 [Tape [] (Some a) (map Some list)])) = 0 \<longleftrightarrow> n = 0"
                by (metis \<open>l \<noteq> []\<close> initial_config_l state_0_iff)
              hence state_0_some: "state ((TM.step (Abs_TM (p_tm l)) ^^ n)
                    (TM_config 0 [Tape [] (Some a) (map Some list)])) = 0 \<Longrightarrow>
                    heads ((TM.step (Abs_TM (p_tm l)) ^^ n)
                    (TM_config 0 [Tape [] (Some a) (map Some list)])) ! 0 = None \<Longrightarrow>
                    False" by simp
              ultimately have "TM.TM.next_state (Abs_TM (p_tm l))
                    (state ((TM.step (Abs_TM (p_tm l)) ^^ n)
                    (TM_config 0 [Tape [] (Some a) (map Some list)])))
                    (heads ((TM.step (Abs_TM (p_tm l)) ^^ n)
                    (TM_config 0 [Tape [] (Some a) (map Some list)]))) = Suc n"
                unfolding next_state_l apply (cases n) apply simp
                unfolding state_l_0_iff apply safe
                by (metis \<open>l \<noteq> []\<close> \<open>n \<le> length l\<close> cons_w initial_config_l le_SucI
                    list.discI steps_non_empty_plus_eq_s)
              moreover have "TM.TM.next_state (Abs_TM (p_tm (b # l)))
                    (state ((TM.step (Abs_TM (p_tm l)) ^^ n)
                    (TM_config 0 [Tape [] (Some a) (map Some list)])))
                    (heads ((TM.step (Abs_TM (p_tm (b # l))) ^^ n)
                    (TM_config 0 [Tape [] (Some a) (map Some list)]))) = Suc n"
                by (smt (verit, best) One_nat_def TM.step_final TM.step_not_final
                    TM.step_not_final_simps(1) state_0_some \<open>n \<le> length l\<close>
                    states_IH [unfolded cons_w, symmetric] state_not_final_4
                    state_not_final_3 add_Suc_shift cons_w funpow_0 initial_config_bl
                    le_Suc_eq length_Cons list.distinct(1) mult_Suc n_not_Suc_n
                    numeral_2_eq_2 plus_1_eq_Suc state_step_s state_step_s2
                    steps_non_empty_plus_eq_s)
              ultimately show "TM.TM.next_state (Abs_TM (p_tm l))
                    (state ((TM.step (Abs_TM (p_tm l)) ^^ n)
                    (TM_config 0 [Tape [] (Some a) (map Some list)])))
                    (heads ((TM.step (Abs_TM (p_tm l)) ^^ n)
                    (TM_config 0 [Tape [] (Some a) (map Some list)]))) =
                    TM.TM.next_state (Abs_TM (p_tm (b # l)))
                    (state ((TM.step (Abs_TM (p_tm l)) ^^ n)
                    (TM_config 0 [Tape [] (Some a) (map Some list)])))
                    (heads ((TM.step (Abs_TM (p_tm (b # l))) ^^ n)
                    (TM_config 0 [Tape [] (Some a) (map Some list)])))" by simp
            qed
          qed
        qed
        have tapes_l_bl: "\<And>n. n \<le> length l \<Longrightarrow>
                          tapes ((TM.step (Abs_TM (p_tm l)) ^^ n)
                          (TM.initial_config (Abs_TM (p_tm l)) w)) =
                          tapes ((TM.step (Abs_TM (p_tm (b#l))) ^^ n)
                          (TM.initial_config (Abs_TM (p_tm (b#l))) w))"
        proof -
          fix n :: nat
          show "n \<le> length l \<Longrightarrow> tapes ((TM.step (Abs_TM (p_tm l)) ^^ n)
                (TM.initial_config (Abs_TM (p_tm l)) w)) =
                tapes ((TM.step (Abs_TM (p_tm (b#l))) ^^ n)
                (TM.initial_config (Abs_TM (p_tm (b#l))) w))"
            apply (induction n)
             apply (auto simp add: initial_configs_eq)
            apply (rule same_tps_shift_write2)
                 apply simp
          proof -
            fix n k :: nat
            assume "tapes ((TM.step (Abs_TM (p_tm l)) ^^ n)
                    (TM.initial_config (Abs_TM (p_tm (b # l))) w)) =
                    tapes ((TM.step (Abs_TM (p_tm (b # l))) ^^ n)
                    (TM.initial_config (Abs_TM (p_tm (b # l))) w))" and
                    "Suc n \<le> length l" and
                    k_lt_tpc: "k < TM.TM.tape_count (Abs_TM (p_tm l))"
            hence n_le_suc_l: "n \<le> Suc (length l)" by simp
            hence n_le_suc_bl: "n \<le> Suc (length (b#l))" by simp
            have k0: "k = 0" using k_lt_tpc by (simp add: \<open>l \<noteq> []\<close> tape_count_1)
            have "n = 0 \<Longrightarrow> TM.TM.next_write (Abs_TM (p_tm l))
                  (state ((TM.step (Abs_TM (p_tm l)) ^^ n)
                  (TM.initial_config (Abs_TM (p_tm (b # l))) w)))
                  (heads ((TM.step (Abs_TM (p_tm l)) ^^ n)
                  (TM.initial_config (Abs_TM (p_tm (b # l))) w))) k = Some a"
              unfolding k0 steps_eq_states_l [OF n_le_suc_l, unfolded initial_configs_eq]
              apply auto
              by (simp add: TM.initial_config_heads_0 \<open>l \<noteq> []\<close> cons_w next_write_s)
            moreover have "n = 0 \<Longrightarrow> TM.TM.next_write (Abs_TM (p_tm (b # l)))
                           (state ((TM.step (Abs_TM (p_tm (b # l))) ^^ n)
                           (TM.initial_config (Abs_TM (p_tm (b # l))) w)))
                           (heads ((TM.step (Abs_TM (p_tm (b # l))) ^^ n)
                           (TM.initial_config (Abs_TM (p_tm (b # l))) w))) k = Some a"
              unfolding k0 steps_eq_states_bl [OF n_le_suc_bl] apply auto
              by (simp add: initial_config_bl next_write_s)
            moreover have "n \<noteq> 0 \<Longrightarrow> TM.TM.next_write (Abs_TM (p_tm l))
                  (state ((TM.step (Abs_TM (p_tm l)) ^^ n)
                  (TM.initial_config (Abs_TM (p_tm (b # l))) w)))
                  (heads ((TM.step (Abs_TM (p_tm l)) ^^ n)
                  (TM.initial_config (Abs_TM (p_tm (b # l))) w))) k =
                  Some (l ! (length l - n))"
              using \<open>l \<noteq> []\<close> initial_configs_eq n_le_suc_l next_write_s
                steps_eq_states_l by presburger
            moreover have "n \<noteq> 0 \<Longrightarrow> TM.TM.next_write (Abs_TM (p_tm (b # l)))
                           (state ((TM.step (Abs_TM (p_tm (b # l))) ^^ n)
                           (TM.initial_config (Abs_TM (p_tm (b # l))) w)))
                           (heads ((TM.step (Abs_TM (p_tm (b # l))) ^^ n)
                           (TM.initial_config (Abs_TM (p_tm (b # l))) w))) k =
                           Some ((b#l) ! (length (b#l) - n))"
              using n_le_suc_bl next_write_s steps_eq_states_bl by auto
            hence "n \<noteq> 0 \<Longrightarrow> TM.TM.next_write (Abs_TM (p_tm (b # l)))
                           (state ((TM.step (Abs_TM (p_tm (b # l))) ^^ n)
                           (TM.initial_config (Abs_TM (p_tm (b # l))) w)))
                           (heads ((TM.step (Abs_TM (p_tm (b # l))) ^^ n)
                           (TM.initial_config (Abs_TM (p_tm (b # l))) w))) k =
                           Some (l ! (length l - n))"
              using \<open>Suc n \<le> length l\<close> by auto
            ultimately show "TM.TM.next_write (Abs_TM (p_tm l))
                  (state ((TM.step (Abs_TM (p_tm l)) ^^ n)
                  (TM.initial_config (Abs_TM (p_tm (b # l))) w)))
                  (heads ((TM.step (Abs_TM (p_tm l)) ^^ n)
                  (TM.initial_config (Abs_TM (p_tm (b # l))) w))) k =
                  TM.TM.next_write (Abs_TM (p_tm (b # l)))
                  (state ((TM.step (Abs_TM (p_tm (b # l))) ^^ n)
                  (TM.initial_config (Abs_TM (p_tm (b # l))) w)))
                  (heads ((TM.step (Abs_TM (p_tm (b # l))) ^^ n)
                  (TM.initial_config (Abs_TM (p_tm (b # l))) w))) k" by metis
          next
            fix n k :: nat
            assume "tapes ((TM.step (Abs_TM (p_tm l)) ^^ n)
                    (TM.initial_config (Abs_TM (p_tm (b # l))) w)) =
                    tapes ((TM.step (Abs_TM (p_tm (b # l))) ^^ n)
                    (TM.initial_config (Abs_TM (p_tm (b # l))) w))" and
                   "Suc n \<le> length l" and "k < TM.TM.tape_count (Abs_TM (p_tm (b # l)))"
            hence k0: "k = 0" by (simp add: tape_count_1)
            have n_le_suc_l: "n \<le> Suc (length l)" using \<open>Suc n \<le> length l\<close> by auto
            hence n_le_suc_bl: "n \<le> Suc (length (b#l))" by simp
            have "n = 0 \<Longrightarrow> TM.TM.next_move (Abs_TM (p_tm l))
                  (state ((TM.step (Abs_TM (p_tm l)) ^^ n)
                  (TM.initial_config (Abs_TM (p_tm (b # l))) w)))
                  (heads ((TM.step (Abs_TM (p_tm l)) ^^ n)
                  (TM.initial_config (Abs_TM (p_tm (b # l))) w))) k = Shift_Left"
              unfolding k0 cons_w steps_eq_states_l [OF n_le_suc_l,
                  unfolded initial_configs_eq, unfolded cons_w] apply auto
              using \<open>l \<noteq> []\<close> cons_w initial_config_bl p_tm_def valid_l
                valid_tm_next_move by fastforce
            moreover have "n = 0 \<Longrightarrow> TM.TM.next_move (Abs_TM (p_tm (b # l)))
                  (state ((TM.step (Abs_TM (p_tm (b # l))) ^^ n)
                  (TM.initial_config (Abs_TM (p_tm (b # l))) w)))
                  (heads ((TM.step (Abs_TM (p_tm (b # l))) ^^ n)
                  (TM.initial_config (Abs_TM (p_tm (b # l))) w))) k = Shift_Left"
              unfolding k0 cons_w apply auto
              using cons_w initial_config_bl p_tm_def valid_bl
                valid_tm_next_move by fastforce
            moreover have "n \<noteq> 0 \<Longrightarrow> TM.TM.next_move (Abs_TM (p_tm l))
                  (state ((TM.step (Abs_TM (p_tm l)) ^^ n)
                  (TM.initial_config (Abs_TM (p_tm (b # l))) w)))
                  (heads ((TM.step (Abs_TM (p_tm l)) ^^ n)
                  (TM.initial_config (Abs_TM (p_tm (b # l))) w))) k = Shift_Left"
              unfolding steps_eq_states_l [OF n_le_suc_l, unfolded initial_configs_eq]
              using \<open>Suc n \<le> length l\<close> p_tm_def valid_l valid_tm_next_move by fastforce
            moreover have "n \<noteq> 0 \<Longrightarrow> TM.TM.next_move (Abs_TM (p_tm (b # l)))
                  (state ((TM.step (Abs_TM (p_tm (b # l))) ^^ n)
                  (TM.initial_config (Abs_TM (p_tm (b # l))) w)))
                  (heads ((TM.step (Abs_TM (p_tm (b # l))) ^^ n)
                  (TM.initial_config (Abs_TM (p_tm (b # l))) w))) k = Shift_Left"
              unfolding steps_eq_states_bl [OF n_le_suc_bl] k0
              using \<open>Suc n \<le> length l\<close> p_tm_def valid_bl valid_tm_next_move by fastforce
            ultimately show "TM.TM.next_move (Abs_TM (p_tm l))
                  (state ((TM.step (Abs_TM (p_tm l)) ^^ n)
                  (TM.initial_config (Abs_TM (p_tm (b # l))) w)))
                  (heads ((TM.step (Abs_TM (p_tm l)) ^^ n)
                  (TM.initial_config (Abs_TM (p_tm (b # l))) w))) k =
                  TM.TM.next_move (Abs_TM (p_tm (b # l)))
                  (state ((TM.step (Abs_TM (p_tm (b # l))) ^^ n)
                  (TM.initial_config (Abs_TM (p_tm (b # l))) w)))
                  (heads ((TM.step (Abs_TM (p_tm (b # l))) ^^ n)
                  (TM.initial_config (Abs_TM (p_tm (b # l))) w))) k" by metis
          next
            fix n :: nat
            assume "tapes ((TM.step (Abs_TM (p_tm l)) ^^ n)
                    (TM.initial_config (Abs_TM (p_tm (b # l))) w)) =
                    tapes ((TM.step (Abs_TM (p_tm (b # l))) ^^ n)
                    (TM.initial_config (Abs_TM (p_tm (b # l))) w))" and
                   "Suc n \<le> length l"
            have "\<not>TM.is_final (Abs_TM (p_tm l)) ((TM.step (Abs_TM (p_tm l)) ^^ n)
                  (TM.initial_config (Abs_TM (p_tm (b # l))) w))"
              by (smt (verit, ccfv_threshold) Suc_n_not_le_n TM.final_le_steps
                  \<open>Suc n \<le> length l\<close> initial_configs_eq nat_le_linear
                  steps_eq_states_l)
            moreover have "\<not>TM.is_final (Abs_TM (p_tm (b # l)))
                  ((TM.step (Abs_TM (p_tm (b # l))) ^^ n)
                  (TM.initial_config (Abs_TM (p_tm (b # l))) w))"
              by (smt (verit) TM.final_le_steps \<open>Suc n \<le> length l\<close> cons_w le_add2
                  list.distinct(1) not_less_eq_eq plus_1_eq_Suc states_l_bl
                  steps_eq_states_l steps_non_empty_plus_le_s)
            ultimately show "TM.is_final (Abs_TM (p_tm l))
                  ((TM.step (Abs_TM (p_tm l)) ^^ n)
                  (TM.initial_config (Abs_TM (p_tm (b # l))) w)) =
                  TM.is_final (Abs_TM (p_tm (b # l)))
                  ((TM.step (Abs_TM (p_tm (b # l))) ^^ n)
                  (TM.initial_config (Abs_TM (p_tm (b # l))) w))" by simp
          next
            show "TM.TM.tape_count (Abs_TM (p_tm l)) =
                  TM.TM.tape_count (Abs_TM (p_tm (b # l)))"
              by (simp add: \<open>l \<noteq> []\<close> tape_count_1)
          next
            show "\<And>n. TM.TM.tape_count (Abs_TM (p_tm l)) =
                  length (tapes ((TM.step (Abs_TM (p_tm l)) ^^ n)
                  (TM.initial_config (Abs_TM (p_tm (b # l))) w)))"
              by (metis TM.run_tapes_len initial_configs_eq)
          qed
        qed
        have suc_l_shl: "map (TM_abbrevs.tape_shift Shift_Left)
              (tapes ((TM.step (Abs_TM (p_tm l)) ^^ (Suc (length l)))
              (TM.initial_config (Abs_TM (p_tm l)) w))) =
              tapes ((TM.step (Abs_TM (p_tm (b#l))) ^^ (Suc (length l)))
              (TM.initial_config (Abs_TM (p_tm (b#l))) w))"
          apply (rule sym)
          unfolding initial_configs_eq [symmetric]
          apply auto
          apply (rule tps_same_write_left_no_shift)
          using initial_configs_eq tapes_l_bl apply auto[1]
        proof -
          fix k :: nat
          have "TM.TM.next_write (Abs_TM (p_tm (b # l)))
                (state ((TM.step (Abs_TM (p_tm (b # l))) ^^ length l)
                (TM.initial_config (Abs_TM (p_tm l)) w)))
                (heads ((TM.step (Abs_TM (p_tm (b # l))) ^^ length l)
                (TM.initial_config (Abs_TM (p_tm l)) w))) k = Some (hd l)"
            by (smt (z3) Suc_le_length_iff \<open>l \<noteq> []\<close> add_Suc_right add_Suc_shift
                diff_is_0_eq getSub initial_configs_eq le_add1 length_0_conv length_Cons
                length_Suc0_not_empty lessI less_iff_Suc_add list.distinct(1)
                list.sel(1) next_write_s nth_Cons_0 states_l_bl steps_eq_states_l)
          moreover have "TM.TM.next_write (Abs_TM (p_tm l))
                         (state ((TM.step (Abs_TM (p_tm l)) ^^ length l)
                         (TM.initial_config (Abs_TM (p_tm l)) w)))
                         (heads ((TM.step (Abs_TM (p_tm l)) ^^ length l)
                         (TM.initial_config (Abs_TM (p_tm l)) w))) k = Some (hd l)"
            using \<open>l \<noteq> []\<close> calculation initial_configs_eq next_write_s states_l_bl
              steps_eq_states_l by force
          ultimately show "TM.TM.next_write (Abs_TM (p_tm (b # l)))
                (state ((TM.step (Abs_TM (p_tm (b # l))) ^^ length l)
                (TM.initial_config (Abs_TM (p_tm l)) w)))
                (heads ((TM.step (Abs_TM (p_tm (b # l))) ^^ length l)
                (TM.initial_config (Abs_TM (p_tm l)) w))) k =
                TM.TM.next_write (Abs_TM (p_tm l))
                (state ((TM.step (Abs_TM (p_tm l)) ^^ length l)
                (TM.initial_config (Abs_TM (p_tm l)) w)))
                (heads ((TM.step (Abs_TM (p_tm l)) ^^ length l)
                (TM.initial_config (Abs_TM (p_tm l)) w))) k" by simp
        next
          fix k :: nat
          show "TM.TM.next_move (Abs_TM (p_tm (b # l)))
                (state ((TM.step (Abs_TM (p_tm (b # l))) ^^ length l)
                (TM.initial_config (Abs_TM (p_tm l)) w)))
                (heads ((TM.step (Abs_TM (p_tm (b # l))) ^^ length l)
                (TM.initial_config (Abs_TM (p_tm l)) w))) k = Shift_Left"
            using \<open>l \<noteq> []\<close> initial_configs_eq p_tm_def steps_eq_states_bl valid_bl
              valid_tm_next_move by fastforce
        next
          fix k :: nat
          show "TM.TM.next_move (Abs_TM (p_tm l))
                (state ((TM.step (Abs_TM (p_tm l)) ^^ length l)
                (TM.initial_config (Abs_TM (p_tm l)) w)))
                (heads ((TM.step (Abs_TM (p_tm l)) ^^ length l)
                (TM.initial_config (Abs_TM (p_tm l)) w))) k = No_Shift"
            using p_tm_def steps_eq_states_l valid_l valid_tm_next_move by fastforce
        next
          show "\<not> TM.is_final (Abs_TM (p_tm (b # l)))
                ((TM.step (Abs_TM (p_tm (b # l))) ^^ length l)
                (TM.initial_config (Abs_TM (p_tm l)) w))"
            by (metis TM.final_le_steps initial_configs_eq le_eq_less_or_eq n_not_Suc_n
                states_l_bl steps_eq_states_l suc_is_ge)
        next
          show "\<not> TM.is_final (Abs_TM (p_tm l))
                ((TM.step (Abs_TM (p_tm l)) ^^ length l)
                (TM.initial_config (Abs_TM (p_tm l)) w))"
            by (metis TM.final_le_steps add_cancel_left_left le_refl plus_1_eq_Suc
                steps_eq_states_l suc_is_ge zero_neq_one)
        next
          show "TM.TM.tape_count (Abs_TM (p_tm (b # l))) =
                TM.TM.tape_count (Abs_TM (p_tm l))" by (simp add: \<open>l \<noteq> []\<close> tape_count_1)
        next
          show "TM.TM.tape_count (Abs_TM (p_tm (b # l))) =
                length (tapes ((TM.step (Abs_TM (p_tm (b # l))) ^^ length l)
                (TM.initial_config (Abs_TM (p_tm l)) w)))"
            by (simp add: TM.run_tapes_len initial_configs_eq)
        qed
        have "tapes ((TM.step (Abs_TM (p_tm (b#l))) ^^ (Suc (length l)))
               (TM.initial_config (Abs_TM (p_tm (b#l))) w)) =
               [Tape [] None (map Some (l @ w))]"
        proof -
          obtain h :: 's and t :: "'s list" where ht_def: "l = h#t"
            by (metis \<open>l \<noteq> []\<close> neq_Nil_conv)
          have Least_final: "(LEAST n. TM.is_final (Abs_TM (p_tm l))
                             ((TM.step (Abs_TM (p_tm l)) ^^ n)
                             (TM.initial_config (Abs_TM (p_tm l)) w))) = Suc (length l)"
            apply (rule Least_natI)
             apply (metis TM.run_def TM.time_bounded_wordD \<open>l \<noteq> []\<close> tb)
          proof -
            fix n :: nat
            assume "n < Suc (length l)"
            moreover from this have "state ((TM.step (Abs_TM (p_tm l)) ^^ n)
                   (TM.initial_config (Abs_TM (p_tm l)) w)) = n"
              by (simp add: steps_eq_states_l)
            ultimately show "\<not> TM.is_final (Abs_TM (p_tm l))
                             ((TM.step (Abs_TM (p_tm l)) ^^ n)
                             (TM.initial_config (Abs_TM (p_tm l)) w))"
              by (metis TM.final_le_steps add_le_imp_le_left add_right_mono
                  le_numeral_extra(4) nless_le steps_eq_states_l)
          qed
          have "tapes ((TM.step (Abs_TM (p_tm l)) ^^ (Suc (length l)))
               (TM.initial_config (Abs_TM (p_tm l)) w)) =
               [Tape [] (Some h) (map Some (t @ w))]"
            using tapes_IH [unfolded TM.compute_def TM.compute_config_def]
            unfolding ht_def Least_final [unfolded ht_def]
            by (metis One_nat_def TM.run_tapes_len TM_abbrevs.input_tape.simps(2)
                \<open>l \<noteq> []\<close> append_Cons ht_def length_1_last_iff tape_count_1)
          thus "tapes ((TM.step (Abs_TM (p_tm (b#l))) ^^ (Suc (length l)))
               (TM.initial_config (Abs_TM (p_tm (b#l))) w)) =
               [Tape [] None (map Some (l @ w))]"
            by (metis TM_abbrevs.tape_shift.simps(1) append_Cons ht_def list.simps(8)
                list.simps(9) suc_l_shl)
        qed
        hence suc_l_bl: "(TM.step (Abs_TM (p_tm (b#l))) ^^ (Suc (length l)))
               (TM.initial_config (Abs_TM (p_tm (b#l))) w) =
               TM_config (Suc (length l)) [Tape [] None (map Some (l @ w))]"
          by (metis TM_config.collapse le_add2 length_Cons plus_1_eq_Suc
              steps_eq_states_bl)
        have "tapes ((TM.step (Abs_TM (p_tm (b#l))) ^^ (Suc (Suc (length l))))
              (TM.initial_config (Abs_TM (p_tm (b#l))) w)) =
              [Tape [] (Some b) (map Some (l @ w))]"
        proof -
          have last_write_bl: "\<And>hds. TM.next_write (Abs_TM (p_tm (b#l)))
                (state ((TM.step (Abs_TM (p_tm (b#l))) ^^ (Suc (length l)))
                (TM.initial_config (Abs_TM (p_tm (b#l))) w))) hds 0 = Some b"
            by (metis cancel_comm_monoid_add_class.diff_cancel get0 le_add2 length_Cons
                list.distinct(1) nat.simps(3) next_write_s plus_1_eq_Suc
                steps_eq_states_bl)
          have last_move_bl: "\<And>hds. TM.next_move (Abs_TM (p_tm (b#l)))
                (state ((TM.step (Abs_TM (p_tm (b#l))) ^^ (Suc (length l)))
                (TM.initial_config (Abs_TM (p_tm (b#l))) w))) hds 0 = No_Shift"
            by (smt (verit, del_insts) Suc_n_not_le_n length_Cons not_less_eq_eq
                p_tm_def select_convs(9) states_l_bl steps_eq_states_l valid_bl
                valid_tm_next_move)
          have non_final_bl: "\<not>TM.is_final (Abs_TM (p_tm (b#l)))
                ((TM.step (Abs_TM (p_tm (b#l))) ^^ (Suc (length l)))
                (TM.initial_config (Abs_TM (p_tm (b#l))) w))"
            by (metis TM.final_le_steps le_add2 le_refl length_Cons n_not_Suc_n
                plus_1_eq_Suc steps_eq_states_bl)
          have final_bl: "TM.is_final (Abs_TM (p_tm (b#l)))
                ((TM.step (Abs_TM (p_tm (b#l))) ^^ (Suc (Suc (length l))))
                (TM.initial_config (Abs_TM (p_tm (b#l))) w))"
            by (metis Suc_n_not_le_n final_states_bl insertI1 is_finalI length_Cons
                not_less_eq_eq steps_eq_states_bl)
          have bl_not_empty: "b#l \<noteq> []" by simp
          have suc_l_le: "Suc (length l) \<le> Suc (length (b#l))" by simp
          show "tapes ((TM.step (Abs_TM (p_tm (b#l))) ^^ (Suc (Suc (length l))))
                (TM.initial_config (Abs_TM (p_tm (b#l))) w)) =
                [Tape [] (Some b) (map Some (l @ w))]" apply auto
            unfolding suc_l_bl [simplified]
            unfolding TM.step_def apply auto
             apply (metis TM_config.sel(1) is_finalI non_final_bl suc_l_bl)
            unfolding TM.next_actions_def TM.next_writes_def TM.next_moves_def
            tape_count_1 [OF bl_not_empty] apply auto
            unfolding last_write_bl [unfolded steps_eq_states_bl [OF suc_l_le]]
              last_move_bl [unfolded steps_eq_states_bl [OF suc_l_le]]
              TM_abbrevs.tape_action_def apply auto
            unfolding TM_abbrevs.tape_shift.simps(5)
              by (rule TM_abbrevs.tape_write_simps)
        qed
        thus "last (tapes (TM.compute (Abs_TM (p_tm (b # l))) w)) =
           TM_abbrevs.input_tape (b # l @ w)"
          by (metis One_nat_def TM.compute_run_eqI TM.run_def
              TM_abbrevs.input_tape.simps(2) add_Suc_shift final_states_bl insertI1
              is_finalI last_ConsL le_add2 length_Cons plus_1_eq_Suc steps_eq_states_bl)
      qed
    qed
  qed
  ultimately have "(\<forall>w\<in>syms*. TM.computes_word (Abs_TM (p_tm p)) w (p @ w)) \<and>
             (\<forall>w. TM.time_bounded_word (Abs_TM (p_tm p))
             (\<lambda>_. Suc (length p)) w)" using Cons by blast
  moreover have "TM.TM.tape_count (Abs_TM (p_tm p)) = 1"
    using tape_count_1 Cons by simp
  moreover have "TM.symbols (Abs_TM (p_tm p)) = syms \<union> set p"
    unfolding valid_tm_symbols [OF p_valid] unfolding p_tm_def by auto
  ultimately show "\<exists>tm::(nat, 's) TM_decider.
            (\<forall>w\<in>syms*. TM.computes_word tm w (p @ w)) \<and>
            (\<forall>w. TM.time_bounded_word tm (\<lambda>_. Suc (length p)) w) \<and>
            TM.tape_count tm = 1 \<and> TM.symbols tm = syms \<union> set p" by auto
qed

lemma add_const_prefix_finite:
  fixes p :: "('s::finite) list"
  shows "\<exists>tm::(nat, 's) TM_decider. TM.computes tm ((@) p) \<and>
                        TM.time_bounded tm (\<lambda>_. Suc (length p)) \<and>
                        TM.tape_count tm = 1 \<and> TM.symbols tm = UNIV"
proof -
  have "finite (UNIV::'s set)" by simp
  moreover have "(UNIV::'s set) \<noteq> {}" by simp
  ultimately have "\<exists>tm::(nat, 's) TM_decider.
                   (\<forall>w\<in>(UNIV::'s set)*. TM.computes_word tm w (p@w)) \<and>
                   TM.time_bounded tm (\<lambda>_. Suc (length p)) \<and>
                   TM.tape_count tm = 1 \<and> TM.symbols tm = UNIV \<union> set p"
    by (rule add_const_prefix)
  thus ?thesis by (simp add: TM.computes_def)
qed

lemma add_const_prefix_computable: "computable_in_time
       (\<lambda>_. Suc (length (p::('s::finite) list))) ((@) p)"
  apply (rule typed_comp_in_time_natI)
  using add_const_prefix_finite unfolding typed_computable_in_time_def by blast

lemma word_empty_decidable: "finite (alphabet L) \<Longrightarrow>
      (\<And>w. set w \<subseteq> alphabet L \<Longrightarrow> w \<in>\<^sub>L L \<longleftrightarrow> w = []) \<Longrightarrow> L \<in> DTIME (\<lambda>_. 1)"
proof
  assume a1: "finite (alphabet L)" and a2: "\<And>w. set w \<subseteq> alphabet L \<Longrightarrow> w \<in>\<^sub>L L \<longleftrightarrow> w = []"
  define M :: "(nat, 'a, bool) TM_record" where
    "M \<equiv> TM 1 (alphabet L \<union> {undefined}) {0..2} 0 {1, 2}
          (\<lambda>st. if st = 1 then True else False)
          (\<lambda>st hds. if hds ! 0 = None then 1 else 2)
          (\<lambda>_ _ _. None)
          (\<lambda>_ _ _. No_Shift)"
  have valid_M [intro, simp]: "valid_TM M"
    apply standard
    unfolding M_def by auto fact
  show alphabet_subset: "alphabet L \<subseteq> TM.TM.symbols (Abs_TM M)"
    unfolding valid_tm_symbols [OF valid_M] unfolding M_def by auto
  show tb [THEN spec, THEN mp]: "\<forall>w. set w \<subseteq> TM.TM.symbols (Abs_TM M) \<longrightarrow>
        TM.time_bounded_word (Abs_TM M) (\<lambda>_. 1) w" apply auto
    unfolding TM.time_bounded_word_def TM.is_final_def TM.run_def
      valid_tm_final_states [OF valid_M] apply simp
    unfolding TM.step_def apply auto
    unfolding valid_tm_final_states [OF valid_M] apply assumption
    unfolding valid_tm_next_state [OF valid_M] TM.initial_config_def apply simp
    unfolding TM_abbrevs.input_tape_def valid_tm_initial_state [OF valid_M] apply auto
    unfolding M_def by simp_all
  have 1: "\<And>w. (LEAST n. TM.is_final (Abs_TM M)
           ((TM.step (Abs_TM M) ^^ n) (TM.initial_config (Abs_TM M) w))) = 1"
    apply standard
     apply auto
    unfolding TM.step_def TM.is_final_def valid_tm_final_states [OF valid_M]
     apply (auto simp add: valid_tm_next_state [OF valid_M] TM.initial_config_def
        TM_abbrevs.input_tape_def valid_tm_initial_state [OF valid_M]
        valid_tm_tape_count [OF valid_M])
      apply (subst (1 2 4) M_def)
      apply simp
     apply (subst (1 2 4) M_def)
     apply simp
    unfolding M_def by simp
  show "alphabet L \<subseteq> TM.TM.symbols (Abs_TM M) \<and>
        (\<forall>w\<in>(alphabet L)*. TM_decider.decides_word (Abs_TM M) L w)"
    apply standard
     apply fact
    apply auto
    unfolding TM_decider.decides_def a2
  proof auto
    show "TM_decider.accepts (Abs_TM M) []"
      unfolding TM_decider.accepts_def TM.compute_def TM_decider.acc_def
        TM.compute_config_def apply (auto simp add: 1)
      using tb [of "[]", simplified] unfolding TM.time_bounded_word_def TM.is_final_def
        TM.run_def apply simp
      unfolding valid_tm_label [OF valid_M] TM.step_def apply auto
      unfolding valid_tm_final_states [OF valid_M] apply (simp add: TM.initial_config_def
          valid_tm_initial_state)
       apply (subst (asm) (1 2) M_def)
       apply simp
      unfolding valid_tm_next_state [OF valid_M] TM.initial_config_def apply simp
      unfolding TM_abbrevs.input_tape_def valid_tm_initial_state [OF valid_M]
      valid_tm_tape_count [OF valid_M] apply simp
      unfolding M_def by simp
    thus "TM_decider.rejects (Abs_TM M) [] \<Longrightarrow> False"
      using TM_decider.rejects_accepts by blast
    fix w :: "'a list"
    assume a3: "set w \<subseteq> alphabet L"
    show "TM_decider.accepts (Abs_TM M) w \<Longrightarrow> w = []"
      unfolding TM_decider.accepts_def TM.compute_def TM.compute_config_def
        1 TM_decider.acc_def apply auto
      unfolding TM.step_def valid_tm_final_states [OF valid_M]
      apply (cases "state (TM.initial_config (Abs_TM M) w) \<in> final_states M")
       apply auto
       apply (simp add: TM.initial_config_def valid_tm_initial_state)
       apply (subst (asm) (3 4) M_def) apply simp
      unfolding valid_tm_next_state [OF valid_M] TM.initial_config_def
        TM_abbrevs.input_tape_def apply simp
      apply (cases "w = []")
       apply (auto simp add: valid_tm_tape_count valid_tm_initial_state valid_tm_label)
      unfolding M_def by simp
    thus "w \<noteq> [] \<Longrightarrow> TM_decider.rejects (Abs_TM M) w"
      by (meson TM.halts_altdef TM.time_bounded_word_def TM_decider.rejects_accepts
          alphabet_subset a3 dual_order.trans tb)
  qed
qed

lemma identity_function_computable: "typed_computable_in_time TYPE('q) TYPE('l) T
                                     (id::('s::finite) list \<Rightarrow> 's list)"
proof (unfold typed_computable_in_time_def)
  define M :: "('q, 's, 'l) TM_record" where
    "M \<equiv> halting_TM_rec undefined UNIV undefined"
  have M_valid: "valid_TM M"
    unfolding M_def apply (rule halting_TM_valid)
    by simp_all
  have [simp]: "\<And>w. (LEAST n. TM.is_final (Abs_TM M)
                ((TM.step (Abs_TM M) ^^ n) (TM.initial_config (Abs_TM M) w))) = 0"
    apply standard
     apply auto
    unfolding TM.is_final_def TM.initial_config_def apply simp
    unfolding valid_tm_initial_state [OF M_valid] valid_tm_final_states [OF M_valid]
    unfolding M_def halting_TM_rec_def by simp
  have "TM.TM.symbols (Abs_TM M) = UNIV" unfolding valid_tm_symbols [OF M_valid]
    unfolding M_def halting_TM_rec_def by simp
  moreover have 1: "\<And>w. TM.time_bounded_word (Abs_TM M) (\<lambda>_. 0) w"
    unfolding TM.time_bounded_word_def TM.is_final_def TM.run_def apply simp
    unfolding TM.initial_config_def apply simp
    unfolding valid_tm_initial_state [OF M_valid] valid_tm_final_states [OF M_valid]
    unfolding M_def halting_TM_rec_def by simp
  hence "\<And>w. TM.time_bounded_word (Abs_TM M) T w" by (rule TM.time_bounded_word_mono) simp
  moreover have "TM.computes (Abs_TM M) id"
    unfolding TM.computes_def apply auto
    unfolding TM.computes_word_def apply auto
    using 1 TM.time_bounded_altdef2 apply blast
    unfolding TM.compute_def TM.compute_config_def apply auto
    unfolding TM.has_output_def TM.initial_config_def TM_abbrevs.input_tape_def
      TM.clean_output_of_def apply auto
       apply (simp add: TM.output_of_def)
    apply (metis TM.clean_outputI TM_abbrevs.input_tape.simps(1) TM_config.sel(2) last.simps
        last_replicate replicate_empty)
    unfolding TM.clean_output_def TM.output_of_def apply auto
       apply (smt (verit, best) TM_abbrevs.input_tape.cases list.sel(1,3) map_takeWhile
        option.sel takeWhile_eq_all_conv those_map_Some)
    unfolding valid_tm_tape_count [OF M_valid]
      apply (subst M_def)
    unfolding halting_TM_rec_def apply simp
    by (metis TM_abbrevs.input_tape_def)+
  ultimately show "\<exists>M::('q, 's, 'l) TM. TM.computes M id \<and>
                   (\<forall>w. TM.time_bounded_word M T w) \<and> TM.TM.symbols M = UNIV" by blast
qed

lemma rev_computable: "computable_in_time (\<lambda>n. n + 1) (rev::('a::finite) list \<Rightarrow> 'a list)"
proof (rule typed_comp_in_time_natI)
  define M :: "(nat \<times> 'a option, 'a, unit) TM_record" where
    "M \<equiv> TM 2 UNIV ({1,2,3} \<times> UNIV) (1, None) ({3} \<times> UNIV) (\<lambda>_. ())
         (\<lambda>st hds. if hds ! 0 = None then (3, snd st) else (2, hds ! 0))
         (\<lambda>st hds k. if k = 0 then hds ! 0 else if fst st = 1 then hds ! 1 else snd st)
         (\<lambda>st hds k. if k = 0 then Shift_Right else if fst st = 1 \<or> hds ! 0 = None then No_Shift else Shift_Left)"
  have valid_M [simp, intro]: "valid_TM M"
    apply standard
    unfolding M_def by auto
  show "typed_computable_in_time TYPE(nat \<times> 'a option) TYPE(unit) (\<lambda>n. n + 1)
        (rev::('a::finite) list \<Rightarrow> 'a list)"
  proof (unfold typed_computable_in_time_def, rule exI, auto)
    show "\<And>x. x \<in> TM.symbols (Abs_TM M)" by (simp add: valid_tm_symbols) (simp add: M_def)
    have f11: "state (TM.step (Abs_TM M) (TM.initial_config (Abs_TM M) w)) = (2, Some (hd w))" and
         f12: "heads (TM.step (Abs_TM M) (TM.initial_config (Abs_TM M) w)) =
               [if tl w = [] then None else Some (w ! 1), None]" and
         f13: "right (tapes (TM.step (Abs_TM M) (TM.initial_config (Abs_TM M) w)) ! 0) =
               map Some (drop 2 w)" and
         f14: "tapes (TM.step (Abs_TM M) (TM.initial_config (Abs_TM M) w)) ! 1 = Tape [] None []"
         if "w \<noteq> []" for w :: "'a list"
    proof -
      have [simp]: "state (TM.initial_config (Abs_TM M) w) \<notin> TM.TM.final_states (Abs_TM M)"
        unfolding TM.initial_config_def valid_tm_final_states [OF valid_M] apply simp
        unfolding valid_tm_initial_state [OF valid_M] unfolding M_def by simp
      show "state (TM.step (Abs_TM M) (TM.initial_config (Abs_TM M) w)) = (2, Some (hd w))"
        unfolding TM.step_def apply auto
        unfolding TM.initial_config_def valid_tm_initial_state [OF valid_M]
          valid_tm_final_states [OF valid_M] valid_tm_next_state [OF valid_M]
          valid_tm_tape_count [OF valid_M] TM_abbrevs.input_tape_def using that apply auto
        unfolding M_def by simp_all
      show "heads (TM.step (Abs_TM M) (TM.initial_config (Abs_TM M) w)) =
            [if tl w = [] then None else Some (w ! 1), None]"
        unfolding TM.step_def apply auto
         apply (rule nth_equalityI)
          apply auto
        unfolding TM.next_actions_def TM.next_writes_def TM.next_moves_def apply auto
        unfolding valid_tm_tape_count [OF valid_M] TM.initial_config_def apply auto
          apply (subst M_def)
          apply simp
         apply (subst (asm) M_def)
         apply simp
        unfolding valid_tm_next_write [OF valid_M] valid_tm_next_move [OF valid_M]
          TM_abbrevs.tape_action_def TM_abbrevs.tape_write_def apply auto
        unfolding valid_tm_initial_state [OF valid_M] TM_abbrevs.input_tape_def using that apply auto
         apply (auto simp add: M_def TM_abbrevs.tape_shift.simps)
        apply (rule nth_equalityI)
         apply auto
         apply (cases "map Some (tl w)")
          apply auto
        unfolding TM_abbrevs.tape_shift.simps apply auto
        by (metis length_Cons nth_Cons_0 nth_tl zero_less_Suc)
      show "right (tapes (TM.step (Abs_TM M) (TM.initial_config (Abs_TM M) w)) ! 0) = map Some (drop 2 w)"
        unfolding TM.step_def apply auto
        apply (rule nth_equalityI)
         apply auto
        unfolding TM.next_actions_def TM.next_writes_def TM.next_moves_def valid_tm_next_write [OF valid_M]
          valid_tm_next_move [OF valid_M] valid_tm_tape_count [OF valid_M] TM.initial_config_def
         apply auto
        unfolding TM_abbrevs.input_tape_def valid_tm_initial_state [OF valid_M] using that apply auto
        unfolding TM_abbrevs.tape_action_def M_def apply auto
        by (smt (verit, best) One_nat_def Suc_diff_Suc diff_Suc_eq_diff_pred diff_less length_greater_0_conv
            length_map length_tl less_trans_Suc nth_map nth_tl zero_less_Suc)
      show "tapes (TM.step (Abs_TM M) (TM.initial_config (Abs_TM M) w)) ! 1 = Tape [] None []"
        unfolding TM.step_def apply auto
        apply (subst nth_map2)
        unfolding TM.next_actions_def TM.next_writes_def TM.next_moves_def apply auto
        unfolding valid_tm_tape_count [OF valid_M] TM.initial_config_def apply auto
        unfolding valid_tm_next_write [OF valid_M] valid_tm_next_move [OF valid_M] TM.initial_config_def
          TM_abbrevs.input_tape_def using that apply auto
        unfolding valid_tm_initial_state [OF valid_M] unfolding M_def apply auto
        unfolding TM_abbrevs.tape_action_def TM_abbrevs.tape_write_def apply simp
        unfolding TM_abbrevs.tape_shift.simps ..
    qed
    have f11': "state (TM.step (Abs_TM M) (TM.initial_config (Abs_TM M) [])) = (3, None)"
      unfolding TM.step_def apply auto
      unfolding valid_tm_final_states [OF valid_M] TM.initial_config_def apply auto
      unfolding valid_tm_initial_state [OF valid_M] valid_tm_next_state [OF valid_M]
        TM_abbrevs.input_tape_def valid_tm_tape_count [OF valid_M] apply auto
      unfolding M_def by simp_all
    have f21: "state (TM.steps (Abs_TM M) n (TM.initial_config (Abs_TM M) w)) = (2, Some (w ! (n - 1)))" and
         f22: "heads (TM.steps (Abs_TM M) n (TM.initial_config (Abs_TM M) w)) = [Some (w ! n), None]" and
         f23: "right (tapes (TM.steps (Abs_TM M) n (TM.initial_config (Abs_TM M) w)) ! 0) =
               map Some (drop (Suc n) w)" and
         f24: "tapes (TM.steps (Abs_TM M) n (TM.initial_config (Abs_TM M) w)) ! 1 =
               Tape [] None (map Some (rev (take (n - 1) w)))"
         if "n \<ge> 1" and "n < length w" for w :: "'a list" and n :: nat using that
    proof (induction n rule: nat_induct_at_least)
      case base
      {
        case 1
        hence "w \<noteq> []" by auto
        then show ?case using f11 [of w] by (simp add: hd_conv_nth)
      next
        case 2
        hence "tl w \<noteq> []" by (metis Nitpick.size_list_simp(2) One_nat_def le_imp_less_Suc nat_less_le)
        moreover have "w \<noteq> []" using 2 by auto
        ultimately show ?case using f12 [of w] by simp
      next
        case 3
        hence "w \<noteq> []" by auto
        then show ?case using f13 [of w] by (simp add: numeral_2_eq_2)
      next
        case 4
        hence "w \<noteq> []" by auto
        then show ?case using f14 [of w] by simp
      }
    next
      case (Suc n)
      {
        case 1
        hence *: "n < length w" by simp
        have [simp]: "state ((TM.step (Abs_TM M) ^^ n) (TM.initial_config (Abs_TM M) w)) \<notin>
                      TM.TM.final_states (Abs_TM M)"
          unfolding Suc(2) [OF *] valid_tm_final_states [OF valid_M] unfolding M_def by simp
        show ?case apply simp
          apply (subst TM.step_def)
          apply auto
          unfolding Suc(2) [OF *] valid_tm_next_state [OF valid_M] apply (subst M_def)
          apply auto
          using Suc(3) [OF *] by simp_all
      next
        case 2
        hence *: "n < length w" by simp
        have [simp]: "state ((TM.step (Abs_TM M) ^^ n) (TM.initial_config (Abs_TM M) w)) \<notin>
                      TM.TM.final_states (Abs_TM M)"
          unfolding Suc(2) [OF *] valid_tm_final_states [OF valid_M] unfolding M_def by simp
        show ?case apply simp
          apply (subst TM.step_def)
          apply auto
          apply (rule nth_equalityI')
           apply auto
          unfolding TM.next_actions_def TM.next_writes_def TM.next_moves_def apply auto
           apply (metis * Suc.IH(2) TM.run_tapes_len length_Cons length_map list.size(3) min.idem)
          unfolding TM_abbrevs.tape_action_def Suc(2) [OF *] valid_tm_next_write [OF valid_M]
            valid_tm_next_move [OF valid_M] apply simp
          apply (subst (1 4) M_def)
          apply auto
          unfolding TM_abbrevs.tape_write_def
           apply (cases "right (tapes ((TM.step (Abs_TM M) ^^ n) (TM.initial_config (Abs_TM M) w)) ! 0)")
            apply (auto simp add: TM_abbrevs.tape_shift.simps)
          using 2 Suc.IH(3) apply force
           apply (metis * 2 Cons_nth_drop_Suc Suc.IH(3) list.discI list.map_sel(1) list.sel(1))
          using Suc(5) [OF *] apply (simp_all add: TM.run_tapes_len le_less_Suc_eq)
          using * Suc.IH(2) apply fastforce
          by (metis (no_types, lifting) * 2 Cons_nth_drop_Suc Shift_Right_is_right_not_empty Suc.IH(3)
              diff_is_0_eq length_drop linorder_not_less list.map_disc_iff list.map_sel(1) list.sel(1)
              list.size(3) tape.collapse)
      next
        case 3
        hence *: "n < length w" by simp
        have [simp]: "state ((TM.step (Abs_TM M) ^^ n) (TM.initial_config (Abs_TM M) w)) \<notin>
                      TM.TM.final_states (Abs_TM M)"
          unfolding Suc(2) [OF *] valid_tm_final_states [OF valid_M] unfolding M_def by simp
        show ?case apply simp
          apply (subst TM.step_def)
          apply auto
          apply (rule nth_equalityI')
           apply auto
          unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_writes_def TM.next_moves_def
            Suc(2) [OF *] valid_tm_next_write [OF valid_M] valid_tm_next_move [OF valid_M] Suc(3) [OF *]
            valid_tm_tape_count [OF valid_M] apply (subst (1 2 3 4) M_def)
           apply simp
           apply (subst nth_map2)
             apply auto
          using * Suc.IH(2) apply fastforce
          unfolding Suc(4) [OF *] apply simp
          apply (subst nth_map2)
            apply auto
          using valid_TM_def apply blast
           apply (metis * Suc.IH(2) length_greater_0_conv list.discI length_map)
          unfolding TM_abbrevs.tape_write_def apply (subst (3) M_def)
          apply simp
          apply (subst (1 2) nth_zip)
             apply auto
          using valid_TM_def apply blast
          using valid_TM_def apply blast
          using valid_TM_def apply blast
          apply (subst (1 2) nth_map)
           apply auto
          using valid_TM_def apply blast
          unfolding Suc(4) [OF *] apply (subst nth_tl)
            apply auto
          by (metis valid_tm_tape_count [OF valid_M] TM.at_least_one_tape nth_map_upto map_ident
              less_not_refl)
      next
        case 4
        hence *: "n < length w" by simp
        have [simp]: "state ((TM.step (Abs_TM M) ^^ n) (TM.initial_config (Abs_TM M) w)) \<notin>
                      TM.TM.final_states (Abs_TM M)"
          unfolding Suc(2) [OF *] valid_tm_final_states [OF valid_M] unfolding M_def by simp
        show ?case apply simp
          apply (subst TM.step_def)
          apply auto
          apply (subst nth_map2)
            apply (metis Suc.IH(2) * less_Suc0 length_map zero_less_Suc TM.run_tapes_len
              TM.next_actions_simps(2) length_Cons not_less_eq)
          using * Suc.IH(2) apply fastforce
          unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_writes_def TM.next_moves_def
          apply (subst (1 2) nth_zip)
            apply auto
            apply (metis * Suc.IH(2) TM.run_tapes_len length_Cons length_map lessI list.size(3))
          apply (metis * Suc.IH(2) TM.run_tapes_len length_Cons length_map lessI list.size(3))
          apply (subst (1 2) nth_map)
           apply auto
           apply (metis * Suc.IH(2) TM.run_tapes_len length_Cons length_map lessI list.size(3))
          unfolding valid_tm_next_move [OF valid_M] valid_tm_next_write [OF valid_M] Suc(2) [OF *]
            Suc(3) [OF *] valid_tm_tape_count [OF valid_M] Suc(5) [OF *, simplified] unfolding M_def apply simp
          unfolding TM_abbrevs.tape_write_def apply simp
          unfolding TM_abbrevs.tape_shift.simps apply simp
          by (metis * One_nat_def Suc.hyps Suc_pred less_eq_Suc_le less_imp_diff_less list.simps(9)
              list_take_rev_Cons)
      }
    qed
    have f31: "state (TM.steps (Abs_TM M) (length w) (TM.initial_config (Abs_TM M) w)) =
               (2, Some (last w))" and
         f32: "heads (TM.steps (Abs_TM M) (length w) (TM.initial_config (Abs_TM M) w)) = [None, None]" and
         f33: "right (tapes (TM.steps (Abs_TM M) (length w) (TM.initial_config (Abs_TM M) w)) ! 0) = []" and
         f34: "tapes (TM.steps (Abs_TM M) (length w) (TM.initial_config (Abs_TM M) w)) ! 1 =
               Tape [] None (map Some (rev (butlast w)))"
         if "w \<noteq> []" for w :: "'a list"
    proof -
      have *: "length w = Suc (length w - 1)" using that by simp
      have **: "length w - 1 < length w" using that by simp
      have 1 [simp]: "state ((TM.step (Abs_TM M) ^^ (length w - Suc 0)) (TM.initial_config (Abs_TM M) w))
                      \<notin> TM.TM.final_states (Abs_TM M)"
        apply (cases "length w - 1 = 0")
         apply auto
         apply (subst (asm) TM.initial_config_def)
         apply simp
        unfolding valid_tm_initial_state [OF valid_M] valid_tm_final_states [OF valid_M]
         apply (subst (asm) (1 2) M_def)
         apply simp
        apply (subst (asm) f21 [of "length w - 1" w, simplified])
          apply auto
        unfolding M_def by simp
      show "state ((TM.step (Abs_TM M) ^^ length w) (TM.initial_config (Abs_TM M) w)) = (2, Some (last w))"
        apply (subst *)
        apply simp
        apply (subst TM.step_def)
        apply auto
        apply (cases "1 \<le> length w - 1")
         apply auto
        unfolding f21 [OF _ **, simplified] valid_tm_next_state [OF valid_M] apply (subst M_def)
         apply auto
          apply (simp_all add: f22)
         apply (simp_all add: last_conv_nth that)
        by (metis * One_nat_def TM.step_def TM.step_not_final_simps(1) valid_tm_next_state [OF valid_M]
            1 diff_is_0_eq f11 funpow_0 hd_conv_nth list.size(3) not_less_eq_eq)
      show 2: "heads ((TM.step (Abs_TM M) ^^ length w) (TM.initial_config (Abs_TM M) w)) = [None, None]"
        apply (subst *)
        apply simp
        apply (subst TM.step_def)
        apply auto
        apply (rule nth_equalityI')
         apply auto
        unfolding TM.next_actions_def TM.next_writes_def TM.next_moves_def apply auto
         apply (metis (lifting) M_def TM.run_tapes_len min.idem numeral_2_eq_2 simps(1) valid_M
            valid_tm_tape_count)
        unfolding TM_abbrevs.tape_action_def TM.next_writes_def TM.next_moves_def apply auto
        unfolding valid_tm_next_move [OF valid_M] valid_tm_next_write [OF valid_M] apply (subst M_def)
        apply auto
           apply (subst M_def)
           apply auto
        apply (smt (verit, best) * One_nat_def TM.initial_config_def TM_abbrevs.input_tape.simps(2)
            TM_abbrevs.tape_shift.simps(3) TM_abbrevs.tape_write_id TM_config.sel(2) diff_is_0_eq drop_all
            f23 funpow_0 head_right_empty length_0_conv length_Suc_conv lessI less_eq_Suc_le
            list.map_disc_iff not_less_eq_eq nth_Cons_0 tape.sel(2))
        unfolding TM_abbrevs.tape_shift.simps apply (subst M_def)
          apply auto
          apply (metis (no_types, lifting) * One_nat_def TM.initial_tapes_empty TM.run_tapes_len
            TM_abbrevs.tape_write_id diff_is_0_eq f24 funpow_0 less_antisym less_not_refl min.idem
            not_less_eq not_less_eq_eq tape.sel(2))
         apply (subst M_def)
         apply auto
        apply (metis (no_types, lifting) * One_nat_def TM.initial_config_def[of "Abs_TM M" w]
            TM_abbrevs.input_tape.simps(2)[of _ "[]"] TM_abbrevs.tape_shift.simps(3)[of "[]" "Some _"]
            TM_abbrevs.tape_write_id[of
              "tapes ((TM.step (Abs_TM M) ^^ (length w - Suc 0)) (TM.initial_config (Abs_TM M) w)) ! 0"]
            TM_config.sel(2)[of "TM.TM.initial_state (Abs_TM M)"
              "TM_abbrevs.input_tape w # Tape [] None [] \<up> (TM.TM.tape_count (Abs_TM M) - 1)"]
            diff_is_0_eq[of "Suc (length w - 1)" "1"] drop_all[of w "length w"] f23[of "length w - 1" w]
            funpow_0[of "TM.step (Abs_TM M)" "TM.initial_config (Abs_TM M) w"]
            head_right_empty[of "tapes ((TM.step (Abs_TM M) ^^ (length w - 1))
              (TM.initial_config (Abs_TM M) w)) ! 0"]
            length_0_conv length_Suc_conv[of w "0"] less_eq_Suc_le[of "1" "1"]
            less_eq_Suc_le[of "length w - 1" "Suc (length w - 1)"]
            less_eq_Suc_le[of "Suc (length w - 1)" "Suc (length w - 1)"]
            less_not_refl[of "1"] less_not_refl[of "Suc (length w - 1)"]
            list.map_disc_iff[of Some "[]"] not_less_eq_eq[of "1" "1"] not_less_eq_eq[of "1" "length w - 1"]
            not_less_eq_eq[of "length w" "length w"]
            nth_Cons_0[of "TM_abbrevs.input_tape w" "Tape [] None [] \<up> (TM.TM.tape_count (Abs_TM M) - 1)"]
            tape.sel(2)[of "[Some _]" None "[]"])
        apply (subst M_def)
        apply simp
        unfolding TM_abbrevs.tape_write_def apply auto
           apply (metis * One_nat_def TM.initial_config_heads_0 f22 funpow_0 length_Suc0_not_empty
            length_drop less_not_refl list.size(3) not_less_eq nth_Cons_0 option.distinct(1))
          apply (metis * One_nat_def TM.head_input_None_iff[of "Abs_TM M" "[]"]
            TM.head_input_None_iff[of "Abs_TM M" w] TM.run_tapes_len[of "0" "Abs_TM M" "[]"]
            TM.run_tapes_len[of "length w - Suc 0" "Abs_TM M" w]
            f22[of "length (drop 1 w)" w] funpow_0[of "TM.step (Abs_TM M)" "TM.initial_config (Abs_TM M) []"]
            funpow_0[of "TM.step (Abs_TM M)" "TM.initial_config (Abs_TM M) w"]
            hd_conv_nth[of "tapes (TM.initial_config (Abs_TM M) w)"]
            hd_conv_nth[of "heads ((TM.step (Abs_TM M) ^^ length (drop 1 w)) (TM.initial_config (Abs_TM M) w))"]
            length_Suc0_not_empty[of "tapes (TM.initial_config (Abs_TM M) [])"]
            length_Suc0_not_empty[of "drop 1 w"]
            length_drop[of "1" w] less_not_refl[of "Suc (length (drop 1 w))"]
            list.map_disc_iff[of head "tapes (TM.initial_config (Abs_TM M) w)"]
            list.map_sel(1)[of "tapes (TM.initial_config (Abs_TM M) w)" head] list.size(3)
            not_less_eq[of "length (drop 1 w)" "Suc (length (drop 1 w))"]
            nth_Cons_0[of "Some (w ! length (drop 1 w))" "[None]"] option.distinct(1)[of "w ! length (drop 1 w)"])
         apply (smt (verit, best) * ** One_nat_def TM.initial_tapes_non_empty_Cons drop_all f23
            funpow_0 head_right_empty length_Suc0_not_empty length_Suc_conv less_eq_Suc_le
            list.map_disc_iff list.size(3) tape.sel(3))
        by (metis (no_types, lifting) ** One_nat_def TM.initial_tapes_empty TM.run_tapes_len f24 funpow_0
            head_left_empty length_Suc0_not_empty length_drop less_Suc0 less_antisym list.size(3)
            min.idem not_gr_zero tape.sel(1))
      show "right (tapes ((TM.step (Abs_TM M) ^^ length w) (TM.initial_config (Abs_TM M) w)) ! 0) = []"
        apply (subst *)
        apply simp
        apply (subst TM.step_def)
        apply auto
        apply (subst nth_map2)
          apply auto
        apply (metis TM.next_actions_simps(2) lessI list.size(3) not_less_eq valid_M valid_TM_def
            valid_tm_tape_count)
         apply (metis TM.run_tapes_len Zero_not_Suc 2 length_Cons length_map list.size(3))
        unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_writes_def TM.next_moves_def apply auto
        unfolding valid_tm_next_move [OF valid_M] valid_tm_next_write [OF valid_M] apply (subst (1 6) M_def)
        apply auto
        apply (cases "length w - Suc 0 = 0")
         apply auto
        apply (metis (no_types, lifting) * Suc_leD TM.initial_tapes_non_empty_Cons diff_is_0_eq length_0_conv
            length_Suc0_not_empty length_Suc_conv length_map length_tl not_less_eq_eq tape.sel(3))
        using f23 [of "length w - Suc 0" w] that by simp
      show "tapes ((TM.step (Abs_TM M) ^^ length w) (TM.initial_config (Abs_TM M) w)) ! 1 =
            Tape [] None (map Some (rev (butlast w)))"
        apply (subst *)
        apply simp
        apply (subst TM.step_def)
        apply auto
        apply (subst nth_map2)
        apply (metis (no_types, lifting) M_def TM.next_actions_simps(2) lessI numeral_2_eq_2 simps(1) valid_M
            valid_tm_tape_count)
         apply (metis (lifting) M_def TM.run_tapes_len lessI numeral_2_eq_2 simps(1) valid_M valid_tm_tape_count)
        unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_writes_def TM.next_moves_def
        apply (subst (1 2) nth_zip)
          apply auto
        using M_def valid_tm_tape_count apply fastforce
        using M_def valid_tm_tape_count apply fastforce
        apply (subst (1 2) nth_map)
         apply auto
        using M_def valid_tm_tape_count apply fastforce
        unfolding valid_tm_next_move [OF valid_M] valid_tm_next_write [OF valid_M]
        apply (cases "1 \<le> length w - Suc 0")
         apply (frule f21 [where w=w])
          apply linarith
         apply simp
         apply (frule f22 [simplified, where w=w])
          apply linarith
         apply simp
         apply (subst (1 3) M_def)
         apply auto
          apply (metis TM.run_tapes_len le_zero_eq length_Cons length_Suc0_not_empty lessI list.size(3,4) nth_upt)
        unfolding TM_abbrevs.tape_write_def apply (frule f24 [simplified, where w=w])
          apply linarith
         apply auto
        unfolding TM_abbrevs.tape_shift.simps apply auto
      proof -
        assume a1: "Suc 0 \<le> length w - Suc 0"
        have "Some (w ! (length w - Suc (Suc 0))) # map Some (drop (Suc (Suc 0)) (rev w)) =
              map Some (drop (Suc 0) (rev w))"
          by (metis * Cons_nth_drop_Suc One_nat_def a1 le_imp_less_Suc length_rev list.simps(9) rev_nth)
        also have "... = map Some (rev (butlast w))"
          by (metis One_nat_def butlast_conv_take drop_rev)
        finally show "Some (w ! (length w - Suc (Suc 0))) # map Some (drop (Suc (Suc 0)) (rev w)) =
                      map Some (rev (butlast w))" .
      next
        assume a1: "\<not> Suc 0 \<le> length w - Suc 0"
        hence 1: "length w = 1" using that
          by (metis a1 * One_nat_def list.size(3) Ex_list_of_length length_Suc0_not_empty)
        show "TM_abbrevs.tape_shift (next_move M (state (TM.initial_config (Abs_TM M) w))
              (heads (TM.initial_config (Abs_TM M) w)) ([0..<TM.TM.tape_count (Abs_TM M)] ! Suc 0))
              (Tape (left (tapes (TM.initial_config (Abs_TM M) w) ! Suc 0))
              (next_write M (state (TM.initial_config (Abs_TM M) w))
              (heads (TM.initial_config (Abs_TM M) w)) ([0..<TM.TM.tape_count (Abs_TM M)] ! Suc 0))
              (right (tapes (TM.initial_config (Abs_TM M) w) ! Suc 0))) =
              Tape [] None (map Some (rev (butlast w)))"
          unfolding TM.initial_config_def apply simp
          unfolding valid_tm_initial_state [OF valid_M] TM_abbrevs.input_tape_def using that apply auto
          unfolding valid_tm_tape_count [OF valid_M] unfolding M_def apply simp
          unfolding TM_abbrevs.tape_shift.simps using 1 apply simp
          by (metis not_less_eq length_greater_0_conv ** length_butlast)
      qed
    qed
    have f41: "state (TM.steps (Abs_TM M) (Suc (length w)) (TM.initial_config (Abs_TM M) w)) =
               (3, Some (last w))" and
         f42: "tapes (TM.steps (Abs_TM M) (Suc (length w)) (TM.initial_config (Abs_TM M) w)) ! 1 =
               Tape [] (Some (last w)) (map Some (rev (butlast w)))"
         if "w \<noteq> []" for w :: "'a list"
    proof -
      have [simp]: "state ((TM.step (Abs_TM M) ^^ length w) (TM.initial_config (Abs_TM M) w)) \<notin>
                    TM.TM.final_states (Abs_TM M)" unfolding f31 [OF that] valid_tm_final_states [OF valid_M]
        unfolding M_def by simp
      show "state ((TM.step (Abs_TM M) ^^ Suc (length w)) (TM.initial_config (Abs_TM M) w)) =
            (3, Some (last w))"
        apply simp
        apply (subst TM.step_def)
        apply auto
        unfolding valid_tm_next_state [OF valid_M] f31 [OF that] f32 [OF that] unfolding M_def by simp
      show "tapes ((TM.step (Abs_TM M) ^^ Suc (length w)) (TM.initial_config (Abs_TM M) w)) ! 1 =
            Tape [] (Some (last w)) (map Some (rev (butlast w)))"
        apply simp
        apply (subst TM.step_def)
        apply auto
        unfolding TM.next_actions_def TM.next_writes_def TM.next_moves_def apply (subst nth_map2)
          apply auto
        using M_def valid_tm_tape_count apply force
         apply (metis (no_types, lifting) M_def TM.run_tapes_len less_not_refl not_less_eq
            numeral_2_eq_2 simps(1) valid_M valid_tm_tape_count)
        apply (subst nth_zip)
          apply auto
        using M_def valid_tm_tape_count apply fastforce
        using M_def valid_tm_tape_count apply fastforce
        unfolding valid_tm_next_write [OF valid_M] valid_tm_next_move [OF valid_M]
        unfolding f31 [OF that] f32 [OF that] valid_tm_tape_count [OF valid_M] f34 [OF that, simplified]
        unfolding M_def apply simp
        unfolding TM_abbrevs.tape_action_def TM_abbrevs.tape_write_def apply auto
        unfolding TM_abbrevs.tape_shift.simps ..
    qed
    show tb: "TM.time_bounded_word (Abs_TM M) (\<lambda>n. Suc n) w" for w :: "'a list"
    proof (unfold TM.time_bounded_word_def, cases "w = []")
      case True
      then show "TM.is_final (Abs_TM M) (TM.run (Abs_TM M) (Suc (length w)) w)"
        apply (simp add: TM.run_def TM.is_final_def valid_tm_final_states)
        unfolding f11' unfolding M_def by simp
    next
      case False
      then show "TM.is_final (Abs_TM M) (TM.run (Abs_TM M) (Suc (length w)) w)"
        unfolding TM.is_final_def TM.run_def f41 [OF False] valid_tm_final_states [OF valid_M]
        unfolding M_def by simp
    qed
    show "TM.computes (Abs_TM M) rev"
    proof (unfold TM.computes_def, auto)
      fix w :: "'a list"
      have 1: "(LEAST n. TM.is_final (Abs_TM M) ((TM.step (Abs_TM M) ^^ n)
               (TM.initial_config (Abs_TM M) []))) = 1"
        apply (rule Least_natI)
         apply auto
        using tb [of "[]"] unfolding TM.time_bounded_word_def TM.run_def apply simp
        unfolding TM.is_final_def valid_tm_final_states [OF valid_M] TM.initial_config_def apply simp
        unfolding valid_tm_initial_state [OF valid_M] unfolding M_def by simp
      have 2: "\<And>w. state (TM.initial_config (Abs_TM M) w) \<notin> TM.TM.final_states (Abs_TM M)"
        unfolding TM.initial_config_def valid_tm_final_states [OF valid_M] apply simp
        unfolding valid_tm_initial_state [OF valid_M] unfolding M_def by simp
      show "TM.computes_word (Abs_TM M) w (rev w)"
      proof (unfold TM.computes_word_def, cases "w = []")
        case True
        then show "TM.halts (Abs_TM M) w \<and> TM.has_output (TM.compute (Abs_TM M) w) (rev w)"
          apply auto
          using tb [of "[]"] TM.time_bounded_wordD apply blast
          unfolding TM.has_output_def TM.compute_def TM.clean_output_of_def TM.clean_output_def
            TM.compute_config_def 1 apply auto
          unfolding TM.step_def apply (auto simp add: 2)
          unfolding TM.output_of_def Let_def apply auto
        proof -
          fix w' :: "'a list"
          assume a1: "last (map2 TM_abbrevs.tape_action (TM.next_actions (Abs_TM M)
                      (state (TM.initial_config (Abs_TM M) [])) (heads (TM.initial_config (Abs_TM M) [])))
                      (tapes (TM.initial_config (Abs_TM M) []))) = TM_abbrevs.input_tape w'"
          have 1: "head (last (map2 TM_abbrevs.tape_action (TM.next_actions (Abs_TM M)
                   (state (TM.initial_config (Abs_TM M) [])) (heads (TM.initial_config (Abs_TM M) [])))
                   (tapes (TM.initial_config (Abs_TM M) [])))) = None"
            unfolding TM.next_actions_def TM.next_writes_def TM.next_moves_def valid_tm_tape_count [OF valid_M]
              valid_tm_next_write [OF valid_M] valid_tm_next_move [OF valid_M] TM.initial_config_def
              TM_abbrevs.input_tape_def apply auto
            unfolding valid_tm_initial_state [OF valid_M] unfolding M_def apply simp
            unfolding TM_abbrevs.tape_action_def TM_abbrevs.tape_write_def apply (subst last_map2)
              apply auto
            apply (subst (1 2) last_zip)
               apply auto
            apply (subst (1 2) last_map)
             apply auto
            unfolding TM_abbrevs.tape_shift.simps by simp
          show "(case head (TM_abbrevs.input_tape w') of None \<Rightarrow> [] | Some h \<Rightarrow>
                h # the (those (takeWhile (\<lambda>s. s \<noteq> None)
                (right (last (tapes (TM.step_not_final (Abs_TM M)
                (TM.initial_config (Abs_TM M) [])))))))) = []"
            unfolding a1 [symmetric] 1 by simp
        next
          show "\<exists>w. last (map2 TM_abbrevs.tape_action (TM.next_actions (Abs_TM M)
                (state (TM.initial_config (Abs_TM M) [])) (heads (TM.initial_config (Abs_TM M) [])))
                (tapes (TM.initial_config (Abs_TM M) []))) = TM_abbrevs.input_tape w"
            apply (rule exI [where x="[]"])
            unfolding TM_abbrevs.input_tape_def TM.next_actions_def TM.next_writes_def
              TM.next_moves_def apply simp
            unfolding valid_tm_next_write [OF valid_M] valid_tm_next_move [OF valid_M]
              valid_tm_tape_count [OF valid_M] TM.initial_config_def TM_abbrevs.input_tape_def apply simp
            unfolding valid_tm_initial_state [OF valid_M] unfolding M_def apply simp
            apply (subst last_map2)
              apply auto
            apply (subst last_zip)
               apply auto
            apply (subst (1 2) last_map)
             apply auto
            unfolding TM_abbrevs.tape_action_def TM_abbrevs.tape_action_def TM_abbrevs.tape_write_def
            apply simp
            unfolding TM_abbrevs.tape_shift.simps ..
        qed
      next
        case False
        have 1: "(LEAST n. TM.is_final (Abs_TM M) ((TM.step (Abs_TM M) ^^ n) (TM.initial_config (Abs_TM M) w))) =
                 Suc (length w)"
          apply (rule Least_natI)
          unfolding TM.is_final_def f41 [OF False] unfolding valid_tm_final_states [OF valid_M]
           apply (subst M_def)
           apply simp
        proof
          fix n :: nat
          assume a1: "n < Suc (length w)" and
                 a2: "state ((TM.step (Abs_TM M) ^^ n) (TM.initial_config (Abs_TM M) w)) \<in> final_states M"
          have "state ((TM.step (Abs_TM M) ^^ (length w)) (TM.initial_config (Abs_TM M) w)) \<notin> final_states M"
            unfolding f31 [OF False] unfolding M_def by simp
          hence "state ((TM.step (Abs_TM M) ^^ n) (TM.initial_config (Abs_TM M) w)) \<notin> final_states M"
            using a1
            by (metis (no_types, lifting) Suc_lessD TM.conf_time_gt_rev TM.conf_time_lessD
                valid_tm_final_states [OF valid_M] halts_confI is_finalD is_finalI less_antisym
                less_trans_Suc)
          thus False using a2 by contradiction
        qed
        have "length (tapes (TM.step (Abs_TM M) ((TM.step (Abs_TM M) ^^ length w)
              (TM.initial_config (Abs_TM M) w)))) = 2" using f32 [OF False]
          by (metis (lifting) M_def TM.run_tapes_len TM.step_l_tps simps(1) valid_M valid_tm_tape_count)
        hence 2: "last (tapes (TM.step (Abs_TM M) ((TM.step (Abs_TM M) ^^ length w)
                 (TM.initial_config (Abs_TM M) w)))) =
                 tapes (TM.step (Abs_TM M) ((TM.step (Abs_TM M) ^^ length w)
                 (TM.initial_config (Abs_TM M) w))) ! 1"
          by (metis Nitpick.size_list_simp(2) Zero_not_Suc add_diff_cancel_left' last_conv_nth numeral_2_eq_2
              one_add_one)
        have 3: "head (last
                 (tapes (TM.step (Abs_TM M) ((TM.step (Abs_TM M) ^^ length w) (TM.initial_config (Abs_TM M) w))))) =
                 Some (last w)" unfolding 2 [simplified] unfolding f42 [OF False, simplified] by simp
        have 4: "takeWhile (\<lambda>s. \<exists>y. s = Some y) (map Some (rev (butlast w))) = map Some (rev (butlast w))" by simp
        have "TM.halts (Abs_TM M) w" using tb [of w] TM.time_bounded_altdef2 tb by blast
        moreover have "TM.has_output (TM.compute (Abs_TM M) w) (rev w)"
          unfolding TM.compute_def TM.compute_config_def 1 TM.has_output_def TM.clean_output_of_def
          apply auto
          unfolding TM.clean_output_def apply auto
          unfolding 2 [simplified] unfolding f42 [OF False, simplified]
          unfolding TM.output_of_def Let_def 3 apply simp
          unfolding 2 [simplified] f42 [OF False, simplified] apply simp
           apply (erule subst)
           apply (simp add: 4)
           apply (metis False append_butlast_last_id rev.simps(2) rev_rev_ident)
          apply (rule exI [where x="rev w"])
          unfolding TM_abbrevs.input_tape_def apply auto
          using False apply simp
           apply (simp add: hd_rev)
          using rev_butlast_is_tl_rev by blast
        ultimately show "TM.halts (Abs_TM M) w \<and> TM.has_output (TM.compute (Abs_TM M) w) (rev w)" ..
      qed
    qed
  qed
qed

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
  fixes T :: "nat \<Rightarrow> nat"
    and L\<^sub>1 L\<^sub>2 :: "bool lang"
    and f\<^sub>R :: "word \<Rightarrow> word" \<comment> \<open>the reduction\<close>
    and l\<^sub>R :: "nat \<Rightarrow> nat" \<comment> \<open>length bound of the reduction\<close>
  assumes "L\<^sub>1 \<in> DTIME(T)"
    and f\<^sub>R_MOST: "MOST w. (f\<^sub>R w \<in>\<^sub>L L\<^sub>1 \<longleftrightarrow> w \<in>\<^sub>L L\<^sub>2) \<and> (length (f\<^sub>R w) \<le> l\<^sub>R (length w))"
    and "computable_in_time T f\<^sub>R"
    and T_superlinear: "\<forall>N. \<exists>n\<^sub>0. \<forall>n\<ge>n\<^sub>0. T(n)/n \<ge> N"
    and T_l\<^sub>R_mono: "MOST n. T (l\<^sub>R n) \<ge> T(n)" \<comment> \<open>allows reasoning about \<^term>\<open>T\<close> and \<^term>\<open>l\<^sub>R\<close> as if both were \<^const>\<open>mono\<close>.\<close>
  shows "L\<^sub>2 \<in> DTIME(\<lambda>n. T(l\<^sub>R n))" \<comment> \<open>Reducing \<^term>\<open>L\<^sub>2\<close> to \<^term>\<open>L\<^sub>1\<close>\<close>
proof -
  from \<open>computable_in_time T f\<^sub>R\<close> obtain M\<^sub>R :: "('q0, bool) TM_decider"
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
    and f\<^sub>R_MOST: "MOST w. (f\<^sub>R w \<in>\<^sub>L L\<^sub>1 \<longleftrightarrow> w \<in>\<^sub>L L\<^sub>2) \<and> (length (f\<^sub>R w) \<le> length w)"
    and "computable_in_time T f\<^sub>R"
    and T_superlinear: "\<forall>N. \<exists>n\<^sub>0. \<forall>n\<ge>n\<^sub>0. T(n)/n \<ge> N"
  shows "L\<^sub>2 \<in> DTIME(T)" \<comment> \<open>Reducing \<^term>\<open>L\<^sub>2\<close> to \<^term>\<open>L\<^sub>1\<close>\<close>
  using assms apply (rule reduce_DTIME')
*)
end \<comment> \<open>context \<^locale>\<open>TM_abbrevs\<close>\<close>

(* returns the maximum time that T takes to process an input f(w), where length(w) = n; used 
   to model/analyze the composition of two TMs *)
definition max_Tf :: "(nat \<Rightarrow> nat) \<Rightarrow> (('s::finite) list \<Rightarrow> 's list) \<Rightarrow> nat \<Rightarrow> nat" where
  "max_Tf T f n \<equiv> Max {t. \<exists>w. length w = n \<and> T (length (f w)) = t}"

lemma finite_max_Tf: "finite {t::nat. \<exists>w. length w = n \<and>
                      T (length ((f::('s::finite) list \<Rightarrow> 's list) w)) = t}"
proof -
  have 1: "{t. \<exists>w. length w = n \<and> T (length (f w)) = t} =
           image (T \<circ> length \<circ> f) {w. length w = n}" by auto
  show "finite {t. \<exists>w. length w = n \<and> T (length (f w)) = t}" unfolding 1 apply auto
    using finite_list_length by blast
qed

lemma max_Tf_not_empty: "{t. \<exists>w. length w = n \<and> T (length (f w)) = t} \<noteq> {}"
  using length_replicate by fastforce

lemma max_Tf_ge: "max_Tf T f (length w) \<ge> T (length (f w))"
  unfolding max_Tf_def using finite_max_Tf max_Tf_not_empty
proof -
  have "\<forall>N n. infinite N \<or> (n::nat) \<le> Max N \<or> n \<notin> N"
    using Max.coboundedI by blast
  then show "T (length (f w)) \<le> Max {n. \<exists>as. length as = length w \<and> T (length (f as)) = n}"
    using finite_max_Tf by blast
qed

lemma max_Tf_w: obtains w :: "('s::finite) list" where
  "length w = n" and "T (length (f w)) = max_Tf T f (length w)"
  unfolding max_Tf_def using max_Tf_not_empty finite_max_Tf
proof -
  obtain bb :: "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> ('s list \<Rightarrow> 's list) \<Rightarrow> nat \<Rightarrow> bool" where
    f1: "\<forall>X0 X1 E_x x. bb X0 X1 E_x x = (\<exists>Y0. length Y0 = X0 \<and> X1 (length (E_x Y0)) = x)"
    by moura
  have f2: "\<forall>n f fa. {na. \<exists>ss. length (ss::'s list) = n \<and> f (length (fa ss::'s list)) =
            (na::nat)} \<noteq> {}"
    using max_Tf_not_empty by blast
  have f3: "\<forall>n f fa. finite {na. \<exists>ss. length (ss::'s list) = n \<and>
            f (length (fa ss::'s list)) = (na::nat)}"
    using finite_max_Tf by blast
  have f4: "\<forall>n f fa. max_Tf f fa n = Max {na. \<exists>ss. length (ss::'s list) = n \<and>
            f (length (fa ss)) = na}"
    by (simp add: max_Tf_def)
  have f5: "\<forall>n f fa. Collect (bb n f fa) \<noteq> {}"
    using f2 f1 by presburger
  have f6: "\<forall>n f fa. finite (Collect (bb n f fa))"
    using f3 f1 by presburger
  have "\<forall>n f fa. max_Tf f fa n = Max (Collect (bb n f fa))"
    using f4 f1 by presburger
  then show ?thesis
    using f6 f5 f1 by (metis eq_Max_iff mem_Collect_eq that)
qed

lemma max_Tf_constant: "(\<And>n. T n = k) \<Longrightarrow> max_Tf T (f::('s::finite) list \<Rightarrow> 's list) n = k"
  by (rule max_Tf_w [of n T f]) simp

lemma typed_comp_in_time_words: "bij_betw (g::'a \<Rightarrow> 's) UNIV S \<Longrightarrow>
       typed_computable_in_time TYPE('q) TYPE('l) T (f::'a list \<Rightarrow> 'a list) \<Longrightarrow>
       \<exists>M::('q, 's, 'l) TM. TM.symbols M = S \<and>
       (\<forall>w\<in>S*. TM.computes_word M w (map g (f (map (inv g) w))) \<and>
        TM.time_bounded_word M T w)"
proof (erule computableE)
  fix M :: "('q, 'a, 'l) TM"
  assume a1: "bij_betw g UNIV S" and a2: "TM.computes M f" and
         a3: "\<forall>w. TM.time_bounded_word M T w" and a4: "TM.symbols M = UNIV"
  have a5: "finite S"
  proof -
    have "finite (UNIV :: 'a set)" using a4 by (metis a4 TM.symbol_axioms(1))
    thus "finite S" using a1 bij_betw_finite by blast
  qed
  have a6: "S \<noteq> {}" using a1 by (metis a1 UNIV_I equals0D bij_betwE)
  let ?invg = "inv g"
  define M' :: "('q, 's, 'l) TM_record" where
    "M' \<equiv> TM (TM.tape_count M) S (TM.states M) (TM.initial_state M) (TM.final_states M)
           (TM.label M) (\<lambda>st hds. TM.next_state M st (map (\<lambda>op. map_option ?invg op) hds))
           (\<lambda>st hds k. map_option g (TM.next_write M st
           (map (\<lambda>op. map_option ?invg op) hds) k))
           (\<lambda>st hds k. TM.next_move M st (map (\<lambda>op. map_option ?invg op) hds) k)"
  have valid_M' [intro, simp]: "valid_TM M'"
    unfolding M'_def apply standard
           apply auto
       apply fact
    using a6 apply simp
     apply (simp add: a4)
  proof -
    fix q :: 'q and hds :: "'s option list" and i :: nat
    assume a7: "q \<in> TM.TM.states M" and a8: "length hds = TM.TM.tape_count M" and
           a9: "set hds \<subseteq> options S" and a10: "i < TM.TM.tape_count M" and
           a11: "hds ! i \<in> options S"
    have "TM.next_write M q (map (map_option (inv g)) hds) i \<in> options (TM.symbols M)"
      unfolding a4 by simp
    thus "map_option g (TM.TM.next_write M q (map (map_option (inv g)) hds) i) \<in> options S"
      using a1 by (metis UNIV_I UNIV_options bij_betw_def image_eqI options_map_option)
  qed
  have "TM.symbols (Abs_TM M') = S"
    unfolding valid_tm_symbols [OF valid_M'] unfolding M'_def by simp
  moreover have "\<And>w. set w \<subseteq> S \<Longrightarrow>
                 TM.computes_word (Abs_TM M') w (map g (f (map (inv g) w)))"
  proof -
    fix w :: "'s list"
    assume a7: "set w \<subseteq> S"
    have tpc_eq [simp]: "TM.tape_count (Abs_TM M') = TM.tape_count M"
      unfolding valid_tm_tape_count [OF valid_M']
      unfolding M'_def by simp
    have f1: "state (TM.steps (Abs_TM M') n (TM.initial_config (Abs_TM M') w)) =
          state (TM.steps M n (TM.initial_config M (map (inv g) w)))" and
         f2: "\<And>i. i < TM.tape_count M \<Longrightarrow> left (tapes (TM.steps (Abs_TM M') n
              (TM.initial_config (Abs_TM M') w)) ! i) =
              map (\<lambda>op. map_option g op) (left (tapes (TM.steps M n
              (TM.initial_config M (map (inv g) w))) ! i))" and
         f3: "\<And>i. i < TM.tape_count M \<Longrightarrow> right (tapes (TM.steps (Abs_TM M') n
              (TM.initial_config (Abs_TM M') w)) ! i) =
              map (\<lambda>op. map_option g op) (right (tapes (TM.steps M n
              (TM.initial_config M (map (inv g) w))) ! i))" and
         f4: "\<And>i. i < TM.tape_count M \<Longrightarrow> head (tapes (TM.steps (Abs_TM M') n
              (TM.initial_config (Abs_TM M') w)) ! i) =
              map_option g (head (tapes (TM.steps M n
              (TM.initial_config M (map (inv g) w))) ! i))" for n :: nat
    proof (induction n)
      case 0
      {
        case 1
        then show ?case apply (simp add: TM.initial_config_def)
          unfolding valid_tm_initial_state [OF valid_M']
          unfolding M'_def by simp
      next
        case 2
        then show ?case
          by (simp add: TM.initial_config_def TM_abbrevs.input_tape_def nth_Cons')
      next
        case 3
        then show ?case
        proof (auto simp add: TM.initial_config_def TM_abbrevs.input_tape_def nth_Cons')
          assume a8: "w \<noteq> []" and a9: "i = 0"
          have 1: "map (map_option g \<circ> Some) (tl (map (inv g) w)) =
                   map (Some \<circ> g) (tl (map (inv g) w))" by simp
          have 2: "\<And>f1 f2 l. map (f1 \<circ> f2) l = map f1 (map f2 l)" by simp
          have 3: "map g (tl (map (inv g) w)) = tl w" using a1 a7
            by (metis bij_betw_def map_map_inv_into_id map_tl)
          show "map Some (tl w) = map (map_option g \<circ> Some) (tl (map (inv g) w))"
            unfolding 1 unfolding 2 3 ..
        qed
      next
        case 4
        then show ?case
          apply (auto simp add: TM.initial_config_def TM_abbrevs.input_tape_def nth_Cons')
          using a1 a7 by (simp add: bij_betw_inv_into_right list.map_sel(1) subsetD)
      }
    next
      case IH: (Suc n)
      {
        case 1
        have 2: "map (map_option (inv g) \<circ> head)
                 (tapes ((TM.step (Abs_TM M') ^^ n) (TM.initial_config (Abs_TM M') w))) =
                 heads ((TM.step M ^^ n) (TM.initial_config M (map (inv g) w)))"
          apply (rule nth_equalityI)
           apply auto
           apply (simp add: TM.run_tapes_len)
          apply (subst IH(4))
           apply (simp add: TM.run_tapes_len)
          apply (subst nth_map)
           apply (simp add: TM.run_tapes_len)
        proof -
          fix i :: nat
          show "i < length (tapes ((TM.step (Abs_TM M') ^^ n)
                (TM.initial_config (Abs_TM M') w))) \<Longrightarrow>
                map_option (inv g) (map_option g
                (head (tapes ((TM.step M ^^ n)
                (TM.initial_config M (map (inv g) w))) ! i))) =
                head (tapes ((TM.step M ^^ n) (TM.initial_config M (map (inv g) w))) ! i)"
            apply (cases "head (tapes ((TM.step M ^^ n)
                (TM.initial_config M (map (inv g) w))) ! i)")
             apply auto
            using a1 by (simp add: bij_betw_inv_into_left)
        qed
        show ?case using 1 apply simp
          apply (subst (1 2) TM.step_def)
          apply auto
          using IH.IH(1) apply blast
          using IH.IH(1) M'_def valid_tm_final_states apply force
          using IH.IH(1) M'_def valid_tm_final_states apply force
          unfolding IH(1) valid_tm_next_state [OF valid_M']
          apply (subst M'_def)
          by (simp add: 2)
      next
        case 2
        have 1: "heads ((TM.step (Abs_TM M') ^^ n) (TM.initial_config (Abs_TM M') w)) =
                 map (map_option g) (heads ((TM.step M ^^ n)
                 (TM.initial_config M (map (inv g) w))))"
          apply (rule nth_equalityI)
           apply auto
           apply (simp add: TM.run_tapes_len)
          by (simp add: IH.IH(4) TM.run_tapes_len)
        have 3: "set (heads ((TM.step M ^^ n) (TM.initial_config M (map (inv g) w)))) \<subseteq>
                 options (image (inv g) S)" apply auto
          by (metis UNIV_I UNIV_options a1 bij_betw_def image_inv_f_f)
        have 4: "TM.TM.next_move M (state ((TM.step M ^^ n)
                 (TM.initial_config M (map (inv g) w))))
                 (map (map_option (inv g) \<circ> (map_option g \<circ> head))
                 (tapes ((TM.step M ^^ n) (TM.initial_config M (map (inv g) w))))) i =
                 TM.TM.next_move M (state ((TM.step M ^^ n)
                 (TM.initial_config M (map (inv g) w))))
                 (heads ((TM.step M ^^ n) (TM.initial_config M (map (inv g) w)))) i"
          apply (rule arg_cong [where x="map (map_option (inv g) \<circ> (map_option g \<circ> head))
                 (tapes ((TM.step M ^^ n) (TM.initial_config M (map (inv g) w))))"])
          using a1 by (simp add: bij_betw_imp_inj_on map_option.compositionality
              option.map_id)
        have 5: "map (map_option (inv g) \<circ> (map_option g \<circ> head))
                 (tapes ((TM.step M ^^ n) (TM.initial_config M (map (inv g) w)))) =
                 heads ((TM.step M ^^ n) (TM.initial_config M (map (inv g) w)))"
          using a1 by (simp add: bij_betw_imp_inj_on map_option.compositionality
              option.map_id)
        show ?case using 2 apply simp
          apply (subst (1 2) TM.step_def)
          apply auto
          using IH.IH(2) apply blast
            apply (smt (verit) IH.IH(1) M'_def select_convs(5) valid_M'
              valid_tm_final_states)
           apply (smt (verit) IH.IH(1) M'_def select_convs(5) valid_M'
              valid_tm_final_states)
          apply (subst (1 2) nth_map2)
              apply (simp_all add: TM.next_actions_simps(2))
            apply (simp_all add: TM.run_tapes_len)
          unfolding IH(1) TM.next_actions_def TM.next_writes_def TM.next_moves_def
          apply (simp add: 1)
          unfolding valid_tm_next_write [OF valid_M'] valid_tm_next_move [OF valid_M']
          apply (subst (1 2) M'_def)
          apply simp
          unfolding TM_abbrevs.tape_action_def apply simp
          apply (cases "TM.TM.next_move M (state ((TM.step M ^^ n)
                        (TM.initial_config M (map (inv g) w))))
                        (map (map_option (inv g) \<circ> (map_option g \<circ> head))
                        (tapes ((TM.step M ^^ n) (TM.initial_config M (map (inv g) w))))) i")
            apply (auto simp add: 4)
             apply (simp add: IH.IH(2) map_tl)
          unfolding TM_abbrevs.tape_write_hd 5 apply standard
          using IH.IH(2) apply blast
          by (simp add: IH.IH(2) TM_abbrevs.tape_shift.simps(5))
      next
        case 3
        have 1: "heads ((TM.step (Abs_TM M') ^^ n) (TM.initial_config (Abs_TM M') w)) =
                 map (map_option g) (heads ((TM.step M ^^ n)
                 (TM.initial_config M (map (inv g) w))))"
          apply (rule nth_equalityI)
           apply auto
           apply (simp add: TM.run_tapes_len)
          by (simp add: IH.IH(4) TM.run_tapes_len)
        have 2: "set (heads ((TM.step M ^^ n) (TM.initial_config M (map (inv g) w)))) \<subseteq>
                 options (image (inv g) S)" apply auto
          by (metis UNIV_I UNIV_options a1 bij_betw_def image_inv_f_f)
        have 4: "TM.TM.next_move M (state ((TM.step M ^^ n)
                 (TM.initial_config M (map (inv g) w))))
                 (map (map_option (inv g) \<circ> (map_option g \<circ> head))
                 (tapes ((TM.step M ^^ n) (TM.initial_config M (map (inv g) w))))) i =
                 TM.TM.next_move M (state ((TM.step M ^^ n)
                 (TM.initial_config M (map (inv g) w))))
                 (heads ((TM.step M ^^ n) (TM.initial_config M (map (inv g) w)))) i"
          apply (rule arg_cong [where x="map (map_option (inv g) \<circ> (map_option g \<circ> head))
                 (tapes ((TM.step M ^^ n) (TM.initial_config M (map (inv g) w))))"])
          using a1 by (simp add: bij_betw_imp_inj_on map_option.compositionality
              option.map_id)
        have 5: "map (map_option (inv g) \<circ> (map_option g \<circ> head))
                 (tapes ((TM.step M ^^ n) (TM.initial_config M (map (inv g) w)))) =
                 heads ((TM.step M ^^ n) (TM.initial_config M (map (inv g) w)))"
          using a1 by (simp add: bij_betw_imp_inj_on map_option.compositionality
              option.map_id)
        then show ?case using 3 apply simp
          apply (subst (1 2) TM.step_def)
          apply auto
          using IH.IH(3) apply blast
            apply (smt (verit) IH.IH(1) M'_def select_convs(5) valid_M'
              valid_tm_final_states)
           apply (smt (verit) IH.IH(1) M'_def select_convs(5) valid_M'
              valid_tm_final_states)
          apply (subst (1 2) nth_map2)
              apply (simp_all add: TM.next_actions_simps(2))
            apply (simp_all add: TM.run_tapes_len)
          unfolding IH(1) TM.next_actions_def TM.next_writes_def TM.next_moves_def
          apply (simp add: 1)
          unfolding valid_tm_next_write [OF valid_M'] valid_tm_next_move [OF valid_M']
          apply (subst (1 2) M'_def)
          apply simp
          unfolding TM_abbrevs.tape_action_def apply simp
          apply (cases "TM.TM.next_move M (state ((TM.step M ^^ n)
                        (TM.initial_config M (map (inv g) w))))
                        (map (map_option (inv g) \<circ> (map_option g \<circ> head))
                        (tapes ((TM.step M ^^ n) (TM.initial_config M (map (inv g) w))))) i")
          apply (simp add: 5 TM_abbrevs.tape_write_hd)
             apply (simp add: IH.IH(3) map_tl)
          unfolding TM_abbrevs.tape_write_hd 4 apply simp
          apply (simp add: IH.IH(3) map_tl)
          apply (simp add: IH.IH(2) TM_abbrevs.tape_shift.simps(5))
          using IH.IH(3) by blast
      next
        case 4
        have 1: "tapes ((TM.step (Abs_TM M') ^^ n) (TM.initial_config (Abs_TM M') w)) ! i =
                 map_tape g (tapes ((TM.step M ^^ n)
                 (TM.initial_config M (map (inv g) w))) ! i)"
          by (simp add: 4 IH.IH(2) IH.IH(3) IH.IH(4) tape.expand tape.map_sel(1)
              tape.map_sel(2) tape.map_sel(3))
        have 2: "head (tapes ((TM.step M ^^ n) (TM.initial_config M (map (inv g) w))) ! i) \<in>
                 options (image (inv g) S)"
          by (metis UNIV_I UNIV_options a1 bij_betw_def image_inv_f_f)
        have 3: "\<And>i. i < TM.tape_count M \<Longrightarrow> map (map_option (inv g) \<circ> head)
                 (tapes ((TM.step (Abs_TM M') ^^ n) (TM.initial_config (Abs_TM M') w))) ! i =
                 heads ((TM.step M ^^ n) (TM.initial_config M (map (inv g) w))) ! i"
          apply (subst nth_map)
          using 4 apply (simp add: TM.run_tapes_len)
          apply auto
          unfolding IH(4) apply (subst nth_map)
          using 4 apply (simp add: TM.run_tapes_len)
        proof -
          fix i :: nat
          show "i < TM.TM.tape_count M \<Longrightarrow> map_option (inv g)
                (map_option g (head (tapes ((TM.step M ^^ n)
                (TM.initial_config M (map (inv g) w))) ! i))) =
                head (tapes ((TM.step M ^^ n) (TM.initial_config M (map (inv g) w))) ! i)"
            apply (cases "head (tapes ((TM.step M ^^ n)
                (TM.initial_config M (map (inv g) w))) ! i)")
           apply auto
            using a1 2 by (simp add: bij_betw_inv_into_left)
        qed
        have 5: "TM.TM.next_move M (state ((TM.step M ^^ n)
                 (TM.initial_config M (map (inv g) w))))
                 (map (map_option (inv g) \<circ> head)
                 (tapes ((TM.step (Abs_TM M') ^^ n) (TM.initial_config (Abs_TM M') w)))) i =
                 TM.TM.next_move M (state ((TM.step M ^^ n)
                 (TM.initial_config M (map (inv g) w))))
                 (heads ((TM.step M ^^ n) (TM.initial_config M (map (inv g) w)))) i"
        proof -
          have "length (map (map_option (inv g) \<circ> head)
                (tapes ((TM.step (Abs_TM M') ^^ n) (TM.initial_config (Abs_TM M') w)))) =
                length (heads ((TM.step M ^^ n) (TM.initial_config M (map (inv g) w))))"
            by (simp add: TM.run_tapes_len)
          hence 1: "map (map_option (inv g) \<circ> head)
                    (tapes ((TM.step (Abs_TM M') ^^ n) (TM.initial_config (Abs_TM M') w))) =
                    heads ((TM.step M ^^ n) (TM.initial_config M (map (inv g) w)))" using 3
            by (metis TM.run_tapes_len length_map nth_equalityI)
          show "TM.TM.next_move M (state ((TM.step M ^^ n)
                (TM.initial_config M (map (inv g) w))))
                (map (map_option (inv g) \<circ> head)
                (tapes ((TM.step (Abs_TM M') ^^ n) (TM.initial_config (Abs_TM M') w)))) i =
                TM.TM.next_move M (state ((TM.step M ^^ n)
                (TM.initial_config M (map (inv g) w))))
                (heads ((TM.step M ^^ n) (TM.initial_config M (map (inv g) w)))) i"
            unfolding 1 ..
        qed
        show ?case using 4 apply simp
          apply (subst (1 2) TM.step_def)
          apply auto
          using IH.IH(4) apply blast
            apply (smt (verit, del_insts) IH.IH(1) M'_def select_convs(5) valid_M'
              valid_tm_final_states)
           apply (smt (verit, del_insts) IH.IH(1) M'_def select_convs(5) valid_M'
              valid_tm_final_states)
          apply (subst (1 2) nth_map2)
              apply (simp_all add: TM.next_actions_simps(2))
            apply (simp_all add: TM.run_tapes_len)
          unfolding TM.next_actions_def TM.next_writes_def TM.next_moves_def apply simp
          unfolding IH(1) valid_tm_next_write [OF valid_M'] valid_tm_next_move [OF valid_M']
          apply (subst (1 4) M'_def)
          apply (simp add: 1 3 [OF 4] 5)
          apply (cases "TM.next_move M (state ((TM.step M ^^ n)
                        (TM.initial_config M (map (inv g) w))))
                        (heads ((TM.step M ^^ n) (TM.initial_config M (map (inv g) w)))) i")
          unfolding TM_abbrevs.tape_action_def apply auto
            apply (cases "left (map_tape g (tapes ((TM.step M ^^ n)
                          (TM.initial_config M (map (inv g) w))) ! i))")
          apply auto
             apply (simp add: tape.map_sel(1))
            apply (subst Shift_Left_is_left_not_empty)
             apply auto
            apply (smt (verit, best) TM_abbrevs.map_tape_def TM_abbrevs.tape_shift.simps(2)
              TM_abbrevs.tape_shift_map left_after_write tape.map_sel(1) tape.sel(2))
           apply (smt (verit, del_insts) Shift_Right_is_right_not_empty
              TM_abbrevs.tape_shift_map TM_abbrevs.tape_write_map head_right_empty
              right_after_write tape.map_sel(2))
          unfolding TM_abbrevs.tape_shift.simps(5) TM_abbrevs.tape_write_hd
          by (metis 3 TM.run_tapes_len length_map nth_equalityI tpc_eq)
      }
    qed
    have 1: "TM.halts (Abs_TM M') w" using a3 [THEN spec, where x="map (inv g) w",
          unfolded TM.time_bounded_word_def] unfolding TM.halts_def TM.halts_config_def
      TM.run_def using f1
      by (metis (no_types, lifting) M'_def is_finalD is_finalI select_convs(5) valid_M'
          valid_tm_final_states)
    have 2: "TM.is_final (Abs_TM M') (TM.steps (Abs_TM M') n
             (TM.initial_config (Abs_TM M') w)) \<longleftrightarrow>
             TM.is_final M (TM.steps M n (TM.initial_config M (map (inv g) w)))" for n :: nat
      using f1 by (smt (verit, best) M'_def is_finalD is_finalI select_convs(5)
          valid_M' valid_tm_final_states)
    show "TM.computes_word (Abs_TM M') w (map g (f (map (inv g) w)))"
      using a2 unfolding TM.computes_def TM.computes_word_def apply auto
       apply (rule 1)
      unfolding TM.has_output_def TM.compute_def TM.compute_config_def 2
      apply (drule spec [where x="map (inv g) w"])
    proof (erule conjE)
      assume a8: "TM.halts M (map (inv g) w)" and
             a9: "TM.clean_output_of ((TM.step M ^^
       (LEAST n. TM.is_final M ((TM.step M ^^ n) (TM.initial_config M (map (inv g) w)))))
       (TM.initial_config M (map (inv g) w))) = Some (f (map (inv g) w))"
      have 1: "state (TM.steps (Abs_TM M') (LEAST n. TM.is_final M ((TM.step M ^^ n)
               (TM.initial_config M (map (inv g) w))))
               (TM.initial_config (Abs_TM M') w)) = state (TM.steps M
               (LEAST n. TM.is_final M ((TM.step M ^^ n)
               (TM.initial_config M (map (inv g) w))))
               (TM.initial_config M (map (inv g) w)))" using f1 by blast
      have 2: "tapes (TM.steps (Abs_TM M') (LEAST n. TM.is_final M ((TM.step M ^^ n)
               (TM.initial_config M (map (inv g) w))))
               (TM.initial_config (Abs_TM M') w)) =
               map (\<lambda>t. tape.map_tape (\<lambda>s. g s) t)
               (tapes (TM.steps M (LEAST n. TM.is_final M ((TM.step M ^^ n)
               (TM.initial_config M (map (inv g) w))))
               (TM.initial_config M (map (inv g) w))))"
        apply (rule nth_equalityI)
         apply auto
         apply (metis (no_types, lifting) M'_def TM.init_conf_len TM.steps_l_tps
            select_convs(1) valid_M' valid_tm_tape_count)
        apply (subst nth_map)
         apply (metis (no_types, lifting) M'_def TM.init_conf_len TM.steps_l_tps
            select_convs(1) valid_M' valid_tm_tape_count)
      proof (rule tape.exhaust)
        fix i :: nat and x1 x3 :: "'a option list" and x2 :: "'a option"
        assume a1: "i < length (tapes ((TM.step (Abs_TM M') ^^
                    (LEAST n. TM.is_final M ((TM.step M ^^ n)
                    (TM.initial_config M (map (inv g) w)))))
                    (TM.initial_config (Abs_TM M') w)))" and
               a2: "(tapes ((TM.step M ^^
                    (LEAST n. TM.is_final M ((TM.step M ^^ n)
                    (TM.initial_config M (map (inv g) w)))))
                    (TM.initial_config M (map (inv g) w))) ! i) = Tape x1 x2 x3"
        show "tapes ((TM.step (Abs_TM M') ^^
              (LEAST n. TM.is_final M ((TM.step M ^^ n)
              (TM.initial_config M (map (inv g) w)))))
              (TM.initial_config (Abs_TM M') w)) ! i =
              map_tape g (tapes ((TM.step M ^^
              (LEAST n. TM.is_final M ((TM.step M ^^ n)
              (TM.initial_config M (map (inv g) w)))))
              (TM.initial_config M (map (inv g) w))) ! i)"
          unfolding a2 using a1
          by (simp add: TM.init_conf_len TM.steps_l_tps a2 f2 f3 f4 tape.expand)
      qed
      have 3: "TM.steps (Abs_TM M') (LEAST n. TM.is_final M ((TM.step M ^^ n)
               (TM.initial_config M (map (inv g) w))))
               (TM.initial_config (Abs_TM M') w) = TM_config (state (TM.steps M
               (LEAST n. TM.is_final M ((TM.step M ^^ n)
               (TM.initial_config M (map (inv g) w))))
               (TM.initial_config M (map (inv g) w))))
               (map (\<lambda>t. map_tape (\<lambda>s. g s) t)
               (tapes (TM.steps M (LEAST n. TM.is_final M ((TM.step M ^^ n)
               (TM.initial_config M (map (inv g) w))))
               (TM.initial_config M (map (inv g) w)))))"
        using 1 2 by (metis TM_config.exhaust_sel)
      have 4: "TM.clean_output (TM_config (state ((TM.step M ^^
               (LEAST n. TM.is_final M ((TM.step M ^^ n)
               (TM.initial_config M (map (inv g) w)))))
               (TM.initial_config M (map (inv g) w))))
               (map (map_tape g) (tapes ((TM.step M ^^
               (LEAST n. TM.is_final M ((TM.step M ^^ n)
               (TM.initial_config M (map (inv g) w)))))
               (TM.initial_config M (map (inv g) w)))))) \<Longrightarrow>
               TM.clean_output ((TM.step M ^^
               (LEAST n. TM.is_final M ((TM.step M ^^ n)
               (TM.initial_config M (map (inv g) w)))))
               (TM.initial_config M (map (inv g) w)))"
        by (metis TM.clean_output_of_def a9 option.discI)
      have 5: "head (last (map (map_tape g) (tapes ((TM.step M ^^
               (LEAST n. TM.is_final M ((TM.step M ^^ n)
               (TM.initial_config M (map (inv g) w)))))
               (TM.initial_config M (map (inv g) w)))))) =
               map_option g (head (last (tapes ((TM.step M ^^
               (LEAST n. TM.is_final M ((TM.step M ^^ n)
               (TM.initial_config M (map (inv g) w)))))
               (TM.initial_config M (map (inv g) w))))))"
        by (smt (verit, best) TM.at_least_one_tape TM.run_tapes_len last_map
            list.size(3) order_less_irrefl tape.map_sel(2))
      have 6: "the (those (takeWhile (\<lambda>s. \<exists>y. s = Some y) (right (last (map (map_tape g)
               (tapes ((TM.step M ^^
               (LEAST n. TM.is_final M ((TM.step M ^^ n)
               (TM.initial_config M (map (inv g) w)))))
               (TM.initial_config M (map (inv g) w))))))))) =
               map g (the (those (takeWhile (\<lambda>s. \<exists>y. s = Some y) (right (last (
               (tapes ((TM.step M ^^
               (LEAST n. TM.is_final M ((TM.step M ^^ n)
               (TM.initial_config M (map (inv g) w)))))
               (TM.initial_config M (map (inv g) w))))))))))"
        apply (cases "right (last (
               (tapes ((TM.step M ^^
               (LEAST n. TM.is_final M ((TM.step M ^^ n)
               (TM.initial_config M (map (inv g) w)))))
               (TM.initial_config M (map (inv g) w))))))")
         apply auto
          apply (rule nth_equalityI)
           apply auto
      proof -
        fix i :: nat
        assume a1: "right (last (tapes ((TM.step M ^^ (LEAST n. TM.is_final M
                    ((TM.step M ^^ n) (TM.initial_config M (map (inv g) w)))))
                    (TM.initial_config M (map (inv g) w))))) = []"
        have "\<forall>f ts. map (map_option f) (right (last ts::'a tape)) =
              right (last (map (map_tape f) ts)::'s tape) \<or> [] = ts"
          by (metis last_map tape.map_sel(3))
        then show "the (those (takeWhile (\<lambda>z. \<exists>s. z = Some s)
                   (right (last (map (map_tape g) (tapes ((TM.step M ^^ (LEAST n.
                   TM.is_final M ((TM.step M ^^ n) (TM.initial_config M (map (inv g) w)))))
                   (TM.initial_config M (map (inv g) w))))))))) = []"
          using a1 by (smt (z3) TM.at_least_one_tape TM.init_conf_len TM.steps_l_tps
              list.simps(8) list.size(3) option.sel order_less_irrefl takeWhile.simps(1)
              those.simps(1))
        then show "right (last (tapes ((TM.step M ^^ (LEAST n.
              TM.is_final M ((TM.step M ^^ n) (TM.initial_config M (map (inv g) w)))))
              (TM.initial_config M (map (inv g) w))))) = [] \<Longrightarrow> i < length
              (the (those (takeWhile (\<lambda>s. \<exists>y. s = Some y) (right (last (map (map_tape g)
              (tapes ((TM.step M ^^ (LEAST n. TM.is_final M
              ((TM.step M ^^ n) (TM.initial_config M (map (inv g) w)))))
              (TM.initial_config M (map (inv g) w)))))))))) \<Longrightarrow>
              the (those (takeWhile (\<lambda>s. \<exists>y. s = Some y) (right (last (map (map_tape g)
              (tapes ((TM.step M ^^ (LEAST n. TM.is_final M
              ((TM.step M ^^ n) (TM.initial_config M (map (inv g) w)))))
              (TM.initial_config M (map (inv g) w))))))))) ! i = [] ! i" by simp
      next
        fix h :: 'a and t :: "'a option list"
        assume a8: "right (last (tapes ((TM.step M ^^
                    (LEAST n. TM.is_final M ((TM.step M ^^ n)
                    (TM.initial_config M (map (inv g) w)))))
                    (TM.initial_config M (map (inv g) w))))) = Some h # t"
        have 1: "right (last (map (map_tape g)
                 (tapes ((TM.step M ^^ (LEAST n. TM.is_final M
                 ((TM.step M ^^ n) (TM.initial_config M (map (inv g) w)))))
                 (TM.initial_config M (map (inv g) w)))))) =
                 Some (g h) # (map (map_option g) t)"
          by (smt (verit, best) TM.at_least_one_tape TM.run_tapes_len a8
              bot_nat_0.not_eq_extremum last_map length_0_conv map_eq_Cons_conv
              map_option_eq_Some tape.map_sel(3))
        have 2: "those (takeWhile (\<lambda>s. \<exists>y. s = Some y) (map (map_option g) t)) =
                 Some (map the (takeWhile (\<lambda>s. \<exists>y. s = Some y) (map (map_option g) t)))"
          apply (subst those_Some_map_the)
           apply auto
          using set_takeWhileD by fastforce
        have "those (takeWhile (\<lambda>s. \<exists>y. s = Some y) (right (last (map (map_tape g)
              (tapes ((TM.step M ^^ (LEAST n. TM.is_final M
              ((TM.step M ^^ n) (TM.initial_config M (map (inv g) w)))))
              (TM.initial_config M (map (inv g) w)))))))) =
              Some (map g (the (map_option ((#) h) (those
              (takeWhile (\<lambda>s. \<exists>y. s = Some y) t)))))" unfolding 1 apply simp
          unfolding 2
        proof simp
          have 1: "the (map_option ((#) h) (those (takeWhile (\<lambda>s. \<exists>y. s = Some y) t))) =
                   h#(the (those (takeWhile (\<lambda>s. \<exists>y. s = Some y) t)))"
            by (smt (verit, del_insts) option.discI option.map_sel set_takeWhileD
                those_Some_map_the)
          show "g h # map the (takeWhile (\<lambda>s. \<exists>y. s = Some y) (map (map_option g) t)) =
                map g (the (map_option ((#) h) (those (takeWhile (\<lambda>s. \<exists>y. s = Some y) t))))"
            apply (simp add: 1)
            apply (subst those_Some_map_the)
            using set_takeWhileD apply fastforce
            apply (auto simp add: map_takeWhile [symmetric])
            using set_takeWhileD by force
        qed
        thus "the (those (takeWhile (\<lambda>s. \<exists>y. s = Some y) (right (last (map (map_tape g)
              (tapes ((TM.step M ^^ (LEAST n. TM.is_final M
              ((TM.step M ^^ n) (TM.initial_config M (map (inv g) w)))))
              (TM.initial_config M (map (inv g) w))))))))) =
              map g (the (map_option ((#) h) (those (takeWhile (\<lambda>s. \<exists>y. s = Some y) t))))"
          by simp
      next
        fix t :: "'a option list"
        assume a1: "right (last (tapes ((TM.step M ^^
                    (LEAST n. TM.is_final M ((TM.step M ^^ n)
                    (TM.initial_config M (map (inv g) w)))))
                    (TM.initial_config M (map (inv g) w))))) = None # t"
        have 1: "right (last (map (map_tape g) (tapes ((TM.step M ^^ (LEAST n. TM.is_final M
                 ((TM.step M ^^ n) (TM.initial_config M (map (inv g) w)))))
                 (TM.initial_config M (map (inv g) w)))))) = None#(map (map_option g) t)"
          by (metis (no_types, lifting) None_eq_map_option_iff TM.at_least_one_tape
              TM.run_tapes_len a1 bot_nat_0.not_eq_extremum last_map list.simps(9)
              list.size(3) tape.map_sel(3))
        show "the (those (takeWhile (\<lambda>s. \<exists>y. s = Some y) (right (last (map (map_tape g)
              (tapes ((TM.step M ^^ (LEAST n. TM.is_final M
              ((TM.step M ^^ n) (TM.initial_config M (map (inv g) w)))))
              (TM.initial_config M (map (inv g) w))))))))) = []"
          apply (subst those_Some_map_the)
           apply auto
          using set_takeWhileD apply fastforce
          by (simp add: 1)
      qed
      show "TM.clean_output_of ((TM.step (Abs_TM M') ^^
       (LEAST n. TM.is_final M ((TM.step M ^^ n) (TM.initial_config M (map (inv g) w)))))
       (TM.initial_config (Abs_TM M') w)) = Some (map g (f (map (inv g) w)))"
        unfolding TM.clean_output_of_def apply auto
        unfolding TM.output_of_def Let_def apply (cases "head (last (tapes
               ((TM.step (Abs_TM M') ^^
               (LEAST n. TM.is_final M ((TM.step M ^^ n)
               (TM.initial_config M (map (inv g) w)))))
               (TM.initial_config (Abs_TM M') w))))")
        unfolding 3 apply auto
        using a2 [unfolded TM.computes_def TM.computes_word_def, THEN spec,
            of "map (inv g) w", THEN conjunct2, unfolded TM.compute_def
            TM.compute_config_def TM.has_output_def TM.clean_output_of_def]
          apply (smt (verit) None_eq_map_option_iff TM.at_least_one_tape
            TM.clean_output_altdef TM.run_tapes_len TM_abbrevs.input_tape_empty_hd_iff
            bot_nat_0.not_eq_extremum last_map list.size(3) not_Some_eq option.inject
            tape.map_sel(2))
        apply (drule 4)
        using a2 [unfolded TM.computes_def TM.computes_word_def, THEN spec,
            of "map (inv g) w", THEN conjunct2, unfolded TM.compute_def
            TM.compute_config_def TM.has_output_def TM.clean_output_of_def TM.output_of_def
            Let_def] apply auto[1]
        unfolding 5 apply auto[1]
        unfolding 6 apply (metis list.simps(9))
        unfolding TM.clean_output_def apply simp
        by (smt (verit) TM.at_least_one_tape TM.clean_output_of_altdef TM.run_tapes_len
            TM_abbrevs.input_tape_map a9 bot_nat_0.not_eq_extremum last_map list.size(3)
            option.discI)
    qed
  qed
  moreover have "set w \<subseteq> S \<Longrightarrow> TM.time_bounded_word (Abs_TM M') T w" for w :: "'s list"
  proof (unfold TM.time_bounded_word_def TM.run_def)
    assume a7: "set w \<subseteq> S"
    have tpc_eq [simp]: "TM.tape_count (Abs_TM M') = TM.tape_count M"
      unfolding valid_tm_tape_count [OF valid_M']
      unfolding M'_def by simp
    have f1: "state (TM.steps (Abs_TM M') n (TM.initial_config (Abs_TM M') w)) =
          state (TM.steps M n (TM.initial_config M (map (inv g) w)))" and
         f2: "\<And>i. i < TM.tape_count M \<Longrightarrow> left (tapes (TM.steps (Abs_TM M') n
              (TM.initial_config (Abs_TM M') w)) ! i) =
              map (\<lambda>op. map_option g op) (left (tapes (TM.steps M n
              (TM.initial_config M (map (inv g) w))) ! i))" and
         f3: "\<And>i. i < TM.tape_count M \<Longrightarrow> right (tapes (TM.steps (Abs_TM M') n
              (TM.initial_config (Abs_TM M') w)) ! i) =
              map (\<lambda>op. map_option g op) (right (tapes (TM.steps M n
              (TM.initial_config M (map (inv g) w))) ! i))" and
         f4: "\<And>i. i < TM.tape_count M \<Longrightarrow> head (tapes (TM.steps (Abs_TM M') n
              (TM.initial_config (Abs_TM M') w)) ! i) =
              map_option g (head (tapes (TM.steps M n
              (TM.initial_config M (map (inv g) w))) ! i))" for n :: nat
    proof (induction n)
      case 0
      {
        case 1
        then show ?case apply (simp add: TM.initial_config_def)
          unfolding valid_tm_initial_state [OF valid_M']
          unfolding M'_def by simp
      next
        case 2
        then show ?case
          by (simp add: TM.initial_config_def TM_abbrevs.input_tape_def nth_Cons')
      next
        case 3
        then show ?case
        proof (auto simp add: TM.initial_config_def TM_abbrevs.input_tape_def nth_Cons')
          assume a8: "w \<noteq> []" and a9: "i = 0"
          have 1: "map (map_option g \<circ> Some) (tl (map (inv g) w)) =
                   map (Some \<circ> g) (tl (map (inv g) w))" by simp
          have 2: "\<And>f1 f2 l. map (f1 \<circ> f2) l = map f1 (map f2 l)" by simp
          have 3: "map g (tl (map (inv g) w)) = tl w" using a1 a7
            by (metis bij_betw_def map_map_inv_into_id map_tl)
          show "map Some (tl w) = map (map_option g \<circ> Some) (tl (map (inv g) w))"
            unfolding 1 unfolding 2 3 ..
        qed
      next
        case 4
        then show ?case
          apply (auto simp add: TM.initial_config_def TM_abbrevs.input_tape_def nth_Cons')
          using a1 a7 by (simp add: bij_betw_inv_into_right list.map_sel(1) subsetD)
      }
    next
      case IH: (Suc n)
      {
        case 1
        have 2: "map (map_option (inv g) \<circ> head)
                 (tapes ((TM.step (Abs_TM M') ^^ n) (TM.initial_config (Abs_TM M') w))) =
                 heads ((TM.step M ^^ n) (TM.initial_config M (map (inv g) w)))"
          apply (rule nth_equalityI)
           apply auto
           apply (simp add: TM.run_tapes_len)
          apply (subst IH(4))
           apply (simp add: TM.run_tapes_len)
          apply (subst nth_map)
           apply (simp add: TM.run_tapes_len)
        proof -
          fix i :: nat
          show "i < length (tapes ((TM.step (Abs_TM M') ^^ n)
                (TM.initial_config (Abs_TM M') w))) \<Longrightarrow>
                map_option (inv g) (map_option g
                (head (tapes ((TM.step M ^^ n)
                (TM.initial_config M (map (inv g) w))) ! i))) =
                head (tapes ((TM.step M ^^ n) (TM.initial_config M (map (inv g) w))) ! i)"
            apply (cases "head (tapes ((TM.step M ^^ n)
                (TM.initial_config M (map (inv g) w))) ! i)")
             apply auto
            using a1 by (simp add: bij_betw_inv_into_left)
        qed
        show ?case using 1 apply simp
          apply (subst (1 2) TM.step_def)
          apply auto
          using IH.IH(1) apply blast
          using IH.IH(1) M'_def valid_tm_final_states apply force
          using IH.IH(1) M'_def valid_tm_final_states apply force
          unfolding IH(1) valid_tm_next_state [OF valid_M']
          apply (subst M'_def)
          by (simp add: 2)
      next
        case 2
        have 1: "heads ((TM.step (Abs_TM M') ^^ n) (TM.initial_config (Abs_TM M') w)) =
                 map (map_option g) (heads ((TM.step M ^^ n)
                 (TM.initial_config M (map (inv g) w))))"
          apply (rule nth_equalityI)
           apply auto
           apply (simp add: TM.run_tapes_len)
          by (simp add: IH.IH(4) TM.run_tapes_len)
        have 3: "set (heads ((TM.step M ^^ n) (TM.initial_config M (map (inv g) w)))) \<subseteq>
                 options (image (inv g) S)" apply auto
          by (metis UNIV_I UNIV_options a1 bij_betw_def image_inv_f_f)
        have 4: "TM.TM.next_move M (state ((TM.step M ^^ n)
                 (TM.initial_config M (map (inv g) w))))
                 (map (map_option (inv g) \<circ> (map_option g \<circ> head))
                 (tapes ((TM.step M ^^ n) (TM.initial_config M (map (inv g) w))))) i =
                 TM.TM.next_move M (state ((TM.step M ^^ n)
                 (TM.initial_config M (map (inv g) w))))
                 (heads ((TM.step M ^^ n) (TM.initial_config M (map (inv g) w)))) i"
          apply (rule arg_cong [where x="map (map_option (inv g) \<circ> (map_option g \<circ> head))
                 (tapes ((TM.step M ^^ n) (TM.initial_config M (map (inv g) w))))"])
          using a1 by (simp add: bij_betw_imp_inj_on map_option.compositionality
              option.map_id)
        have 5: "map (map_option (inv g) \<circ> (map_option g \<circ> head))
                 (tapes ((TM.step M ^^ n) (TM.initial_config M (map (inv g) w)))) =
                 heads ((TM.step M ^^ n) (TM.initial_config M (map (inv g) w)))"
          using a1 by (simp add: bij_betw_imp_inj_on map_option.compositionality
              option.map_id)
        show ?case using 2 apply simp
          apply (subst (1 2) TM.step_def)
          apply auto
          using IH.IH(2) apply blast
            apply (smt (verit) IH.IH(1) M'_def select_convs(5) valid_M'
              valid_tm_final_states)
           apply (smt (verit) IH.IH(1) M'_def select_convs(5) valid_M'
              valid_tm_final_states)
          apply (subst (1 2) nth_map2)
              apply (simp_all add: TM.next_actions_simps(2))
            apply (simp_all add: TM.run_tapes_len)
          unfolding IH(1) TM.next_actions_def TM.next_writes_def TM.next_moves_def
          apply (simp add: 1)
          unfolding valid_tm_next_write [OF valid_M'] valid_tm_next_move [OF valid_M']
          apply (subst (1 2) M'_def)
          apply simp
          unfolding TM_abbrevs.tape_action_def apply simp
          apply (cases "TM.TM.next_move M (state ((TM.step M ^^ n)
                        (TM.initial_config M (map (inv g) w))))
                        (map (map_option (inv g) \<circ> (map_option g \<circ> head))
                        (tapes ((TM.step M ^^ n) (TM.initial_config M (map (inv g) w))))) i")
            apply (auto simp add: 4)
             apply (simp add: IH.IH(2) map_tl)
          unfolding TM_abbrevs.tape_write_hd 5 apply standard
          using IH.IH(2) apply blast
          by (simp add: IH.IH(2) TM_abbrevs.tape_shift.simps(5))
      next
        case 3
        have 1: "heads ((TM.step (Abs_TM M') ^^ n) (TM.initial_config (Abs_TM M') w)) =
                 map (map_option g) (heads ((TM.step M ^^ n)
                 (TM.initial_config M (map (inv g) w))))"
          apply (rule nth_equalityI)
           apply auto
           apply (simp add: TM.run_tapes_len)
          by (simp add: IH.IH(4) TM.run_tapes_len)
        have 2: "set (heads ((TM.step M ^^ n) (TM.initial_config M (map (inv g) w)))) \<subseteq>
                 options (image (inv g) S)" apply auto
          by (metis UNIV_I UNIV_options a1 bij_betw_def image_inv_f_f)
        have 4: "TM.TM.next_move M (state ((TM.step M ^^ n)
                 (TM.initial_config M (map (inv g) w))))
                 (map (map_option (inv g) \<circ> (map_option g \<circ> head))
                 (tapes ((TM.step M ^^ n) (TM.initial_config M (map (inv g) w))))) i =
                 TM.TM.next_move M (state ((TM.step M ^^ n)
                 (TM.initial_config M (map (inv g) w))))
                 (heads ((TM.step M ^^ n) (TM.initial_config M (map (inv g) w)))) i"
          apply (rule arg_cong [where x="map (map_option (inv g) \<circ> (map_option g \<circ> head))
                 (tapes ((TM.step M ^^ n) (TM.initial_config M (map (inv g) w))))"])
          using a1 by (simp add: bij_betw_imp_inj_on map_option.compositionality
              option.map_id)
        have 5: "map (map_option (inv g) \<circ> (map_option g \<circ> head))
                 (tapes ((TM.step M ^^ n) (TM.initial_config M (map (inv g) w)))) =
                 heads ((TM.step M ^^ n) (TM.initial_config M (map (inv g) w)))"
          using a1 by (simp add: bij_betw_imp_inj_on map_option.compositionality
              option.map_id)
        then show ?case using 3 apply simp
          apply (subst (1 2) TM.step_def)
          apply auto
          using IH.IH(3) apply blast
            apply (smt (verit) IH.IH(1) M'_def select_convs(5) valid_M'
              valid_tm_final_states)
           apply (smt (verit) IH.IH(1) M'_def select_convs(5) valid_M'
              valid_tm_final_states)
          apply (subst (1 2) nth_map2)
              apply (simp_all add: TM.next_actions_simps(2))
            apply (simp_all add: TM.run_tapes_len)
          unfolding IH(1) TM.next_actions_def TM.next_writes_def TM.next_moves_def
          apply (simp add: 1)
          unfolding valid_tm_next_write [OF valid_M'] valid_tm_next_move [OF valid_M']
          apply (subst (1 2) M'_def)
          apply simp
          unfolding TM_abbrevs.tape_action_def apply simp
          apply (cases "TM.TM.next_move M (state ((TM.step M ^^ n)
                        (TM.initial_config M (map (inv g) w))))
                        (map (map_option (inv g) \<circ> (map_option g \<circ> head))
                        (tapes ((TM.step M ^^ n) (TM.initial_config M (map (inv g) w))))) i")
          apply (simp add: 5 TM_abbrevs.tape_write_hd)
             apply (simp add: IH.IH(3) map_tl)
          unfolding TM_abbrevs.tape_write_hd 4 apply simp
          apply (simp add: IH.IH(3) map_tl)
          apply (simp add: IH.IH(2) TM_abbrevs.tape_shift.simps(5))
          using IH.IH(3) by blast
      next
        case 4
        have 1: "tapes ((TM.step (Abs_TM M') ^^ n) (TM.initial_config (Abs_TM M') w)) ! i =
                 map_tape g (tapes ((TM.step M ^^ n)
                 (TM.initial_config M (map (inv g) w))) ! i)"
          by (simp add: 4 IH.IH(2) IH.IH(3) IH.IH(4) tape.expand tape.map_sel(1)
              tape.map_sel(2) tape.map_sel(3))
        have 2: "head (tapes ((TM.step M ^^ n) (TM.initial_config M (map (inv g) w))) ! i) \<in>
                 options (image (inv g) S)"
          by (metis UNIV_I UNIV_options a1 bij_betw_def image_inv_f_f)
        have 3: "\<And>i. i < TM.tape_count M \<Longrightarrow> map (map_option (inv g) \<circ> head)
                 (tapes ((TM.step (Abs_TM M') ^^ n) (TM.initial_config (Abs_TM M') w))) ! i =
                 heads ((TM.step M ^^ n) (TM.initial_config M (map (inv g) w))) ! i"
          apply (subst nth_map)
          using 4 apply (simp add: TM.run_tapes_len)
          apply auto
          unfolding IH(4) apply (subst nth_map)
          using 4 apply (simp add: TM.run_tapes_len)
        proof -
          fix i :: nat
          show "i < TM.TM.tape_count M \<Longrightarrow> map_option (inv g)
                (map_option g (head (tapes ((TM.step M ^^ n)
                (TM.initial_config M (map (inv g) w))) ! i))) =
                head (tapes ((TM.step M ^^ n) (TM.initial_config M (map (inv g) w))) ! i)"
            apply (cases "head (tapes ((TM.step M ^^ n)
                (TM.initial_config M (map (inv g) w))) ! i)")
           apply auto
            using a1 2 by (simp add: bij_betw_inv_into_left)
        qed
        have 5: "TM.TM.next_move M (state ((TM.step M ^^ n)
                 (TM.initial_config M (map (inv g) w))))
                 (map (map_option (inv g) \<circ> head)
                 (tapes ((TM.step (Abs_TM M') ^^ n) (TM.initial_config (Abs_TM M') w)))) i =
                 TM.TM.next_move M (state ((TM.step M ^^ n)
                 (TM.initial_config M (map (inv g) w))))
                 (heads ((TM.step M ^^ n) (TM.initial_config M (map (inv g) w)))) i"
        proof -
          have "length (map (map_option (inv g) \<circ> head)
                (tapes ((TM.step (Abs_TM M') ^^ n) (TM.initial_config (Abs_TM M') w)))) =
                length (heads ((TM.step M ^^ n) (TM.initial_config M (map (inv g) w))))"
            by (simp add: TM.run_tapes_len)
          hence 1: "map (map_option (inv g) \<circ> head)
                    (tapes ((TM.step (Abs_TM M') ^^ n) (TM.initial_config (Abs_TM M') w))) =
                    heads ((TM.step M ^^ n) (TM.initial_config M (map (inv g) w)))" using 3
            by (metis TM.run_tapes_len length_map nth_equalityI)
          show "TM.TM.next_move M (state ((TM.step M ^^ n)
                (TM.initial_config M (map (inv g) w))))
                (map (map_option (inv g) \<circ> head)
                (tapes ((TM.step (Abs_TM M') ^^ n) (TM.initial_config (Abs_TM M') w)))) i =
                TM.TM.next_move M (state ((TM.step M ^^ n)
                (TM.initial_config M (map (inv g) w))))
                (heads ((TM.step M ^^ n) (TM.initial_config M (map (inv g) w)))) i"
            unfolding 1 ..
        qed
        show ?case using 4 apply simp
          apply (subst (1 2) TM.step_def)
          apply auto
          using IH.IH(4) apply blast
            apply (smt (verit, del_insts) IH.IH(1) M'_def select_convs(5) valid_M'
              valid_tm_final_states)
           apply (smt (verit, del_insts) IH.IH(1) M'_def select_convs(5) valid_M'
              valid_tm_final_states)
          apply (subst (1 2) nth_map2)
              apply (simp_all add: TM.next_actions_simps(2))
            apply (simp_all add: TM.run_tapes_len)
          unfolding TM.next_actions_def TM.next_writes_def TM.next_moves_def apply simp
          unfolding IH(1) valid_tm_next_write [OF valid_M'] valid_tm_next_move [OF valid_M']
          apply (subst (1 4) M'_def)
          apply (simp add: 1 3 [OF 4] 5)
          apply (cases "TM.next_move M (state ((TM.step M ^^ n)
                        (TM.initial_config M (map (inv g) w))))
                        (heads ((TM.step M ^^ n) (TM.initial_config M (map (inv g) w)))) i")
          unfolding TM_abbrevs.tape_action_def apply auto
            apply (cases "left (map_tape g (tapes ((TM.step M ^^ n)
                          (TM.initial_config M (map (inv g) w))) ! i))")
          apply auto
             apply (simp add: tape.map_sel(1))
            apply (subst Shift_Left_is_left_not_empty)
             apply auto
            apply (smt (verit, best) TM_abbrevs.map_tape_def TM_abbrevs.tape_shift.simps(2)
              TM_abbrevs.tape_shift_map left_after_write tape.map_sel(1) tape.sel(2))
           apply (smt (verit, del_insts) Shift_Right_is_right_not_empty
              TM_abbrevs.tape_shift_map TM_abbrevs.tape_write_map head_right_empty
              right_after_write tape.map_sel(2))
          unfolding TM_abbrevs.tape_shift.simps(5) TM_abbrevs.tape_write_hd
          by (metis 3 TM.run_tapes_len length_map nth_equalityI tpc_eq)
      }
    qed
    have 1: "TM.is_final (Abs_TM M') ((TM.step (Abs_TM M') ^^ n)
             (TM.initial_config (Abs_TM M') w)) \<longleftrightarrow>
             TM.is_final M ((TM.step M ^^ n) (TM.initial_config M (map (inv g) w)))"
      for n :: nat
      by (smt (verit, ccfv_threshold) M'_def TM.is_final_def f1 select_convs(5) valid_M'
          valid_tm_final_states)
    show "TM.is_final (Abs_TM M') ((TM.step (Abs_TM M') ^^ T (length w))
          (TM.initial_config (Abs_TM M') w))" apply (simp add: 1)
      using a3 unfolding TM.time_bounded_word_def TM.run_def by (metis length_map)
  qed
  ultimately show "\<exists>M::('q, 's, 'l) TM. TM.TM.symbols M = S \<and> (\<forall>w\<in>S*. TM.computes_word M w
                   (map g (f (map (inv g) w))) \<and> TM.time_bounded_word M T w)" by blast
qed

lemma typed_comp_in_time_sym_type: "bij_betw (g::'a \<Rightarrow> 's) UNIV S \<Longrightarrow>
       typed_computable_in_time TYPE('q) TYPE('l) T (f::'a list \<Rightarrow> 'a list) \<Longrightarrow>
       \<exists>M::('q, 's, 'l) TM. TM.symbols M = S \<and>
       (\<forall>w\<in>S*. TM.computes_word M w (map g (f (map (inv g) w)))) \<and> TM.time_bounded M T"
proof (frule (1) typed_comp_in_time_words, auto)
  fix M :: "('q, 's, 'l) TM"
  assume a1: "\<forall>w\<in>(TM.TM.symbols M)*. TM.computes_word M w (map g (f (map (inv g) w))) \<and>
              TM.time_bounded_word M T w" and
         a2: "S = TM.TM.symbols M" and
         a3: "bij_betw g UNIV (TM.TM.symbols M)"
  obtain fs :: 'q where fs_final: "fs \<in> TM.final_states M"
    using a1 [THEN bspec, of "[]", simplified, THEN conjunct2] TM.time_bounded_word_final_state by blast
  obtain sym :: 's where sym_in_M: "sym \<in> TM.symbols M" by fastforce
  define M' :: "('q, 's, 'l) TM_record" where
    "M' \<equiv> TM (TM.tape_count M) (TM.symbols M) (TM.states M) (TM.initial_state M) (TM.final_states M)
           (TM.label M) (\<lambda>st hds. if hds ! 0 \<notin> options (TM.symbols M) then fs else TM.next_state M st hds)
           (TM.next_write M) (TM.next_move M)"
  have valid_M' [simp, intro]: "valid_TM M'"
    apply unfold_locales
    unfolding M'_def using fs_final by auto
  have M'_syms [simp]: "TM.TM.symbols (Abs_TM M') = TM.TM.symbols M"
    unfolding valid_tm_symbols [OF valid_M'] unfolding M'_def by simp
  have M'_init_state [simp]: "TM.initial_state (Abs_TM M') = TM.initial_state M"
    unfolding valid_tm_initial_state [OF valid_M'] unfolding M'_def by simp
  have M'_final_states [simp]: "TM.final_states (Abs_TM M') = TM.final_states M"
    unfolding valid_tm_final_states [OF valid_M'] unfolding M'_def by simp
  have M'_next_state [simp]: "TM.next_state (Abs_TM M') =
                           (\<lambda>st hds. if hds ! 0 \<notin> options (TM.symbols M) then fs else TM.next_state M st hds)"
    unfolding valid_tm_next_state [OF valid_M'] unfolding M'_def by simp
  have M'_next_write [simp]: "TM.next_write (Abs_TM M') = TM.next_write M"
    unfolding valid_tm_next_write [OF valid_M'] unfolding M'_def by simp
  have M'_next_move [simp]: "TM.next_move (Abs_TM M') = TM.next_move M"
    unfolding valid_tm_next_move [OF valid_M'] unfolding M'_def by simp
  have M'_label [simp]: "TM.label (Abs_TM M') = TM.label M"
    unfolding valid_tm_label [OF valid_M'] unfolding M'_def by simp
  have M'_tape_count [simp]: "TM.tape_count (Abs_TM M') = TM.tape_count M"
    unfolding valid_tm_tape_count [OF valid_M'] unfolding M'_def by simp
  have f11: "state (TM.steps (Abs_TM M') k (TM.initial_config (Abs_TM M') w)) =
             state (TM.steps M k (TM.initial_config M w))" and
       f12: "tapes (TM.steps (Abs_TM M') k (TM.initial_config (Abs_TM M') w)) =
             tapes (TM.steps M k (TM.initial_config M w))"
    if "\<And>n. n < k \<Longrightarrow> head (tapes (TM.steps (Abs_TM M') n (TM.initial_config (Abs_TM M') w)) ! 0) \<in>
        options (TM.symbols M)" for k :: nat and w :: "'s list" using that
  proof (induction k)
    case 0
    {
      case 1
      then show ?case apply simp
        unfolding TM.initial_config_def by simp
    next
      case 2
      then show ?case apply simp
        unfolding TM.initial_config_def by simp
    }
  next
    case (Suc k)
    {
      case 1
      hence *: "\<And>n. n \<le> k \<Longrightarrow> head (tapes ((TM.step (Abs_TM M') ^^ n) (TM.initial_config (Abs_TM M') w)) ! 0) \<in>
                options (TM.TM.symbols M)" by simp
      show ?case apply simp
        apply (subst (1 2) TM.step_def)
        apply auto
        unfolding Suc(1) [OF *, simplified] apply auto
        using * [OF Nat.le_refl] apply (subst (asm) nth_map)
          apply auto
         apply (metis TM.run_tapes_len TM.at_least_one_tape list.size(3) bot_nat_0.not_eq_extremum)
        unfolding Suc(2) [OF *, simplified] ..
    next
      case 2
      hence *: "\<And>n. n < k \<Longrightarrow> head (tapes ((TM.step (Abs_TM M') ^^ n) (TM.initial_config (Abs_TM M') w)) ! 0) \<in>
                options (TM.TM.symbols M)" by simp
      show ?case apply simp
        apply (subst (1 2) TM.step_def)
        apply auto
        unfolding Suc(1) [OF *, simplified] apply auto
         apply (rule Suc(2))
         apply (erule *)
        unfolding TM.next_actions_def TM.next_writes_def TM.next_moves_def TM_abbrevs.tape_action_def apply simp
        unfolding Suc(2) [OF *, simplified] ..
    }
  qed
  have f1: "(\<And>n. n < k \<Longrightarrow> head (tapes (TM.steps (Abs_TM M') n (TM.initial_config (Abs_TM M') w)) ! 0) \<in>
            options (TM.symbols M)) \<Longrightarrow> TM.steps (Abs_TM M') k (TM.initial_config (Abs_TM M') w) =
            TM.steps M k (TM.initial_config M w)" for w :: "'s list" and k :: nat
    using f11 [of k w] f12 [of k w] TM_config_eq by blast
  show "\<exists>M'::('q, 's, 'l) TM. TM.TM.symbols M' = TM.TM.symbols M \<and>
        (\<forall>w\<in>(TM.TM.symbols M)*. TM.computes_word M' w (map g (f (map (inv g) w)))) \<and>
        (\<forall>w. TM.time_bounded_word M' T w)"
  proof (rule exI [where x="Abs_TM M'"], auto)
    show tb: "TM.time_bounded_word (Abs_TM M') T w" for w :: "'s list"
      unfolding TM.time_bounded_word_def TM.is_final_def TM.run_def
      apply (cases "\<forall>n < T (length w). head (tapes (TM.steps (Abs_TM M') n
                  (TM.initial_config (Abs_TM M') w)) ! 0) \<in> options (TM.symbols M)")
       apply auto
    proof (simp add: f1)
      assume a4: "\<forall>n<T (length w).
                  head (tapes ((TM.step (Abs_TM M') ^^ n) (TM.initial_config (Abs_TM M') w)) ! 0)
                  \<in> options (TM.TM.symbols M)"
      have 1: "\<And>n. n<T (length w) \<Longrightarrow> head (tapes ((TM.step M ^^ n) (TM.initial_config M w)) ! 0)
                  \<in> options (TM.TM.symbols M)" using a4 apply (subst f1 [symmetric])
        by simp_all
      define w' :: "'s list" where "w' \<equiv> map (\<lambda>s. if s \<in> TM.symbols M then s else sym) w"
      have w'_syms: "set w' \<subseteq> TM.symbols M"
        unfolding w'_def by (auto simp add: sym_in_M)
      have w'_tb: "state ((TM.step M ^^ T (length w')) (TM.initial_config M w')) \<in> TM.TM.final_states M"
        using a1 [THEN bspec, of w', simplified, OF w'_syms, THEN conjunct2]
        unfolding TM.time_bounded_word_def TM.is_final_def TM.run_def .
      have w'_length: "length w' = length w"
        unfolding w'_def by simp
      have 2: "state ((TM.step M ^^ n) (TM.initial_config M w)) =
               state ((TM.step M ^^ n) (TM.initial_config M w'))" and
           3: "heads ((TM.step M ^^ n) (TM.initial_config M w)) =
               heads ((TM.step M ^^ n) (TM.initial_config M w'))" and
           4: "\<And>i. i < TM.tape_count M \<Longrightarrow> left (tapes (TM.steps M n (TM.initial_config M w')) ! i) =
               left (tapes (TM.steps M n (TM.initial_config M w)) ! i)" and
           5: "\<And>i. i < TM.tape_count M \<Longrightarrow> i > 0 \<Longrightarrow> right (tapes (TM.steps M n (TM.initial_config M w')) ! i) =
               right (tapes (TM.steps M n (TM.initial_config M w)) ! i)" and
           6: "\<exists>k suff. set (take k (right (tapes (TM.steps M n (TM.initial_config M w')) ! 0))) \<subseteq>
               options (TM.symbols M) \<and> (suff \<noteq> [] \<longrightarrow> hd suff \<notin> options (TM.symbols M)) \<and>
               right (tapes (TM.steps M n (TM.initial_config M w)) ! 0) =
               take k (right (tapes (TM.steps M n (TM.initial_config M w')) ! 0)) @ suff" and
           7: "length (right (tapes (TM.steps M n (TM.initial_config M w)) ! 0)) =
               length (right (tapes (TM.steps M n (TM.initial_config M w')) ! 0))"
           if "n < T (length w)" for n :: nat using that
      proof (induction n)
        case 0
        {
          case 1
          then show ?case by (simp add: TM.initial_config_def)
        next
          case 2
          then show ?case apply simp
            unfolding TM.initial_config_def TM_abbrevs.input_tape_def apply auto
            unfolding w'_def apply auto
            using 1 [of 0, simplified, unfolded TM.initial_config_def TM_abbrevs.input_tape_def]
            by (simp add: list.map_sel(1))
        next
          case 3
          then show ?case apply simp
            unfolding TM.initial_config_def TM_abbrevs.input_tape_def apply auto
            using w'_def apply blast
            using w'_def apply blast
            apply (cases i)
            by simp_all
        next
          case 4
          then show ?case apply simp
            unfolding TM.initial_config_def TM_abbrevs.input_tape_def by simp
        next
          case 5
          define k :: nat where "k \<equiv> length (takeWhile (\<lambda>s. s \<in> options (TM.symbols M))
                                     (right (tapes ((TM.step M ^^ 0) (TM.initial_config M w)) ! 0)))"
          have 1: "set (take k (right (tapes ((TM.step M ^^ 0) (TM.initial_config M w)) ! 0))) \<subseteq>
                   options (TM.TM.symbols M)"
            unfolding k_def apply auto
            by (metis set_takeWhileD takeWhile_eq_take)
          have 2: "drop k (right (tapes ((TM.step M ^^ 0) (TM.initial_config M w)) ! 0)) \<noteq> [] \<Longrightarrow>
                   hd (drop k (right (tapes ((TM.step M ^^ 0) (TM.initial_config M w)) ! 0))) \<notin>
                   options (TM.TM.symbols M)" using 1
            by (metis drop_eq_Nil hd_drop_conv_nth k_def linorder_not_less nth_length_takeWhile)
          have 3: "\<not> length w - Suc 0 \<le> k \<Longrightarrow> \<exists>h t. drop k (map Some (tl w)) = h#t"
            by (metis One_nat_def drop_eq_Nil drop_map length_tl list.exhaust list.map_disc_iff)
          have 4: "take (length (takeWhile (\<lambda>s. s \<in> options (TM.TM.symbols M)) (map Some (tl w))))
                   (map Some (tl (map (\<lambda>s. if s \<in> TM.TM.symbols M then s else sym) w))) =
                   take (length (takeWhile (\<lambda>s. s \<in> options (TM.TM.symbols M)) (map Some (tl w))))
                   (map Some (tl w))"
            apply (rule nth_equalityI)
             apply auto
            apply (subst (1 2) nth_tl)
              apply auto
            by (metis One_nat_def Some_options_iff length_tl nth_map nth_mem nth_tl set_takeWhileD
                takeWhile_nth)
          show ?case apply (rule exI [where x=k])
            apply (rule exI [where x="drop k (right (tapes ((TM.step M ^^ 0) (TM.initial_config M w)) ! 0))"])
            apply auto
            unfolding TM.initial_config_def TM_abbrevs.input_tape_def apply auto
                apply (cases "w' = []")
                 apply auto
            unfolding w'_def apply auto
              apply (drule set_take_subset [THEN subsetD])
              apply auto
              apply (drule set_tl_subset [THEN subsetD])
              apply auto
              apply (rule sym_in_M)
             apply (cases "w = []")
              apply auto
             apply (drule 3)
             apply auto
            unfolding k_def apply auto
            unfolding TM.initial_config_def TM_abbrevs.input_tape_def apply auto
             apply (erule (1) hd_drop_length_takeWhile)
            unfolding 4 by simp
        next
          case 6
          then show ?case apply simp
            unfolding TM.initial_config_def TM_abbrevs.input_tape_def apply auto
            unfolding w'_def by simp_all
        }
      next
        case (Suc n)
        {
          case 1
          hence *: "n < T (length w)" by simp
          show ?case apply simp
            apply (subst (1 2) TM.step_def)
            apply auto
            unfolding Suc(1) [OF *] apply auto
            unfolding Suc(2) [OF *] ..
        next
          case 2
          hence *: "n < T (length w)" by simp
          show ?case using 1 [OF 2] apply simp
            apply (subst (1 2) TM.step_def)
            apply (subst (asm) TM.step_def)
            apply auto
            unfolding Suc(1) [OF *] apply auto
            unfolding Suc(2) [OF *] apply standard
            unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_writes_def
              TM.next_moves_def apply (rule nth_equalityI)
             apply auto
             apply (simp_all add: TM.run_tapes_len)
          proof -
            fix i :: nat
            assume a5: "i < TM.TM.tape_count M"
            show "head (TM_abbrevs.tape_shift (TM.TM.next_move M (state ((TM.step M ^^ n)
                  (TM.initial_config M w'))) (heads ((TM.step M ^^ n) (TM.initial_config M w'))) 0)
                  (TM_abbrevs.tape_write (TM.TM.next_write M (state ((TM.step M ^^ n) (TM.initial_config M w')))
                  (heads ((TM.step M ^^ n) (TM.initial_config M w'))) 0)
                  (tapes ((TM.step M ^^ n) (TM.initial_config M w)) ! 0))) \<in> options (TM.TM.symbols M) \<Longrightarrow>
                  head (TM_abbrevs.tape_shift (TM.TM.next_move M (state ((TM.step M ^^ n)
                  (TM.initial_config M w'))) (heads ((TM.step M ^^ n) (TM.initial_config M w'))) i)
                  (TM_abbrevs.tape_write (TM.TM.next_write M (state ((TM.step M ^^ n) (TM.initial_config M w')))
                  (heads ((TM.step M ^^ n) (TM.initial_config M w'))) i)
                  (tapes ((TM.step M ^^ n) (TM.initial_config M w)) ! i))) =
                  head (TM_abbrevs.tape_shift (TM.TM.next_move M (state ((TM.step M ^^ n)
                  (TM.initial_config M w'))) (heads ((TM.step M ^^ n) (TM.initial_config M w'))) i)
                  (TM_abbrevs.tape_write (TM.TM.next_write M (state ((TM.step M ^^ n) (TM.initial_config M w')))
                  (heads ((TM.step M ^^ n) (TM.initial_config M w'))) i)
                  (tapes ((TM.step M ^^ n) (TM.initial_config M w')) ! i)))"
              apply (cases "TM.TM.next_move M (state ((TM.step M ^^ n) (TM.initial_config M w')))
                            (heads ((TM.step M ^^ n) (TM.initial_config M w'))) i")
                apply auto
                apply (cases "left (tapes ((TM.step M ^^ n) (TM.initial_config M w)) ! i)")
                 apply auto
                 apply (simp add: * Suc.IH(3) a5)
                apply (simp add: * Shift_Left_is_left_not_empty Suc.IH(3) a5)
               apply (cases "right (tapes ((TM.step M ^^ n) (TM.initial_config M w)) ! i)")
                apply auto
              using Suc(6) [OF *] * Suc.IH(4) a5 apply force
               apply (subst (1 2) Shift_Right_is_right_not_empty)
                 apply auto
                apply (cases i)
                 apply auto
              using Suc(6) [OF *] apply simp
              using Suc(4) [OF _ _ *] a5 apply simp
               apply (cases "i = 0")
                apply auto
                apply (subst (asm) Shift_Right_is_right_not_empty)
                 apply auto
              using Suc(5) [OF *] apply auto[1]
                 apply (metis bot_nat_0.extremum hd_take le_eq_less_or_eq list.distinct(1) list.sel(1) take0)
                apply (metis bot_nat_0.not_eq_extremum hd_append2 hd_take list.sel(1) self_append_conv2
                  take_eq_Nil)
              unfolding Suc(4) [OF a5 _ *] apply simp
              unfolding TM_abbrevs.tape_shift.simps TM_abbrevs.tape_write_def by simp
          qed
        next
          case 3
          hence *: "n < T (length w)" by simp
          show ?case apply simp
            apply (subst (1 2) TM.step_def)
            apply auto
            unfolding Suc(1) [OF *] apply auto
            using * "3.prems"(1) Suc.IH(3) apply blast
            apply (subst (1 2) nth_map2)
                apply (simp add: "3.prems"(1) TM.next_actions_simps(2))
               apply (simp add: "3.prems"(1) TM.run_tapes_len)
              apply (simp add: "3.prems"(1) TM.next_actions_simps(2))
             apply (simp add: "3.prems"(1) TM.run_tapes_len)
            unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_writes_def TM.next_moves_def
            using 3(1) apply simp
            unfolding Suc(2) [OF *]
            apply (cases "TM.TM.next_move M (state ((TM.step M ^^ n) (TM.initial_config M w')))
                          (heads ((TM.step M ^^ n) (TM.initial_config M w'))) i")
              apply auto
            using * Suc.IH(3) apply presburger
            unfolding TM_abbrevs.tape_write_def apply auto
            using * Suc.IH(3) apply blast
            unfolding TM_abbrevs.tape_shift.simps apply simp
            using * Suc.IH(3) by blast
        next
          case 4
          hence *: "n < T (length w)" by simp
          show ?case apply simp
            apply (subst (1 2) TM.step_def)
            apply auto
            unfolding Suc(1) [OF *] apply auto
            using * "4.prems"(1,2) Suc.IH(4) apply blast
            unfolding Suc(2) [OF *] apply (subst (1 2) nth_map2)
               apply (simp add: "4.prems"(1) TM.next_actions_simps(2))
              apply (simp add: "4.prems"(1) TM.run_tapes_len)
             apply (simp add: "4.prems"(1) TM.run_tapes_len)
            unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_writes_def TM.next_moves_def
            using 4(1) apply simp
            apply (cases "TM.TM.next_move M (state ((TM.step M ^^ n) (TM.initial_config M w')))
                          (heads ((TM.step M ^^ n) (TM.initial_config M w'))) i")
              apply auto
            unfolding TM_abbrevs.tape_write_def apply auto
            using 4(2) * Suc.IH(4) apply blast
            using * "4.prems"(2) Suc.IH(4) apply presburger
            unfolding TM_abbrevs.tape_shift.simps apply simp
            using * "4.prems"(2) Suc.IH(4) by blast
        next
          case 5
          hence *: "n < T (length w)" by simp
          note Suc(5) [OF *]
          then obtain k :: nat and suff :: "'s option list" where
            k_in_syms: "set (take k (right (tapes ((TM.step M ^^ n) (TM.initial_config M w')) ! 0))) \<subseteq>
                        options (TM.TM.symbols M)" and
            hd_suff_not_syms: "suff \<noteq> [] \<Longrightarrow> hd suff \<notin> options (TM.TM.symbols M)" and
            right_eq: "right (tapes ((TM.step M ^^ n) (TM.initial_config M w)) ! 0) =
                       take k (right (tapes ((TM.step M ^^ n) (TM.initial_config M w')) ! 0)) @ suff" by blast
          show ?case using 1 [OF 5(1)] apply simp
            apply (subst (1 2) TM.step_def)
            apply (subst (asm) TM.step_def)
            unfolding Suc(1) [OF *] apply auto
             apply (rule exI [where x=k])
            using k_in_syms apply simp
             apply (rule exI [where x=suff])
             apply auto
            using hd_suff_not_syms right_eq apply simp
             apply (subst right_eq)
             apply (subst TM.step_def)
             apply simp
            apply (subst (1 2) nth_map2)
                apply auto
                apply (metis One_nat_def TM.at_least_one_tape' TM.next_actions_simps(2) le_refl list.size(3)
                not_less_eq_eq)
               apply (metis TM.at_least_one_tape TM.run_tapes_len less_numeral_extra(3) list.size(3))
              apply (metis TM.next_actions_simps(2) list.size(3) One_nat_def not_less_eq_eq le_refl
                TM.at_least_one_tape')
             apply (metis TM.at_least_one_tape TM.run_tapes_len less_numeral_extra(3) list.size(3))
            apply (subst (asm) nth_map2)
              apply (simp add: TM.next_actions_simps(2))
             apply (simp add: TM.run_tapes_len)
            unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_writes_def TM.next_moves_def
            apply simp
            unfolding Suc(1) [OF *] Suc(2) [OF *]
            apply (cases "TM.TM.next_move M (state ((TM.step M ^^ n) (TM.initial_config M w')))
                          (heads ((TM.step M ^^ n) (TM.initial_config M w'))) 0")
              apply auto
            unfolding TM_abbrevs.tape_write_def apply auto
              apply (rule exI [where x="Suc k"])
              apply simp
              apply (rule conjI)
               apply (rule TM.next_write_valid)
            using TM_steps_valid_stateI w'_syms apply blast
                 apply (simp add: TM.run_tapes_len)
                apply (metis TM.run_tapes_len TM.tapes_heads_valid in_set_conv_nth set_tape_in_symbols w'_syms)
               apply simp
              apply (rule conjI)
            using k_in_syms apply force
              apply (rule exI [where x=suff])
              apply auto
            using hd_suff_not_syms apply blast
              apply (subst TM.step_def)
              apply auto
              apply (subst nth_map2)
                apply (simp add: TM.next_actions_simps(2))
               apply (simp add: TM.run_tapes_len)
            unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_moves_def TM.next_writes_def
              apply simp
            unfolding TM_abbrevs.tape_write_def apply simp
              apply (rule right_eq)
             apply (rule exI [where x="k - 1"])
             apply (rule conjI)
            using k_in_syms apply (metis order_trans set_tl_subset tl_take)
             apply (cases "k = 0")
              apply (rule exI [where x="tl suff"])
              apply auto[1]
            using Shift_Right_is_right_not_empty[of
                "Tape (left (tapes ((TM.step M ^^ n) (TM.initial_config M w)) ! k))
                 (TM.TM.next_write M (state ((TM.step M ^^ n) (TM.initial_config M w')))
                 (heads ((TM.step M ^^ n) (TM.initial_config M w'))) k) suff"]
                hd_suff_not_syms right_eq apply force
              apply (simp add: right_eq)
             apply (rule exI [where x=suff])
             apply auto
            using hd_suff_not_syms apply fastforce
             apply (subst right_eq [THEN arg_cong, of tl])
             apply (cases "right (tapes ((TM.step M ^^ n) (TM.initial_config M w')) ! 0)")
              apply auto
              apply (metis * Suc.IH(6) TM.at_least_one_tape TM.run_tapes_len length_0_conv list.sel(2)
                right_empty_after_Shift_Right right_eq self_append_conv take_eq_Nil)
             apply (subst TM.step_def)
             apply simp
             apply (subst nth_map2)
               apply (metis TM.at_least_one_tape TM.next_actions_simps(2))
              apply (metis TM.run_tapes_len TM.at_least_one_tape)
            unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_writes_def TM.next_moves_def
             apply simp
             apply (simp add: take_Cons')
            unfolding TM_abbrevs.tape_shift.simps apply simp
            apply (rule exI [where x=k])
            apply (rule conjI)
             apply (rule k_in_syms)
            apply (rule exI [where x=suff])
            apply auto
            using hd_suff_not_syms apply blast
            by (simp add: TM.run_tapes_len no_move_same_right right_eq)
        next
          case 6
          hence *: "n < T (length w)" by simp
          show ?case apply simp
            apply (subst (1 2) TM.step_def)
            apply auto
            unfolding Suc(1) [OF *] apply auto
            using * Suc.IH(6) apply fastforce
            apply (subst (1 2) nth_map2)
                apply (simp add: TM.next_actions_simps(2))
               apply (simp add: TM.run_tapes_len)
              apply (simp add: TM.next_actions_simps(2))
             apply (simp add: TM.run_tapes_len)
            unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_moves_def TM.next_writes_def
            apply simp
            unfolding Suc(1) [OF *] Suc(2) [OF *]
            apply (cases "TM.TM.next_move M (state ((TM.step M ^^ n) (TM.initial_config M w')))
                          (heads ((TM.step M ^^ n) (TM.initial_config M w'))) 0")
              apply auto
            using * Suc.IH(6) apply blast
            using * Suc.IH(6) apply argo
            by (simp add: * Suc.IH(6) TM_abbrevs.tape_shift.simps(5))
        }
      qed
      show "state ((TM.step M ^^ T (length w)) (TM.initial_config M w)) \<in> TM.TM.final_states M"
        apply (cases "T (length w) = 0")
         apply auto
        using a1 [THEN bspec, of w', simplified, OF w'_syms, THEN conjunct2,
            unfolded TM.time_bounded_word_def w'_length TM.is_final_def TM.run_def] apply simp
         apply (subst TM.initial_config_def)
         apply (subst (asm) TM.initial_config_def)
         apply simp
      proof -
        assume a5: "0 < T (length w)"
        hence 8: "T (length w) - 1 < T (length w)" and 9: "Suc (T (length w) - 1) = T (length w)" by simp_all
        have 10: "state ((TM.step M ^^ Suc (T (length w) - 1)) (TM.initial_config M w')) \<in> TM.TM.final_states M"
          using a1 [THEN bspec, simplified, OF w'_syms, THEN conjunct2, unfolded TM.time_bounded_word_def
              TM.is_final_def TM.run_def] unfolding 9 w'_length .
        show ?thesis apply (subst 9 [symmetric])
          apply simp
          apply (subst TM.step_def)
          apply auto
          unfolding 2 [OF 8, simplified] 3 [OF 8, simplified] using 10 apply simp
          apply (subst (asm) TM.step_def)
          by simp
      qed
    next
      fix n :: nat
      assume a4: "n < T (length w)" and
             a5: "head (tapes ((TM.step (Abs_TM M') ^^ n) (TM.initial_config (Abs_TM M') w)) ! 0)
                  \<notin> options (TM.TM.symbols M)"
      define n' :: nat where "n' \<equiv> (LEAST n. head (tapes ((TM.step (Abs_TM M') ^^ n)
                                    (TM.initial_config (Abs_TM M') w)) ! 0) \<notin> options (TM.TM.symbols M))"
      note 1 = LeastI [of "\<lambda>n. head (tapes ((TM.step (Abs_TM M') ^^ n)
                           (TM.initial_config (Abs_TM M') w)) ! 0) \<notin> options (TM.TM.symbols M)",
          OF a5, folded n'_def]
      note 2 = Least_le [of "\<lambda>n. head (tapes ((TM.step (Abs_TM M') ^^ n)
                             (TM.initial_config (Abs_TM M') w)) ! 0) \<notin> options (TM.TM.symbols M)", folded n'_def]
      hence 3: "\<And>k. k < n' \<Longrightarrow> head (tapes ((TM.step (Abs_TM M') ^^ k) (TM.initial_config (Abs_TM M') w)) ! 0) \<in>
                options (TM.TM.symbols M)" by fastforce
      have 4: "Suc n' \<le> T (length w)"
        using 2 [OF a5] a4 by simp
      have 5: "state ((TM.step (Abs_TM M') ^^ (Suc n')) (TM.initial_config (Abs_TM M') w)) \<in>
               TM.TM.final_states M" apply simp
        apply (subst TM.step_def)
        apply auto
         apply (rule fs_final)
        using 1 apply (subst (asm) nth_map)
         apply auto
        by (metis TM.run_tapes_len TM.at_least_one_tape list.size(3) bot_nat_0.not_eq_extremum)
      show "state ((TM.step (Abs_TM M') ^^ T (length w)) (TM.initial_config (Abs_TM M') w)) \<in>
            TM.TM.final_states M" using 5
        by (metis 4 M'_final_states TM.final_le_steps is_finalI)
    qed
    show "TM.computes_word (Abs_TM M') w (map g (f (map (inv g) w)))" if "set w \<subseteq> TM.TM.symbols M"
      for w :: "'s list"
      unfolding TM.computes_word_def
    proof
      show "TM.halts (Abs_TM M') w" using tb [of w] unfolding TM.time_bounded_word_def TM.halts_def
          TM.halts_config_def TM.run_def ..
      have steps_eq: "(TM.step (Abs_TM M') ^^ k) (TM.initial_config (Abs_TM M') w) =
                      (TM.step M ^^ k) (TM.initial_config M w)" for k :: nat
      proof (induction k)
        case 0
        then show ?case by (simp add: TM.initial_config_def)
      next
        case (Suc k)
        show ?case apply simp
          unfolding Suc apply (subst (1 2) TM.step_def)
          apply auto
          unfolding TM.step_not_final_def Let_def apply auto
            apply (simp_all add: TM.run_tapes_len TM.set_tape_valid set_tape_in_symbols that)
          unfolding TM.next_actions_def TM.next_writes_def TM.next_moves_def by simp
      qed
      have comps_eq: "TM.compute (Abs_TM M') w = TM.compute M w"
        unfolding TM.compute_def TM.compute_config_def steps_eq TM.is_final_def by simp
      show "TM.has_output (TM.compute (Abs_TM M') w) (map g (f (map (inv g) w)))"
        unfolding comps_eq using a1 [THEN bspec, simplified, OF that, THEN conjunct1,
            unfolded TM.computes_word_def, THEN conjunct2] .
    qed
  qed
qed

(* Get computability of a function in datatype 'a by assuming it for datatype 's *)
lemma typed_comp_in_time_convert: "bij (g::'s\<Rightarrow>('a::finite)) \<Longrightarrow>
       typed_computable_in_time TYPE('q) TYPE('l) T f \<Longrightarrow>
       typed_computable_in_time TYPE('q) TYPE('l) T ((map g) \<circ> f \<circ> (map (inv g)))"
  using typed_comp_in_time_words [of g UNIV T f, where 'q='q and 'l='l]
  by auto (metis TM.computes_def comp_eq_dest_lhs typed_computable_in_time_def)

lemma poly_reducibleI':
  assumes "\<And>w::'s list. set w \<subseteq> alphabet L1 \<Longrightarrow> w \<in>\<^sub>L L1 \<longleftrightarrow> f w \<in>\<^sub>L L2" and
          "\<And>w. set w \<subseteq> alphabet L1 \<Longrightarrow> TM.computes_word (M::('q, 's, unit) TM) w (f w)" and
          "\<And>w. set w \<subseteq> alphabet L1 \<Longrightarrow> set (f w) \<subseteq> alphabet L2" and
          "alphabet L1 \<subseteq> TM.symbols M" and
          "alphabet L2 \<subseteq> TM.symbols M" and
          "\<And>w. set w \<subseteq> alphabet L1 \<Longrightarrow> TM.time_bounded_word M T w" and
          "\<And>n::nat. n \<ge> n0 \<Longrightarrow> T n \<le> n^k"
        shows "L1 \<le>\<^sub>p L2"
proof
  fix wi wo :: "'s list"
  define h :: "'q \<Rightarrow> nat" where "h \<equiv> (SOME h. inj_on h (TM.states M))"
  assume a1: "set wi \<subseteq> alphabet L1"
  have 1: "\<exists>h::'q\<Rightarrow>nat. inj_on h (TM.states M)"
    by (metis finite_imp_inj_to_nat_fix_one TM.state_axioms(1))
  have 2: "inj_on h (TM.states M)"
    unfolding h_def using 1 [THEN someI_ex] .
  show "\<exists>wo. set wo \<subseteq> alphabet L2 \<and>
        TM.computes_word (Abs_TM (map_states_tmrec h M)) wi wo"
    apply (rule exI [where x="f wi"])
  proof
    show "TM.computes_word (Abs_TM (map_states_tmrec h M)) wi (f wi)"
      using assms(2) [OF a1] 2 a1 assms(4) map_states_tmrec_comp_word_iff by blast
    show "set (f wi) \<subseteq> alphabet L2"
      using assms(3) a1 .
  qed
  assume a2: "set wo \<subseteq> alphabet L2" and
         a3: "TM.computes_word (Abs_TM (map_states_tmrec h M)) wi wo"
  have 3: "valid_TM (map_states_tmrec h M)" by (rule map_states_tmrec_valid) (rule 2)
  have 4: "set wi \<subseteq> TM.symbols M" using assms(4) a1 by order
  have 5: "set wo \<subseteq> TM.symbols M" using assms(5) a2 by order
  have 6: "wo = f wi"
  proof -
    note 6 = map_states_tmrec_comp_word_iff [OF 2 4, of wo, THEN iffD1, OF a3]
    note 7 = assms(2) [OF a1]
    show "wo = f wi" using 6 7 by (rule computes_word_unique)
  qed
  show "wi \<in>\<^sub>L L1 \<longleftrightarrow> wo \<in>\<^sub>L L2" unfolding 6 by (rule assms(1)) fact
  assume a4: "n0 \<le> length wi"
  note 7 = assms(6) [OF a1, unfolded TM.time_bounded_word_def TM.is_final_def]
  have 8: "state (TM.run (Abs_TM (map_states_tmrec h M)) (T (length wi)) wi) \<in>
           TM.final_states ((Abs_TM (map_states_tmrec h M)))"
  proof -
    have 8: "TM.final_states ((Abs_TM (map_states_tmrec h M))) = h ` (TM.final_states M)"
      unfolding valid_tm_final_states [OF 3] unfolding map_states_tmrec_def [OF 2] by auto
    show "state (TM.run (Abs_TM (map_states_tmrec h M)) (T (length wi)) wi)
          \<in> TM.TM.final_states (Abs_TM (map_states_tmrec h M))"
      unfolding map_states_tmrec_run(1) [OF 2 4] 8 using 7 by simp
  qed
  show "TM.time_bounded_word (Abs_TM (map_states_tmrec h M)) (\<lambda>n. n ^ k) wi" using 8
    by (meson TM.is_final_def TM.time_bounded_word_def TM.time_bounded_word_mono a4 assms(7))
qed

definition empty_word_lang :: "'s set \<Rightarrow> 's lang" where
  "empty_word_lang S \<equiv> Lang S (\<lambda>w. w = [])"

lemma empty_word_decidable_1: "finite (S::'s set) \<Longrightarrow> empty_word_lang S \<in> DTIME (\<lambda>_. 1)"
proof
  assume a1: "finite S"
  define M :: "(nat, 's, bool) TM_record" where
    "M \<equiv> TM 1 (S \<union> {undefined}) {0,1,2} 0 {1,2} (\<lambda>st. st = 1)
         (\<lambda>_ hds. if hds ! 0 = None then 1 else 2)
         (\<lambda>_ hds _. hds ! 0)
         (\<lambda>_ _ _. No_Shift)"
  have M_valid: "valid_TM M" by standard (auto simp add: M_def a1)
  show *: "alphabet (empty_word_lang S) \<subseteq> TM.TM.symbols (Abs_TM M)"
    unfolding valid_tm_symbols [OF M_valid] unfolding M_def empty_word_lang_def by auto
  show 1 [THEN spec,
      THEN mp]: "\<forall>w. set w \<subseteq> TM.TM.symbols (Abs_TM M) \<longrightarrow> TM.time_bounded_word (Abs_TM M) (\<lambda>_. 1) w"
    apply auto
    unfolding TM.time_bounded_word_def TM.is_final_def TM.run_def apply simp
    apply (subst TM.step_def)
    apply auto
    unfolding valid_tm_next_state [OF M_valid] valid_tm_final_states [OF M_valid]
      TM.initial_config_def TM_abbrevs.input_tape_def apply auto
    unfolding valid_tm_initial_state [OF M_valid] valid_tm_tape_count [OF M_valid]
    unfolding M_def by simp_all
  show "alphabet (empty_word_lang S) \<subseteq> TM.TM.symbols (Abs_TM M) \<and>
        (\<forall>w\<in>(alphabet (empty_word_lang S))*. TM_decider.decides_word (Abs_TM M) (empty_word_lang S) w)"
    apply standard
     apply fact
    apply auto
    unfolding TM_decider.decides_def apply auto
  proof -
    fix w :: "'s list"
    assume a2: "set w \<subseteq> alphabet (empty_word_lang S)"
    have 2: "set w \<subseteq> TM.symbols (Abs_TM M)" using a2 * by blast
    have 3: "(LEAST n. TM.is_final (Abs_TM M) ((TM.step (Abs_TM M) ^^ n)
             (TM.initial_config (Abs_TM M) w))) = 1"
      apply (rule Least_natI)
       apply auto
      using 1 [OF 2] unfolding TM.time_bounded_word_def TM.run_def apply simp
      unfolding TM.is_final_def TM.initial_config_def valid_tm_final_states [OF M_valid] apply simp
      unfolding valid_tm_initial_state [OF M_valid] unfolding M_def by simp
    have 4: "\<And>w. state (TM.initial_config (Abs_TM M) w) \<notin> TM.TM.final_states (Abs_TM M)"
      unfolding TM.initial_config_def valid_tm_final_states [OF M_valid]
      apply simp
      unfolding valid_tm_initial_state [OF M_valid] unfolding M_def by simp
    show 5: "w \<in>\<^sub>L empty_word_lang S \<Longrightarrow> TM_decider.accepts (Abs_TM M) w"
      unfolding empty_word_lang_def TM_decider.accepts_def apply auto
      unfolding TM.compute_def TM.compute_config_def
      apply (erule subst [where P="\<lambda>w'. state ((TM.step (Abs_TM M) ^^
       (LEAST n. TM.is_final (Abs_TM M) ((TM.step (Abs_TM M) ^^ n) (TM.initial_config (Abs_TM M) w'))))
       (TM.initial_config (Abs_TM M) [])) \<in> TM_decider.accepting_states (Abs_TM M)"])
      unfolding 3 apply simp
      unfolding TM_decider.acc_def apply auto
      unfolding TM.step_def apply (auto simp add: 4)
      unfolding valid_tm_next_state [OF M_valid] TM.initial_config_def TM_abbrevs.input_tape_def apply auto
      unfolding valid_tm_tape_count [OF M_valid] valid_tm_initial_state [OF M_valid]
        valid_tm_final_states [OF M_valid] valid_tm_label [OF M_valid] unfolding M_def by simp_all
    show "TM_decider.accepts (Abs_TM M) w \<Longrightarrow> w \<in>\<^sub>L empty_word_lang S"
      unfolding TM_decider.accepts_def empty_word_lang_def TM.compute_def TM_decider.acc_def apply auto
      using a2 unfolding empty_word_lang_def apply auto
      unfolding TM.compute_config_def 3 apply simp
      unfolding valid_tm_label [OF M_valid] apply (subst (asm) (2) TM.step_def)
      apply (simp add: 4)
      unfolding valid_tm_next_state [OF M_valid] TM.initial_config_def apply auto
      unfolding valid_tm_initial_state [OF M_valid] TM_abbrevs.input_tape_def
      apply (cases "w = []")
       apply auto
      unfolding valid_tm_tape_count [OF M_valid] apply (subst (asm) (5 6 7 8) M_def)
      by simp
    thus "w \<notin> words (empty_word_lang S) \<Longrightarrow> TM_decider.rejects (Abs_TM M) w"
      by (meson 1 2 TM.halts_altdef TM.time_bounded_word_def TM_decider.rejects_accepts)
    show "TM_decider.rejects (Abs_TM M) w \<Longrightarrow> w \<in>\<^sub>L empty_word_lang S \<Longrightarrow> False"
      apply (drule 5)
      by (metis TM_decider.acc_not_rej)
  qed
qed

lemma const_computable: "computable_in_time (\<lambda>_. length (c::('s::finite) list)) (\<lambda>_. c)"
proof -
  define M :: "(nat, 's, unit) TM_record" where
    "M \<equiv> TM 2 UNIV {0..length c} 0 {length c} (\<lambda>_. ())
         (\<lambda>st _. min (length c) (Suc st))
         (\<lambda>st _ _. Some (c ! (length c - st - 1)))
         (\<lambda>st _ _. if st \<ge> length c - 1 then No_Shift else Shift_Left)"
  have valid_M [simp, intro]: "valid_TM M"
    apply standard
    unfolding M_def by auto
  have f11: "state (TM.steps (Abs_TM M) k (TM.initial_config (Abs_TM M) w)) = k" and
       f12: "tapes (TM.steps (Abs_TM M) k (TM.initial_config (Abs_TM M) w)) ! 1 =
             Tape [] None (map Some (drop (length c - k) c))"
       if "Suc k < length c" for k :: nat and w :: "'s list" using that
  proof (induction k)
    case 0
    {
      case 1
      then show ?case apply (simp add: TM.initial_config_def valid_tm_initial_state)
        by (simp add: M_def)
    next
      case 2
      then show ?case apply (simp add: TM.initial_config_def valid_tm_tape_count)
        by (simp add: M_def)
    }
  next
    case (Suc k)
    {
      case 1
      hence *: "Suc k < length c" by simp
      have [simp]: "state ((TM.step (Abs_TM M) ^^ k) (TM.initial_config (Abs_TM M) w)) \<notin>
                    TM.TM.final_states (Abs_TM M)" unfolding Suc(1) [OF *] valid_tm_final_states [OF valid_M]
        unfolding M_def using * by simp
      show ?case apply simp
        apply (subst TM.step_def)
        apply auto
        unfolding valid_tm_next_state [OF valid_M] Suc(1) [OF *] apply (subst M_def)
        apply simp
        using * by simp
    next
      case 2
      hence *: "Suc k < length c" by simp
      have [simp]: "state ((TM.step (Abs_TM M) ^^ k) (TM.initial_config (Abs_TM M) w)) \<notin>
                    TM.TM.final_states (Abs_TM M)" unfolding Suc(1) [OF *] valid_tm_final_states [OF valid_M]
        unfolding M_def using * by simp
      show ?case apply simp
        apply (subst TM.step_def)
        apply auto
        apply (subst nth_map2)
        unfolding TM.next_actions_def TM.next_writes_def TM.next_moves_def apply auto
        using M_def valid_tm_tape_count apply fastforce
        apply (metis (no_types, lifting) M_def TM.run_tapes_len lessI numeral_2_eq_2 simps(1) valid_M
            valid_tm_tape_count)
        apply (subst nth_zip)
          apply auto
        using M_def valid_tm_tape_count apply fastforce
        using M_def valid_tm_tape_count apply fastforce
        apply (subst (1 2) nth_map)
         apply auto
        using M_def valid_tm_tape_count apply fastforce
        apply (simp add: valid_tm_next_write valid_tm_next_move valid_tm_tape_count)
        unfolding Suc(1) [OF *] apply (subst M_def)
        apply simp
        apply (subst M_def)
        using * apply auto
        unfolding TM_abbrevs.tape_action_def TM_abbrevs.tape_write_def apply simp
        unfolding Suc(2) [OF *, simplified] apply simp
        unfolding TM_abbrevs.tape_shift.simps apply simp
        by (smt (verit, best) Cons_nth_drop_Suc Suc_diff_Suc Suc_lessD diff_less drop_Nil drop_diff_length
            length_greater_0_conv list.simps(9) nat_less_le zero_less_Suc)
    }
  qed
  have f21: "state (TM.steps (Abs_TM M) (length c - 1) (TM.initial_config (Abs_TM M) w)) = length c - 1" and
       f22: "tapes (TM.steps (Abs_TM M) (length c - 1) (TM.initial_config (Abs_TM M) w)) ! 1 =
             Tape [] None (map Some (tl c))" for w :: "'s list"
  proof -
    show "state ((TM.step (Abs_TM M) ^^ (length c - 1)) (TM.initial_config (Abs_TM M) w)) = length c - 1"
    proof (cases "length c > 1")
      case True
      hence *: "Suc (length c - 2) = length c - 1" by simp
      show ?thesis apply (subst * [symmetric])
        apply simp
        apply (subst TM.step_def)
        apply (subst f11)
        using True apply simp
        unfolding valid_tm_final_states [OF valid_M] apply (subst M_def)
        using True apply auto
        unfolding valid_tm_next_state [OF valid_M] apply (subst f11)
         apply auto
        apply (subst M_def)
        by simp
    next
      case False
      then show ?thesis apply simp
        unfolding TM.initial_config_def valid_tm_initial_state [OF valid_M] apply simp
        unfolding M_def by simp
    qed
    show "tapes ((TM.step (Abs_TM M) ^^ (length c - 1)) (TM.initial_config (Abs_TM M) w)) ! 1 =
          Tape [] None (map Some (tl c))"
    proof (cases "length c > 1")
      case True
      hence *: "Suc (length c - 2) = length c - 1" by simp
      show ?thesis apply (subst * [symmetric])
        apply simp
        apply (subst TM.step_def)
        apply (subst f11)
        using True apply simp
        unfolding valid_tm_final_states [OF valid_M] apply (subst M_def)
        apply auto
        using True apply linarith
        apply (subst nth_map2)
          apply (metis (lifting) M_def TM.next_actions_simps(2) bot_nat_0.not_eq_extremum less_eq_Suc_le
            nat.distinct(1) nat_less_le numeral_2_eq_2 simps(1) valid_M valid_tm_tape_count)
         apply (metis (no_types, lifting) M_def TM.run_tapes_len bot_nat_0.not_eq_extremum less_eq_Suc_le
            nat.distinct(1) nat_less_le numeral_2_eq_2 simps(1) valid_M valid_tm_tape_count)
        unfolding TM.next_actions_def TM.next_writes_def TM.next_moves_def apply (subst nth_zip)
          apply auto
        using M_def valid_tm_tape_count apply fastforce
        using M_def valid_tm_tape_count apply fastforce
        apply (subst (1 2) nth_map)
         apply auto
        using M_def valid_tm_tape_count apply fastforce
        unfolding TM_abbrevs.tape_action_def apply simp
        unfolding valid_tm_next_move [OF valid_M] valid_tm_next_write [OF valid_M] apply (subst (1 2) f11)
        using True apply linarith
        apply (subst M_def)
        using True apply auto
        apply (subst M_def)
        apply simp
        apply (subst f12 [simplified])
         apply auto
        unfolding TM_abbrevs.tape_write_def apply simp
        unfolding TM_abbrevs.tape_shift.simps apply auto
        unfolding numeral_2_eq_2 drop_Suc apply simp
        by (metis (no_types, lifting) Nitpick.size_list_simp(2) One_nat_def diff_is_0_eq hd_conv_nth length_tl
            linorder_not_less list.collapse list.simps(9) nth_tl zero_less_diff)
    next
      case False
      then show ?thesis apply simp
        unfolding TM.initial_config_def TM_abbrevs.input_tape_def apply simp
        unfolding valid_tm_tape_count [OF valid_M] unfolding M_def apply simp
        by (metis Nil_tl Suc_lessI length_1_ex_iff length_greater_0_conv)
    qed
  qed
  have f31: "state (TM.steps (Abs_TM M) (length c) (TM.initial_config (Abs_TM M) w)) = length c" and
       f32: "c \<noteq> [] \<Longrightarrow> tapes (TM.steps (Abs_TM M) (length c) (TM.initial_config (Abs_TM M) w)) ! 1 =
             Tape [] (Some (c ! 0)) (map Some (tl c))" and
       f33: "c = [] \<Longrightarrow> tapes (TM.steps (Abs_TM M) (length c) (TM.initial_config (Abs_TM M) w)) ! 1 =
             Tape [] None []" for w :: "'s list"
  proof -
    have *: "c \<noteq> [] \<Longrightarrow> length c = Suc (length c - 1)" by simp
    show "state ((TM.step (Abs_TM M) ^^ length c) (TM.initial_config (Abs_TM M) w)) = length c"
      apply (cases "c = []")
       apply auto
       apply (subst TM.initial_config_def)
      unfolding valid_tm_initial_state [OF valid_M] apply simp
       apply (subst M_def)
       apply simp
      apply (subst *)
       apply assumption
      unfolding funpow_Suc_right comp_def funpow_swap1 [symmetric] apply (subst TM.step_def)
      apply auto
      unfolding f21 [simplified] valid_tm_final_states [OF valid_M] apply (subst (asm) M_def)
       apply simp
      unfolding valid_tm_next_state [OF valid_M] apply (subst M_def)
      by simp
    show "tapes ((TM.step (Abs_TM M) ^^ length c) (TM.initial_config (Abs_TM M) w)) ! 1 =
          Tape [] (Some (c ! 0)) (map Some (tl c))" if "c \<noteq> []"
      apply (subst * [OF that])
      apply simp
      apply (subst TM.step_def)
      apply auto
      unfolding f21 [simplified] valid_tm_final_states [OF valid_M] apply (subst (asm) M_def)
      using that apply simp
      using * apply presburger
      apply (subst nth_map2)
        apply (metis (lifting) M_def TM.next_actions_simps(2) lessI numeral_2_eq_2 simps(1) valid_M
          valid_tm_tape_count)
       apply (metis (no_types, lifting) M_def TM.run_tapes_len lessI numeral_2_eq_2 simps(1) valid_M
          valid_tm_tape_count)
      unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_writes_def TM.next_moves_def
      apply (subst (1 2) nth_zip)
        apply auto
      using M_def valid_tm_tape_count apply fastforce
      using M_def valid_tm_tape_count apply fastforce
      apply (subst (1 2) nth_map)
       apply auto
      using M_def valid_tm_tape_count apply fastforce
      unfolding valid_tm_next_move [OF valid_M] valid_tm_next_write [OF valid_M] apply (subst M_def)
      apply simp
      unfolding TM_abbrevs.tape_shift.simps apply (subst M_def)
      apply simp
      unfolding TM_abbrevs.tape_write_def apply auto
      unfolding f22 [simplified] by simp_all
    show "tapes ((TM.step (Abs_TM M) ^^ length c) (TM.initial_config (Abs_TM M) w)) ! 1 = Tape [] None []"
      if "c = []"
      unfolding that apply simp
      unfolding TM.initial_config_def TM_abbrevs.input_tape_def apply simp
      unfolding valid_tm_tape_count [OF valid_M] unfolding M_def by simp
  qed
  show "computable_in_time (\<lambda>_. length c) (\<lambda>_. c)"
    unfolding typed_computable_in_time_def apply (rule exI [where x="Abs_TM M"])
  proof auto
    fix s :: 's
    show "s \<in> TM.symbols (Abs_TM M)" unfolding valid_tm_symbols [OF valid_M] unfolding M_def by simp
    show tb: "\<And>w. TM.time_bounded_word (Abs_TM M) (\<lambda>_. length c) w"
      unfolding TM.time_bounded_word_def TM.is_final_def TM.run_def f31 valid_tm_final_states [OF valid_M]
      unfolding M_def by simp
    have 1: "(LEAST n. TM.is_final (Abs_TM M) ((TM.step (Abs_TM M) ^^ n) (TM.initial_config (Abs_TM M) w))) =
             length c" for w :: "'s list"
      apply (rule Least_nat_monoI)
        apply auto
      unfolding TM.is_final_def f31 f21 [simplified] valid_tm_final_states [OF valid_M]
      unfolding M_def apply auto
      by (metis Suc_diff_Suc diff_zero length_greater_0_conv n_not_Suc_n)
    show "TM.computes (Abs_TM M) (\<lambda>_. c)"
      unfolding TM.computes_def TM.computes_word_def apply auto
      using tb apply (metis tb TM.time_bounded_altdef2)
      unfolding TM.has_output_def TM.clean_output_of_def TM.compute_def TM.compute_config_def 1
      apply auto
      unfolding TM.clean_output_def TM_abbrevs.input_tape_def
    proof -
      fix w :: "'s list"
      have "length (tapes ((TM.step (Abs_TM M) ^^ length c) (TM.initial_config (Abs_TM M) w))) = 2"
        by (metis (no_types, lifting) M_def TM.run_tapes_len simps(1) valid_M valid_tm_tape_count)
      hence 1: "last (tapes ((TM.step (Abs_TM M) ^^ length c) (TM.initial_config (Abs_TM M) w))) =
                tapes ((TM.step (Abs_TM M) ^^ length c) (TM.initial_config (Abs_TM M) w)) ! 1"
        by (metis One_nat_def diff_Suc_1' last_conv_nth list.size(3) nat.distinct(1) numeral_2_eq_2)
      show "\<exists>w'. last (tapes ((TM.step (Abs_TM M) ^^ length c) (TM.initial_config (Abs_TM M) w))) =
            (if w' = [] then Tape [] None [] else Tape [] (Some (hd w')) (map Some (tl w')))"
        unfolding 1 apply (cases "c = []")
        unfolding f32 f33 apply (rule exI [where x="[]"])
         apply simp
        apply (rule exI [where x=c])
        apply simp
        by (metis hd_conv_nth)
      have 2: "takeWhile (\<lambda>s. \<exists>y. s = Some y) (map Some (tl c)) = map Some (tl c)" by simp
      show "TM.output_of ((TM.step (Abs_TM M) ^^ length c) (TM.initial_config (Abs_TM M) w)) = c"
        unfolding TM.output_of_def Let_def 1 apply (cases "c = []")
        unfolding f32 f33 apply auto
        unfolding 2 apply simp
        by (metis list.collapse zeroth_is_head)
    qed
  qed
qed

lemma rev_takeWhile_computable: "computable_in_time (\<lambda>n. n + 1)
                                 ((rev::('s::finite) list \<Rightarrow> 's list) \<circ> takeWhile P)"
proof (rule typed_comp_in_time_natI)
  define M :: "('s option \<times> nat, 's, unit) TM_record" where
    "M \<equiv> TM 2 UNIV (UNIV \<times> {1, 2, 3}) (None, 1) (UNIV \<times> {3}) (\<lambda>_. ())
         (\<lambda>st hds. if hds ! 0 = None \<or> \<not>P (the (hds ! 0)) then (fst st, 3) else (hds ! 0, 2))
         (\<lambda>st hds k. if snd st = 1 then hds ! k else fst st)
         (\<lambda>st hds k. if k = 0 then Shift_Right else if snd st = 1 \<or> hds ! 0 = None \<or> \<not>P (the (hds ! 0)) then
          No_Shift else Shift_Left)"
  have valid_M [simp, intro]: "valid_TM M"
    apply unfold_locales
    unfolding M_def by auto
  show "typed_computable_in_time TYPE('s option \<times> nat) TYPE(unit) (\<lambda>n. n + 1) (rev \<circ> takeWhile P)"
  proof (unfold typed_computable_in_time_def, rule exI, auto)
    show M_syms: "\<And>s. s \<in> TM.TM.symbols (Abs_TM M)"
      unfolding valid_tm_symbols [OF valid_M] unfolding M_def by simp
    have f11: "state (TM.steps (Abs_TM M) k (TM.initial_config (Abs_TM M) w)) = (Some (w ! (k - 1)), 2)" and
         f12: "k < length w \<Longrightarrow> 
               head (tapes (TM.steps (Abs_TM M) k (TM.initial_config (Abs_TM M) w)) ! 0) = Some (w ! k)" and
         f13: "k = length w \<Longrightarrow>
               head (tapes (TM.steps (Abs_TM M) k (TM.initial_config (Abs_TM M) w)) ! 0) = None" and
         f14: "right (tapes (TM.steps (Abs_TM M) k (TM.initial_config (Abs_TM M) w)) ! 0) =
               map Some (drop (Suc k) w)" and
         f15: "tapes (TM.steps (Abs_TM M) k (TM.initial_config (Abs_TM M) w)) ! 1 =
               Tape [] None (map Some (rev (take (k - 1) (takeWhile P w))))"
         if "k \<ge> 1" and "k \<le> length w" and "\<And>n. n < k \<Longrightarrow> P (w ! n)" for w :: "'s list" and k :: nat
      using that
    proof (induction k rule: nat_induct_at_least)
      case base
      {
        case 1
        then show ?case apply simp
          unfolding TM.step_def TM.initial_config_def apply auto
          unfolding valid_tm_final_states [OF valid_M] valid_tm_initial_state [OF valid_M]
            valid_tm_next_state [OF valid_M] unfolding M_def apply auto
          unfolding TM_abbrevs.input_tape_def by (auto simp add: zeroth_is_head)
      next
        case 2
        then show ?case apply simp
          unfolding TM.step_def TM.initial_config_def apply auto
          unfolding valid_tm_final_states [OF valid_M] valid_tm_initial_state [OF valid_M]
            TM_abbrevs.tape_action_def TM.next_actions_def TM.next_writes_def TM.next_moves_def apply auto
          unfolding valid_tm_next_move [OF valid_M] valid_tm_next_write [OF valid_M] unfolding M_def apply auto
          unfolding TM_abbrevs.input_tape_def TM_abbrevs.tape_write_def apply simp
          apply (cases "map Some (tl w)")
           apply auto
           apply (simp add: Nitpick.size_list_simp(2))
          unfolding TM_abbrevs.tape_shift.simps apply simp
          by (metis Nitpick.size_list_simp(2) nth_Cons_0 nth_tl not_less_eq nat.inject)
      next
        case 3
        show ?case using 3(1) [symmetric] 3(2, 3) apply simp
          unfolding TM.step_def TM.initial_config_def apply auto
          unfolding valid_tm_final_states [OF valid_M] valid_tm_initial_state [OF valid_M]
            TM_abbrevs.tape_action_def TM.next_actions_def TM.next_writes_def TM.next_moves_def apply auto
          unfolding valid_tm_next_move [OF valid_M] valid_tm_next_write [OF valid_M] unfolding M_def apply auto
          unfolding TM_abbrevs.input_tape_def TM_abbrevs.tape_write_def apply auto
          apply (cases "map Some (tl w)")
           apply auto
          by (simp add: Nitpick.size_list_simp(2))
      next
        case 4
        then show ?case apply simp
          unfolding TM.step_def TM.initial_config_def apply auto
          unfolding valid_tm_final_states [OF valid_M] valid_tm_initial_state [OF valid_M]
            TM_abbrevs.tape_action_def TM.next_actions_def TM.next_writes_def TM.next_moves_def apply auto
          unfolding valid_tm_next_move [OF valid_M] valid_tm_next_write [OF valid_M] unfolding M_def apply auto
          unfolding TM_abbrevs.input_tape_def TM_abbrevs.tape_write_def apply auto
          by (simp add: drop_Suc map_tl)
      next
        case 5
        then show ?case apply simp
          unfolding TM.step_def TM.initial_config_def apply auto
          unfolding valid_tm_final_states [OF valid_M] valid_tm_initial_state [OF valid_M]
            TM_abbrevs.tape_action_def TM.next_actions_def TM.next_writes_def TM.next_moves_def
            valid_tm_tape_count [OF valid_M] valid_tm_next_move [OF valid_M] valid_tm_next_write [OF valid_M]
          unfolding M_def by (auto simp add: TM_abbrevs.tape_shift.simps(5) TM_abbrevs.tape_write_def)
      }
    next
      case (Suc k)
      {
        case 1
        hence *: "k \<le> length w" and **: "\<And>n. n < k \<Longrightarrow> P (w ! n)" and ***: "P (w ! k)" by simp_all
        have 2: "k < length w" using 1 by simp
        have [simp]: "state ((TM.step (Abs_TM M) ^^ k) (TM.initial_config (Abs_TM M) w)) \<notin>
                      TM.TM.final_states (Abs_TM M)"
          unfolding Suc(2) [OF * **, simplified] unfolding valid_tm_final_states [OF valid_M]
          unfolding M_def by simp
          show ?case apply simp
            apply (subst TM.step_def)
            apply simp
            unfolding Suc(2) [OF * **, simplified] valid_tm_next_state [OF valid_M] apply (subst M_def)
            apply auto
              apply (subst nth_map)
               apply (metis TM.run_tapes_len TM.at_least_one_tape)
            unfolding Suc(3) [OF 2 * **, simplified] apply simp
             apply (subst nth_map)
              apply (metis TM.run_tapes_len TM.at_least_one_tape)
            unfolding Suc(3) [OF 2 * **, simplified] apply (simp add: ***)
            apply (subst (asm) nth_map)
             apply (metis TM.run_tapes_len TM.at_least_one_tape)
            unfolding Suc(3) [OF 2 * **, simplified] by simp
      next
        case 2
        hence *: "k \<le> length w" and **: "\<And>n. n < k \<Longrightarrow> P (w ! n)" and ***: "P (w ! k)" by simp_all
        have 1: "k < length w" using 2 by simp
        have [simp]: "state ((TM.step (Abs_TM M) ^^ k) (TM.initial_config (Abs_TM M) w)) \<notin>
                      TM.TM.final_states (Abs_TM M)"
          unfolding Suc(2) [OF * **, simplified] unfolding valid_tm_final_states [OF valid_M]
          unfolding M_def by simp
        show ?case apply simp
          apply (subst TM.step_def)
          apply simp
          unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_writes_def TM.next_moves_def
          apply (subst nth_map2)
            apply auto
           apply (metis TM.run_tapes_len TM.at_least_one_tape nat_less_le list.size(3))
          unfolding valid_tm_next_move [OF valid_M] valid_tm_next_write [OF valid_M]
            Suc(2) [OF * **, simplified] apply (subst M_def)
          apply simp
          by (metis (no_types, lifting) * ** "2.prems"(1) Shift_Right_is_right_not_empty Suc.IH(4) drop_eq_Nil
              hd_drop_conv_nth linorder_not_less list.map_disc_iff list.map_sel(1) right_after_write)
      next
        case 3
        hence *: "k \<le> length w" and **: "\<And>n. n < k \<Longrightarrow> P (w ! n)" and ***: "P (w ! k)" by simp_all
        have 1: "k < length w" using 3 by simp
        have [simp]: "state ((TM.step (Abs_TM M) ^^ k) (TM.initial_config (Abs_TM M) w)) \<notin>
                      TM.TM.final_states (Abs_TM M)"
          unfolding Suc(2) [OF * **, simplified] unfolding valid_tm_final_states [OF valid_M]
          unfolding M_def by simp
        show ?case apply simp
          apply (subst TM.step_def)
          apply simp
          unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_moves_def TM.next_writes_def
          apply (subst nth_map2)
            apply auto
           apply (metis TM.run_tapes_len TM.at_least_one_tape list.size(3) bot_nat_0.not_eq_extremum)
          unfolding valid_tm_next_move [OF valid_M] Suc(2) [OF * **, simplified] apply (subst M_def)
          by (simp add: * ** "3.prems"(1) Suc.IH(4))
      next
        case 4
        hence *: "k \<le> length w" and **: "\<And>n. n < k \<Longrightarrow> P (w ! n)" and ***: "P (w ! k)" by simp_all
        have 1: "k < length w" using 4 by simp
        have [simp]: "state ((TM.step (Abs_TM M) ^^ k) (TM.initial_config (Abs_TM M) w)) \<notin>
                      TM.TM.final_states (Abs_TM M)"
          unfolding Suc(2) [OF * **, simplified] unfolding valid_tm_final_states [OF valid_M]
          unfolding M_def by simp
        show ?case apply simp
          apply (subst TM.step_def)
          apply simp
          unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_moves_def TM.next_writes_def
          apply (subst nth_map2)
            apply auto
           apply (metis TM.run_tapes_len TM.at_least_one_tape list.size(3) nat_less_le)
          unfolding valid_tm_next_move [OF valid_M] Suc(2) [OF * **, simplified] apply (subst M_def)
          apply simp
          using * "4.prems"(2) Suc.IH(4) drop_Suc[of "Suc k" "map Some w"] drop_map[of "Suc (Suc k)" Some w]
            drop_map[of "Suc k" Some w] tl_drop[of "Suc k" "map Some w"] by force
      next
        case 5
        hence *: "k \<le> length w" and **: "\<And>n. n < k \<Longrightarrow> P (w ! n)" and ***: "P (w ! k)" by simp_all
        have 1: "k < length w" using 5 by simp
        have 2: "Suc 0 < TM.TM.tape_count (Abs_TM M)" using M_def valid_tm_tape_count by fastforce
        have 3: "w ! (k - Suc 0) = (takeWhile P w) ! (k - Suc 0)"
          by (metis 1 "5.prems"(2) diff_le_self diff_less_Suc linorder_not_less nth_length_takeWhile
              order_le_less_trans takeWhile_nth)
        have [simp]: "state ((TM.step (Abs_TM M) ^^ k) (TM.initial_config (Abs_TM M) w)) \<notin>
                      TM.TM.final_states (Abs_TM M)"
          unfolding Suc(2) [OF * **, simplified] unfolding valid_tm_final_states [OF valid_M]
          unfolding M_def by simp
        show ?case apply simp
          apply (subst TM.step_def)
          apply simp
          unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_moves_def TM.next_writes_def
          apply (subst nth_map2)
            apply (auto simp add: 2)
           apply (metis (lifting) M_def TM.run_tapes_len lessI numeral_2_eq_2 simps(1) valid_M
              valid_tm_tape_count)
          unfolding valid_tm_next_move [OF valid_M] Suc(2) [OF * **, simplified] apply (subst M_def)
          apply auto
            apply (simp add: * ** 1 Suc.IH(2) TM.run_tapes_len)
           apply (simp add: * ** *** 1 Suc.IH(2) TM.run_tapes_len)
          apply (rule tape.expand)
          apply auto
          using * ** Suc.IH(5) apply fastforce
           apply (cases "left (tapes ((TM.step (Abs_TM M) ^^ k) (TM.initial_config (Abs_TM M) w)) ! Suc 0)")
            apply auto
           apply (metis * ** One_nat_def Suc.IH(5) list.distinct(1) tape.sel(1))
          unfolding valid_tm_next_write [OF valid_M] apply (subst M_def)
          apply simp
          unfolding TM_abbrevs.tape_write_def apply simp
          unfolding Suc(6) [OF * **, simplified] apply simp
          unfolding 3
          by (smt (verit, best) 1 "5.prems"(2) One_nat_def Suc.hyps Suc_diff_Suc diff_zero le_Suc_eq
              less_Suc_eq_le linorder_not_less list.simps(9) list_take_rev_Cons nth_length_takeWhile
              order_less_le_trans)
      }
    qed
    have f11': "state (TM.step (Abs_TM M) (TM.initial_config (Abs_TM M) [])) = (None, 3)" and
         f12': "tapes (TM.step (Abs_TM M) (TM.initial_config (Abs_TM M) [])) ! 1 = Tape [] None []"
      unfolding TM.step_def apply auto
      unfolding valid_tm_final_states [OF valid_M] TM.initial_config_def valid_tm_initial_state [OF valid_M]
        valid_tm_tape_count [OF valid_M] valid_tm_next_state [OF valid_M] apply (unfold M_def)[3]
         apply auto
      unfolding TM_abbrevs.input_tape_def apply simp_all
      unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_writes_def TM.next_moves_def
      apply (subst nth_map2)
        apply auto
      using M_def valid_tm_tape_count [OF valid_M] apply simp
      using M_def apply simp
      apply (subst (1 2) nth_zip)
        apply auto
      using M_def valid_tm_tape_count [OF valid_M] apply simp
      using M_def valid_tm_tape_count [OF valid_M] apply simp
      apply (subst (1 2) nth_map)
       apply auto
      using M_def valid_tm_tape_count [OF valid_M] apply simp
      unfolding valid_tm_next_move [OF valid_M] valid_tm_tape_count [OF valid_M]
        valid_tm_next_write [OF valid_M] unfolding M_def apply simp
      unfolding TM_abbrevs.tape_shift.simps TM_abbrevs.tape_write_def by simp
    have f21: "\<exists>s. state (TM.steps (Abs_TM M) (Suc k) (TM.initial_config (Abs_TM M) w)) = (s, 3)" and
         f22: "tapes (TM.steps (Abs_TM M) (Suc k) (TM.initial_config (Abs_TM M) w)) ! 1 =
               Tape [] (if k = 0 then None else Some (w ! (k - 1))) (map Some (tl (rev (takeWhile P w))))"
      if "k < length w" and "\<And>n. n < k \<Longrightarrow> P (w ! n)" and "\<not>P (w ! k)"
      for w :: "'s list" and k :: nat
       apply auto
        apply (subst TM.step_def)
        apply auto
      unfolding valid_tm_final_states [OF valid_M] apply (subst (asm) (3) M_def)
         apply auto
        apply (cases "k = 0")
         apply auto
      unfolding valid_tm_next_state [OF valid_M] apply (subst (1 2) TM.initial_config_def)
      unfolding TM_abbrevs.input_tape_def valid_tm_initial_state [OF valid_M] using that(1) apply auto
         apply (subst (1 2) M_def)
         apply simp
         apply (metis that(3) hd_conv_nth)
        apply (subst M_def)
        apply auto
        apply (subst (asm) nth_map)
         apply auto
         apply (metis length_greater_0_conv TM.run_tapes_len TM.at_least_one_tape)
        apply (subst (asm) f12)
            apply auto
         apply (erule that(2))
      using that(3) apply simp
      using that(3) apply simp
       apply (subst TM.step_def)
       apply auto
        apply (subst (asm) TM.initial_config_def)
      unfolding valid_tm_final_states [OF valid_M] valid_tm_initial_state [OF valid_M] using M_def apply simp
      unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_writes_def TM.next_moves_def
       apply (subst nth_map2)
         apply auto
         apply (metis (no_types, lifting) M_def lessI numeral_2_eq_2 simps(1) valid_M valid_tm_tape_count)
        apply (metis (lifting) M_def TM.init_conf_len lessI numeral_2_eq_2 simps(1) valid_M valid_tm_tape_count)
       apply (subst (1 2) nth_zip)
         apply auto
         apply (metis (lifting) M_def lessI numeral_2_eq_2 simps(1) valid_M valid_tm_tape_count)
        apply (metis (lifting) M_def lessI numeral_2_eq_2 simps(1) valid_M valid_tm_tape_count)
       apply (subst (1 2) nth_map)
        apply auto
        apply (metis (lifting) M_def lessI numeral_2_eq_2 simps(1) valid_M valid_tm_tape_count)
      unfolding valid_tm_next_move [OF valid_M] valid_tm_next_write [OF valid_M]
       apply (unfold TM.initial_config_def)[1]
      unfolding TM_abbrevs.input_tape_def apply simp
      unfolding valid_tm_initial_state [OF valid_M] apply (subst (1 2) M_def)
       apply auto
        apply (metis (no_types, lifting) M_def One_nat_def Suc_eq_plus1 lessI nat.distinct(1)
          nth_upt numeral_2_eq_2 simps(1) valid_M valid_tm_tape_count)
      unfolding TM_abbrevs.tape_shift.simps TM_abbrevs.tape_write_def apply auto
      unfolding valid_tm_tape_count [OF valid_M] apply (unfold M_def)[3]
         apply auto
       apply (metis (no_types, lifting) Cons_nth_drop_Suc Nil_is_rev_conv Nil_tl append_Nil drop0
          takeWhile.simps(1) takeWhile_tail that(1))
      apply (subst TM.step_def)
      apply auto
      unfolding valid_tm_final_states [OF valid_M] apply (subst (asm) f11)
          apply auto
        apply (erule that(2))
       apply (subst (asm) M_def)
       apply simp
      unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_writes_def TM.next_moves_def
      apply (subst nth_map2)
        apply auto
      using M_def valid_tm_tape_count [OF valid_M] apply simp
       apply (metis (lifting) M_def TM.run_tapes_len valid_tm_tape_count [OF valid_M] lessI numeral_2_eq_2
          select_convs(1))
      apply (subst (1 2) nth_zip)
        apply auto
      using M_def valid_tm_tape_count [OF valid_M] apply simp
      using M_def valid_tm_tape_count [OF valid_M] apply simp
      apply (subst (1 2) nth_map)
       apply auto
      using M_def valid_tm_tape_count [OF valid_M] apply simp
      unfolding valid_tm_next_move [OF valid_M] valid_tm_next_write [OF valid_M]
        valid_tm_tape_count [OF valid_M] apply (subst M_def)
      apply auto
             apply (simp add: M_def)
            apply (subst M_def)
            apply simp
      unfolding TM_abbrevs.tape_shift.simps TM_abbrevs.tape_write_def apply auto
                  apply (metis One_nat_def f15 less_eq_Suc_le nat_less_le tape.sel(1) that(2))
                 apply (subst (asm) (2) f11)
                    apply auto
                 apply (erule that(2))
                apply (subst (asm) (2) f11)
                   apply auto
                apply (erule that(2))
               apply (simp add: M_def)
              apply (subst f15 [simplified])
                 apply auto
              apply (erule that(2))
             apply (subst (asm) nth_map)
              apply (simp add: TM.run_tapes_len)
             apply (subst (asm) f12)
                 apply auto
             apply (erule that(2))
            apply (subst (asm) nth_map)
             apply (simp add: TM.run_tapes_len)
            apply (subst (asm) f12)
                apply auto
            apply (erule that(2))
           apply (simp add: M_def)
          apply (metis One_nat_def f15 less_eq_Suc_le nat_less_le tape.sel(1) that(2))
         apply (subst f11)
            apply auto
          apply (erule that(2))
         apply (subst M_def)
         apply simp
        apply (subst f15 [simplified])
           apply auto
         apply (erule that(2))
        apply (rule nth_equalityI)
         apply auto
         apply (subst (1 2) length_takeWhile_eq)
               apply auto
            apply (erule that(2))
      using that(3) apply simp
          apply (erule that(2))
      using that(3) apply simp
        apply (subst rev_nth)
         apply simp
        apply (subst nth_tl)
         apply simp
      using length_takeWhile_eq that(2,3) apply blast
        apply (subst rev_nth)
         apply (metis One_nat_def Suc_eq_plus1 Suc_lessI length_takeWhile_le less_diff_conv less_eq_Suc_le
          less_imp_diff_less not_less_eq nth_length_takeWhile that(2))
        apply (subst nth_take)
         apply auto
        apply (metis One_nat_def diff_Suc_eq_diff_pred diff_less length_takeWhile_eq lessI min.absorb4 that(2,3))
       apply (simp add: M_def numeral_2_eq_2 plus_1_eq_Suc)
      apply (subst (asm) nth_map)
       apply auto
       apply (metis One_nat_def TM.at_least_one_tape' TM.run_tapes_len lessI linorder_not_less list.size(3))
      apply (subst (asm) f12)
          apply auto
       apply (erule that(2))
      using that(3) by simp
    have f31: "state (TM.steps (Abs_TM M) (Suc (length w)) (TM.initial_config (Abs_TM M) w)) =
               (Some (w ! (length w - 1)), 3)" and
         f32: "tapes (TM.steps (Abs_TM M) (Suc (length w)) (TM.initial_config (Abs_TM M) w)) ! 1 =
               Tape [] (Some (last w)) (map Some (tl (rev (takeWhile P w))))"
         if "w \<noteq> []" and "\<And>n. n < length w \<Longrightarrow> P (w ! n)" for w :: "'s list" and k :: nat
       apply auto
       apply (subst TM.step_def)
       apply auto
        apply (subst (asm) f11)
      using that(1) apply (auto intro: that(2))
      unfolding valid_tm_final_states [OF valid_M] apply (subst (asm) M_def)
        apply simp
      unfolding valid_tm_next_state [OF valid_M] apply (subst f11)
          apply auto
        apply (erule that(2))
       apply (subst M_def)
       apply auto
       apply (subst (asm) nth_map)
        apply auto
        apply (metis TM.run_tapes_len TM.at_least_one_tape list.size(3) bot_nat_0.not_eq_extremum)
       apply (subst (asm) f13)
           apply auto
       apply (erule that(2))
      apply (subst TM.step_def)
      apply auto
      unfolding valid_tm_final_states [OF valid_M] apply (subst (asm) f11)
          apply auto
        apply (erule that(2))
       apply (subst (asm) M_def)
       apply simp
      unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_writes_def TM.next_moves_def
      apply (subst nth_map2)
        apply auto
      unfolding valid_tm_tape_count [OF valid_M] apply (simp add: M_def)
       apply (metis (lifting) M_def TM.run_tapes_len valid_tm_tape_count [OF valid_M] lessI numeral_2_eq_2
          simps(1))
      apply (subst (1 2) nth_zip)
        apply auto
        apply (simp add: M_def)
       apply (simp add: M_def)
      apply (subst (1 2) nth_map)
       apply (simp add: M_def)
      unfolding valid_tm_next_move [OF valid_M] valid_tm_next_write [OF valid_M] apply (subst (1 2) f11)
         apply auto
       apply (erule that(2))
      apply (subst M_def)
      apply auto
           apply (simp add: M_def)
      unfolding TM_abbrevs.tape_shift.simps TM_abbrevs.tape_write_def apply auto
              apply (metis One_nat_def f15 le_refl length_Suc0_not_empty tape.sel(1) that(2))
             apply (subst M_def)
             apply simp
             apply (simp add: last_conv_nth)
            apply (subst f15 [simplified])
               apply auto
             apply (erule that(2))
            apply (metis Suc_pred length_greater_0_conv length_takeWhile_le lessI list.sel(3) list_take_rev_Cons
          nat_less_le nth_length_takeWhile take_eq that(2))
           apply (simp add: M_def)
          apply (metis One_nat_def f15 le_refl length_Suc0_not_empty tape.sel(1) that(2))
         apply (subst M_def)
         apply auto
         apply (metis One_nat_def last_conv_nth)
        apply (subst f15 [simplified])
           apply auto
         apply (erule that(2))
        apply (metis Suc_pred length_greater_0_conv length_takeWhile_le lessI list.sel(3) list_take_rev_Cons
          nat_less_le nth_length_takeWhile take_eq that(2))
       apply (simp add: M_def)
      apply (rule tape.expand)
      apply auto
        apply (subst f15 [simplified])
           apply auto
        apply (erule that(2))
       apply (subst (asm) nth_map)
        apply auto
        apply (metis TM.at_least_one_tape TM.run_tapes_len less_not_refl list.size(3))
       apply (subst (asm) f13)
           apply auto
       apply (erule that(2))
      apply (subst (asm) nth_map)
       apply auto
      apply (metis TM.at_least_one_tape TM.run_tapes_len less_not_refl list.size(3))
      apply (subst (asm) f13)
          apply auto
      by (rule that(2))
    show M_tb: "TM.time_bounded_word (Abs_TM M) Suc w" for w :: "'s list"
    proof (unfold TM.time_bounded_word_def TM.is_final_def TM.run_def)
      show "state ((TM.step (Abs_TM M) ^^ Suc (length w)) (TM.initial_config (Abs_TM M) w)) \<in>
            TM.TM.final_states (Abs_TM M)"
        apply (cases "\<forall>n < length w. P (w ! n)")
         apply (cases "w = []")
          apply simp
        unfolding valid_tm_final_states [OF valid_M]
        unfolding f11' apply (subst M_def)
          apply simp
         apply (subst f31)
           apply auto
         apply (subst M_def)
         apply simp
      proof -
        fix n :: nat
        assume a1: "n < length w" and a2: "\<not> P (w ! n)"
        define n' :: nat where "n' \<equiv> (LEAST m. \<not>P (w ! m))"
        have 1: "\<not> P (w ! n')" unfolding n'_def apply (rule LeastI)
          by fact
        have 2: "\<And>m. m < n' \<Longrightarrow> P (w ! m)"
          unfolding n'_def using not_less_Least by blast
        have 3: "n' \<le> n" unfolding n'_def by (rule Least_le) fact
        have 4: "n' < length w" using a1 3 by simp
        show "state (TM.step (Abs_TM M) ((TM.step (Abs_TM M) ^^ length w) (TM.initial_config (Abs_TM M) w)))
              \<in> final_states M" using f21 [OF 4 2 1] apply auto
        proof -
          fix s :: "'s option"
          assume a3: "state (TM.step (Abs_TM M) ((TM.step (Abs_TM M) ^^ n')
                      (TM.initial_config (Abs_TM M) w))) = (s, 3)"
          have 5: "state (TM.step (Abs_TM M) ((TM.step (Abs_TM M) ^^ n')
                   (TM.initial_config (Abs_TM M) w))) \<in> TM.final_states (Abs_TM M)"
            unfolding a3 valid_tm_final_states [OF valid_M] unfolding M_def by simp
          have 6: "state (TM.step (Abs_TM M) ((TM.step (Abs_TM M) ^^ length w) (TM.initial_config (Abs_TM M) w)))
                   \<in> TM.final_states (Abs_TM M)" using 4 5 unfolding TM.is_final_def [symmetric]
            using TM.final_steps_le[of "Abs_TM M" "length w"
                "TM.step (Abs_TM M) (TM.initial_config (Abs_TM M) w)" n']
              funpow_swap1[of "TM.step (Abs_TM M)" "length w" "TM.initial_config (Abs_TM M) w"]
              funpow_swap1[of "TM.step (Abs_TM M)" n' "TM.initial_config (Abs_TM M) w"] by auto
          show "state (TM.step (Abs_TM M) ((TM.step (Abs_TM M) ^^ length w) (TM.initial_config (Abs_TM M) w)))
                \<in> final_states M" using 6 unfolding valid_tm_final_states [OF valid_M] .
        qed
      qed
    qed
    show "TM.computes (Abs_TM M) (rev \<circ> takeWhile P)"
    proof (unfold TM.computes_def TM.computes_word_def, auto)
      fix w :: "'s list"
      show "TM.halts (Abs_TM M) w" using M_tb [of w] M_tb TM.time_bounded_altdef2 by blast
      have "\<And>w k. length (tapes (TM.steps (Abs_TM M) k (TM.initial_config (Abs_TM M) w))) = 2"
        by (metis (no_types, lifting) M_def TM.run_tapes_len simps(1) valid_M valid_tm_tape_count)
      hence 0: "\<And>w k. last (tapes (TM.steps (Abs_TM M) k (TM.initial_config (Abs_TM M) w))) =
                tapes (TM.steps (Abs_TM M) k (TM.initial_config (Abs_TM M) w)) ! 1"
        by (metis (no_types, lifting) One_nat_def diff_Suc_1' last_conv_nth list.size(3) nat.distinct(1)
            numeral_2_eq_2)
      show "TM.has_output (TM.compute (Abs_TM M) w) (rev (takeWhile P w))"
        apply (cases "w = []")
        unfolding TM.compute_def TM.compute_config_def TM.has_output_def TM.clean_output_of_def apply auto
        unfolding TM.clean_output_def apply auto
      proof -
        have 1: "(LEAST n. TM.is_final (Abs_TM M) ((TM.step (Abs_TM M) ^^ n)
                 (TM.initial_config (Abs_TM M) []))) = 1"
          apply (rule Least_natI)
           apply auto
          unfolding TM.is_final_def valid_tm_final_states [OF valid_M] f11' unfolding TM.initial_config_def
            valid_tm_initial_state [OF valid_M] by (simp_all add: M_def)
        show "\<exists>w. last (tapes ((TM.step (Abs_TM M) ^^
              (LEAST n. TM.is_final (Abs_TM M) ((TM.step (Abs_TM M) ^^ n) (TM.initial_config (Abs_TM M) []))))
              (TM.initial_config (Abs_TM M) []))) = TM_abbrevs.input_tape w" unfolding 1 apply simp
          apply (rule exI [where x="[]"])
          unfolding 0 [of 1 "[]", simplified] f12' [simplified] unfolding TM_abbrevs.input_tape_def by simp
        show "TM.output_of ((TM.step (Abs_TM M) ^^
              (LEAST n. TM.is_final (Abs_TM M) ((TM.step (Abs_TM M) ^^ n) (TM.initial_config (Abs_TM M) []))))
              (TM.initial_config (Abs_TM M) [])) = []" unfolding 1 apply auto
          unfolding TM.output_of_def Let_def 0 [of 1 "[]", simplified] unfolding f12' [simplified] by simp
      next
        assume a1: "w \<noteq> []"
        show "\<exists>w'. last (tapes ((TM.step (Abs_TM M) ^^
              (LEAST n. TM.is_final (Abs_TM M) ((TM.step (Abs_TM M) ^^ n) (TM.initial_config (Abs_TM M) w))))
              (TM.initial_config (Abs_TM M) w))) = TM_abbrevs.input_tape w'"
        proof (cases "\<forall>n<length w. P (w ! n)")
          case [THEN spec, THEN mp]: True
          have 1: "(LEAST n. TM.is_final (Abs_TM M) ((TM.step (Abs_TM M) ^^ n)
                   (TM.initial_config (Abs_TM M) w))) = length w + 1"
            apply (rule Least_nat_monoI)
              apply auto
            unfolding TM.is_final_def f31 [OF a1 True, simplified] valid_tm_final_states [OF valid_M]
             apply (subst M_def)
             apply simp
            apply (subst (asm) f11 [OF _ Nat.le_refl, of w])
            using a1 apply simp
             apply (erule True)
            unfolding M_def by simp
          show ?thesis unfolding 1 apply simp
            unfolding 0 [of "Suc (length w)", simplified] apply (subst f32 [simplified])
              apply fact
             apply (erule True)
            unfolding TM_abbrevs.input_tape_def apply (rule exI)
            by auto
        next
          case [simplified]: False
          define n :: nat where "n \<equiv> (LEAST m. m < length w \<and> \<not>P (w ! m))"
          note 1 = LeastI_ex [OF False, folded n_def]
          note 2 = Least_le [of "\<lambda>m. m < length w \<and> \<not>P (w ! m)", folded n_def, OF conjI]
          have 3: "\<And>m. m < n \<Longrightarrow> P (w ! m)" by (meson 1 2 leD order.strict_trans)
          have 4: "(LEAST n. TM.is_final (Abs_TM M) ((TM.step (Abs_TM M) ^^ n)
                   (TM.initial_config (Abs_TM M) w))) = n + 1"
            apply (rule Least_nat_monoI)
              apply auto
            unfolding TM.is_final_def using f21 [OF 1 [THEN conjunct1] 3 1 [THEN conjunct2]] apply auto
            unfolding valid_tm_final_states [OF valid_M] apply (subst M_def)
             apply simp
            apply (cases "n = 0")
             apply auto
             apply (subst (asm) TM.initial_config_def)
            unfolding valid_tm_initial_state [OF valid_M] apply simp
             apply (subst (asm) (1 2) M_def)
             apply simp
            using f11 [of n w, OF _ 1 [THEN conjunct1, THEN less_imp_le] 3] apply simp
            apply (subst (asm) M_def)
            by simp
          show ?thesis unfolding 4 0 apply simp
            unfolding f22 [OF 1 [THEN conjunct1] 3 1 [THEN conjunct2], simplified] apply auto
             apply (rule exI [where x="[]"])
            unfolding TM_abbrevs.input_tape_def apply simp
            using 1 apply simp
             apply (erule conjE)
             apply (metis 1 3 Nil_tl Nitpick.size_list_simp(2) length_rev length_takeWhile_eq nat.distinct(1))
            apply (rule exI [where x="rev (takeWhile P w)"])
            apply auto
            using 1 3 length_takeWhile_eq apply blast
            by (metis 1 3 Nil_is_rev_conv Suc_pred hd_conv_nth length_takeWhile_eq not_less_eq rev_nth
                takeWhile_nth)
        qed
        show "TM.output_of ((TM.step (Abs_TM M) ^^
              (LEAST n. TM.is_final (Abs_TM M) ((TM.step (Abs_TM M) ^^ n) (TM.initial_config (Abs_TM M) w))))
              (TM.initial_config (Abs_TM M) w)) = rev (takeWhile P w)"
        proof (cases "\<forall>n<length w. P (w ! n)")
          case [THEN spec, THEN mp]: True
          have 1: "(LEAST n. TM.is_final (Abs_TM M) ((TM.step (Abs_TM M) ^^ n)
                   (TM.initial_config (Abs_TM M) w))) = length w + 1"
            apply (rule Least_nat_monoI)
              apply auto
            unfolding TM.is_final_def f31 [OF a1 True, simplified] valid_tm_final_states [OF valid_M]
             apply (subst M_def)
             apply simp
            apply (subst (asm) f11 [OF _ Nat.le_refl, of w])
            using a1 apply simp
             apply (erule True)
            unfolding M_def by simp
          have 2: "\<And>w. the (those (takeWhile (\<lambda>s. \<exists>y. s = Some y) (map Some w))) = w"
            by (smt (verit, best) map_takeWhile option.sel takeWhile_eq_all_conv those_map_Some)
          show ?thesis unfolding 1 apply simp
            unfolding TM.output_of_def Let_def 0 [of "Suc (length w)", simplified] f32 [OF a1 True, simplified]
            apply (simp add: 2)
            by (smt (verit, best) Nitpick.size_list_simp(2) \<open>\<forall>n<length w. P (w ! n)\<close> a1 butlast_rev
                last_conv_nth length_greater_0_conv length_takeWhile_le length_tl lessI nat_less_le
                nth_length_takeWhile rev_eq_Cons_iff rev_rev_ident snoc_eq_iff_butlast takeWhile_nth)
        next
          case False
          case [simplified]: False
          define n :: nat where "n \<equiv> (LEAST m. m < length w \<and> \<not>P (w ! m))"
          note 1 = LeastI_ex [OF False, folded n_def]
          note 2 = Least_le [of "\<lambda>m. m < length w \<and> \<not>P (w ! m)", folded n_def, OF conjI]
          have 3: "\<And>m. m < n \<Longrightarrow> P (w ! m)" by (meson 1 2 leD order.strict_trans)
          have 4: "(LEAST n. TM.is_final (Abs_TM M) ((TM.step (Abs_TM M) ^^ n)
                   (TM.initial_config (Abs_TM M) w))) = n + 1"
            apply (rule Least_nat_monoI)
              apply auto
            unfolding TM.is_final_def using f21 [OF 1 [THEN conjunct1] 3 1 [THEN conjunct2]] apply auto
            unfolding valid_tm_final_states [OF valid_M] apply (subst M_def)
             apply simp
            apply (cases "n = 0")
             apply auto
             apply (subst (asm) TM.initial_config_def)
            unfolding valid_tm_initial_state [OF valid_M] apply simp
             apply (subst (asm) (1 2) M_def)
             apply simp
            using f11 [of n w, OF _ 1 [THEN conjunct1, THEN less_imp_le] 3] apply simp
            apply (subst (asm) M_def)
            by simp
          have 5: "\<And>w. the (those (takeWhile (\<lambda>s. \<exists>y. s = Some y) (map Some w))) = w"
            by (smt (verit, best) map_takeWhile option.sel takeWhile_eq_all_conv those_map_Some)
          show ?thesis unfolding 4 TM.output_of_def Let_def 0 apply simp
            unfolding f22 [OF 1 [THEN conjunct1] 3 1 [THEN conjunct2], simplified] apply auto
            using 1 apply auto
             apply (metis 1 3 Nitpick.size_list_simp(2) length_takeWhile_eq nat.distinct(1))
            using f22 [OF 1 [THEN conjunct1] 3 1 [THEN conjunct2]] apply simp
            unfolding 5 apply (rule nth_equalityI)
             apply auto
             apply (simp add: 3 length_takeWhile_eq)
            unfolding nth_Cons' apply auto
             apply (simp add: 3 length_takeWhile_eq rev_nth takeWhile_nth)
            by (simp add: nth_tl)
        qed
      qed
    qed
  qed
qed

lemma rev_dropWhile_computable: "computable_in_time (\<lambda>n. n + 1)
                                 ((rev::('s::finite) list \<Rightarrow> 's list) \<circ> dropWhile P)"
proof (rule typed_comp_in_time_natI)
  define M :: "('s option \<times> nat, 's, unit) TM_record" where
    "M \<equiv> TM 2 UNIV (UNIV \<times> {1, 2, 3}) (None, 1) (UNIV \<times> {3}) (\<lambda>_. ())
         (\<lambda>st hds. if snd st = 1 then if hds ! 0 = None then (fst st, 3) else if P (the (hds ! 0)) then
          (None, 1) else (hds ! 0, 2) else if hds ! 0 = None then (fst st, 3) else (hds ! 0, 2))
         (\<lambda>st _ _. fst st)
         (\<lambda>st hds k. if k = 0 then Shift_Right else if snd st = 1 \<or> hds ! 0 = None then No_Shift else
          Shift_Left)"
  have valid_M: "valid_TM M"
    apply unfold_locales
    unfolding M_def by auto
  have f11: "state (TM.steps (Abs_TM M) k (TM.initial_config (Abs_TM M) w)) = (None, 1)" and
       f12: "k < length w \<Longrightarrow> head (tapes (TM.steps (Abs_TM M) k (TM.initial_config (Abs_TM M) w)) ! 0) =
             Some (w ! k)" and
       f13: "k = length w \<Longrightarrow> head (tapes (TM.steps (Abs_TM M) k (TM.initial_config (Abs_TM M) w)) ! 0) =
             None" and
       f14: "right (tapes (TM.steps (Abs_TM M) k (TM.initial_config (Abs_TM M) w)) ! 0) =
             map Some (drop (Suc k) w)" and
       f15: "tapes (TM.steps (Abs_TM M) k (TM.initial_config (Abs_TM M) w)) ! 1 = Tape [] None []"
       if "k \<le> length w" and "\<And>n. n < k \<Longrightarrow> P (w ! n)" for k :: nat and w :: "'s list" using that
  proof (induction k)
    case 0
    {
      case 1
      then show ?case apply simp
        unfolding TM.initial_config_def valid_tm_initial_state [OF valid_M] apply simp
        unfolding M_def by simp
    next
      case 2
      then show ?case apply simp
        unfolding TM.initial_config_def TM_abbrevs.input_tape_def apply simp
        by (rule hd_conv_nth)
    next
      case 3
      show ?case apply simp
        unfolding TM.initial_config_def TM_abbrevs.input_tape_def using 3 by simp
    next
      case 4
      then show ?case apply simp
        unfolding TM.initial_config_def TM_abbrevs.input_tape_def apply auto
        by (simp add: drop_Suc)
    next
      case 5
      then show ?case apply simp
        unfolding TM.initial_config_def TM_abbrevs.input_tape_def valid_tm_tape_count [OF valid_M] apply auto
        unfolding M_def by simp
    }
  next
    case (Suc k)
    {
      case 1
      hence *: "k \<le> length w" and **: "\<And>n. n < k \<Longrightarrow> P (w ! n)" by simp_all
      have [simp]: "state ((TM.step (Abs_TM M) ^^ k) (TM.initial_config (Abs_TM M) w)) \<notin>
                    TM.TM.final_states (Abs_TM M)" unfolding Suc(1) [OF * **, simplified]
        valid_tm_final_states [OF valid_M] unfolding M_def by simp
      show ?case apply simp
        apply (subst TM.step_def)
        apply simp
        unfolding Suc(1) [OF * **, simplified] valid_tm_next_state [OF valid_M] apply (subst M_def)
        apply auto
          apply (subst nth_map)
           apply (simp add: TM.run_tapes_len)
          apply (subst Suc(2) [OF _ * **])
        using 1(1) apply simp
           apply assumption
          apply blast
         apply (subst nth_map)
          apply (simp add: TM.run_tapes_len)
         apply (subst Suc(2) [OF _ * **])
        using 1(1) apply simp
          apply assumption
         apply blast
        apply (subst (asm) nth_map)
         apply (simp add: TM.run_tapes_len)
        apply (subst (asm) Suc(2) [OF _ * **])
        using 1(1) apply simp
         apply assumption
        apply simp
        using "1.prems"(2) by blast
    next
      case 2
      hence *: "k \<le> length w" and **: "\<And>n. n < k \<Longrightarrow> P (w ! n)" by simp_all
      have [simp]: "state ((TM.step (Abs_TM M) ^^ k) (TM.initial_config (Abs_TM M) w)) \<notin>
                    TM.TM.final_states (Abs_TM M)" unfolding Suc(1) [OF * **, simplified]
        valid_tm_final_states [OF valid_M] unfolding M_def by simp
      show ?case apply simp
        apply (subst TM.step_def)
        apply simp
        unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_writes_def TM.next_moves_def
        apply (subst nth_map2)
          apply auto
         apply (metis TM.run_tapes_len TM.at_least_one_tape list.size(3) bot_nat_0.not_eq_extremum)
        unfolding valid_tm_next_move [OF valid_M] apply (subst M_def)
        apply simp
        apply (subst Shift_Right_is_right_not_empty)
         apply auto
        using ** "2.prems"(1) Suc.IH(4) apply force
        by (metis * ** "2.prems"(1) Suc.IH(4) drop_eq_Nil hd_drop_conv_nth linorder_not_less list.map_sel(1))
    next
      case 3
      hence *: "k \<le> length w" and **: "\<And>n. n < k \<Longrightarrow> P (w ! n)" by simp_all
      have [simp]: "state ((TM.step (Abs_TM M) ^^ k) (TM.initial_config (Abs_TM M) w)) \<notin>
                    TM.TM.final_states (Abs_TM M)" unfolding Suc(1) [OF * **, simplified]
        valid_tm_final_states [OF valid_M] unfolding M_def by simp
      show ?case apply simp
        apply (subst TM.step_def)
        apply simp
        unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_writes_def TM.next_moves_def
        apply (subst nth_map2)
          apply auto
         apply (metis TM.run_tapes_len TM.at_least_one_tape list.size(3) bot_nat_0.not_eq_extremum)
        unfolding valid_tm_next_move [OF valid_M] apply (subst M_def)
        apply simp
        apply (cases "right (tapes ((TM.step (Abs_TM M) ^^ k) (TM.initial_config (Abs_TM M) w)) ! 0)")
         apply auto
        by (simp add: * ** "3.prems"(1) Suc.IH(4))
    next
      case 4
      hence *: "k \<le> length w" and **: "\<And>n. n < k \<Longrightarrow> P (w ! n)" by simp_all
      have [simp]: "state ((TM.step (Abs_TM M) ^^ k) (TM.initial_config (Abs_TM M) w)) \<notin>
                    TM.TM.final_states (Abs_TM M)" unfolding Suc(1) [OF * **, simplified]
        valid_tm_final_states [OF valid_M] unfolding M_def by simp
      show ?case apply simp
        apply (subst TM.step_def)
        apply simp
        unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_writes_def TM.next_moves_def
        apply (subst nth_map2)
          apply auto
         apply (metis TM.run_tapes_len TM.at_least_one_tape list.size(3) bot_nat_0.not_eq_extremum)
        unfolding valid_tm_next_move [OF valid_M] apply (subst M_def)
        apply simp
        unfolding Suc(4) [OF * **, simplified] by (metis drop_Suc tl_drop drop_map)
    next
      case 5
      hence *: "k \<le> length w" and **: "\<And>n. n < k \<Longrightarrow> P (w ! n)" by simp_all
      have [simp]: "state ((TM.step (Abs_TM M) ^^ k) (TM.initial_config (Abs_TM M) w)) \<notin>
                    TM.TM.final_states (Abs_TM M)" unfolding Suc(1) [OF * **, simplified]
        valid_tm_final_states [OF valid_M] unfolding M_def by simp
      show ?case apply simp
        apply (subst TM.step_def)
        apply simp
        unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_writes_def TM.next_moves_def
        apply (subst nth_map2)
          apply auto
        unfolding valid_tm_tape_count [OF valid_M] apply (simp add: M_def)
         apply (metis (lifting) M_def TM.run_tapes_len valid_tm_tape_count [OF valid_M] lessI numeral_2_eq_2
            simps(1))
        apply (subst (1 2) nth_zip)
          apply auto
          apply (simp add: M_def)
         apply (simp add: M_def)
        apply (subst (1 2) nth_map)
         apply (simp add: M_def)
        unfolding Suc(1) [OF * **, simplified] valid_tm_next_move [OF valid_M] valid_tm_next_write [OF valid_M]
        apply (subst (1 4 5 8) M_def)
        apply simp
        unfolding TM_abbrevs.tape_shift.simps TM_abbrevs.tape_write_def apply auto
        unfolding Suc(5) [OF * **, simplified] by simp_all
    }
  qed
  have f21: "state (TM.steps (Abs_TM M) (Suc (length w)) (TM.initial_config (Abs_TM M) w)) = (None, 3)" and
       f22: "tapes (TM.steps (Abs_TM M) (Suc (length w)) (TM.initial_config (Abs_TM M) w)) ! 1 =
             Tape [] None []"
       if "\<And>n. n < length w \<Longrightarrow> P (w ! n)" for k :: nat and w :: "'s list"
  proof -
    show "state ((TM.step (Abs_TM M) ^^ Suc (length w)) (TM.initial_config (Abs_TM M) w)) = (None, 3)"
      apply simp
      apply (subst TM.step_def)
      apply auto
      unfolding f11 [OF Nat.le_refl that, simplified] valid_tm_final_states [OF valid_M]
       apply (subst (asm) M_def)
       apply simp
      unfolding valid_tm_next_state [OF valid_M] apply (subst M_def)
      apply simp
      apply (subst nth_map)
       apply (simp add: TM.run_tapes_len)
      by (rule f13 [OF Nat.le_refl that, simplified])
    have [simp]: "[0..<TM.TM.tape_count (Abs_TM M)] ! Suc 0 = Suc 0"
      using M_def valid_M valid_tm_tape_count by fastforce
    show "tapes ((TM.step (Abs_TM M) ^^ Suc (length w)) (TM.initial_config (Abs_TM M) w)) ! 1 = Tape [] None []"
      apply simp
      apply (subst TM.step_def)
      apply auto
      unfolding f11 [OF Nat.le_refl that, simplified] valid_tm_final_states [OF valid_M]
       apply (subst (asm) M_def)
       apply simp
      apply (subst nth_map2)
        apply (metis (no_types, lifting) M_def TM.next_actions_simps(2) lessI numeral_2_eq_2 simps(1) valid_M
          valid_tm_tape_count)
       apply (metis (no_types, lifting) M_def TM.run_tapes_len lessI numeral_2_eq_2 simps(1) valid_M
          valid_tm_tape_count)
      unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_moves_def TM.next_writes_def
      apply (subst (1 2) nth_zip)
        apply auto
      using M_def valid_M valid_tm_tape_count apply fastforce
      using M_def valid_M valid_tm_tape_count apply fastforce
      apply (subst (1 2) nth_map)
       apply auto
      using M_def valid_M valid_tm_tape_count apply fastforce
      unfolding valid_tm_next_move [OF valid_M] valid_tm_next_write [OF valid_M] apply (subst (1 4) M_def)
      apply simp
      unfolding TM_abbrevs.tape_shift.simps TM_abbrevs.tape_write_def apply auto
      unfolding f15 [OF Nat.le_refl that, simplified] by simp_all
  qed
  have f31: "state (TM.steps (Abs_TM M) k' (TM.initial_config (Abs_TM M) w)) = (Some (w ! (k' - 1)), 2)" and
       f32: "k' < length w \<Longrightarrow> head (tapes (TM.steps (Abs_TM M) k'
             (TM.initial_config (Abs_TM M) w)) ! 0) = Some (w ! k')" and
       f33: "k' = length w \<Longrightarrow> head (tapes (TM.steps (Abs_TM M) k'
             (TM.initial_config (Abs_TM M) w)) ! 0) = None" and
       f34: "right (tapes (TM.steps (Abs_TM M) k' (TM.initial_config (Abs_TM M) w)) ! 0) =
             map Some (drop (Suc k') w)" and
       f35: "tapes (TM.steps (Abs_TM M) k' (TM.initial_config (Abs_TM M) w)) ! 1 =
             Tape [] None (rev (drop k (take (k' - 1) (map Some w))))"
       if "Suc k \<le> k'" and "\<And>n. n < k \<Longrightarrow> P (w ! n)" and "\<not>P (w ! k)" and "k' \<le> length w"
       for k k' :: nat and w :: "'s list" using that
  proof (induction k' rule: nat_induct_at_least)
    case base
    {
      case 1
      hence *: "k \<le> length w" by simp
      have [simp]: "state ((TM.step (Abs_TM M) ^^ k) (TM.initial_config (Abs_TM M) w)) \<notin>
                    TM.TM.final_states (Abs_TM M)"
        unfolding f11 [OF * 1(1), simplified] valid_tm_final_states [OF valid_M] unfolding M_def by simp
      have [simp]: "heads ((TM.step (Abs_TM M) ^^ k) (TM.initial_config (Abs_TM M) w)) ! 0 = Some (w ! k)"
        apply (subst nth_map)
         apply (simp add: TM.run_tapes_len)
        apply (subst f12)
           apply fact
          apply (erule 1(1))
        using 1(3) by simp_all
      show ?case apply simp
        apply (subst TM.step_def)
        apply simp
        unfolding valid_tm_next_state [OF valid_M] f11 [OF * 1(1), simplified] apply (subst M_def)
        using 1(2) by simp
    next
      case 2
      hence *: "k \<le> length w" by simp
      have [simp]: "state ((TM.step (Abs_TM M) ^^ k) (TM.initial_config (Abs_TM M) w)) \<notin>
                    TM.TM.final_states (Abs_TM M)"
        unfolding f11 [OF * 2(2), simplified] valid_tm_final_states [OF valid_M] unfolding M_def by simp
      have [simp]: "heads ((TM.step (Abs_TM M) ^^ k) (TM.initial_config (Abs_TM M) w)) ! 0 = Some (w ! k)"
        apply (subst nth_map)
         apply (simp add: TM.run_tapes_len)
        apply (subst f12)
           apply fact
          apply (erule 2(2))
        using 2(4) by simp_all
      show ?case apply simp
        apply (subst TM.step_def)
        apply simp
        unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_writes_def TM.next_moves_def
        apply (subst nth_map2)
          apply auto
         apply (metis TM.at_least_one_tape TM.run_tapes_len length_0_conv less_not_refl)
        unfolding valid_tm_next_move [OF valid_M] apply (subst M_def)
        apply simp
        unfolding valid_tm_next_write [OF valid_M] apply (subst M_def)
        apply simp
        apply (subst Shift_Right_is_right_not_empty)
         apply auto
        using "2.prems"(1) f14 that(2) apply force
        unfolding f14 [OF * 2(2), simplified]
        by (metis "2.prems"(1) drop_eq_Nil hd_drop_conv_nth linorder_not_less list.map_sel(1))
    next
      case 3
      hence *: "k \<le> length w" by simp
      have [simp]: "state ((TM.step (Abs_TM M) ^^ k) (TM.initial_config (Abs_TM M) w)) \<notin>
                    TM.TM.final_states (Abs_TM M)"
        unfolding f11 [OF * 3(2), simplified] valid_tm_final_states [OF valid_M] unfolding M_def by simp
      have [simp]: "heads ((TM.step (Abs_TM M) ^^ k) (TM.initial_config (Abs_TM M) w)) ! 0 = Some (w ! k)"
        apply (subst nth_map)
         apply (simp add: TM.run_tapes_len)
        apply (subst f12)
           apply fact
          apply (erule 3(2))
        using 3(4) by simp_all
      show ?case apply simp
        apply (subst TM.step_def)
        apply simp
        apply (subst nth_map2)
          apply (simp add: TM.next_actions_simps(2))
         apply (simp add: TM.run_tapes_len)
        unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_writes_def TM.next_moves_def apply simp
        unfolding valid_tm_next_move [OF valid_M] apply (subst M_def)
        apply simp
        apply (cases "right (tapes ((TM.step (Abs_TM M) ^^ k) (TM.initial_config (Abs_TM M) w)) ! 0)")
         apply auto
        by (simp add: * "3.prems"(1) f14 that(2))
    next
      case 4
      hence *: "k \<le> length w" by simp
      have [simp]: "state ((TM.step (Abs_TM M) ^^ k) (TM.initial_config (Abs_TM M) w)) \<notin>
                    TM.TM.final_states (Abs_TM M)"
        unfolding f11 [OF * 4(1), simplified] valid_tm_final_states [OF valid_M] unfolding M_def by simp
      have [simp]: "heads ((TM.step (Abs_TM M) ^^ k) (TM.initial_config (Abs_TM M) w)) ! 0 = Some (w ! k)"
        apply (subst nth_map)
         apply (simp add: TM.run_tapes_len)
        apply (subst f12)
           apply fact
          apply (erule 4(1))
        using 4(3) by simp_all
      show ?case apply simp
        apply (subst TM.step_def)
        apply simp
        apply (subst nth_map2)
          apply (simp add: TM.next_actions_simps(2))
         apply (simp add: TM.run_tapes_len)
        unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_writes_def TM.next_moves_def apply simp
        unfolding valid_tm_next_move [OF valid_M] apply (subst M_def)
        apply simp
        by (metis (no_types, lifting) "4.prems"(3) drop_Suc f14 less_eq_Suc_le map_tl nat_less_le that(2) tl_drop)
    next
      case 5
      hence *: "k \<le> length w" by simp
      have [simp]: "state ((TM.step (Abs_TM M) ^^ k) (TM.initial_config (Abs_TM M) w)) \<notin>
                    TM.TM.final_states (Abs_TM M)"
        unfolding f11 [OF * 5(1), simplified] valid_tm_final_states [OF valid_M] unfolding M_def by simp
      have [simp]: "heads ((TM.step (Abs_TM M) ^^ k) (TM.initial_config (Abs_TM M) w)) ! 0 = Some (w ! k)"
        apply (subst nth_map)
         apply (simp add: TM.run_tapes_len)
        apply (subst f12)
           apply fact
          apply (erule 5(1))
        using 5(3) by simp_all
      have [simp]: "[0..<TM.TM.tape_count (Abs_TM M)] ! Suc 0 = Suc 0"
        unfolding valid_tm_tape_count [OF valid_M] unfolding M_def by simp
      show ?case apply simp
        apply (subst TM.step_def)
        apply simp
        apply (subst nth_map2)
          apply (metis (no_types, lifting) M_def TM.next_actions_simps(2) lessI numeral_2_eq_2 simps(1) valid_M
            valid_tm_tape_count)
         apply (metis (no_types, lifting) M_def TM.run_tapes_len lessI numeral_2_eq_2 simps(1) valid_M
            valid_tm_tape_count)
        unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_writes_def TM.next_moves_def
        apply (subst (1 2) nth_zip)
          apply auto
        using M_def valid_M valid_tm_tape_count apply fastforce
        using M_def valid_M valid_tm_tape_count apply fastforce
        apply (subst (1 2) nth_map)
        using M_def valid_M valid_tm_tape_count apply fastforce
        apply simp
        unfolding f11 [OF * 5(1), simplified] valid_tm_next_move [OF valid_M] valid_tm_next_write [OF valid_M]
        apply (subst M_def)
        apply simp
        apply (subst M_def)
        apply simp
        unfolding TM_abbrevs.tape_shift.simps TM_abbrevs.tape_write_def apply auto
        using * f15 that(2) by auto
    }
  next
    case (Suc n)
    {
      case 1
      hence *: "n \<le> length w" by simp
      have [simp]: "state ((TM.step (Abs_TM M) ^^ n) (TM.initial_config (Abs_TM M) w)) \<notin>
                    TM.TM.final_states (Abs_TM M)" unfolding Suc(2) [OF 1(1, 2) *, simplified]
        valid_tm_final_states [OF valid_M] unfolding M_def by simp
      show ?case apply simp
        apply (subst TM.step_def)
        apply simp
        unfolding valid_tm_next_state [OF valid_M] Suc(2) [OF 1(1, 2) *, simplified] apply (subst M_def)
        apply auto
         apply (subst nth_map)
          apply (simp add: TM.run_tapes_len)
        apply (rule exI)
         apply (rule Suc(3))
        using 1 apply simp_all[4]
        apply (subst (asm) nth_map)
         apply (simp add: TM.run_tapes_len)
        apply (subst (asm) Suc(3))
        using 1 by simp_all
    next
      case 2
      hence *: "n \<le> length w" by simp
      have [simp]: "state ((TM.step (Abs_TM M) ^^ n) (TM.initial_config (Abs_TM M) w)) \<notin>
                    TM.TM.final_states (Abs_TM M)" unfolding Suc(2) [OF 2(2, 3) *, simplified]
        valid_tm_final_states [OF valid_M] unfolding M_def by simp
      show ?case apply simp
        apply (subst TM.step_def)
        apply simp
        apply (subst nth_map2)
          apply (simp add: TM.next_actions_simps(2))
         apply (simp add: TM.run_tapes_len)
        unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_writes_def TM.next_moves_def
        apply simp
        unfolding valid_tm_next_move [OF valid_M] apply (subst M_def)
        apply simp
        apply (subst Shift_Right_is_right_not_empty)
         apply auto
        using "2.prems"(1) Suc.IH(4) that(2,3) apply fastforce
        unfolding Suc(5) [OF 2(2, 3) *, simplified]
        by (metis "2.prems"(1) linorder_not_less hd_drop_conv_nth list.map_sel(1) drop_eq_Nil)
    next
      case 3
      hence *: "n \<le> length w" by simp
      have [simp]: "state ((TM.step (Abs_TM M) ^^ n) (TM.initial_config (Abs_TM M) w)) \<notin>
                    TM.TM.final_states (Abs_TM M)" unfolding Suc(2) [OF 3(2, 3) *, simplified]
        valid_tm_final_states [OF valid_M] unfolding M_def by simp
      show ?case apply simp
        apply (subst TM.step_def)
        apply simp
        apply (subst nth_map2)
          apply (simp add: TM.next_actions_simps(2))
         apply (simp add: TM.run_tapes_len)
        unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_moves_def TM.next_writes_def apply simp
        unfolding valid_tm_next_move [OF valid_M] apply (subst M_def)
        apply simp
        apply (cases "right (tapes ((TM.step (Abs_TM M) ^^ n) (TM.initial_config (Abs_TM M) w)) ! 0)")
         apply auto
        by (simp add: * "3.prems"(1) Suc.IH(4) that(2,3))
    next
      case 4
      hence *: "n \<le> length w" by simp
      have [simp]: "state ((TM.step (Abs_TM M) ^^ n) (TM.initial_config (Abs_TM M) w)) \<notin>
                    TM.TM.final_states (Abs_TM M)" unfolding Suc(2) [OF 4(1, 2) *, simplified]
        valid_tm_final_states [OF valid_M] unfolding M_def by simp
      show ?case apply simp
        apply (subst TM.step_def)
        apply simp
        apply (subst nth_map2)
          apply (simp add: TM.next_actions_simps(2))
         apply (simp add: TM.run_tapes_len)
        unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_writes_def TM.next_moves_def apply simp
        unfolding valid_tm_next_move [OF valid_M] apply (subst M_def)
        apply simp
        using * Suc.IH(4) drop_Suc[of "Suc n" "map Some w"] drop_map[of "Suc (Suc n)" Some w]
          drop_map[of "Suc n" Some w] that(2,3) tl_drop[of "Suc n" "map Some w"] by presburger
    next
      case 5
      hence *: "n \<le> length w" by simp
      have [simp]: "state ((TM.step (Abs_TM M) ^^ n) (TM.initial_config (Abs_TM M) w)) \<notin>
                    TM.TM.final_states (Abs_TM M)" unfolding Suc(2) [OF 5(1, 2) *, simplified]
        valid_tm_final_states [OF valid_M] unfolding M_def by simp
      have [simp]: "[0..<TM.TM.tape_count (Abs_TM M)] ! Suc 0 = Suc 0"
        unfolding valid_tm_tape_count [OF valid_M] unfolding M_def by simp
      show ?case apply simp
        apply (subst TM.step_def)
        apply simp
        apply (subst nth_map2)
        unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_writes_def TM.next_moves_def apply auto
        using M_def valid_M valid_tm_tape_count apply fastforce
         apply (metis (no_types, lifting) M_def TM.run_tapes_len lessI numeral_2_eq_2 simps(1) valid_M
            valid_tm_tape_count)
        apply (subst (1 2) nth_zip)
          apply auto
        using M_def valid_M valid_tm_tape_count apply fastforce
        using M_def valid_M valid_tm_tape_count apply fastforce
        apply (subst (1 2) nth_map)
         apply simp_all
        using M_def valid_M valid_tm_tape_count apply fastforce
        unfolding valid_tm_next_move [OF valid_M] valid_tm_next_write [OF valid_M]
          Suc(2) [OF 5(1, 2) *, simplified] apply (subst M_def)
        apply auto
         apply (smt (verit, best) "5.prems"(3) M_def Suc.IH(2) TM.run_tapes_len hd_conv_nth lessI less_eq_Suc_le
            list.map_disc_iff list.map_sel(1) list.size(3) nat_less_le numeral_2_eq_2 option.distinct(1) simps(1)
            that(2,3) valid_M valid_tm_tape_count)
        apply (rule tape.expand)
        apply auto
          apply (metis "5.prems"(3) One_nat_def Suc.IH(5) less_eq_Suc_le list.sel(2) nat_less_le tape.sel(1)
            that(2,3))
         apply (cases "left (tapes ((TM.step (Abs_TM M) ^^ n) (TM.initial_config (Abs_TM M) w)) ! Suc 0)")
          apply auto
         apply (metis * One_nat_def Suc.IH(5) list.distinct(1) tape.sel(1) that(2,3))
        apply (subst M_def)
        apply simp
        unfolding TM_abbrevs.tape_write_def apply simp
        unfolding Suc(6) [OF 5(1, 2) *, simplified] apply simp
        apply (rule nth_equalityI)
         apply auto
         apply (metis * One_nat_def Suc.hyps Suc_diff_Suc diff_Suc_eq_diff_pred diff_le_self le_trans
            less_eq_Suc_le min.absorb2)
        apply (subst rev_nth)
         apply auto
        apply (metis * One_nat_def Suc.hyps Suc_diff_Suc[of k n] Suc_le_D[of k n] diff_Suc_1'
            diff_Suc_eq_diff_pred[of n k] less_eq_Suc_le[of _ "length w"] less_eq_Suc_le[of k n]
            min.absorb2[of n "length w"] min.absorb4[of _ "length w"])
        apply (subst nth_drop)
         apply auto
        using * Suc.hyps Suc_leD le_trans apply blast
        using Suc.hyps Suc_leD apply blast
        apply (subst nth_Cons')
        apply auto
         apply (subst nth_take)
        using Suc.hyps apply linarith
        using * apply simp
         apply (subst nth_map)
          apply auto
        using Suc.hyps apply linarith
         apply (simp add: Suc.hyps)
        apply (subst rev_nth)
        using * by simp_all
    }
  qed
  have f41: "state (TM.steps (Abs_TM M) (Suc (length w)) (TM.initial_config (Abs_TM M) w)) =
             (Some (last w), 3)" and
       f42: "tapes (TM.steps (Abs_TM M) (Suc (length w)) (TM.initial_config (Abs_TM M) w)) ! 1 =
             Tape [] (Some (last w)) (rev (drop k (butlast (map Some w))))"
       if "\<And>n. n < k \<Longrightarrow> P (w ! n)" and "\<not>P (w ! k)" and "k < length w"
       for k :: nat and w :: "'s list"
  proof simp_all
    have [simp]: "state ((TM.step (Abs_TM M) ^^ length w) (TM.initial_config (Abs_TM M) w)) \<notin>
                  TM.TM.final_states (Abs_TM M)"
      using f31 [of k "length w" w, OF _ that(1, 2), simplified] that(3) apply simp
      unfolding valid_tm_final_states [OF valid_M] apply (subst M_def)
      by simp
    show "state (TM.step (Abs_TM M) ((TM.step (Abs_TM M) ^^ length w) (TM.initial_config (Abs_TM M) w))) =
          (Some (last w), 3)" apply (subst TM.step_def)
      apply simp
      unfolding valid_tm_next_state [OF valid_M]
      using f31 [of k "length w" w, OF _ that(1, 2), simplified] that(3) apply simp
      apply (subst M_def)
      apply auto
       apply (metis One_nat_def last_conv_nth length_greater_0_conv less_nat_zero_code neq0_conv)
      by (smt (verit, ccfv_SIG) M_def TM.run_tapes_len f33 hd_conv_nth le_refl less_eq_Suc_le list.map_disc_iff
          list.map_sel(1) list.size(3) nat_less_le numeral_2_eq_2 simps(1) that(1,2) valid_M valid_tm_tape_count)
    have [simp]: "[0..<tape_count M] ! Suc 0 = Suc 0" by (simp add: M_def)
    show "tapes (TM.step (Abs_TM M) ((TM.step (Abs_TM M) ^^ length w) (TM.initial_config (Abs_TM M) w))) ! Suc 0 =
          Tape [] (Some (last w)) (rev (drop k (butlast (map Some w))))" apply (subst TM.step_def)
      apply simp
      apply (subst nth_map2)
        apply (metis (no_types, lifting) M_def TM.next_actions_simps(2) lessI numeral_2_eq_2 simps(1) valid_M
          valid_tm_tape_count)
       apply (metis (no_types, lifting) M_def TM.run_tapes_len lessI numeral_2_eq_2 simps(1) valid_M
          valid_tm_tape_count)
      unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_moves_def TM.next_writes_def
      apply (subst (1 2) nth_zip)
        apply auto
      unfolding valid_tm_tape_count [OF valid_M] apply (simp add: M_def)
       apply (simp add: M_def)
      apply (subst (1 2) nth_map)
       apply (simp add: M_def)
      unfolding valid_tm_next_move [OF valid_M]
      using f31 [of k "length w" w, OF _ that(1, 2), simplified] that(3) apply simp
      apply (subst M_def)
      apply auto
      unfolding TM_abbrevs.tape_shift.simps valid_tm_next_write [OF valid_M] apply (subst M_def)
       apply simp
      unfolding TM_abbrevs.tape_write_def apply auto
         apply (subst f35 [simplified, of k])
      using that(3) apply simp
            apply (erule that(1))
           apply (rule that(2))
          apply (rule Nat.le_refl)
         apply simp
        apply (metis One_nat_def list.size(3) less_nat_zero_code last_conv_nth)
       apply (subst f35 [simplified, of k])
      using that(3) apply simp
          apply (erule that(1))
         apply (rule that(2))
        apply (rule Nat.le_refl)
       apply simp
       apply (simp add: butlast_conv_take)
      apply (rule tape.expand)
      apply auto
      by (smt (verit, best) M_def Suc_pred TM.run_tapes_len valid_tm_tape_count [OF valid_M] f33
          hd_conv_nth length_greater_0_conv lessI less_eq_Suc_le list.map_disc_iff list.map_sel(1) list.size(3)
          not_less_zero numeral_2_eq_2 option.distinct(1) simps(1) that(1,2))+
  qed
  show "typed_computable_in_time TYPE('s option \<times> nat) TYPE(unit) (\<lambda>n. n + 1)
        ((rev::('s::finite) list \<Rightarrow> 's list) \<circ> dropWhile P)"
  proof (unfold typed_computable_in_time_def, rule exI, auto)
    show M_syms: "\<And>s. s \<in> TM.symbols (Abs_TM M)"
      unfolding valid_tm_symbols [OF valid_M] unfolding M_def by simp
    show M_tb: "TM.time_bounded_word (Abs_TM M) Suc w" for w :: "'s list"
    proof (unfold TM.time_bounded_word_def TM.is_final_def TM.run_def)
      show "state ((TM.step (Abs_TM M) ^^ Suc (length w)) (TM.initial_config (Abs_TM M) w)) \<in>
            TM.TM.final_states (Abs_TM M)"
        apply (cases "\<forall>n<length w. P (w ! n)")
         apply (subst f21)
          apply simp
        unfolding valid_tm_final_states [OF valid_M] apply (subst M_def)
      proof auto
        fix n :: nat
        assume a1: "n < length w" and a2: "\<not> P (w ! n)"
        define n' :: nat where "n' \<equiv> (LEAST n. n < length w \<and> \<not> P (w ! n))"
        note 1 = LeastI [of "\<lambda>n. n < length w \<and> \<not> P (w ! n)", OF conjI [OF a1 a2], folded n'_def]
        note 2 = not_less_Least [where P="\<lambda>n. n < length w \<and> \<not> P (w ! n)", folded n'_def, simplified,
            THEN mp]
        show "state (TM.step (Abs_TM M) ((TM.step (Abs_TM M) ^^ length w) (TM.initial_config (Abs_TM M) w)))
              \<in> final_states M" using f41 [OF 2, of n'] 1 apply auto
          by (simp add: M_def)
      qed
    qed
    show "TM.computes (Abs_TM M) (rev \<circ> dropWhile P)"
    proof (unfold TM.computes_def TM.computes_word_def, auto)
      fix w :: "'s list"
      show "TM.halts (Abs_TM M) w" using M_tb [of w] M_tb TM.time_bounded_altdef2 by blast
      have 0: "(LEAST n. TM.is_final (Abs_TM M) ((TM.step (Abs_TM M) ^^ n) (TM.initial_config (Abs_TM M) w))) =
               Suc (length w)"
        apply (rule Least_nat_monoI)
          apply auto
        unfolding TM.is_final_def valid_tm_final_states [OF valid_M] apply (cases "\<forall>n<length w. P (w ! n)")
          apply auto
          apply (subst f21 [simplified])
           apply simp
      proof (simp add: M_def)
        fix n :: nat
        assume a1: "n < length w" and a2: "\<not> P (w ! n)"
        define n' :: nat where "n' \<equiv> (LEAST n. n < length w \<and> \<not> P (w ! n))"
        note 1 = LeastI [of "\<lambda>n. n < length w \<and> \<not> P (w ! n)", OF conjI [OF a1 a2], folded n'_def]
        note 2 = not_less_Least [where P="\<lambda>n. n < length w \<and> \<not> P (w ! n)", folded n'_def, simplified,
            THEN mp]
        show "state (TM.step (Abs_TM M) ((TM.step (Abs_TM M) ^^ length w) (TM.initial_config (Abs_TM M) w)))
              \<in> final_states M" using f41 [OF 2, of n'] 1 by (simp add: M_def)
      next
        show "state ((TM.step (Abs_TM M) ^^ length w) (TM.initial_config (Abs_TM M) w)) \<in> final_states M \<Longrightarrow>
              False" apply (cases "\<forall>n<length w. P (w ! n)")
           apply auto
           apply (subst (asm) f11)
             apply auto
          apply (subst (asm) M_def)
        proof simp
          fix n :: nat
          assume a1: "state ((TM.step (Abs_TM M) ^^ length w) (TM.initial_config (Abs_TM M) w)) \<in>
                      final_states M" and
                 a2: "n < length w" and a3: "\<not> P (w ! n)"
          define n' :: nat where "n' \<equiv> (LEAST n. n < length w \<and> \<not> P (w ! n))"
          note 1 = LeastI [of "\<lambda>n. n < length w \<and> \<not> P (w ! n)", OF conjI [OF a2 a3], folded n'_def]
          note 2 = not_less_Least [where P="\<lambda>n. n < length w \<and> \<not> P (w ! n)", folded n'_def, simplified,
            THEN mp]
          show False using a1 apply (subst (asm) f31 [of n'])
            using 1 apply auto
             apply (rule 2)
              apply assumption
            using 1 apply simp
            unfolding M_def by simp
        qed
      qed
      show "TM.has_output (TM.compute (Abs_TM M) w) (rev (dropWhile P w))"
        unfolding TM.compute_def TM.compute_config_def 0 TM.has_output_def TM.clean_output_of_def
        apply (cases "\<forall>n<length w. P (w ! n)")
         apply auto
        unfolding TM.clean_output_def TM.output_of_def Let_def
      proof auto
        assume a1: "\<forall>n<length w. P (w ! n)"
        have "length (tapes (TM.step (Abs_TM M) ((TM.step (Abs_TM M) ^^ length w)
              (TM.initial_config (Abs_TM M) w)))) = 2"
          by (metis (no_types, lifting) M_def TM.run_tapes_len TM.step_l_tps simps(1) valid_M
              valid_tm_tape_count)
        hence 1: "last (tapes (TM.step (Abs_TM M) ((TM.step (Abs_TM M) ^^ length w)
                  (TM.initial_config (Abs_TM M) w)))) =
                  tapes (TM.step (Abs_TM M) ((TM.step (Abs_TM M) ^^ length w)
                  (TM.initial_config (Abs_TM M) w))) ! 1"
          by (metis Nitpick.size_list_simp(2) One_nat_def diff_Suc_1 last_conv_nth nat.distinct(1)
              numeral_2_eq_2)
        show "\<exists>w'. last (tapes (TM.step (Abs_TM M) ((TM.step (Abs_TM M) ^^ length w)
              (TM.initial_config (Abs_TM M) w)))) = TM_abbrevs.input_tape w'"
          unfolding 1 [simplified] apply (subst f22 [simplified])
          using a1 apply simp
          unfolding TM_abbrevs.input_tape_def apply (rule exI)
          by simp
        fix w' :: "'s list"
        assume a2 [unfolded 1]: "last (tapes (TM.step (Abs_TM M) ((TM.step (Abs_TM M) ^^ length w)
                                 (TM.initial_config (Abs_TM M) w)))) = TM_abbrevs.input_tape w'"
        show "(case head (TM_abbrevs.input_tape w') of None \<Rightarrow> [] | Some h \<Rightarrow>
               h # the (those (takeWhile (\<lambda>s. s \<noteq> None) (right (last (tapes (TM.step (Abs_TM M)
               ((TM.step (Abs_TM M) ^^ length w) (TM.initial_config (Abs_TM M) w))))))))) =
               rev (dropWhile P w)" using a2 [simplified] apply (subst (asm) f22 [simplified])
          using 1 apply simp
          using a1 apply simp
          unfolding TM_abbrevs.input_tape_def apply auto
          apply (cases w')
           apply auto
          by (metis a1 set_listE)
      next
        fix n :: nat and w' :: "'s list"
        assume a1: "n < length w" and a2: "\<not> P (w ! n)"
        define n' :: nat where "n' \<equiv> (LEAST n. n < length w \<and> \<not> P (w ! n))"
        note 1 = LeastI [of "\<lambda>n. n < length w \<and> \<not> P (w ! n)", OF conjI [OF a1 a2], folded n'_def]
        note 2 = not_less_Least [where P="\<lambda>n. n < length w \<and> \<not> P (w ! n)", folded n'_def, simplified,
            THEN mp]
        have "length (tapes (TM.step (Abs_TM M) ((TM.step (Abs_TM M) ^^ length w)
              (TM.initial_config (Abs_TM M) w)))) = 2"
          by (metis (no_types, lifting) M_def TM.run_tapes_len TM.step_l_tps simps(1) valid_M
              valid_tm_tape_count)
        hence 3: "last (tapes (TM.step (Abs_TM M) ((TM.step (Abs_TM M) ^^ length w)
                  (TM.initial_config (Abs_TM M) w)))) =
                  tapes (TM.step (Abs_TM M) ((TM.step (Abs_TM M) ^^ length w)
                  (TM.initial_config (Abs_TM M) w))) ! 1"
          by (metis Nitpick.size_list_simp(2) One_nat_def diff_Suc_1 last_conv_nth nat.distinct(1)
              numeral_2_eq_2)
        show "\<exists>w'. last (tapes (TM.step (Abs_TM M) ((TM.step (Abs_TM M) ^^ length w)
              (TM.initial_config (Abs_TM M) w)))) = TM_abbrevs.input_tape w'" unfolding 3 apply simp
          apply (subst f42 [simplified])
             apply (rule 2)
              apply assumption
          using 1 apply simp
          using 1 apply simp
          using 1 apply simp
          unfolding TM_abbrevs.input_tape_def apply (rule exI)
          apply auto
          unfolding rev_drop apply simp
          unfolding map_butlast [symmetric] rev_map take_map ..
        assume a2 [unfolded 3, simplified]: "last (tapes (TM.step (Abs_TM M) ((TM.step (Abs_TM M) ^^ length w)
                                             (TM.initial_config (Abs_TM M) w)))) = TM_abbrevs.input_tape w'"
        have 4: "takeWhile (\<lambda>s. \<exists>y. s = Some y) (right (last
                 (tapes (TM.step (Abs_TM M) ((TM.step (Abs_TM M) ^^ length w)
                 (TM.initial_config (Abs_TM M) w)))))) = right (last
                 (tapes (TM.step (Abs_TM M) ((TM.step (Abs_TM M) ^^ length w)
                 (TM.initial_config (Abs_TM M) w)))))" unfolding 3 [simplified]
          apply (subst (1 2) f42 [simplified])
                apply (rule 2)
                 apply assumption
          using 1 apply simp
          using 1 apply simp
          using 1 apply simp
             apply (rule 2)
              apply assumption
          using 1 apply simp
          using 1 apply simp
          using 1 apply simp
          apply auto
          by (metis in_set_butlastD in_set_dropD ex_map_conv)
        have 5: "length (dropWhile P w) = length w - n'" apply (subst length_dropWhile_eq)
             apply (rule 1 [THEN conjunct1])
            apply (rule 2)
             apply assumption
          using 1 apply simp
          using 1 by simp_all
        show "(case head (TM_abbrevs.input_tape w') of None \<Rightarrow> []
              | Some h \<Rightarrow> h # the (those (takeWhile (\<lambda>s. s \<noteq> None) (right (last (tapes (TM.step (Abs_TM M)
              ((TM.step (Abs_TM M) ^^ length w) (TM.initial_config (Abs_TM M) w))))))))) =
              rev (dropWhile P w)" using a2 apply (subst (asm) f42 [simplified])
             apply (rule 2)
              apply assumption
          using 1 apply simp
          using 1 apply simp
          using 1 apply simp
          unfolding TM_abbrevs.input_tape_def apply auto
          unfolding 4 unfolding 3 [simplified] apply (subst f42 [simplified])
             apply (rule 2)
              apply assumption
          using 1 apply auto
          apply (rule nth_equalityI)
           apply auto
           apply (drule arg_cong [where f=length])
           apply simp
          unfolding 5 apply (metis Suc_diff_Suc Suc_pred length_greater_0_conv)
          apply (subst rev_nth)
          unfolding 5
           apply (metis Nitpick.size_list_simp(2) Suc_diff_Suc diff_diff_left length_butlast length_drop
              length_map length_rev plus_1_eq_Suc)
          apply (subst dropWhile_nth)
          unfolding 5 apply linarith
          apply (subst length_takeWhile_eq)
             apply (rule 1 [THEN conjunct1])
            apply (rule 2)
             apply assumption
          using 1 apply simp
          using 1 apply simp
        proof -
          fix i :: nat
          assume a1: "w' \<noteq> []" and a2: "last w = hd w'" and
                 a3: "rev (drop n' (butlast (map Some w))) = map Some (tl w')" and
                 a4: "i < length w'"
          have 1: "length w - n' - Suc i + n' = length w - Suc i" using 1 [THEN conjunct1]
            by (smt (verit, best) Nat.add_diff_assoc2 Nitpick.size_list_simp(2) Suc_diff_Suc a1 a3 a4
                diff_diff_left le_add_diff_inverse2 length_butlast length_drop length_map length_rev
                less_eq_Suc_le nat_less_le plus_1_eq_Suc)
          have 2: "length w' \<le> length w" using a3 [THEN arg_cong, of length, simplified]
            \<open>n < length w\<close> a1 by linarith
          show "w' ! i = w ! (length w - n' - Suc i + n')" unfolding 1 apply (cases i)
             apply auto
            using a2 apply (subst zeroth_is_head)
              apply (rule a1)
             apply (erule subst [where s="last w"])
            using \<open>n < length w\<close> apply (metis One_nat_def last_conv_nth less_nat_zero_code list.size(3))
          proof -
            fix n2 :: nat
            assume a5: "i = Suc n2"
            show "w' ! Suc n2 = w ! (length w - Suc (Suc n2))"
              using a3 [THEN arg_cong, of "\<lambda>l. l ! n2"]
              apply (subst (asm) nth_map)
              using a4 a5 apply simp
              apply (subst (asm) nth_tl)
              using a4 a5 apply simp
              unfolding rev_drop apply (subst (asm) nth_take)
               apply simp
               apply (metis Nitpick.size_list_simp(2) Suc_less_eq a1 a3 a4 a5 diff_diff_left length_butlast
                  length_drop length_map length_rev plus_1_eq_Suc)
              apply (subst (asm) rev_nth)
               apply simp
              using 2 a4 a5 apply linarith
              apply simp
              apply (subst (asm) nth_butlast)
              apply simp
              using 2 a4 a5 apply linarith
              apply (subst (asm) nth_map)
              using 2 a4 a5 apply linarith
              by simp
          qed
        qed
      qed
    qed
  qed
qed

lemma replicate_input_on_tapes: "finite S \<Longrightarrow> S \<noteq> {} \<Longrightarrow> ns \<subseteq> {1..k-1} \<Longrightarrow> k > 0 \<Longrightarrow>
                                 \<exists>M::(nat, 's, 'l) TM. TM.symbols M = S \<and> TM.tape_count M = k \<and>
                                 (\<forall>w\<in>S*. (\<forall>n\<in>ns. tapes (TM.compute M w) ! n = TM_abbrevs.input_tape w) \<and>
                                 (\<forall>n\<in>{1..k-1}-ns. tapes (TM.compute M w) ! n = Tape [] None []) \<and>
                                 TM.time_bounded_word M (\<lambda>n. 2 * n + 1) w)"
proof -
  assume a1: "finite S" and a2: "S \<noteq> {}" and a3: "ns \<subseteq> {1..k - 1}" and a4: "0 < k"
  define M :: "(nat \<times> 's option, 's, 'l) TM_record" where
    "M \<equiv> TM k S ({0..3} \<times> options S) (0, None) ({3} \<times> options S) (\<lambda>_. undefined)
         (\<lambda>st hds. if fst st = 0 then if hds ! 0 = None then (3, hds ! 0) else (1, hds ! 0) else
                   if fst st = 1 then if hds ! 0 = None then (2, snd st) else (1, hds ! 0) else
                   if hds ! 0 = None then (3, snd st) else (2, snd st))
         (\<lambda>st hds k. if k = 0 then if fst st = 0 then None else hds ! 0 else
                     if k \<in> ns then if fst st \<le> 1 then snd st else hds ! k else None)
         (\<lambda>st hds k. if k = 0 then if fst st \<le> 1 \<and> hds ! 0 \<noteq> None then Shift_Right else Shift_Left else
                     if k \<in> ns then if fst st \<le> 1 then if hds ! 0 = None \<or> fst st = 0 then No_Shift else
                      Shift_Right else if fst st = 2 then if hds ! 0 = None then No_Shift else
                      Shift_Left else No_Shift else No_Shift)"
  have valid_M [simp, intro]: "valid_TM M"
    apply unfold_locales
    unfolding M_def apply auto
         apply fact+
    using a2 apply simp
    using a1 apply simp
    by (metis a4 nth_mem subset_optionsD)+
  have f11: "state (TM.steps (Abs_TM M) l (TM.initial_config (Abs_TM M) w)) = (1, Some (w ! (l - 1)))" and
       f12: "\<And>i. i \<in> ns \<Longrightarrow> i < k \<Longrightarrow> tapes (TM.steps (Abs_TM M) l (TM.initial_config (Abs_TM M) w)) ! i =
             Tape (rev (map Some (take (l - 1) w))) None []" and
       f13: "\<And>i. i \<in> {1..k-1}-ns \<Longrightarrow> i < k \<Longrightarrow>
             tapes (TM.steps (Abs_TM M) l (TM.initial_config (Abs_TM M) w)) ! i = Tape [] None []" and
       f14: "tapes (TM.steps (Abs_TM M) l (TM.initial_config (Abs_TM M) w)) ! 0 =
             Tape (rev (map Some (tl (take l w)))@[None]) (if l < length w then Some (w ! l) else None)
             (map Some (drop (Suc l) w))"
       if "l \<ge> 1" and "l \<le> length w" for l :: nat and w :: "'s list" using that
  proof (induction l rule: nat_induct_at_least)
    case base
    {
      case 1
      then show ?case apply (auto simp add: TM.step_def)
        unfolding valid_tm_next_state [OF valid_M] valid_tm_final_states [OF valid_M]
          TM.initial_config_def valid_tm_initial_state [OF valid_M] valid_tm_tape_count [OF valid_M] apply auto
        unfolding M_def apply auto
        unfolding TM_abbrevs.input_tape_def by (auto simp add: hd_conv_nth)
    next
      case 2
      have 1: "[0..<tape_count M] ! i = i" unfolding M_def using 2 by simp
      show ?case using 2 apply (auto simp add: TM.step_def)
        unfolding valid_tm_next_state [OF valid_M] valid_tm_final_states [OF valid_M]
          TM.initial_config_def valid_tm_initial_state [OF valid_M] valid_tm_tape_count [OF valid_M] apply auto
        unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_writes_def TM.next_moves_def
        valid_tm_next_write [OF valid_M] valid_tm_next_move [OF valid_M] valid_tm_tape_count [OF valid_M]
         apply (unfold M_def)[1]
         apply simp
        apply (subst nth_map2)
          apply auto
          apply (simp add: M_def)
         apply (simp add: M_def)
        apply (subst (1 2) nth_zip)
          apply auto
          apply (simp add: M_def)
         apply (simp add: M_def)
        apply (subst (1 2) nth_map)
         apply (simp add: M_def)
        unfolding 1 unfolding M_def apply auto
        unfolding TM_abbrevs.input_tape_def apply auto
        unfolding TM_abbrevs.tape_write_def apply auto
        using a3 apply fastforce
        unfolding TM_abbrevs.tape_shift.simps ..
    next
      case 3
      have 1: "[0..<TM.TM.tape_count (Abs_TM M)] ! i = i"
        unfolding valid_tm_tape_count [OF valid_M] unfolding M_def using 3 by simp
      show ?case using 3 apply (auto simp add: TM.step_def)
         apply (metis (no_types, lifting) M_def TM.init_conf_len TM.initial_tapes_empty linorder_not_less
            not_less_eq_eq simps(1) valid_M valid_tm_tape_count)
        apply (subst nth_map2)
          apply (metis (lifting) M_def TM.next_actions_simps(2) simps(1) valid_M valid_tm_tape_count)
         apply (metis (lifting) M_def TM.init_conf_len simps(1) valid_M valid_tm_tape_count)
        unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_moves_def TM.next_writes_def
        apply (subst (1 2) nth_zip)
          apply auto
        using M_def valid_tm_tape_count [OF valid_M] apply fastforce
        using M_def valid_tm_tape_count [OF valid_M] apply fastforce
        apply (subst (1 2) nth_map)
         apply auto
        using M_def valid_tm_tape_count [OF valid_M] apply fastforce
        unfolding 1 valid_tm_next_move [OF valid_M] valid_tm_next_write [OF valid_M] TM.initial_config_def
          TM_abbrevs.input_tape_def apply auto
        unfolding valid_tm_tape_count [OF valid_M] valid_tm_initial_state [OF valid_M]
          valid_tm_final_states [OF valid_M] unfolding M_def apply simp
        unfolding TM_abbrevs.tape_write_def TM_abbrevs.tape_shift.simps by simp
    next
      case 4
      then show ?case apply (auto simp add: TM.step_def)
        unfolding TM.initial_config_def TM_abbrevs.input_tape_def apply auto
        unfolding valid_tm_initial_state [OF valid_M] valid_tm_final_states [OF valid_M] apply (simp add: M_def)
            apply (simp add: M_def)
         apply (subst nth_map2)
           apply auto
          apply (metis TM.at_least_one_tape TM.next_actions_simps(2) length_0_conv nat_less_le)
        unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_moves_def TM.next_writes_def
         apply auto
        unfolding valid_tm_next_move [OF valid_M] valid_tm_next_write [OF valid_M]
          valid_tm_tape_count [OF valid_M] unfolding M_def apply auto
        unfolding TM_abbrevs.tape_write_def apply auto
         apply (cases "tl w")
          apply auto
        unfolding TM_abbrevs.tape_shift.simps apply auto
            apply (simp add: Nitpick.size_list_simp(2))
           apply (metis take0 take_tl)
          apply (metis length_greater_0_conv list.distinct(1) nth_Cons_0 nth_tl)
         apply (simp add: drop_Suc)
        apply (cases "tl w")
         apply auto
        unfolding TM_abbrevs.tape_shift.simps apply auto
        by (metis Nitpick.size_list_simp(2) zero_less_Suc length_Cons Suc_mono)
    }
  next
    case (Suc n)
    {
      case 1
      hence *: "n \<le> length w" by simp
      have [simp]: "state ((TM.step (Abs_TM M) ^^ n) (TM.initial_config (Abs_TM M) w)) \<notin>
                    TM.TM.final_states (Abs_TM M)"
        unfolding Suc(2) [OF *] valid_tm_final_states [OF valid_M] unfolding M_def by simp
      show ?case apply simp
        apply (subst TM.step_def)
        apply simp
        unfolding valid_tm_next_state [OF valid_M] Suc(2) [OF *] apply (subst M_def)
        apply auto
         apply (subst nth_map)
          apply (metis TM.at_least_one_tape TM.run_tapes_len)
        unfolding Suc(5) [OF *] using 1 apply simp
        apply (subst (asm) nth_map)
         apply (metis TM.at_least_one_tape TM.run_tapes_len)
        unfolding Suc(5) [OF *] using 1 by simp
    next
      case 2
      hence *: "n \<le> length w" by simp
      have [simp]: "state ((TM.step (Abs_TM M) ^^ n) (TM.initial_config (Abs_TM M) w)) \<notin>
                    TM.TM.final_states (Abs_TM M)"
        unfolding Suc(2) [OF *] valid_tm_final_states [OF valid_M] unfolding M_def by simp
      have [simp]: "i < TM.tape_count (Abs_TM M)"
        unfolding valid_tm_tape_count [OF valid_M] unfolding M_def apply simp
        by fact
      show ?case apply simp
        apply (subst TM.step_def)
        apply simp
        apply (subst nth_map2)
          apply (metis (no_types, lifting) "2.prems"(2) M_def TM.next_actions_simps(2) simps(1) valid_M
            valid_tm_tape_count)
         apply (metis (no_types, lifting) "2.prems"(2) M_def TM.run_tapes_len simps(1) valid_M
            valid_tm_tape_count)
        unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_writes_def TM.next_moves_def apply simp
        unfolding valid_tm_next_move [OF valid_M] valid_tm_next_write [OF valid_M] Suc(2) [OF *]
        apply (subst M_def)
        using 2(1) a3 apply auto
        unfolding TM_abbrevs.tape_shift.simps apply (subst M_def)
         apply auto
        unfolding TM_abbrevs.tape_write_def apply auto
         apply (subst (asm) nth_map)
          apply (simp add: TM.run_tapes_len)
        unfolding Suc(5) [OF *] using 2 apply auto
        unfolding Suc(3) [OF _ _ *] apply auto
        apply (subst M_def)
        apply simp
        unfolding TM_abbrevs.tape_shift.simps apply simp
        by (metis * One_nat_def Suc.hyps Suc_pred less_eq_Suc_le list.simps(9) list_take_rev_Cons rev_map)
    next
      case 3
      hence *: "n \<le> length w" by simp
      have [simp]: "state ((TM.step (Abs_TM M) ^^ n) (TM.initial_config (Abs_TM M) w)) \<notin>
                    TM.TM.final_states (Abs_TM M)"
        unfolding Suc(2) [OF *] valid_tm_final_states [OF valid_M] unfolding M_def by simp
      have [simp]: "i < TM.tape_count (Abs_TM M)"
        unfolding valid_tm_tape_count [OF valid_M] unfolding M_def apply simp
        by fact
      show ?case apply simp
        apply (subst TM.step_def)
        apply simp
        apply (subst nth_map2)
          apply (simp add: TM.next_actions_simps(2))
         apply (simp add: TM.run_tapes_len)
        unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_writes_def TM.next_moves_def apply simp
        unfolding Suc(2) [OF *] valid_tm_next_move [OF valid_M] valid_tm_next_write [OF valid_M]
        apply (subst M_def)
        using 3 apply auto
        unfolding TM_abbrevs.tape_shift.simps apply (subst M_def)
        apply simp
        unfolding TM_abbrevs.tape_write_def apply auto
        using Suc(4) [OF _ _ *] by auto
    next
      case 4
      hence *: "n \<le> length w" by simp
      have [simp]: "state ((TM.step (Abs_TM M) ^^ n) (TM.initial_config (Abs_TM M) w)) \<notin>
                    TM.TM.final_states (Abs_TM M)"
        unfolding Suc(2) [OF *] valid_tm_final_states [OF valid_M] unfolding M_def by simp
      show ?case apply auto
         apply (subst TM.step_def)
         apply simp
         apply (subst nth_map2)
           apply (simp add: TM.next_actions_simps(2))
          apply (simp add: TM.run_tapes_len)
        unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_moves_def TM.next_writes_def
         apply simp
        unfolding Suc(2) [OF *] valid_tm_next_move [OF valid_M] valid_tm_next_write [OF valid_M]
         apply (subst M_def)
         apply auto
          apply (subst M_def)
          apply simp
          apply (subst (asm) nth_map)
           apply (simp add: TM.run_tapes_len)
        unfolding Suc(5) [OF *] apply auto
        unfolding TM_abbrevs.tape_write_def apply auto
          apply (cases "map Some (drop (Suc n) w)")
           apply auto
        unfolding TM_abbrevs.tape_shift.simps apply auto
            apply (rule nth_equalityI)
             apply auto
        using Suc.hyps Suc_pred less_eq_Suc_le apply presburger
            apply (subst nth_Cons')
            apply auto
             apply (subst rev_nth)
        using Suc.hyps apply simp
             apply (subst nth_map)
              apply auto
        using Suc.hyps apply linarith
             apply (metis (no_types, lifting) One_nat_def Suc.hyps Suc_pred diff_Suc_1' length_take length_tl lessI
            less_eq_Suc_le min.absorb4 nth_take nth_tl)
            apply (subst (1 2) rev_nth)
              apply auto
            apply (subst (1 2) nth_tl)
              apply auto
           apply (metis nth_via_drop)
          apply (metis drop_Suc list.sel(3) tl_drop)
         apply (subst (asm) nth_map)
          apply (simp add: TM.run_tapes_len)
        unfolding Suc(5) [OF *] apply simp
        apply (subst TM.step_def)
        apply simp
        apply (subst nth_map2)
          apply (simp add: TM.next_actions_simps(2))
         apply (simp add: TM.run_tapes_len)
        unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_writes_def TM.next_moves_def apply simp
        unfolding Suc(2) [OF *] valid_tm_next_move [OF valid_M] valid_tm_next_write [OF valid_M]
        apply (subst M_def)
        apply auto
         apply (subst M_def)
         apply simp
        apply (subst (asm) nth_map)
          apply (simp add: TM.run_tapes_len)
        unfolding Suc(5) [OF *] using 4 apply auto
        unfolding TM_abbrevs.tape_write_def apply auto
        unfolding TM_abbrevs.tape_shift.simps apply auto
         apply (rule nth_equalityI)
          apply auto
          apply (metis One_nat_def Suc_pred bot_nat_0.not_eq_extremum Suc.hyps nat.distinct(1) le_zero_eq
            old.nat.inject)
         apply (subst nth_Cons')
         apply auto
          apply (subst rev_nth)
           apply auto
        using Suc.hyps apply force
          apply (metis One_nat_def Suc.hyps Suc_diff_1 Suc_diff_le diff_Suc_Suc length_tl lessI
            less_eq_Suc_le nth_map nth_tl)
         apply (subst (1 2) rev_nth)
           apply auto
         apply (subst (1 2) nth_tl)
           apply auto
         apply (metis diff_Suc_Suc)
        apply (subst (asm) nth_map)
         apply (simp add: TM.run_tapes_len)
        unfolding Suc(5) [OF *] by simp
    }
  qed
  have f1': "TM.step (Abs_TM M) (TM.initial_config (Abs_TM M) []) =
             TM_config (3, None) ((Tape [] None [None])#(replicate (TM.tape_count (Abs_TM M) - 1)
             (Tape [] None [])))"
    unfolding TM.step_def TM.initial_config_def valid_tm_initial_state [OF valid_M]
      valid_tm_final_states [OF valid_M] valid_tm_tape_count [OF valid_M] apply auto
      apply (simp add: M_def)
     apply (simp add: M_def)
    unfolding TM.step_not_final_def Let_def apply auto
    unfolding valid_tm_next_state [OF valid_M] TM_abbrevs.input_tape_def apply auto
     apply (simp add: M_def)
    unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_writes_def TM.next_moves_def
    apply (rule nth_equalityI)
    apply (auto simp add: valid_tm_tape_count)
     apply (simp add: M_def)
    using a4 apply simp
    unfolding valid_tm_next_move [OF valid_M] valid_tm_next_write [OF valid_M] unfolding M_def apply auto
    unfolding TM_abbrevs.tape_write_def apply auto
    unfolding TM_abbrevs.tape_shift.simps by standard+
  have f21: "state (TM.steps (Abs_TM M) l (TM.initial_config (Abs_TM M) w)) = (2, Some (last w))" and
       f22: "\<And>i. i \<in> ns \<Longrightarrow> i < k \<Longrightarrow> tapes (TM.steps (Abs_TM M) l (TM.initial_config (Abs_TM M) w)) ! i =
             Tape (rev (map Some (take (2 * length w - l) w))) (Some (w ! (2 * length w - l)))
             (map Some (drop (Suc (2 * length w - l)) w))" and
       f23: "\<And>i. i \<in> {1..k-1}-ns \<Longrightarrow> i < k \<Longrightarrow>
             tapes (TM.steps (Abs_TM M) l (TM.initial_config (Abs_TM M) w)) ! i = Tape [] None []" and
       f24: "\<exists>r. tapes (TM.steps (Abs_TM M) l (TM.initial_config (Abs_TM M) w)) ! 0 =
             Tape (rev (take (2 * length w - l) (None#(map Some (tl w)))))
             (if l = 2 * length w then None else Some (w ! (2 * length w - l))) r"
       if "l \<ge> Suc (length w)" and "l \<le> 2 * length w" for l :: nat and w :: "'s list" using that
  proof (induction l rule: nat_induct_at_least)
    case base
    {
      case 1
      hence *: "1 \<le> length w" by simp
      have [simp]: "state ((TM.step (Abs_TM M) ^^ length w) (TM.initial_config (Abs_TM M) w)) \<notin>
                    TM.TM.final_states (Abs_TM M)"
        unfolding f11 [OF * Nat.le_refl] valid_tm_final_states [OF valid_M] by (simp add: M_def)
      show ?case apply simp
        apply (subst TM.step_def)
        apply simp
        unfolding valid_tm_next_state [OF valid_M] f11 [OF * Nat.le_refl] apply (subst M_def)
        apply simp
        apply (subst (1 2) nth_map)
         apply auto
          apply (metis TM.run_tapes_len TM.at_least_one_tape length_greater_0_conv)
        unfolding f14 [OF * Nat.le_refl] apply auto
        using * by (simp add: last_conv_nth)
    next
      case 2
      hence *: "1 \<le> length w" by simp
      have [simp]: "state ((TM.step (Abs_TM M) ^^ length w) (TM.initial_config (Abs_TM M) w)) \<notin>
                    TM.TM.final_states (Abs_TM M)"
        unfolding f11 [OF * Nat.le_refl] valid_tm_final_states [OF valid_M] by (simp add: M_def)
      have [simp]: "i < TM.tape_count (Abs_TM M)"
        unfolding valid_tm_tape_count [OF valid_M] unfolding M_def using 2(2) by simp
      show ?case apply simp
        apply (subst TM.step_def)
        apply simp
        unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_moves_def TM.next_writes_def
        apply (subst nth_map2)
          apply auto
         apply (simp add: TM.run_tapes_len)
        unfolding valid_tm_next_move [OF valid_M] valid_tm_next_write [OF valid_M] f11 [OF * Nat.le_refl]
        apply (subst M_def)
        using 2 a3 apply auto
        unfolding TM_abbrevs.tape_shift.simps apply (subst M_def)
         apply simp
        unfolding TM_abbrevs.tape_write_def apply auto
        unfolding f12 [OF * Nat.le_refl] apply simp_all
        apply (subst M_def)
        apply simp
        unfolding TM_abbrevs.tape_shift.simps apply auto
        apply (subst (asm) nth_map)
         apply (metis TM.at_least_one_tape TM.run_tapes_len)
        unfolding f14 [OF * Nat.le_refl] by simp
    next
      case 3
      hence *: "1 \<le> length w" by simp
      have [simp]: "state ((TM.step (Abs_TM M) ^^ length w) (TM.initial_config (Abs_TM M) w)) \<notin>
                    TM.TM.final_states (Abs_TM M)"
        unfolding f11 [OF * Nat.le_refl] valid_tm_final_states [OF valid_M] by (simp add: M_def)
      have [simp]: "i < TM.tape_count (Abs_TM M)"
        unfolding valid_tm_tape_count [OF valid_M] unfolding M_def using 3(2) by simp
      show ?case apply simp
        apply (subst TM.step_def)
        apply simp
        apply (subst nth_map2)
          apply (simp add: TM.next_actions_simps(2))
         apply (simp add: TM.run_tapes_len)
        unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_writes_def TM.next_moves_def apply simp
        unfolding f11 [OF * Nat.le_refl] valid_tm_next_move [OF valid_M] valid_tm_next_write [OF valid_M]
        apply (subst M_def)
        using 3 a3 apply auto
        unfolding TM_abbrevs.tape_shift.simps TM_abbrevs.tape_write_def apply auto
        using f13 [OF * Nat.le_refl, of i] apply auto
        apply (subst M_def)
        by simp
    next
      case 4
      hence *: "1 \<le> length w" by simp
      have [simp]: "state ((TM.step (Abs_TM M) ^^ length w) (TM.initial_config (Abs_TM M) w)) \<notin>
                    TM.TM.final_states (Abs_TM M)"
        unfolding f11 [OF * Nat.le_refl] valid_tm_final_states [OF valid_M] by (simp add: M_def)
      show ?case apply auto
         apply (drule sym)
         apply (subst TM.step_def)
         apply auto
          apply (subst f14 [OF Nat.le_refl, of w, simplified])
           apply auto
          apply (subst (asm) f11 [OF Nat.le_refl, of w, simplified])
           apply auto
        unfolding valid_tm_final_states [OF valid_M] apply (subst (asm) M_def)
          apply simp
         apply (subst nth_map2)
           apply (metis TM.at_least_one_tape TM.next_actions_simps(2))
          apply (simp add: TM.init_conf_len TM.step_l_tps)
        unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_moves_def TM.next_writes_def
         apply simp
        unfolding valid_tm_next_move [OF valid_M] valid_tm_next_write [OF valid_M]
         apply (subst (1 2) f11 [OF Nat.le_refl, of w, simplified])
          apply auto
         apply (subst M_def)
         apply auto
          apply (subst (asm) nth_map)
           apply (simp add: TM.init_conf_len TM.step_l_tps)
          apply (subst (asm) f14 [OF Nat.le_refl, of w, simplified])
           apply auto
         apply (subst M_def)
         apply simp
        unfolding TM_abbrevs.tape_write_def apply (subst (1 2) f14 [OF Nat.le_refl, of w, simplified])
          apply auto
         apply (cases "rev (map Some (tl w)) @ [None]")
          apply auto
        unfolding TM_abbrevs.tape_shift.simps apply auto
          apply (metis Nil_is_rev_conv Nil_tl length_1_ex_iff list.inject list.map_disc_iff self_append_conv2)
         apply (metis One_nat_def diff_Suc_1' length_map length_rev length_tl nth_Cons_0 nth_append_length)
        apply (subst TM.step_def)
        apply simp
         apply (subst nth_map2)
          apply (simp add: TM.next_actions_simps(2))
         apply (simp add: TM.run_tapes_len)
        unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_writes_def TM.next_moves_def apply simp
        unfolding valid_tm_next_move [OF valid_M] valid_tm_next_write [OF valid_M] f11 [OF * Nat.le_refl]
        apply (subst M_def)
        apply auto
         apply (subst (asm) nth_map)
          apply (simp add: TM.run_tapes_len)
        unfolding f14 [OF * Nat.le_refl] apply simp
        apply (subst M_def)
        apply simp
        unfolding TM_abbrevs.tape_write_def apply auto
        apply (cases "rev (map Some (tl w)) @ [None]")
         apply auto
        unfolding TM_abbrevs.tape_shift.simps apply auto
         apply (rule nth_equalityI)
          apply auto
          apply (metis One_nat_def length_Cons length_map length_rev length_tl old.nat.inject rev.simps(2))
         apply (subst rev_nth)
          apply auto
          apply (metis One_nat_def length_map length_rev length_tl list.sel(3) rev.simps(2))
         apply (smt (verit, best) Suc_diff_le diff_Suc_1' diff_Suc_eq_diff_pred diff_less length_Suc0_not_empty
            length_append_singleton length_map length_rev length_tl list.sel(3) list.size(3)
            not_less_eq nth_take nth_tl rev.simps(2) rev_nth zero_less_Suc)
        using *
        by (metis (no_types, lifting) Nil_is_rev_conv One_nat_def last_conv_nth last_map
            length_greater_0_conv length_tl less_eq_Suc_le list.collapse list.map_disc_iff nat_less_le
            nth_Cons' rev_nth zero_less_diff zeroth_app_non_empty)
    }
  next
    case (Suc n)
    {
      case 1
      hence *: "n \<le> 2 * length w" by simp
      have [simp]: "state ((TM.step (Abs_TM M) ^^ n) (TM.initial_config (Abs_TM M) w)) \<notin>
                    TM.TM.final_states (Abs_TM M)"
        unfolding Suc(2) [OF *] valid_tm_final_states [OF valid_M] unfolding M_def by simp
      show ?case apply simp
        apply (subst TM.step_def)
        apply simp
        unfolding valid_tm_next_state [OF valid_M] Suc(2) [OF *] apply (subst M_def)
        apply simp
        apply (subst nth_map)
         apply (simp add: TM.run_tapes_len)
        using Suc(5) [OF *] apply auto
        using 1 Suc(1) by linarith
    next
      case 2
      hence *: "n \<le> 2 * length w" by simp
      have [simp]: "state ((TM.step (Abs_TM M) ^^ n) (TM.initial_config (Abs_TM M) w)) \<notin>
                    TM.TM.final_states (Abs_TM M)"
        unfolding Suc(2) [OF *] valid_tm_final_states [OF valid_M] unfolding M_def by simp
      have [simp]: "i < TM.tape_count (Abs_TM M)"
        unfolding valid_tm_tape_count [OF valid_M] unfolding M_def apply simp
        by fact
      have 1 [simp]: "min (length w) (2 * length w - n) = 2 * length w - n"
        using Suc(1) by fastforce
      show ?case apply simp
        apply (subst TM.step_def)
        apply simp
        unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_writes_def TM.next_moves_def
        apply (subst nth_map2)
        apply auto
         apply (simp add: TM.run_tapes_len)
        unfolding valid_tm_next_move [OF valid_M] valid_tm_next_write [OF valid_M] Suc(2) [OF *]
        apply (subst M_def)
        using 2 a3 apply auto
         apply (subst (asm) nth_map)
          apply (metis TM.run_tapes_len TM.at_least_one_tape)
        using Suc(5) [OF *] apply auto
        apply (subst M_def)
        apply (auto simp add: TM_abbrevs.tape_shift.simps TM_abbrevs.tape_write_def)
        unfolding Suc(3) [OF _ _ *] apply auto
        apply (cases "length w = Suc 0")
         apply auto
        using Suc.hyps apply linarith
        apply (rule tape.expand)
        apply auto
          apply (rule nth_equalityI)
           apply simp_all
        using 1 min_def not_less_eq_eq apply linarith
          apply (subst nth_tl)
           apply simp_all
          apply (subst (1 2) rev_nth)
            apply simp_all
        using 1 apply linarith
          apply (subst nth_map)
           apply simp
           apply fastforce
          apply (subst nth_take)
           apply simp_all
          apply (metis 1 Suc_diff_Suc add_Suc_right diff_Suc_eq_diff_pred diff_diff_left less_eq_Suc_le
            min.absorb4 min.cobounded1)
         apply (subst Shift_Left_is_left_not_empty)
          apply simp_all
          apply fastforce
        unfolding hd_rev apply (subst last_map)
          apply fastforce
         apply (smt (verit, best) 1 One_nat_def Suc_diff_Suc diff_Suc_1' diff_is_0_eq last_conv_nth
            length_take lessI less_eq_Suc_le list.size(3) not_less_eq_eq nth_take)
        apply (rule nth_equalityI)
         apply auto
        using Suc.hyps Suc_diff_Suc less_eq_Suc_le apply presburger
        apply (subst nth_Cons')
        apply simp
        apply (rule impI)
        apply (subst nth_map)
        apply simp
         apply (metis TM.run_tapes_len \<open>i < TM.TM.tape_count (Abs_TM M)\<close>)
        unfolding Suc(3) [OF _ _ *] apply simp
        apply (subst nth_map)
         apply (metis * 1 One_nat_def Suc.hyps Suc_diff_Suc Suc_n_not_le_n add_diff_cancel_left' diff_diff_cancel
            drop_eq_Nil length_greater_0_conv less_eq_Suc_le min_def mult_Suc nat_mult_1 numeral_2_eq_2)
        apply (subst nth_drop)
         apply simp_all
         apply (metis 1 Suc_diff_Suc less_eq_Suc_le min.cobounded1)
        using Suc_diff_Suc less_eq_Suc_le by presburger
    next
      case 3
      hence *: "n \<le> 2 * length w" by simp
      have [simp]: "state ((TM.step (Abs_TM M) ^^ n) (TM.initial_config (Abs_TM M) w)) \<notin>
                    TM.TM.final_states (Abs_TM M)"
        unfolding Suc(2) [OF *] valid_tm_final_states [OF valid_M] unfolding M_def by simp
      have [simp]: "i < TM.tape_count (Abs_TM M)"
        unfolding valid_tm_tape_count [OF valid_M] unfolding M_def apply simp
        by fact
      show ?case apply simp
        apply (subst TM.step_def)
        apply simp
        apply (subst nth_map2)
          apply (simp add: TM.next_actions_simps(2))
         apply (simp add: TM.run_tapes_len)
        unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_moves_def TM.next_writes_def
        apply simp
        unfolding Suc(2) [OF *] valid_tm_next_move [OF valid_M] valid_tm_next_write [OF valid_M]
        apply (subst M_def)
        using 3 a3 apply auto
        unfolding TM_abbrevs.tape_shift.simps apply (subst M_def)
        apply simp
        unfolding TM_abbrevs.tape_write_def using Suc(4) [OF _ _ *, of i] by force
    next
      case 4
      hence *: "n \<le> 2 * length w" by simp
      have [simp]: "state ((TM.step (Abs_TM M) ^^ n) (TM.initial_config (Abs_TM M) w)) \<notin>
                    TM.TM.final_states (Abs_TM M)"
        unfolding Suc(2) [OF *] valid_tm_final_states [OF valid_M] unfolding M_def by simp
      have 1 [simp]: "min (Suc (length w - Suc 0)) (2 * length w - Suc n) = 2 * length w - Suc n"
        using Suc.hyps by linarith
      show ?case apply auto
         apply (subst TM.step_def)
         apply simp
         apply (subst nth_map2)
           apply (simp add: TM.next_actions_simps(2))
          apply (simp add: TM.run_tapes_len)
        unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_writes_def TM.next_moves_def apply simp
        unfolding Suc(2) [OF *] valid_tm_next_move [OF valid_M] valid_tm_next_write [OF valid_M]
         apply (subst M_def)
         apply simp
         apply (subst M_def)
         apply simp
        unfolding TM_abbrevs.tape_write_def using Suc(5) [OF *] apply auto[1]
         apply (cases "rev (take (2 * length w - n) (None # map Some (tl w)))")
          apply auto
        unfolding TM_abbrevs.tape_shift.simps apply auto
          apply (metis One_nat_def add_diff_cancel_right' len_tl_Cons length_Cons length_rev list.size(3)
            nat.distinct(1) old.nat.inject plus_1_eq_Suc rev.simps(2) take_eq_Nil take_tl)
        apply (metis One_nat_def add_diff_cancel_right' list.inject plus_1_eq_Suc rev.simps(2)
            rev_singleton_conv take0 take_Suc_Cons)
        apply (subst TM.step_def)
        apply simp
        apply (subst nth_map2)
          apply (simp add: TM.next_actions_simps(2))
         apply (simp add: TM.run_tapes_len)
        unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_moves_def TM.next_writes_def
        apply simp
        unfolding Suc(2) [OF *] valid_tm_next_move [OF valid_M] valid_tm_next_write [OF valid_M]
        apply (subst M_def)
        apply simp
        apply (subst M_def)
        apply simp
        unfolding TM_abbrevs.tape_write_def using Suc(5) [OF *] apply auto
        apply (cases "rev (take (2 * length w - n) (None # map Some (tl w)))")
         apply auto
        unfolding TM_abbrevs.tape_shift.simps apply auto
        using 4 not_less_eq_eq apply blast
         apply (rule nth_equalityI)
          apply auto
          apply (smt (verit) 1 4 Nitpick.size_list_simp(2) One_nat_def Suc.hyps Suc_diff_Suc add_diff_cancel_left'
            diff_diff_cancel length_Cons length_append_singleton length_map length_rev length_take less_Suc_eq_le
            linorder_not_less min.absorb4 mult_Suc nat_less_le nat_mult_1 not_add_less2 numeral_2_eq_2
            plus_1_eq_Suc take_all_iff)
         apply (subst rev_nth)
          apply simp
          apply (smt (verit, best) 1 4 One_nat_def Suc_diff_Suc le_Suc_eq length_Cons length_append_singleton
            length_map length_rev length_take length_tl less_eq_Suc_le linorder_not_less min.absorb4
            take_all_iff)
         apply (subst nth_take)
          apply simp
        apply (smt (verit) 4 Nitpick.size_list_simp(2) One_nat_def Suc.hyps Suc_diff_Suc Suc_less_eq
            bot_nat_0.extremum_unique diff_Suc_1' diff_is_0_eq diff_less_mono2 diff_self_eq_0 le_trans
            length_Cons length_map length_rev length_take length_tl less_add_Suc1 less_eq_Suc_le
            linorder_not_less list.size(3) min.absorb4 mult_0_right nat.distinct(1) nat_less_le not_less_zero
            numeral_2_eq_2 plus_1_eq_Suc rev_eq_Cons_iff)
         apply simp
         apply (subst nth_Cons')
        using 4 apply auto
      proof -
        fix r t :: "'s option list" and a :: "'s option" and i :: nat
        assume a1: "Suc n \<noteq> 2 * length w" and
               a2: "tapes ((TM.step (Abs_TM M) ^^ n) (TM.initial_config (Abs_TM M) w)) ! 0 =
                    Tape (a # t) (Some (w ! (2 * length w - n))) r" and
               a3: "take (2 * length w - n) (None # map Some (tl w)) = rev t @ [a]" and
               a4: "i < length t"
        have [simp]: "min (Suc (length w - Suc 0)) (2 * length w - n) = 2 * length w - n"
          using Suc.hyps by linarith
        note a3 [THEN arg_cong, of length, simplified]
        hence 2: "i \<le> 2 * length w - n" using a4 by simp
        show "2 * length w \<le> Suc (Suc (n + i)) \<Longrightarrow> t ! i = None" using 2 a3
          by (smt (verit, best) Nil_is_rev_conv Suc_diff_Suc \<open>2 * length w - n = Suc (length t)\<close> a4
              add_diff_cancel_left' diff_diff_left diff_is_0_eq le_Suc_eq length_0_conv linorder_not_less
              list_take_rev_Cons nth_Cons_0 plus_1_eq_Suc take_Cons' take_eq zeroth_app_non_empty)
      next
        fix r t :: "'s option list" and a :: "'s option" and i :: nat
        assume a1: "tapes ((TM.step (Abs_TM M) ^^ n) (TM.initial_config (Abs_TM M) w)) ! 0 =
                    Tape (a # t) (Some (w ! (2 * length w - n))) r" and
               a2: "take (2 * length w - n) (None # map Some (tl w)) = rev t @ [a]" and
               a3: "i < length t" and
               a4: "\<not> 2 * length w \<le> Suc (Suc (n + i))"
        have [simp]: "min (Suc (length w - Suc 0)) (2 * length w - n) = 2 * length w - n"
          using Suc.hyps by linarith
        note a2 [THEN arg_cong, of length, simplified]
        hence 2: "i \<le> 2 * length w - n" using a4 by simp
        note 3 = a2 [THEN arg_cong, of "\<lambda>l. l ! (length t - i - 1)", simplified]
        have 5: "t \<noteq> []" using a3 by force
        have 6: "length t - Suc (length t - Suc i) = i" using a3 by simp
        have 7: "length t - Suc (Suc i) \<le> 2 * length w - Suc (Suc (Suc (n + i)))"
          using \<open>2 * length w - n = Suc (length t)\<close> by linarith
        have 8: "length t - Suc (Suc i) \<ge> 2 * length w - Suc (Suc (Suc (n + i)))"
          using \<open>2 * length w - n = Suc (length t)\<close> by linarith
        have 9: "length t - Suc (Suc i) = 2 * length w - Suc (Suc (Suc (n + i)))"
          using 7 8 by simp
        show "t ! i = map Some (tl w) ! (2 * length w - Suc (Suc (Suc (n + i))))" using 3
          apply (subst (asm) nth_take)
          using \<open>2 * length w - n = Suc (length t)\<close> diff_less_Suc apply presburger
          unfolding nth_append using 5 apply auto
          apply (subst (asm) rev_nth)
           apply auto
          unfolding 6 nth_Cons' apply (cases "length t - Suc i = 0")
           apply auto
          using \<open>2 * length w - n = Suc (length t)\<close> a4 apply linarith
          unfolding 9 by simp
      next
        fix r t :: "'s option list" and a :: "'s option"
        assume a1: "Suc n \<noteq> 2 * length w" and
               a2: "tapes ((TM.step (Abs_TM M) ^^ n) (TM.initial_config (Abs_TM M) w)) ! 0 =
                    Tape (a # t) (Some (w ! (2 * length w - n))) r" and
               a3: "take (2 * length w - n) (None # map Some (tl w)) = rev t @ [a]"
        have 2: "w \<noteq> []" using 4 by force
        have 3: "\<not> 2 * length w - Suc n < length t \<Longrightarrow> \<not> 2 * length w \<le> Suc (n + length t) \<Longrightarrow>
                 2 * length w - Suc n > length t" by linarith
        show "a = Some (w ! (2 * length w - Suc n))"
          using a3 [THEN arg_cong, of "\<lambda>l. l ! (2 * length w - Suc n)"] apply (subst (asm) nth_take)
           apply (simp add: 4 Suc_diff_Suc less_eq_Suc_le)
          unfolding nth_append apply (cases "2 * length w - Suc n < length (rev t)")
           apply auto
           apply (metis 4 Suc_diff_Suc a3 length_append_singleton length_rev length_take lessI
              linorder_not_less min.absorb4 not_less_eq_eq take_all_iff)
          unfolding nth_Cons' apply (cases "2 * length w - Suc n = 0")
           apply auto
          using 4 a1 le_antisym apply blast
          apply (cases "2 * length w \<le> Suc (n + length t)")
           apply auto
           apply (subst (asm) nth_map)
            apply auto
          using Suc(1) apply auto
           apply (subst nth_tl)
            apply auto
           apply (simp add: Suc_diff_Suc)
          apply (drule (1) 3)
          using a3 [THEN arg_cong, where f=length, simplified] by linarith
      qed
    }
  qed
  have f31: "state (TM.steps (Abs_TM M) (Suc (2 * length w))
             (TM.initial_config (Abs_TM M) w)) = (3, Some (last w))" and
       f32: "\<And>i. i \<in> ns \<Longrightarrow> i < k \<Longrightarrow> tapes (TM.steps (Abs_TM M) (Suc (2 * length w))
             (TM.initial_config (Abs_TM M) w)) ! i = Tape [] (Some (hd w)) (map Some (tl w))" and
       f33: "\<And>i. i \<in> {1..k-1}-ns \<Longrightarrow> i < k \<Longrightarrow>
             tapes (TM.steps (Abs_TM M) (Suc (2 * length w))
             (TM.initial_config (Abs_TM M) w)) ! i = Tape [] None []" if "w \<noteq> []" for w :: "'s list"
  proof -
    have [simp]: "state ((TM.step (Abs_TM M) ^^ (2 * length w)) (TM.initial_config (Abs_TM M) w))
                  \<notin> TM.TM.final_states (Abs_TM M)"
      using f21 [OF _ Nat.le_refl, of w] that apply simp
      unfolding valid_tm_final_states [OF valid_M] by (simp add: M_def)
    show "state ((TM.step (Abs_TM M) ^^ Suc (2 * length w)) (TM.initial_config (Abs_TM M) w)) =
          (3, Some (last w))"
      apply simp
      apply (subst TM.step_def)
      apply simp
      unfolding valid_tm_next_state [OF valid_M] using f21 [OF _ Nat.le_refl, of w] that apply simp
      apply (subst M_def)
      apply simp
      apply (subst nth_map)
       apply auto
       apply (metis TM.at_least_one_tape TM.run_tapes_len less_not_refl list.size(3))
      using f24 [OF _ Nat.le_refl, of w] that by auto
    have [simp]: "TM.tape_count (Abs_TM M) = k"
      unfolding valid_tm_tape_count [OF valid_M] unfolding M_def by simp
    have [simp]: "length (tapes ((TM.step (Abs_TM M) ^^ (2 * length w)) (TM.initial_config (Abs_TM M) w))) =
                  k" by (simp add: TM.run_tapes_len)
    show "tapes ((TM.step (Abs_TM M) ^^ Suc (2 * length w)) (TM.initial_config (Abs_TM M) w)) ! i =
          Tape [] (Some (hd w)) (map Some (tl w))" if "i \<in> ns" and "i < k" for i :: nat
      apply simp
      apply (subst TM.step_def)
      apply simp
      apply (subst nth_map2)
      unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_writes_def TM.next_moves_def apply auto
      unfolding valid_tm_tape_count [OF valid_M] apply (simp add: that)
       apply fact+
      using that apply simp
      unfolding valid_tm_next_write [OF valid_M] valid_tm_next_move [OF valid_M]
      apply (subst (1 2) f21 [OF _ Nat.le_refl])
      using \<open>w \<noteq> []\<close> apply auto
      apply (subst M_def)
      using a3 apply auto
      unfolding TM_abbrevs.tape_shift.simps apply (subst M_def)
       apply simp
      unfolding TM_abbrevs.tape_write_def apply auto
       apply (subst f22 [OF _ Nat.le_refl])
          apply auto
        apply (erule zeroth_is_head)
       apply (metis drop0 drop_Suc)
      using f24 [OF _ Nat.le_refl, of w] by auto
    show "tapes ((TM.step (Abs_TM M) ^^ Suc (2 * length w)) (TM.initial_config (Abs_TM M) w)) ! i =
          Tape [] None []" if "i \<in> {1..k - 1} - ns" and "i < k" for i :: nat
      apply simp
      apply (subst TM.step_def)
      apply simp
      apply (subst nth_map2)
        apply auto
        apply (simp add: TM.next_actions_simps(2) that(2))
       apply fact
      unfolding TM_abbrevs.tape_action_def TM.next_actions_def TM.next_writes_def TM.next_moves_def
      using that apply auto
      unfolding valid_tm_next_move [OF valid_M] valid_tm_next_write [OF valid_M]
      using f21 [OF _ Nat.le_refl, of w] \<open>w \<noteq> []\<close> apply simp
      apply (subst M_def)
      apply simp
      unfolding TM_abbrevs.tape_shift.simps apply (subst M_def)
      apply simp
      unfolding TM_abbrevs.tape_write_def using f23 [OF _ Nat.le_refl, of w i] by simp
  qed
  obtain f :: "nat \<times> 's option \<Rightarrow> nat" where f_inj: "inj_on f (TM.states (Abs_TM M))"
    by (metis bij_betw_def TM.state_axioms(1) ex_bij_betw_finite_nat)
  define M' :: "(nat, 's, 'l) TM_record" where
    "M' \<equiv> map_states_tmrec f (Abs_TM M)"
  have valid_M' [simp, intro]: "valid_TM M'"
    unfolding M'_def apply (rule map_states_tmrec_valid)
    by fact
  show "\<exists>M::(nat, 's, 'l) TM. TM.symbols M = S \<and> TM.tape_count M = k \<and>
        (\<forall>w\<in>S*. (\<forall>n\<in>ns. tapes (TM.compute M w) ! n = TM_abbrevs.input_tape w) \<and>
        (\<forall>n\<in>{1..k-1}-ns. tapes (TM.compute M w) ! n = Tape [] None []) \<and>
        TM.time_bounded_word M (\<lambda>n. 2 * n + 1) w)"
  proof (rule exI [where x="Abs_TM M'"], auto)
    have syms: "TM.TM.symbols (Abs_TM M') = S"
      unfolding valid_tm_symbols [OF valid_M'] unfolding M'_def map_states_tmrec_def [OF f_inj] apply simp
      unfolding valid_tm_symbols [OF valid_M] unfolding M_def by simp
    show "\<And>s. s \<in> TM.TM.symbols (Abs_TM M') \<Longrightarrow> s \<in> S" unfolding syms .
    show "\<And>s. s \<in> S \<Longrightarrow> s \<in> TM.TM.symbols (Abs_TM M')" unfolding syms .
    show "TM.TM.tape_count (Abs_TM M') = k" unfolding valid_tm_tape_count [OF valid_M']
      unfolding M'_def map_states_tmrec_def [OF f_inj] apply simp
      unfolding valid_tm_tape_count [OF valid_M] unfolding M_def by simp
    show tb: "TM.time_bounded_word (Abs_TM M') (\<lambda>n. Suc (2 * n)) w"
      if "set w \<subseteq> S" for w :: "'s list" and n :: nat
      unfolding TM.time_bounded_word_def TM.is_final_def M'_def apply (subst map_states_tmrec_run(1))
        apply fact
      unfolding valid_tm_symbols [OF valid_M] using that apply (simp add: M_def)
      unfolding valid_tm_final_states [OF valid_M' [unfolded M'_def]]
      unfolding map_states_tmrec_def [OF f_inj] apply simp
      unfolding TM.run_def apply (cases "w = []")
       apply auto
      using f1' apply simp
      unfolding valid_tm_final_states [OF valid_M] apply (subst M_def)
       apply auto
      unfolding f31 [simplified] unfolding M_def using that by force
    have 1: "(LEAST n. TM.is_final (Abs_TM M) ((TM.step (Abs_TM M) ^^ n) (TM.initial_config (Abs_TM M) w))) =
             2 * length w + 1" if "set w \<subseteq> S" for w :: "'s list"
      apply (rule Least_nat_monoI)
        apply auto
      unfolding TM.is_final_def apply (cases "w = []")
        apply auto
      unfolding f1' apply simp
      unfolding valid_tm_final_states [OF valid_M] apply (simp add: M_def)
        apply blast
      unfolding f31 [simplified] apply (simp add: M_def)
      using that apply fastforce
      apply (cases "w = []")
       apply simp
       apply (subst (asm) TM.initial_config_def)
       apply simp
      unfolding valid_tm_initial_state [OF valid_M] apply (simp add: M_def)
      using f21 [OF _ Nat.le_refl, of w] that by (simp add: M_def)
    show "tapes (TM.compute (Abs_TM M') w) ! n = TM_abbrevs.input_tape w"
      if "set w \<subseteq> S" and "n \<in> ns" for w :: "'s list" and n :: nat
      unfolding M'_def apply (subst map_states_tmrec_comp)
        apply fact
      unfolding valid_tm_symbols [OF valid_M] using that apply (simp add: M_def)
      unfolding TM.compute_def TM.compute_config_def apply (subst 1)
       apply fact
      unfolding TM_abbrevs.input_tape_def apply auto
      unfolding f1' apply auto
      unfolding valid_tm_tape_count [OF valid_M] using a4 apply (simp add: M_def)
      unfolding nth_Cons' apply auto
      using that a3 apply auto
      apply (subst f32 [simplified])
      using that apply auto
      by fastforce
    show "tapes (TM.compute (Abs_TM M') w) ! n = Tape [] None []"
      if "set w \<subseteq> S" and "n \<notin> ns" and "Suc 0 \<le> n" and "n \<le> k - Suc 0" for n :: nat and w :: "'s list"
      unfolding M'_def apply (subst map_states_tmrec_comp)
        apply fact
      unfolding valid_tm_symbols [OF valid_M] using that apply (simp add: M_def)
      unfolding TM.compute_def TM.compute_config_def apply (subst 1)
       apply fact
      apply (cases "w = []")
       apply auto
      unfolding f1' apply simp
      unfolding valid_tm_tape_count [OF valid_M] apply (simp add: M_def)
      unfolding nth_Cons' using that apply auto
      apply (subst f33 [simplified])
      by simp_all
  qed
qed

lemmas id_computable = identity_function_computable
end