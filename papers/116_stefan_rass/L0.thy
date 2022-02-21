section\<open>The Time Hierarchy Theorem and the Language \<open>L\<^sub>0\<close>\<close>

theory L0
  imports SQ Complexity
begin


subsection\<open>The Time Hierarchy Theorem\<close>

locale tht_assms =
  fixes T t :: "nat \<Rightarrow> nat"
  assumes fully_tconstr_T: "fully_tconstr T"

  \<comment> \<open>This assumption represents the statements containing \<open>lim\<close> @{cite rassOwf2017} and \<open>lim inf\<close> @{cite hopcroftAutomata1979}.
      \<^const>\<open>LIMSEQ\<close> (\<^term>\<open>X \<longlonglongrightarrow> x\<close>) was chosen, as it seems to match the intended meaning
      (@{thm LIMSEQ_def lim_sequentially}).\<close>
    and T_dominates_t: "(\<lambda>n. t n * log 2 (t n) / T n) \<longlonglongrightarrow> 0"
  \<comment> \<open>Additionally, \<open>T n\<close> is assumed not to be zero since in Isabelle,
      \<open>x / 0 = 0\<close> holds over the reals (@{thm division_ring_divide_zero}).
      Thus, the above assumption would trivially hold for \<open>T(n) = 0\<close>.\<close>
    and T_not_0: "ae n. T n \<noteq> 0"

  \<comment> \<open>The following assumption is not found in @{cite rassOwf2017} or the primary source @{cite hopcroftAutomata1979},
    but is taken from the AAU lecture slides of \<^emph>\<open>Algorithms and Complexity Theory\<close>.
    \<^footnote>\<open>TODO properly cite this\<close>
    It patches a hole that allows one to prove \<^const>\<open>False\<close> from the Time Hierarchy Theorem below
    (\<open>time_hierarchy\<close>).
    This is demonstrated in \<^file>\<open>examples/THT_inconsistencies_MWE.thy\<close>.\<close>
    and t_min: "ae n. n \<le> t n"
begin

lemma T_ge_t_log_t_ae:
  fixes c :: real
  assumes "c \<ge> 0"
  shows "ae n. c * t n * log 2 (t n) < T n"
proof (cases "c = 0")
  assume "c = 0"
  from T_not_0 show ?thesis unfolding \<open>c = 0\<close> by (ae_intro_nat) linarith
next
  assume "c \<noteq> 0"
  with \<open>c \<ge> 0\<close> have "c > 0" by simp
  from T_not_0 have "ae n. real (T n) \<noteq> 0" by (ae_intro_nat) linarith
  with T_dominates_t and \<open>c > 0\<close> have "ae n. c * \<bar>t n * log 2 (t n)\<bar> < \<bar>real (T n)\<bar>"
    by (subst (asm) dominates_altdef) presburger+

  then show "ae n. c * t n * log 2 (t n) < T n"
  proof (ae_intro_nat)
    fix n
    from abs_ge_self and \<open>c \<ge> 0\<close> have "c * x \<le> c * \<bar>x\<bar>" for x by (rule mult_left_mono)
    then have "c * t n * log 2 (t n) \<le> c * \<bar>t n * log 2 (t n)\<bar>" by (subst mult.assoc)
    also assume "... < \<bar>real (T n)\<bar>"
    also have "... = T n" by simp
    finally show "c * t n * log 2 (t n) < T n" .
  qed
qed

lemma T_gt_t_ae: "ae n. T n > t n"
proof -
  from T_ge_t_log_t_ae[of 1] have "ae n. t n * log 2 (t n) < T n" unfolding mult_1 by argo
  with t_min show "ae n. T n > t n"
  proof (ae_intro_nat)
    fix n :: nat
    assume "n \<ge> 2" also assume "t n \<ge> n"
    finally have "t n \<ge> 2" .
    then have "log 2 (t n) \<ge> 1" by force

    with \<open>t n \<ge> 2\<close> have "t n \<le> t n * log 2 (t n)" by simp
    also assume "... < T n"
    finally show "t n < T n" by simp
  qed
qed

lemma T_superlinear: "\<forall>N. \<exists>n\<^sub>0. \<forall>n\<ge>n\<^sub>0. T(n)/n \<ge> N"
proof (intro allI)
  fix N :: real

  show "\<exists>n\<^sub>0. \<forall>n\<ge>n\<^sub>0. T(n)/n \<ge> N"
  proof (cases "N > 0")
    assume "\<not> N > 0"
    then have "N \<le> 0" by simp
    also have "0 \<le> T(n)/n" for n by simp
    finally show ?thesis by simp
  next
    assume "N > 0"
    then have *: "N \<le> N * x" if "x \<ge> 1" for x
      using that by (subst mult_le_cancel_left1) simp

    from T_ge_t_log_t_ae[of 1] have "ae n. t n * log 2 (t n) < T n" unfolding mult_1 by argo
    with t_min have "ae n. T(n)/n \<ge> N"
    proof (ae_intro_nat)
      fix n :: nat
      assume "n \<ge> 2 ^ nat\<lceil>N\<rceil>" and t_log_t: "t n * log 2 (t n) < T n"

      from two_realpow_ge_one have "(1::real) \<le> 2 ^ nat\<lceil>N\<rceil>" .
      also from \<open>n \<ge> 2 ^ nat\<lceil>N\<rceil>\<close> have "... \<le> n" by simp
      finally have "n > 0" by simp

      also assume "n \<le> t n"
      finally have "t n > 0" .


      have "n * log 2 n \<le> t n * log 2 (t n)"
      proof (intro mult_mono)
        from \<open>n \<le> t n\<close> show "real n \<le> real (t n)" by simp
        with \<open>n > 0\<close> and \<open>t n > 0\<close> show "log 2 n \<le> log 2 (t n)"
          by (subst log_le_cancel_iff; linarith)

        show "real (t n) \<ge> 0" by (fact of_nat_0_le_iff)
        from \<open>n > 0\<close> show "0 \<le> log 2 (real n)"
          by (subst zero_le_log_cancel_iff) auto
      qed
      also from t_log_t have "... < T n" .
      finally have "n * log 2 n \<le> T n" by simp

      with \<open>n > 0\<close> have "log 2 n \<le> T(n)/n" by (subst pos_le_divide_eq) (simp, argo)

      have "N \<le> log 2 n"
      proof -
        have "N \<le> log 2 (2 ^ nat\<lceil>N\<rceil>)"
          by (subst log_pow_cancel) (simp, simp, linarith)
        also have "... \<le> log 2 n" using \<open>n \<ge> 2 ^ nat\<lceil>N\<rceil>\<close> and \<open>n > 0\<close>
          by (subst log_le_cancel_iff) auto
        finally show "N \<le> log 2 n" .
      qed
      also note \<open>log 2 n \<le> T(n)/n\<close>
      finally show "N \<le> T(n)/n" .
    qed
    then show "\<exists>n\<^sub>0. \<forall>n\<ge>n\<^sub>0. T(n)/n \<ge> N" ..
  qed
qed


text\<open>\<open>L\<^sub>D\<close>, defined as part of the proof for the Time Hierarchy Theorem.

  ``The `diagonal-language' \<open>L\<^sub>D\<close> is thus defined over the alphabet \<open>\<Sigma> = {0, 1}\<close> as
       \<open>L\<^sub>D := {w \<in> \<Sigma>\<^sup>*: M\<^sub>w halts and rejects w within \<le> T(len(w)) steps}\<close>.''
  @{cite rassOwf2017}\<close>

definition L\<^sub>D :: "lang"
  where LD_def[simp]: "L\<^sub>D \<equiv> {w. let M\<^sub>w = TM_decode_pad w in
                  rejects M\<^sub>w w \<and> time_bounded_word T M\<^sub>w w}"

lemma LD_T: "L\<^sub>D \<in> DTIME(T)"
proof -
  \<comment> \<open>\<open>M\<close> is a modified universal TM that executes two TMs in parallel upon an input word \<open>w\<close>.
    \<open>M\<^sub>w\<close> is the input word \<open>w\<close> treated as a TM (\<open>M\<^sub>w \<equiv> TM_decode_pad w\<close>).
    \<open>M\<^sub>T\<close> is a "stopwatch", that halts after exactly \<open>tcomp\<^sub>w T w\<close> steps.
    Its existence is assured by the assumption @{thm fully_tconstr_T}.
    Both machines are simulated with input word \<open>w\<close>.

    Once either of these simulated TM halts, \<open>M\<close> halts as well.
    If \<open>M\<^sub>T\<close> halts before \<open>M\<^sub>w\<close>, \<open>M\<close> rejects \<open>w\<close>.
    If \<open>M\<^sub>w\<close> halts first, \<open>M\<close> inverts the output of \<open>M\<^sub>w\<close>:
    If \<open>M\<^sub>w\<close> accepts, then \<open>M\<close> rejects \<open>w\<close>. If \<open>M\<^sub>w\<close> rejects, then \<open>M\<close> accepts \<open>w\<close>.
    Thus \<open>M\<close> accepts \<open>w\<close>, iff \<open>M\<^sub>w\<close> rejects \<open>w\<close> in time \<open>tcomp\<^sub>w T w\<close>.\<close>

  define L\<^sub>D_P where "L\<^sub>D_P \<equiv> \<lambda>w. let M\<^sub>w = TM_decode_pad w in
    rejects M\<^sub>w w \<and> time_bounded_word T M\<^sub>w w"

  obtain M where "time_bounded T M"
    and *: "\<And>w. if L\<^sub>D_P w then accepts M w else rejects M w" sorry \<comment> \<open>probably out of scope\<close>
  have "decides M L\<^sub>D" unfolding decides_altdef4
    unfolding LD_def mem_Collect_eq L\<^sub>D_P_def[symmetric] using * ..
  with \<open>time_bounded T M\<close> show "L\<^sub>D \<in> DTIME(T)" by blast
qed

lemma LD_t: "L\<^sub>D \<notin> DTIME(t)"
proof -
  have "L \<noteq> L\<^sub>D" if "L \<in> DTIME(t)" for L
  proof -
    from \<open>L \<in> DTIME(t)\<close> obtain M\<^sub>w where "decides M\<^sub>w L" and "time_bounded t M\<^sub>w" and "tm_wf0 M\<^sub>w" ..
    define w' where "w' = encode_TM M\<^sub>w"

    let ?n = "length (encode_TM M\<^sub>w) + 2"
    obtain l where "T(2*l) \<ge> t(2*l)" and "clog l \<ge> ?n"
    proof -
      obtain l\<^sub>1 :: nat where l1: "l \<ge> l\<^sub>1 \<Longrightarrow> T l > t l" for l using T_gt_t_ae by blast
      obtain l\<^sub>2 :: nat where l2: "l \<ge> l\<^sub>2 \<Longrightarrow> clog l \<ge> ?n" for l
      proof
        fix l :: nat
        assume "l \<ge> 2^?n"
        have "?n > 0" by simp
        then have "?n = clog (2^?n)" by (rule clog_exp[symmetric])
        also have "... \<le> clog l" using clog_mono \<open>l \<ge> 2^?n\<close> ..
        finally show "clog l \<ge> ?n" .
      qed

      let ?l = "max l\<^sub>1 l\<^sub>2"
      have "T (2*?l) \<ge> t (2*?l)" by (rule less_imp_le, rule l1) force
      moreover have "clog ?l \<ge> ?n" by (rule l2) force
      ultimately show ?thesis by (intro that) fast+
    qed

    obtain w where "length w = l" and dec_w: "TM_decode_pad w = M\<^sub>w"
      using \<open>tm_wf0 M\<^sub>w\<close> \<open>clog l \<ge> ?n\<close> by (rule embed_TM_in_len)

    have "w \<in> L \<longleftrightarrow> w \<notin> L\<^sub>D"
    proof
      assume "w \<in> L"
      moreover from \<open>decides M\<^sub>w L\<close> have "w \<notin> L \<longleftrightarrow> rejects M\<^sub>w w" unfolding decides_def by blast
      ultimately have "\<not> rejects M\<^sub>w w" by blast
      then show "w \<notin> L\<^sub>D" unfolding LD_def mem_Collect_eq dec_w by presburger
    next
      assume "w \<notin> L\<^sub>D"
      moreover have "time_bounded_word T M\<^sub>w w"
      proof (rule time_bounded_word_mono)
        from \<open>T(2*l) \<ge> t(2*l)\<close> show "real (T (tape_size <w>\<^sub>t\<^sub>p)) \<ge> real (t (tape_size <w>\<^sub>t\<^sub>p))"
          unfolding tape_size_input \<open>length w = l\<close> by (rule of_nat_mono)
        from \<open>time_bounded t M\<^sub>w\<close> show "time_bounded_word t M\<^sub>w w" ..
      qed
      ultimately have "\<not> rejects M\<^sub>w w" unfolding LD_def dec_w mem_Collect_eq Let_def by blast
      with \<open>decides M\<^sub>w L\<close> show "w \<in> L" unfolding decides_def by blast
    qed
    then show "L \<noteq> L\<^sub>D" by blast
  qed
  then show "L\<^sub>D \<notin> DTIME(t)" by blast
qed

theorem time_hierarchy: "L\<^sub>D \<in> DTIME(T) - DTIME(t)" using LD_T and LD_t ..

end \<comment> \<open>\<^locale>\<open>tht_assms\<close>\<close>


subsection\<open>The Hard Language \<open>L\<^sub>0\<close>\<close>


lemma SQ_DTIME: "SQ \<in> DTIME(\<lambda>n. n^3)" sorry


text\<open>From the proof of Lemma 4.6@{cite rassOwf2017}:

   ``To retain \<open>L\<^sub>D \<inter> SQ \<in> DTIME(T)\<close>, we must choose \<open>T\<close> so large that the decision
    \<open>w \<in> SQ\<close> is possible within the time limit incurred by \<open>T\<close>, so we add \<open>T(n) \<ge> n\<^sup>3\<close>
    to our hypothesis besides Assumption 4.4 (note that we do not need an optimal
    complexity bound here).''\<close>

locale tht_sq_assms = tht_assms +
  assumes t_cubic: "ae n. t(n) \<ge> n^3"
    and t_mono: "mono t"
begin

corollary T_cubic: "ae n. T(n) \<ge> n^3"
  by (ae_intro_nat add: t_cubic T_gt_t_ae) linarith

corollary t_superlinear: "\<forall>N. \<exists>n\<^sub>0. \<forall>n\<ge>n\<^sub>0. t(n)/n \<ge> N"
proof (intro allI, ae_intro_nat add: t_cubic)
  fix N :: real and n :: nat
  assume n_min: "n \<ge> max 1 (nat \<lceil>N\<rceil>)" and "t(n) \<ge> n^3"

  from n_min have "n \<ge> 1" by (rule max.boundedE)

  from n_min have "N \<le> n" by simp
  also from \<open>n \<ge> 1\<close> have "... \<le> n^2" using pos2 by (intro of_nat_mono self_le_power) auto
  also have "n^2 \<le> t(n)/n"
  proof (subst pos_le_divide_eq)
    from \<open>n \<ge> 1\<close> show "0 < real n" by force
    have "n^2 * n = n^3" by algebra
    also note \<open>n^3 \<le> t(n)\<close>
    finally show "n\<^sup>2 * real n \<le> t n" by (fold of_nat_mult) linarith
  qed
  finally show "t(n)/n \<ge> N" .
qed

lemma adj_sq_exp_pad:
  fixes w
  defines l: "l \<equiv> length w"
    and w': "w' \<equiv> adj_sq\<^sub>w w"
  assumes "l \<ge> 20"
  shows "strip_exp_pad w' = strip_exp_pad w"
proof -
  from \<open>l \<ge> 20\<close> have "shared_MSBs (clog l) w w'" unfolding l w' by (rule adj_sq_sh_pfx_log)
  then have l_eq: "length w' = l" and d_eq: "drop (l - clog l) w' = drop (l - clog l) w"
    unfolding l by blast+

  have "strip_exp_pad w' = drop (l - clog l) w'" unfolding strip_exp_pad_def l_eq Let_def ..
  also have "... = drop (l - clog l) w" using d_eq .
  also have "... = strip_exp_pad w" unfolding strip_exp_pad_def l Let_def ..
  finally show ?thesis .
qed

corollary adj_sq_TM_dec:
  fixes w
  assumes "length w \<ge> 20"
  defines "w' \<equiv> adj_sq\<^sub>w w"
  shows "TM_decode_pad w' = TM_decode_pad w"
  unfolding TM_decode_pad_def w'_def using \<open>length w \<ge> 20\<close> by (subst adj_sq_exp_pad) fast+

end \<comment> \<open>\<^locale>\<open>tht_sq_assms\<close>\<close>

end
