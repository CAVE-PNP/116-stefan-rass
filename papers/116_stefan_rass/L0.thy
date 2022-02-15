section\<open>The Time Hierarchy Theorem and the Language \<open>L\<^sub>0\<close>\<close>

theory L0
  imports SQ Complexity
begin


subsection\<open>Preliminaries\<close>

lemma SQ_DTIME: "SQ \<in> DTIME(\<lambda>n. n^3)" sorry

lemma dominates_altdef:
  fixes c :: real
  assumes "\<And>n. T n \<noteq> 0"
    and T_dominates_t: "(\<lambda>n. t n / T n) \<longlonglongrightarrow> 0"
  shows "\<exists>N. \<forall>n\<ge>N. \<bar>c * t n\<bar> < \<bar>T n\<bar>"
proof (cases "c = 0")
  assume "c = 0"
  show ?thesis proof (intro exI allI impI)
    fix n
    have "\<bar>c * t n\<bar> = 0" unfolding \<open>c = 0\<close> by simp
    also have "0 < \<bar>T n\<bar>" using \<open>T n \<noteq> 0\<close> by simp
    finally show "\<bar>c * t n\<bar> < \<bar>T n\<bar>" .
  qed
next
  let ?f = "\<lambda>n. t n / T n"
  assume "c \<noteq> 0"
  define c' where c': "c' \<equiv> 1 / c"
  from \<open>c \<noteq> 0\<close> have "c' \<noteq> 0" unfolding c' by simp

  with T_dominates_t have "\<exists>N. \<forall>n\<ge>N. \<bar>?f n\<bar> < \<bar>c'\<bar>"
    unfolding LIMSEQ_def dist_real_def diff_0_right by force
  then obtain N where "\<bar>?f n\<bar> < \<bar>c'\<bar>" if "n \<ge> N" for n by blast

  have "\<bar>c * t n\<bar> < \<bar>T n\<bar>" if "n \<ge> N" for n
  proof -
    from \<open>T n \<noteq> 0\<close> have "\<bar>T n\<bar> > 0" unfolding zero_less_abs_iff .
    from \<open>c \<noteq> 0\<close> have "\<bar>c\<bar> > 0" unfolding zero_less_abs_iff .

    have "\<bar>?f n\<bar> < \<bar>c'\<bar>" using \<open>n \<ge> N\<close> by fact
    then have "\<bar>t n\<bar> / \<bar>T n\<bar> < 1 / \<bar>c\<bar>" unfolding c' abs_divide abs_one .
    then have "\<bar>t n\<bar> < \<bar>T n\<bar> / \<bar>c\<bar>" unfolding \<open>\<bar>T n\<bar> > 0\<close>[THEN pos_divide_less_eq] by argo
    then show "\<bar>c * t n\<bar> < \<bar>T n\<bar>" unfolding \<open>\<bar>c\<bar> > 0\<close>[THEN pos_less_divide_eq] abs_mult by argo
  qed
  then show "\<exists>N. \<forall>n\<ge>N. \<bar>c * t n\<bar> < \<bar>T n\<bar>" by blast
qed


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
    and T_not_0: "T n \<noteq> 0"

  \<comment> \<open>The following assumption is not found in @{cite rassOwf2017} or the primary source @{cite hopcroftAutomata1979},
    but is taken from the AAU lecture slides of \<^emph>\<open>Algorithms and Complexity Theory\<close>.
    \<^footnote>\<open>TODO properly cite this\<close>
    It patches a hole that allows one to prove \<^term>\<open>False\<close> from the Time Hierarchy Theorem below
    (\<open>time_hierarchy\<close>).
    This is demonstrated in \<^file>\<open>examples/THT_inconsistencies_MWE.thy\<close>.\<close>
    and t_min: "n \<le> t n"
begin

lemma T_ge_t_log_t_ae:
  fixes c :: real
  assumes "c \<ge> 0"
  shows "\<exists>N. \<forall>n\<ge>N. c * t n * log 2 (t n) < T n"
proof -
  from T_not_0 have "real (T n) \<noteq> 0" for n unfolding of_nat_eq_0_iff .
  then have "\<exists>N. \<forall>n\<ge>N. \<bar>c * (t n * log 2 (t n))\<bar> < \<bar>real (T n)\<bar>"
    using T_dominates_t by (rule dominates_altdef)
  then obtain N where *: "n \<ge> N \<Longrightarrow> \<bar>c * (t n * log 2 (t n))\<bar> < \<bar>real (T n)\<bar>" for n by blast
  let ?N = "max N 2"

  have "c * t n * log 2 (t n) < T n" if "n \<ge> ?N" for n
  proof -
    from \<open>n \<ge> ?N\<close> have "n \<ge> N" and "n \<ge> 2" by auto
    from \<open>n \<ge> N\<close> have "\<bar>c * (t n * log 2 (t n))\<bar> < \<bar>real (T n)\<bar>" by (fact *)

    from \<open>n \<ge> 2\<close> and t_min have "t n \<ge> 2" by (rule le_trans)
    then have "log 2 (t n) \<ge> 1" by force
    with \<open>t n \<ge> 2\<close> have "t n * log 2 (t n) > 0" by auto

    have "c * t n * log 2 (t n) = c * \<bar>t n * log 2 (t n)\<bar>" using \<open>t n * log 2 (t n) > 0\<close> by fastforce
    also from \<open>c \<ge> 0\<close> have "... = \<bar>c * (t n * log 2 (t n))\<bar>" unfolding abs_mult by force
    also from \<open>n \<ge> N\<close> have "... < \<bar>real (T n)\<bar>" by (fact *)
    also have "... = T n" by simp
    finally show ?thesis .
  qed
  then show "\<exists>N. \<forall>n\<ge>N. c * t n * log 2 (t n) < T n" by blast
qed

lemma T_ge_t_ae: "\<exists>N. \<forall>n\<ge>N. T n > t n"
proof -
  from T_ge_t_log_t_ae[of 1] obtain N where *: "n \<ge> N \<Longrightarrow> t n * log 2 (t n) < T n" for n by auto
  let ?N = "max N 2"

  have "t n < T n" if "n \<ge> ?N" for n
  proof -
    from \<open>n \<ge> ?N\<close> and * have "n \<ge> 2" by simp
    with t_min have "t n \<ge> 2" using le_trans by blast
    then have "log 2 (t n) \<ge> 1" by force

    have "t n \<le> t n * log 2 (t n)" using \<open>log 2 (t n) \<ge> 1\<close> \<open>t n \<ge> 2\<close> by fastforce
    also have "... < T n" using * \<open>n \<ge> ?N\<close> by simp
    finally show "t n < T n" by fastforce
  qed
  then show ?thesis by blast
qed


text\<open>\<open>L\<^sub>D\<close>, defined as part of the proof for the Time Hierarchy Theorem.

  ``The `diagonal-language' \<open>L\<^sub>D\<close> is thus defined over the alphabet \<open>\<Sigma> = {0, 1}\<close> as
       \<open>LD := {w \<in> \<Sigma>\<^sup>*: M\<^sub>w halts and rejects w within \<le> T(len(w)) steps}\<close>.    (9)''
  @{cite rassOwf2017}\<close>

definition L\<^sub>D :: "lang"
  where LD_def[simp]: "L\<^sub>D \<equiv> {w. let M\<^sub>w = TM_decode_pad w in
                  rejects M\<^sub>w w \<and> time_bounded_word T M\<^sub>w w}"

\<comment> \<open>In the above definition, membership is dependent on the whole word \<open>w\<close>,
  as this is the input for \<open>M\<^sub>w\<close>.
  Since no assumptions can be made about the inner workings of \<open>M\<^sub>w\<close>,
  the result of its computation on \<open>w\<close> could depend on the contents of the padding.
  Therefore, the membership of some \<open>w'\<close> with \<open>TM_decode_pad w' = M\<^sub>w\<close>
  is not equivalent to that of \<open>w\<close>.

  To illustrate this, consider a TM that decides word only based on the value of their last bit;
  accepting if it is \<open>1\<close> and rejecting otherwise.
  This TM will reject exactly half of its encodings, causing only these to be members of \<open>L\<^sub>D\<close>.\<close>

text\<open>Alternative formulation: \<open>L\<^sub>D' := {w \<in> \<Sigma>\<^sup>*: M\<^sub>w halts and rejects w' within \<le> T(len(w)) steps}\<close>,
  where \<open>w' := strip_al_prefix (strip_exp_pad w)\<close>.\<close>

definition L\<^sub>D' :: "lang"
  where LD'_def[simp]: "L\<^sub>D' \<equiv> {w. let M\<^sub>w = TM_decode_pad w; w' = strip_al_prefix (strip_exp_pad w) in
                  rejects M\<^sub>w w' \<and> time_bounded_word T M\<^sub>w w'}"


theorem time_hierarchy: "L\<^sub>D \<in> DTIME(T) - DTIME(t)"
proof
  \<comment> \<open>Part 1: \<^term>\<open>L\<^sub>D \<in> DTIME(T)\<close>

    \<open>M\<close> is a modified universal TM that executes two TMs in parallel upon an input word \<open>w\<close>.
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
    and *: "\<And>w. if L\<^sub>D_P w then accepts M w else rejects M w" sorry (* probably out of scope *)
  have "decides M L\<^sub>D" unfolding decides_altdef4 LD_def mem_Collect_eq L\<^sub>D_P_def[symmetric] using * ..
  with \<open>time_bounded T M\<close> show "L\<^sub>D \<in> DTIME(T)" by blast


next \<comment> \<open>Part 2: \<^term>\<open>L\<^sub>D \<notin> DTIME(t)\<close>\<close>

  have "L \<noteq> L\<^sub>D" if "L \<in> DTIME(t)" for L
  proof -
    from \<open>L \<in> DTIME(t)\<close> obtain M\<^sub>w where "decides M\<^sub>w L" and "time_bounded t M\<^sub>w" and "tm_wf0 M\<^sub>w" ..
    define w' where "w' = encode_TM M\<^sub>w"

    let ?n = "length (encode_TM M\<^sub>w) + 2"
    obtain l where "T(2*l) \<ge> t(2*l)" and "clog l \<ge> ?n"
    proof -
      obtain l\<^sub>1 :: nat where l1: "l \<ge> l\<^sub>1 \<Longrightarrow> T l > t l" for l using T_ge_t_ae by blast
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


end \<comment> \<open>\<^locale>\<open>tht_assms\<close>\<close>


subsection\<open>The Hard Language \<open>L\<^sub>0\<close>\<close>

text\<open>From the proof of Lemma 4.6@{cite rassOwf2017}:

   ``To retain \<open>L\<^sub>D \<inter> SQ \<in> DTIME(T)\<close>, we must choose \<open>T\<close> so large that the decision
    \<open>w \<in> SQ\<close> is possible within the time limit incurred by \<open>T\<close>, so we add \<open>T(n) \<ge> n\<^sup>3\<close>
    to our hypothesis besides Assumption 4.4 (note that we do not need an optimal
    complexity bound here).''\<close>

locale tht_sq_assms = tht_assms +
  assumes T_lower_bound: "T n \<ge> n^3"
begin


definition L\<^sub>0 :: lang
  where L0_def[simp]: "L\<^sub>0 \<equiv> L\<^sub>D \<inter> SQ"

definition L\<^sub>0' :: lang
  where L0'_def[simp]: "L\<^sub>0' \<equiv> L\<^sub>D' \<inter> SQ"

(* TODO move lemmas that do not depend on locale defs out of locale context *)

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

lemma L\<^sub>D_adj_sq_iff:
  fixes w
  assumes l: "length w \<ge> 20"
  defines w': "w' \<equiv> adj_sq\<^sub>w w"
  shows "w' \<in> L\<^sub>D \<longleftrightarrow> w \<in> L\<^sub>D"
proof -
    \<comment> \<open>Idea: since \<open>w\<close> and \<open>adj_sq\<^sub>w n\<close> share their prefix (@{thm adj_sq_sh_pfx_log}),
  the relevant parts are identical and this lemma should hold.

  Note: with the current definition of \<^const>\<open>L\<^sub>D\<close>, this likely does not hold,
        as the whole word \<open>w\<close> is referenced in the definition.\<close>

  from l have dec: "TM_decode_pad w' = TM_decode_pad w" unfolding w' by (rule adj_sq_TM_dec)
  from l have pad: "strip_exp_pad w' = strip_exp_pad w" unfolding w' by (rule adj_sq_exp_pad)
  let ?Mw = "TM_decode_pad w"

    \<comment> \<open>Both of the following statements are not provable without further assumptions
        about the contents of \<^term>\<open>w\<close> (and thus \<^term>\<open>?Mw\<close>).\<close>
  have a: "rejects ?Mw w' = rejects ?Mw w" sorry
  have b: "time_bounded_word T ?Mw w' = time_bounded_word T ?Mw w" sorry
  have "w' \<in> L\<^sub>D \<longleftrightarrow> w \<in> L\<^sub>D" unfolding LD_def mem_Collect_eq Let_def
    unfolding dec pad unfolding a b ..
  oops

lemma L\<^sub>D'_adj_sq_iff:
  fixes w
  assumes l: "length w \<ge> 20"
  defines w': "w' \<equiv> adj_sq\<^sub>w w"
  shows "w' \<in> L\<^sub>D' \<longleftrightarrow> w \<in> L\<^sub>D'"
proof -
  from l have dec: "TM_decode_pad w' = TM_decode_pad w" unfolding w' by (rule adj_sq_TM_dec)
  from l have pad: "strip_exp_pad w' = strip_exp_pad w" unfolding w' by (rule adj_sq_exp_pad)
  show "w' \<in> L\<^sub>D' \<longleftrightarrow> w \<in> L\<^sub>D'" unfolding LD'_def mem_Collect_eq unfolding dec pad ..
qed

lemma L\<^sub>D'_L\<^sub>0'_adj_sq_iff:
  fixes w
  assumes l: "length w \<ge> 20"
  defines "w' \<equiv> adj_sq\<^sub>w w"
  shows "w' \<in> L\<^sub>0' \<longleftrightarrow> w \<in> L\<^sub>D'"
proof
  assume "w \<in> L\<^sub>D'"
  then have "w' \<in> L\<^sub>D'" unfolding w'_def using l by (subst L\<^sub>D'_adj_sq_iff)
  moreover have "w' \<in> SQ" unfolding w'_def by (rule adj_sq_word_correct)
  ultimately show "w' \<in> L\<^sub>0'" unfolding L0'_def ..
next
  assume "w' \<in> L\<^sub>0'"
  then have "w' \<in> L\<^sub>D'" unfolding L0'_def ..
  then show "w \<in> L\<^sub>D'" unfolding w'_def using l by (subst (asm) L\<^sub>D'_adj_sq_iff)
qed


text\<open>For now assume that this result will hold for some version of \<open>L\<^sub>D\<close> and \<open>L\<^sub>0\<close>.\<close>

lemma L\<^sub>D_L\<^sub>0_adj_sq_iff:
  fixes w
  assumes l: "length w \<ge> 20"
  defines "w' \<equiv> adj_sq\<^sub>w w"
  shows "w' \<in> L\<^sub>0 \<longleftrightarrow> w \<in> L\<^sub>D"
  sorry


text\<open>From @{cite rassOwf2017}:
 ``Lemma 4.6. Let \<open>t\<close>, \<open>T\<close> be as in Assumption 4.4 and assume \<open>T(n) \<ge> n\<^sup>3\<close>.
  Then, there exists a language \<open>L\<^sub>0 \<in> DTIME(T) - DTIME(t)\<close> for which \<open>dens\<^sub>L\<^sub>0(x) \<le> \<surd>x\<close>.''\<close>

lemma L0_t: "L\<^sub>0 \<notin> DTIME(t)"
proof (rule ccontr, unfold not_not)
  assume "L\<^sub>0 \<in> DTIME(t)"

  have "L\<^sub>D \<in> DTIME(t)"
  proof (rule reduce_DTIME)
    show "almost_everywhere (\<lambda>w. (adj_sq\<^sub>w w \<in> L\<^sub>0) = (w \<in> L\<^sub>D) \<and> length (adj_sq\<^sub>w w) \<le> length w)"
    proof (intro ae_word_lengthI exI allI impI conjI)
      fix w :: word assume "length w \<ge> 20"
      then show "adj_sq\<^sub>w w \<in> L\<^sub>0 \<longleftrightarrow> w \<in> L\<^sub>D" by (fact L\<^sub>D_L\<^sub>0_adj_sq_iff)
      from \<open>length w \<ge> 20\<close> have "length w \<ge> 9" by simp
      then show "length (adj_sq\<^sub>w w) \<le> length w"
        by (intro eq_imp_le sh_msbD) (fact adj_sq_sh_pfx_half)
    qed

    show "\<forall>N. \<exists>n. \<forall>m\<ge>n. N \<le> t m / m" sorry
    \<comment> \<open>This is not correct, since \<^term>\<open>t\<close> could be arbitrarily small.
      Let \<open>t(n) = n\<close> and \<open>T(n) = n\<^sup>3\<close>. Then \<open>DTIME(t)\<close> is limited by \<open>tcomp t n = n + 1\<close>
      and \<open>DTIME(T)\<close> by \<open>tcomp t n = n\<^sup>3\<close> (for \<open>n > 1\<close>).\<close>

    show "computable_in_time t adj_sq\<^sub>w" sorry
    \<comment> \<open>Assume that \<^const>\<open>adj_sq\<^sub>w\<close> can be computed by a TM in time \<open>n\<^sup>3\<close>.\<close>

    show \<open>L\<^sub>0 \<in> DTIME(t)\<close> by fact
  qed

  moreover from time_hierarchy have "L\<^sub>D \<notin> DTIME(t)" ..
  ultimately show False by contradiction
qed

(* TODO move to Complexity.thy *)
lemma DTIME_int: "L\<^sub>1 \<in> DTIME(T\<^sub>1) \<Longrightarrow> L\<^sub>2 \<in> DTIME(T\<^sub>2) \<Longrightarrow> L\<^sub>1 \<inter> L\<^sub>2 \<in> DTIME(\<lambda>n. T\<^sub>1 n + T\<^sub>2 n)" sorry

lemma L0_T: "L\<^sub>0 \<in> DTIME(T)"
proof -
  define T' :: "nat \<Rightarrow> real" where "T' \<equiv> \<lambda>n. T n + n^3"
  have "T' n \<le> 2 * T n" for n unfolding T'_def
    using T_lower_bound by (intro of_nat_mono) force

  have T_superlinear: "\<forall>N. \<exists>n'. \<forall>n\<ge>n'. T(n)/n \<ge> N"
  proof (intro allI exI impI)
    fix N :: real and n :: nat
    let ?n' = "nat \<lceil>N\<rceil>"
    assume "?n' \<le> n"

    have "N \<le> ?n'" by (rule real_nat_ceiling_ge)
    also have "... \<le> n" using \<open>?n' \<le> n\<close> by (rule of_nat_mono)
    also have "... \<le> n\<^sup>2" by (rule of_nat_mono) (rule power2_nat_le_imp_le, rule le_refl)
    also have "... = n powr (3 - 1)" by force
    also have "... = n^3 / n" unfolding powr_diff
      by (simp only: powr_numeral powr_one of_nat_power)
    also have "... \<le> T(n)/n" using T_lower_bound by (intro divide_right_mono of_nat_mono) auto
    finally show "T(n)/n \<ge> N" .
  qed

  from time_hierarchy have "L\<^sub>D \<in> DTIME T" ..
  then have "L\<^sub>0 \<in> DTIME(T')" unfolding T'_def L0_def of_nat_add
    using SQ_DTIME by (rule DTIME_int)
  with \<open>\<And>n. T' n \<le> 2 * T n\<close> have "L\<^sub>0 \<in> DTIME(\<lambda>n. 2 * T n)" by (rule in_dtime_mono)
  then show "L\<^sub>0 \<in> DTIME(T)" unfolding of_nat_mult
    using T_superlinear by (subst (asm) DTIME_speed_up_eq) linarith
qed

\<comment> \<open>Alternative proof for \<open>L\<^sub>0 \<in> DTIME(T)\<close> without the need for the Speed-Up Theorem.
  This version of @{thm DTIME_int} should work, if multiple tapes may be used.\<close>

(* TODO move to Complexity.thy *)
lemma DTIME_int': "L\<^sub>1 \<in> DTIME(T\<^sub>1) \<Longrightarrow> L\<^sub>2 \<in> DTIME(T\<^sub>2) \<Longrightarrow> L\<^sub>1 \<inter> L\<^sub>2 \<in> DTIME(\<lambda>n. max (T\<^sub>1 n) (T\<^sub>2 n))" sorry

lemma L0_T': "L\<^sub>0 \<in> DTIME(T)"
proof -
  let ?T' = "\<lambda>n. real (max (T n) (n^3))"
  from T_lower_bound have "?T' = T" by (intro ext, unfold of_nat_eq_iff) (rule max_absorb1)

  from time_hierarchy have "L\<^sub>D \<in> DTIME T" ..
  then have "L\<^sub>0 \<in> DTIME(?T')" using SQ_DTIME unfolding L0_def of_nat_max by (rule DTIME_int')
  then show "L\<^sub>0 \<in> DTIME(T)" unfolding \<open>?T' = T\<close> .
qed


theorem L0_time_hierarchy: "L\<^sub>0 \<in> DTIME(T) - DTIME(t)" using L0_T L0_t ..

theorem dens_L0: "dens L\<^sub>0 n \<le> dsqrt n"
proof -
  have "dens L\<^sub>0 n = dens (L\<^sub>D \<inter> SQ) n" unfolding L0_def ..
  also have "... \<le> dens SQ n" by (subst Int_commute) (rule dens_intersect_le)
  also have "... = dsqrt n" by (rule dens_SQ)
  finally show ?thesis .
qed

lemmas lemma4_6 = L0_time_hierarchy dens_L0

end \<comment> \<open>\<^locale>\<open>tht_sq_assms\<close>\<close>

end
