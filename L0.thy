section\<open>The Time Hierarchy Theorem and the Language \<open>L\<^sub>0\<close>\<close>

theory L0
  imports SQ Complexity TM_Encoding
begin


subsection\<open>Preliminaries\<close>

lemma SQ_DTIME: "SQ \<in> DTIME(\<lambda>n. n^3)" sorry


locale UTM_Encoding =
  fixes enc\<^sub>U :: "('q, 's) TM \<times> 's list \<Rightarrow> bool list"
    and is_valid_enc\<^sub>U :: "bool list \<Rightarrow> bool"
    and dec\<^sub>U :: "bool list \<Rightarrow> ('q, 's) TM \<times> 's list"
  assumes inj_enc\<^sub>U: "inj enc\<^sub>U"
    and valid_enc: "\<And>M w. TM.wf_input M w \<Longrightarrow> is_valid_enc\<^sub>U (enc\<^sub>U (M, w))"
    and enc_dec:   "\<And>M w. TM.wf_input M w \<Longrightarrow> dec\<^sub>U (enc\<^sub>U (M, w)) = (M, w)"
    and invalid_rejects: "\<And>x. \<not> is_valid_enc\<^sub>U x \<Longrightarrow> let (M, w) = dec\<^sub>U x in TM.rejects M w" (* a nicer version of: "\<exists>q\<^sub>0 s w. dec\<^sub>U x = (rejecting_TM q\<^sub>0 s, w)" *)
    and dec_enc: "\<And>x. is_valid_enc\<^sub>U x \<Longrightarrow> enc\<^sub>U (dec\<^sub>U x) = x" (* this should be easy to achieve *)

locale UTM = UTM: TM M\<^sub>U + UTM_Encoding enc\<^sub>U is_valid_enc\<^sub>U dec\<^sub>U
  for M\<^sub>U :: "('q, bool) TM" (* TODO make 'q = nat ? *)
    and enc\<^sub>U :: "('q, nat) TM \<times> nat list \<Rightarrow> bool list"
    and is_valid_enc\<^sub>U dec\<^sub>U +
  assumes halts_iff: "\<And>M w. TM.halts   M w \<longleftrightarrow> TM.halts   M\<^sub>U (enc\<^sub>U (M, w))"
    and accepts_iff: "\<And>M w. TM.accepts M w \<longleftrightarrow> TM.accepts M\<^sub>U (enc\<^sub>U (M, w))"

locale timed_UTM = UTM M\<^sub>U for M\<^sub>U :: "(nat, bool) TM" +
  fixes T\<^sub>U :: "nat \<Rightarrow> nat" \<comment> \<open>Simulation time overhead of \<^term>\<open>M\<^sub>U\<close>.\<close>
  assumes sim_overhead: "\<And>M::(nat, nat) TM. \<And>w. TM.halts M w \<Longrightarrow>
    TM.time M\<^sub>U (enc\<^sub>U (M, w)) \<le> T\<^sub>U (TM.time M w)"
    and overhead_min: "T\<^sub>U n \<ge> n" \<comment> \<open>This should be trivially true, but is required for the THT.\<close>


subsection\<open>The Time Hierarchy Theorem\<close>

locale tht_assms = TM_Encoding + timed_UTM +
  fixes T t :: "nat \<Rightarrow> nat"
  assumes fully_tconstr_T: "fully_time_constr T"

  \<comment> \<open>This assumption represents the statements containing \<open>lim\<close> @{cite rassOwf2017} and \<open>lim inf\<close> @{cite hopcroftAutomata1979}.
      \<^const>\<open>LIMSEQ\<close> (\<^term>\<open>X \<longlonglongrightarrow> x\<close>) was chosen, as it seems to match the intended meaning
      (@{thm LIMSEQ_def lim_sequentially}).
      The sources additionally specify \<^term>\<open>T\<^sub>U n = n * log 2 n\<close>.\<close>
    and T_dominates_t: "(\<lambda>n. T\<^sub>U (t n) / T n) \<longlonglongrightarrow> 0"
  \<comment> \<open>Additionally, \<open>T n\<close> is assumed not to be zero since in Isabelle,
      \<open>x / 0 = 0\<close> holds over the reals (@{thm division_ring_divide_zero}).
      Thus, the above assumption would trivially hold for \<open>T(n) = 0\<close>.\<close>
    and T_not_0: "\<forall>\<^sub>\<infinity>n. T n \<noteq> 0"

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
  shows "\<forall>\<^sub>\<infinity>n. c * T\<^sub>U (t n) < T n"
proof -
  from T_not_0 and T_dominates_t have "\<forall>\<^sub>\<infinity>n. c * \<bar>real (T\<^sub>U (t n))\<bar> < \<bar>real (T n)\<bar>"
    by (elim dominates_ae) simp
  then show "?thesis" by simp
qed

lemma T_ge_t_ae: "\<forall>\<^sub>\<infinity>n. T n > t n"
proof -
  from T_ge_t_log_t_ae[of 1] have "\<forall>\<^sub>\<infinity>n. T\<^sub>U (t n) < T n" by simp
  then show "\<forall>\<^sub>\<infinity>n. t n < T n"
  proof ae_nat_elim
    fix n
    have "t n \<le> T\<^sub>U (t n)" by (fact overhead_min)
    also assume "T\<^sub>U (t n) < T n"
    finally show "t n < T n" .
  qed
qed


text\<open>\<open>L\<^sub>D\<close>, defined as part of the proof for the Time Hierarchy Theorem.

  ``The `diagonal-language' \<open>L\<^sub>D\<close> is thus defined over the alphabet \<open>\<Sigma> = {0, 1}\<close> as
       \<open>LD := {w \<in> \<Sigma>\<^sup>*: M\<^sub>w halts and rejects w within \<le> T(len(w)) steps}\<close>.    (9)''
  @{cite rassOwf2017}\<close>

definition L\<^sub>D :: "bool lang"
  where "L\<^sub>D \<equiv> Lang UNIV (\<lambda>w. let M\<^sub>w = dec_TM_pad w in
                  TM.rejects M\<^sub>w w \<and> TM.time_bounded_word M\<^sub>w T w)"

\<comment> \<open>In the above definition, membership is dependent on the whole word \<open>w\<close>,
  as this is the input for \<open>M\<^sub>w\<close>.
  Since no assumptions can be made about the inner workings of \<open>M\<^sub>w\<close>,
  the result of its computation on \<open>w\<close> could depend on the contents of the padding.
  Therefore, the membership of some \<open>w'\<close> with \<open>dec_TM_pad w' = M\<^sub>w\<close>
  is not equivalent to that of \<open>w\<close>.

  To illustrate this, consider a TM that decides words only based on the value of their last bit;
  accepting if it is \<open>1\<close> and rejecting otherwise.
  This TM will reject exactly half of its encodings, causing only these to be members of \<open>L\<^sub>D\<close>.\<close>

text\<open>Alternative formulation: \<open>L\<^sub>D' := {w \<in> \<Sigma>\<^sup>*: M\<^sub>w halts and rejects w' within \<le> T(len(w)) steps}\<close>,
  where \<open>w' := strip_al_prefix (strip_exp_pad w)\<close>.\<close>

definition L\<^sub>D' :: "bool lang"
  where "L\<^sub>D' \<equiv> Lang UNIV (\<lambda>w. let w' = strip_al_prefix (strip_exp_pad w); M\<^sub>w = dec_TM w' in
                  TM.rejects M\<^sub>w w' \<and> TM.time_bounded_word M\<^sub>w T w')"

theorem time_hierarchy: "L\<^sub>D \<in> DTIME T - DTIME t"
proof
  \<comment> \<open>Part 1: \<^term>\<open>L\<^sub>D \<in> DTIME T\<close>

    \<open>M\<close> is a modified universal TM that executes two TMs in parallel upon an input word \<open>w\<close>.
    \<open>M\<^sub>w\<close> is the input word \<open>w\<close> treated as a TM (\<open>M\<^sub>w \<equiv> dec_TM_pad w\<close>).
    \<open>M\<^sub>T\<close> is a "stopwatch", that halts after exactly \<open>tcomp\<^sub>w T w\<close> steps.
    Its existence is assured by the assumption @{thm fully_tconstr_T}.
    Both machines are simulated with input word \<open>w\<close>.

    Once either of these simulated TM halts, \<open>M\<close> halts as well.
    If \<open>M\<^sub>T\<close> halts before \<open>M\<^sub>w\<close>, \<open>M\<close> rejects \<open>w\<close>.
    If \<open>M\<^sub>w\<close> halts first, \<open>M\<close> inverts the output of \<open>M\<^sub>w\<close>:
    If \<open>M\<^sub>w\<close> accepts, then \<open>M\<close> rejects \<open>w\<close>. If \<open>M\<^sub>w\<close> rejects, then \<open>M\<close> accepts \<open>w\<close>.
    Thus \<open>M\<close> accepts \<open>w\<close>, iff \<open>M\<^sub>w\<close> rejects \<open>w\<close> in time \<open>tcomp\<^sub>w T w\<close>.\<close>

  define L\<^sub>D_P where "L\<^sub>D_P \<equiv> \<lambda>w. let M\<^sub>w = dec_TM_pad w in
    TM.rejects M\<^sub>w w \<and> TM.time_bounded_word M\<^sub>w T w"
  then have L\<^sub>D[simp]: "L\<^sub>D = Lang UNIV L\<^sub>D_P" unfolding L\<^sub>D_def by simp

  obtain M :: "(nat, bool) TM" where "TM.symbols M = UNIV" and "TM.time_bounded M T"
    and *: "\<And>w. if L\<^sub>D_P w then TM.accepts M w else TM.rejects M w" sorry (* probably out of scope *)
  then have "TM.decides M L\<^sub>D" unfolding TM.decides_altdef4 by simp
  with \<open>TM.time_bounded M T\<close> show "L\<^sub>D \<in> DTIME T" by blast

next \<comment> \<open>Part 2: \<^term>\<open>L\<^sub>D \<notin> DTIME t\<close>\<close>
  have "L \<noteq> L\<^sub>D" if "L \<in> DTIME t" for L
  proof -
    from \<open>L \<in> DTIME t\<close> obtain M\<^sub>w :: "(nat, bool) TM"
      where "TM.decides M\<^sub>w L" and "TM.time_bounded M\<^sub>w t" ..
    interpret TM M\<^sub>w .

    define w' :: "bool list" where "w' = enc_TM M\<^sub>w"

    let ?n = "length (enc_TM M\<^sub>w) + 2"
    obtain l where "T l \<ge> t l" and "clog l \<ge> ?n"
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
      have "T ?l \<ge> t ?l" by (rule less_imp_le, rule l1) force
      moreover have "clog ?l \<ge> ?n" by (rule l2) force
      ultimately show ?thesis by (intro that) fast+
    qed

    from \<open>clog l \<ge> ?n\<close> obtain w where [simp]: "length w = l" and dec_w[simp]: "dec_TM_pad w = M\<^sub>w"
      by (rule embed_TM_in_len)

    have "w \<in>\<^sub>L L \<longleftrightarrow> w \<notin>\<^sub>L L\<^sub>D" if "alphabet L = UNIV"
    proof
      assume "w \<in>\<^sub>L L"
      then have "w \<in> (alphabet L)*" ..
      with \<open>decides L\<close> have "w \<notin>\<^sub>L L \<longleftrightarrow> rejects w" unfolding decides_def by blast
      with \<open>w \<in>\<^sub>L L\<close> have "\<not> rejects w" by blast
      then show "w \<notin>\<^sub>L L\<^sub>D" by (simp add: L\<^sub>D_def)
    next
      assume "w \<notin>\<^sub>L L\<^sub>D"
      moreover from \<open>T l \<ge> t l\<close> and \<open>time_bounded t\<close> have "time_bounded_word T w" by (fold \<open>length w = l\<close>) fast
      ultimately have "\<not> rejects w" unfolding L\<^sub>D_def by force
      with \<open>decides L\<close> show "w \<in>\<^sub>L L" by (auto simp: \<open>alphabet L = UNIV\<close>)
    qed
    moreover have "L \<noteq> L\<^sub>D" if "alphabet L \<noteq> UNIV" using that unfolding L\<^sub>D_def by force
    ultimately show "L \<noteq> L\<^sub>D" by blast
  qed
  then show "L\<^sub>D \<notin> DTIME t" by blast
qed


end \<comment> \<open>\<^locale>\<open>tht_assms\<close>\<close>


subsection\<open>The Hard Language \<open>L\<^sub>0\<close>\<close>

text\<open>From the proof of Lemma 4.6@{cite rassOwf2017}:

   ``To retain \<open>L\<^sub>D \<inter> SQ \<in> DTIME(T)\<close>, we must choose \<open>T\<close> so large that the decision
    \<open>w \<in> SQ\<close> is possible within the time limit incurred by \<open>T\<close>, so we add \<open>T(n) \<ge> n\<^sup>3\<close>
    to our hypothesis besides Assumption 4.4 (note that we do not need an optimal
    complexity bound here).''\<close>

locale tht_sq_assms = tht_assms +
  assumes T_lower_bound: "\<forall>\<^sub>\<infinity> n. T n \<ge> n^3"
begin

lemma T_superlinear: "superlinear T"
proof -
  have "superlinear (\<lambda>n::nat. n^3)" by (rule superlinear_poly_nat) auto
  then show ?thesis by (elim superlinear_ae_mono, ae_nat_elim add: T_lower_bound) simp
qed

lemma T_ge_tcomp_T_ae: "\<forall>\<^sub>\<infinity> n. T n \<ge> tcomp T n" using T_lower_bound
proof ae_nat_elim
  fix n :: nat
  assume "n \<ge> 2"
  from \<open>n \<ge> 2\<close> have "n^1 < n^3" using power_strict_increasing_iff[of n 1 3] by simp
  then have "n + 1 \<le> n^3" by simp
  also assume "n^3 \<le> T n"
  finally show "tcomp T n \<le> T n" by simp
qed


definition "L\<^sub>0  \<equiv> L\<^sub>D  \<inter>\<^sub>L SQ"
definition "L\<^sub>0' \<equiv> L\<^sub>D' \<inter>\<^sub>L SQ"

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
  shows "dec_TM_pad (adj_sq\<^sub>w w) = dec_TM_pad w"
  unfolding dec_TM_pad_def using assms by (subst adj_sq_exp_pad) fast+

lemma L\<^sub>D_adj_sq_iff:
  fixes w
  assumes l: "length w \<ge> 20"
  defines w': "w' \<equiv> adj_sq\<^sub>w w"
  shows "w' \<in>\<^sub>L L\<^sub>D \<longleftrightarrow> w \<in>\<^sub>L L\<^sub>D"
proof -
    \<comment> \<open>Idea: since \<open>w\<close> and \<open>adj_sq\<^sub>w n\<close> share their prefix (@{thm adj_sq_sh_pfx_log}),
  the relevant parts are identical and this lemma should hold.

  Note: with the current definition of \<^const>\<open>L\<^sub>D\<close>, this likely does not hold,
        as the whole word \<open>w\<close> is referenced in the definition.\<close>

  from l have dec: "dec_TM_pad w' = dec_TM_pad w" unfolding w' by (rule adj_sq_TM_dec)
  from l have pad: "strip_exp_pad w' = strip_exp_pad w" unfolding w' by (rule adj_sq_exp_pad)
  let ?Mw = "dec_TM_pad w"
  interpret TM ?Mw .

    \<comment> \<open>Both of the following statements are not provable without further assumptions
        about the contents of \<^term>\<open>w\<close> (and thus \<^term>\<open>dec_TM_pad w\<close>).\<close>
  have a: "rejects w' = rejects w" sorry
  have b: "time_bounded_word T w' = time_bounded_word T w" sorry
  have "w' \<in>\<^sub>L L\<^sub>D \<longleftrightarrow> w \<in>\<^sub>L L\<^sub>D" unfolding L\<^sub>D_def by (simp add: dec pad a b Let_def)
  oops

lemma L\<^sub>D'_adj_sq_iff:
  fixes w
  assumes l: "length w \<ge> 20"
  defines w': "w' \<equiv> adj_sq\<^sub>w w"
  shows "w' \<in>\<^sub>L L\<^sub>D' \<longleftrightarrow> w \<in>\<^sub>L L\<^sub>D'"
proof -
  from l have dec: "dec_TM_pad w' = dec_TM_pad w" unfolding w' by (rule adj_sq_TM_dec)
  from l have pad: "strip_exp_pad w' = strip_exp_pad w" unfolding w' by (rule adj_sq_exp_pad)
  show "w' \<in>\<^sub>L L\<^sub>D' \<longleftrightarrow> w \<in>\<^sub>L L\<^sub>D'" unfolding L\<^sub>D'_def member_lang_iff' dec pad by blast
qed

lemma L\<^sub>D'_L\<^sub>0'_adj_sq_iff:
  fixes w
  assumes l: "length w \<ge> 20"
  defines "w' \<equiv> adj_sq\<^sub>w w"
  shows "w' \<in>\<^sub>L L\<^sub>0' \<longleftrightarrow> w \<in>\<^sub>L L\<^sub>D'"
proof
  assume "w \<in>\<^sub>L L\<^sub>D'"
  then have "w' \<in>\<^sub>L L\<^sub>D'" unfolding w'_def using l by (subst L\<^sub>D'_adj_sq_iff)
  moreover have "w' \<in>\<^sub>L SQ" unfolding w'_def by (rule adj_sq_word_correct)
  ultimately show "w' \<in>\<^sub>L L\<^sub>0'" unfolding L\<^sub>0'_def by simp
next
  assume "w' \<in>\<^sub>L L\<^sub>0'"
  then have "w' \<in>\<^sub>L L\<^sub>D'" unfolding L\<^sub>0'_def by simp
  then show "w \<in>\<^sub>L L\<^sub>D'" unfolding w'_def using l by (subst (asm) L\<^sub>D'_adj_sq_iff)
qed


text\<open>For now assume that this result will hold for some version of \<open>L\<^sub>D\<close> and \<open>L\<^sub>0\<close>.\<close>

lemma L\<^sub>D_L\<^sub>0_adj_sq_iff:
  fixes w
  assumes l: "length w \<ge> 20"
  defines "w' \<equiv> adj_sq\<^sub>w w"
  shows "w' \<in>\<^sub>L L\<^sub>0 \<longleftrightarrow> w \<in>\<^sub>L L\<^sub>D"
  sorry


text\<open>From @{cite rassOwf2017}:
 ``Lemma 4.6. Let \<open>t\<close>, \<open>T\<close> be as in Assumption 4.4 and assume \<open>T(n) \<ge> n\<^sup>3\<close>.
  Then, there exists a language \<open>L\<^sub>0 \<in> DTIME(T) - DTIME(t)\<close> for which \<open>dens\<^sub>L\<^sub>0(x) \<le> \<surd>x\<close>.''\<close>

lemma L0_t: "L\<^sub>0 \<notin> DTIME(t)"
proof (rule ccontr, unfold not_not)
  assume "L\<^sub>0 \<in> DTIME(t)"

  have "L\<^sub>D \<in> DTIME(t)"
  proof - (* (rule reduce_DTIME) *)
    have I: "\<forall>\<^sub>\<infinity>w. (adj_sq\<^sub>w w \<in>\<^sub>L L\<^sub>0 \<longleftrightarrow> w \<in>\<^sub>L L\<^sub>D) \<and> (length (adj_sq\<^sub>w w) \<le> length w)"
    proof (intro ae_word_length_finiteI conjI)
      fix w :: "bool list"
      assume "length w \<ge> 20"
      then show "adj_sq\<^sub>w w \<in>\<^sub>L L\<^sub>0 \<longleftrightarrow> w \<in>\<^sub>L L\<^sub>D" by (fact L\<^sub>D_L\<^sub>0_adj_sq_iff)
      from \<open>length w \<ge> 20\<close> have "length w \<ge> 9" by simp
      then show "length (adj_sq\<^sub>w w) \<le> length w"
        by (intro eq_imp_le sh_msbD) (fact adj_sq_sh_pfx_half)
    qed

    have II: "\<forall>N. \<exists>n. \<forall>m\<ge>n. N \<le> t m / m" sorry
    \<comment> \<open>This is not correct, since \<^term>\<open>t\<close> could be arbitrarily small.
      Let \<open>t(n) = n\<close> and \<open>T(n) = n\<^sup>3\<close>. Then \<open>DTIME(t)\<close> is limited by \<open>tcomp t n = n + 1\<close>
      and \<open>DTIME(T)\<close> by \<open>tcomp t n = n\<^sup>3\<close> (for \<open>n > 1\<close>).\<close>

    have III: "computable_in_time TYPE(nat) t adj_sq\<^sub>w" sorry
    \<comment> \<open>Assume that \<^const>\<open>adj_sq\<^sub>w\<close> can be computed by a TM in time \<open>n\<^sup>3\<close>.\<close>

    have IV: \<open>L\<^sub>0 \<in> DTIME(t)\<close> by fact

    from I II III IV show ?thesis sorry
  qed

  moreover from time_hierarchy have "L\<^sub>D \<notin> DTIME(t)" ..
  ultimately show False by contradiction
qed

(* TODO move to Complexity.thy *)
lemma DTIME_int: "L\<^sub>1 \<in> DTIME(T\<^sub>1) \<Longrightarrow> L\<^sub>2 \<in> DTIME(T\<^sub>2) \<Longrightarrow> L\<^sub>1 \<inter>\<^sub>L L\<^sub>2 \<in> DTIME(\<lambda>n. T\<^sub>1 n + T\<^sub>2 n)" sorry

lemma L0_T: "L\<^sub>0 \<in> DTIME(T)"
proof -
  define T' where "T' \<equiv> \<lambda>n. T n + n^3"

  from time_hierarchy have "L\<^sub>D \<in> DTIME T" ..
  with SQ_DTIME have "L\<^sub>0 \<in> DTIME(T')" unfolding T'_def L\<^sub>0_def of_nat_add by (intro DTIME_int)
  then have "L\<^sub>0 \<in> DTIME(tcomp (\<lambda>n. 2 * real (T n)))"
  proof (rule DTIME_mono_ae)
    show "\<forall>\<^sub>\<infinity>n. T' n \<le> tcomp (\<lambda>n. 2 * real (T n)) n" unfolding T'_def
    proof (ae_nat_elim add: T_lower_bound)
      fix n
      assume "n \<ge> 2" and "n ^ 3 \<le> T n"
      then have "T n + n ^ 3 \<le> max (n + 1) (2 * T n)" by linarith
      also have "... = tcomp (\<lambda>n. real (2 * T n)) n" unfolding tcomp_nat_simps ..
      also have "... = tcomp (\<lambda>n. 2 * real (T n)) n" by simp
      finally show "T n + n ^ 3 \<le> tcomp (\<lambda>n. 2 * real (T n)) n" .
    qed
  qed
  then have "L\<^sub>0 \<in> DTIME(tcomp T)"
  proof (elim DTIME_speed_up_rev)
    show "superlinear T" by (fact T_superlinear)
  qed simp
  with T_ge_tcomp_T_ae show "L\<^sub>0 \<in> DTIME(T)" by (elim DTIME_mono_ae) ae_nat_elim
qed


\<comment> \<open>Alternative proof for \<open>L\<^sub>0 \<in> DTIME(T)\<close> without the need for the Speed-Up Theorem.
  This version of @{thm DTIME_int} should work, if multiple tapes may be used.\<close>

(* TODO move to Complexity.thy *)
lemma DTIME_int': "L\<^sub>1 \<in> DTIME(T\<^sub>1) \<Longrightarrow> L\<^sub>2 \<in> DTIME(T\<^sub>2) \<Longrightarrow> L\<^sub>1 \<inter>\<^sub>L L\<^sub>2 \<in> DTIME(\<lambda>n. max (T\<^sub>1 n) (T\<^sub>2 n))" sorry

lemma L0_T': "L\<^sub>0 \<in> DTIME(T)"
proof -
  from time_hierarchy have "L\<^sub>D \<in> DTIME T" ..
  with SQ_DTIME have "L\<^sub>0 \<in> DTIME(\<lambda>n. max (T n) (n^3))" unfolding L\<^sub>0_def by (intro DTIME_int')
  then show "L\<^sub>0 \<in> DTIME(T)"
  proof (rule DTIME_mono_ae)
    show "\<forall>\<^sub>\<infinity>n. max (T n) (n^3) \<le> T n" by (ae_nat_elim add: T_lower_bound) simp
  qed
qed

theorem L0_time_hierarchy: "L\<^sub>0 \<in> DTIME(T) - DTIME(t)" using L0_T L0_t ..

theorem dens_L0: "dens L\<^sub>0 n \<le> dsqrt n"
  unfolding L\<^sub>0_def dens_SQ[symmetric]
  using dens_intersect_le .

lemmas lemma4_6 = L0_time_hierarchy dens_L0

end \<comment> \<open>\<^locale>\<open>tht_sq_assms\<close>\<close>

end
