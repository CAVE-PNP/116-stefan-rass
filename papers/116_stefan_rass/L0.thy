theory L0
  imports Complexity
begin


section\<open>Time Hierarchy Theorem and the Diagonal Language\<close>

locale tht_assms =
  fixes T t :: "nat \<Rightarrow> nat"
  assumes "fully_tconstr T"
    and "lim (\<lambda>l. t l * log 2 (t l) / T l) = 0"
begin


text\<open>\<open>L\<^sub>D\<close>, defined as part of the proof for the Time Hierarchy Theorem.

  "The “diagonal-language” \<open>L\<^sub>D\<close> is thus defined over the alphabet \<open>\<Sigma> = {0, 1}\<close> as
       \<open>LD := {w \<in> \<Sigma>\<^sup>*: M\<^sub>w halts and rejects w within \<le> T(len(w)) steps}\<close>.    (9)"\<close>

definition L\<^sub>D :: "lang"
  where LD_def[simp]: "L\<^sub>D \<equiv> {w. let M\<^sub>w = TM_decode_pad w in
                  rejects M\<^sub>w w \<and> the (time M\<^sub>w <w>\<^sub>t\<^sub>p) \<le> tcomp\<^sub>w T w}"

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
                  rejects M\<^sub>w w' \<and> the (time M\<^sub>w <w'>\<^sub>t\<^sub>p) \<le> tcomp\<^sub>w T w}"

lemma L\<^sub>DE[elim]:
  fixes w
  assumes "w \<in> L\<^sub>D"
  defines "M\<^sub>w \<equiv> TM_decode_pad w"
  shows "rejects M\<^sub>w w"
    and "halts M\<^sub>w w"
    and "the (time M\<^sub>w <w>\<^sub>t\<^sub>p) \<le> tcomp\<^sub>w T w"
    and "\<exists>n. time M\<^sub>w <w>\<^sub>t\<^sub>p = Some n \<and> n \<le> tcomp\<^sub>w T w"
proof -
  from \<open>w \<in> L\<^sub>D\<close> show "rejects M\<^sub>w w" unfolding M\<^sub>w_def LD_def Let_def by blast
  then show "halts M\<^sub>w w" unfolding rejects_def halts_def by (rule hoare_true)

  define n where "n = the (time M\<^sub>w <w>\<^sub>t\<^sub>p)"
  from \<open>w \<in> L\<^sub>D\<close> show time_T: "the (time M\<^sub>w <w>\<^sub>t\<^sub>p) \<le> tcomp\<^sub>w T w"
    unfolding M\<^sub>w_def LD_def Let_def by blast
  then have "n \<le> tcomp\<^sub>w T w" unfolding n_def .
  moreover from \<open>halts M\<^sub>w w\<close> have "time M\<^sub>w <w>\<^sub>t\<^sub>p = Some n" unfolding n_def halts_altdef by force
  ultimately show "\<exists>n. time M\<^sub>w <w>\<^sub>t\<^sub>p = Some n \<and> n \<le> tcomp\<^sub>w T w" by blast
qed

lemma L\<^sub>D'E[elim]:
  fixes w
  assumes "w \<in> L\<^sub>D'"
  defines "M\<^sub>w \<equiv> TM_decode_pad w"
    and "w' \<equiv> strip_al_prefix (strip_exp_pad w)"
  shows "rejects M\<^sub>w w'"
    and "halts M\<^sub>w w'"
    and "the (time M\<^sub>w <w'>\<^sub>t\<^sub>p) \<le> tcomp\<^sub>w T w"
    and "\<exists>n. time M\<^sub>w <w'>\<^sub>t\<^sub>p = Some n \<and> n \<le> tcomp\<^sub>w T w"
proof -
  from \<open>w \<in> L\<^sub>D'\<close> show "rejects M\<^sub>w w'" unfolding M\<^sub>w_def LD'_def w'_def Let_def by blast
  then show "halts M\<^sub>w w'" unfolding rejects_def halts_def by (rule hoare_true)

  define n where "n = the (time M\<^sub>w <w'>\<^sub>t\<^sub>p)"
  from \<open>w \<in> L\<^sub>D'\<close> show time_T: "the (time M\<^sub>w <w'>\<^sub>t\<^sub>p) \<le> tcomp\<^sub>w T w"
    unfolding M\<^sub>w_def LD'_def w'_def Let_def by blast
  then have "n \<le> tcomp\<^sub>w T w" unfolding n_def .
  moreover from \<open>halts M\<^sub>w w'\<close> have "time M\<^sub>w <w'>\<^sub>t\<^sub>p = Some n" unfolding n_def halts_altdef by force
  ultimately show "\<exists>n. time M\<^sub>w <w'>\<^sub>t\<^sub>p = Some n \<and> n \<le> tcomp\<^sub>w T w" by blast
qed

theorem time_hierarchy: "L\<^sub>D \<in> DTIME T - DTIME t" sorry

end \<comment> \<open>\<^locale>\<open>tht_assms\<close>\<close>


section\<open>\<open>L\<^sub>0\<close>\<close>

text\<open>From the proof of Lemma 4.6, p14:

   "To retain \<open>L\<^sub>D \<inter> SQ \<in> DTIME(T)\<close>, we must choose \<open>T\<close> so large that the decision
    \<open>w \<in> SQ\<close> is possible within the time limit incurred by \<open>T\<close>, so we add \<open>T(n) \<ge> n\<^sup>3\<close>
    to our hypothesis besides Assumption 4.4 (note that we do not need an optimal
    complexity bound here)."\<close>

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
    unfolding l by (elim sh_msbE[symmetric])+

  have "strip_exp_pad w' = drop (l - clog l) w'" unfolding strip_exp_pad_def l_eq Let_def ..
  also have "... = drop (l - clog l) w" using d_eq .
  also have "... = strip_exp_pad w" unfolding strip_exp_pad_def l[symmetric] Let_def ..
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
  assumes "length w \<ge> 20"
  defines "w' \<equiv> adj_sq\<^sub>w w"
  shows "w' \<in> L\<^sub>D \<longleftrightarrow> w \<in> L\<^sub>D"
    \<comment> \<open>Idea: since \<open>w\<close> and \<open>adj_sq\<^sub>w n\<close> share their prefix (@{thm adj_sq_sh_pfx_log}),
  the relevant parts are identical and this lemma should hold.

  Note: with the current definition of \<^const>\<open>L\<^sub>D\<close>, this likely does not hold,
        as the whole word \<open>w\<close> is referenced in the definition.\<close>
  oops


lemma L\<^sub>D'_adj_sq_iff:
  fixes w
  assumes l: "length w \<ge> 20"
  defines w': "w' \<equiv> adj_sq\<^sub>w w"
  shows "w' \<in> L\<^sub>D' \<longleftrightarrow> w \<in> L\<^sub>D'"
proof -
  from \<open>length w \<ge> 20\<close> have "shared_MSBs (clog (length w)) w w'" unfolding w' by (rule adj_sq_sh_pfx_log)
  then have "length w' = length w" by (elim sh_msbE[symmetric])
  then have len: "tape_size <w'>\<^sub>t\<^sub>p = tape_size <w>\<^sub>t\<^sub>p" unfolding tape_size_input by (rule arg_cong)
  from l have dec: "TM_decode_pad w' = TM_decode_pad w" unfolding w' by (rule adj_sq_TM_dec)
  from l have pad: "strip_exp_pad w' = strip_exp_pad w" unfolding w' by (rule adj_sq_exp_pad)
  show "w' \<in> L\<^sub>D' \<longleftrightarrow> w \<in> L\<^sub>D'" unfolding LD'_def mem_Collect_eq unfolding dec pad len ..
qed

lemma L\<^sub>D'_L\<^sub>0'_adj_sq_iff:
  fixes w
  assumes l: "length w \<ge> 20"
  defines "w' \<equiv> adj_sq\<^sub>w w"
  shows "w \<in> L\<^sub>D' \<longleftrightarrow> w' \<in> L\<^sub>0'"
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


\<comment> \<open>For now assume that this result will hold for some version of \<open>L\<^sub>D\<close> and \<open>L\<^sub>0\<close>.\<close>

lemma L\<^sub>D_L\<^sub>0_adj_sq_iff:
  fixes w
  assumes l: "length w \<ge> 20"
  defines "w' \<equiv> adj_sq\<^sub>w w"
  shows "w \<in> L\<^sub>D \<longleftrightarrow> w' \<in> L\<^sub>0"
  sorry


text\<open>Lemma 4.6. Let \<open>t\<close>, \<open>T\<close> be as in Assumption 4.4 and assume \<open>T(n) \<ge> n\<^sup>3\<close>.
  Then, there exists a language \<open>L\<^sub>0 \<in> DTIME(T) - DTIME(t)\<close> for which \<open>dens\<^sub>L\<^sub>0(x) \<le> \<surd>x\<close>.\<close>

lemma L0_t: "L\<^sub>0 \<notin> DTIME(t)"
proof (rule ccontr, unfold not_not)
  assume "L\<^sub>0 \<in> DTIME(t)"
  then obtain M\<^sub>0 where "decides M\<^sub>0 L\<^sub>0" and "time_bounded t M\<^sub>0" ..

  \<comment> \<open>Assume that \<^const>\<open>adj_sq\<^sub>w\<close> can be realized by a TM in time \<open>n\<^sup>3\<close>.\<close>
  define T\<^sub>R where "T\<^sub>R \<equiv> \<lambda>n::nat. n^3"
  obtain M\<^sub>R where "tm_wf0 M\<^sub>R"
    and "\<And>w. {input w} M\<^sub>R {input (adj_sq\<^sub>w w)}"
    and "time_bounded T\<^sub>R M\<^sub>R"
    sorry

  define M where "M \<equiv> M\<^sub>R |+| M\<^sub>0"
  define t' where "t' = (\<lambda>n. real (tcomp T\<^sub>R n + tcomp t n))"

  have "L\<^sub>D \<in> DTIME(t')"
  proof (intro DTIME_ae word_length_ae)
    fix w :: word
    assume "length w \<ge> 20"
    then have "length (adj_sq\<^sub>w w) \<le> length w"
      by (intro eq_imp_le sh_msbE[symmetric]) (rule adj_sq_sh_pfx_log)
    from \<open>length w \<ge> 20\<close> have "w \<in> L\<^sub>D \<longleftrightarrow> adj_sq\<^sub>w w \<in> L\<^sub>0" by (rule L\<^sub>D_L\<^sub>0_adj_sq_iff)

    from \<open>decides M\<^sub>0 L\<^sub>0\<close> have "decides_word M\<^sub>0 L\<^sub>0 (adj_sq\<^sub>w w)" ..
    then show "decides_word M L\<^sub>D w" unfolding M_def
      using \<open>w \<in> L\<^sub>D \<longleftrightarrow> adj_sq\<^sub>w w \<in> L\<^sub>0\<close> \<open>{input w} M\<^sub>R {input (adj_sq\<^sub>w w)}\<close> \<open>tm_wf0 M\<^sub>R\<close>
      by (rule reduce_decides)

    from \<open>time_bounded t M\<^sub>0\<close> have "time_bounded_word t M\<^sub>0 (adj_sq\<^sub>w w)" ..
    moreover from \<open>time_bounded T\<^sub>R M\<^sub>R\<close> have "time_bounded_word T\<^sub>R M\<^sub>R w" ..
    ultimately show "time_bounded_word t' M w" unfolding M_def t'_def
      using \<open>{input w} M\<^sub>R {input (adj_sq\<^sub>w w)}\<close> \<open>length (adj_sq\<^sub>w w) \<le> length w\<close>
      by (rule reduce_time_bounded)
  qed

  then have "L\<^sub>D \<in> DTIME(t)" sorry
  \<comment> \<open>This is not correct, since \<^term>\<open>t\<close> could be arbitrarily small.
    Let \<open>t(n) = n\<close> and \<open>T(n) = n\<^sup>3\<close>. Then \<open>DTIME(t)\<close> is limited by \<open>tcomp t n = n + 1\<close>
    and \<open>DTIME(T)\<close> by \<open>tcomp t n = n\<^sup>3\<close> (for \<open>n > 1\<close>).\<close>

  moreover from time_hierarchy have "L\<^sub>D \<notin> DTIME(t)" ..
  ultimately show False by contradiction
qed


lemma SQ_DTIME: "SQ \<in> DTIME(\<lambda>n. n^3)" sorry
lemma DTIME_int: "L\<^sub>1 \<in> DTIME(T\<^sub>1) \<Longrightarrow> L\<^sub>2 \<in> DTIME(T\<^sub>2) \<Longrightarrow> L\<^sub>1 \<inter> L\<^sub>2 \<in> DTIME(\<lambda>n. T\<^sub>1 n + T\<^sub>2 n)" sorry

lemma L0_T: "L\<^sub>0 \<in> DTIME(T)"
proof -
  define T' :: "nat \<Rightarrow> real" where "T' \<equiv> \<lambda>n. T n + n^3"
  have "T' n \<le> 2 * T n" for n unfolding T'_def
    using T_lower_bound by (intro of_nat_mono) force

  \<comment> \<open>The following is required for use of the speed-up-theorem (@{thm DTIME_speed_up_eq}).
    It likely does not hold given the current assumptions of \<^const>\<open>tht_assms\<close>.\<close>
  have *: "\<forall>N. \<exists>n'. \<forall>n\<ge>n'. T(n)/n \<ge> N" sorry

  from time_hierarchy have "L\<^sub>D \<in> DTIME T" ..
  then have "L\<^sub>0 \<in> DTIME(T')" unfolding T'_def L0_def of_nat_add
    using SQ_DTIME by (rule DTIME_int)
  with \<open>\<And>n. T' n \<le> 2 * T n\<close> have "L\<^sub>0 \<in> DTIME(\<lambda>n. 2 * T n)" by (rule in_dtime_mono)
  then show "L\<^sub>0 \<in> DTIME(T)" unfolding of_nat_mult
    using * by (subst (asm) DTIME_speed_up_eq) linarith
qed

theorem L0_time_hierarchy: "L\<^sub>0 \<in> DTIME(T) - DTIME(t)" using L0_T L0_t ..

theorem dens_L0: "dens L\<^sub>0 n \<le> dsqrt n"
proof -
  have "dens L\<^sub>0 n = dens (L\<^sub>D \<inter> SQ) n" unfolding L0_def ..
  also have "... \<le> dens SQ n" by (subst Int_commute) (rule dens_intersect_le)
  also have "... = dsqrt n" by (rule dens_SQ)
  finally show ?thesis .
qed

end \<comment> \<open>\<^locale>\<open>tht_sq_assms\<close>\<close>


corollary False
proof -
  define T :: "nat \<Rightarrow> nat" where "T \<equiv> \<lambda>n. 1"
  let ?L = "tht_assms.L\<^sub>D T"

  have "fully_tconstr T" unfolding fully_tconstr_def T_def
    by (intro exI allI impI) (rule rej_TM_time)
  moreover have "lim (\<lambda>l. T l * log 2 (T l) / T l) = 0" unfolding T_def by force
  ultimately have "?L \<in> DTIME(T) - DTIME(T)" by (intro tht_assms.time_hierarchy tht_assms.intro)
  then show False by blast
qed

end
