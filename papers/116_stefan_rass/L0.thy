theory L0
  imports Complexity
begin


section\<open>Time Hierarchy Theorem and the Diagonal Language\<close>

locale tht_assms =
  fixes T t :: "nat \<Rightarrow> nat"
  assumes fully_tconstr_T: "fully_tconstr T"
    and T_dominates_t: "lim (\<lambda>l. t l * log 2 (t l) / T l) = 0"
  \<comment> \<open>The following assumption is not found in the paper or the primary source (Hopcroft),
    but is taken from the AAU lecture slides of \<^emph>\<open>Algorithms and Complexity Theory\<close>.
    It patches a hole that allows one to prove \<^term>\<open>False\<close> from the Time Hierarchy Theorem below
    (\<open>time_hierarchy\<close>).
    This is demonstrated in \<^file>\<open>../../isa_examples/THT_inconsistencies_MWE.thy\<close>.\<close>
    and "\<And>n. n \<le> t n"
begin


text\<open>\<open>L\<^sub>D\<close>, defined as part of the proof for the Time Hierarchy Theorem.

  "The “diagonal-language” \<open>L\<^sub>D\<close> is thus defined over the alphabet \<open>\<Sigma> = {0, 1}\<close> as
       \<open>LD := {w \<in> \<Sigma>\<^sup>*: M\<^sub>w halts and rejects w within \<le> T(len(w)) steps}\<close>.    (9)"\<close>

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

lemma L\<^sub>DE[elim]:
  fixes w
  assumes "w \<in> L\<^sub>D"
  defines "M\<^sub>w \<equiv> TM_decode_pad w"
  shows "rejects M\<^sub>w w"
    and "halts M\<^sub>w w"
    and "time_bounded_word T M\<^sub>w w"
proof -
  from \<open>w \<in> L\<^sub>D\<close> show "rejects M\<^sub>w w" unfolding M\<^sub>w_def LD_def Let_def by blast
  then show "halts M\<^sub>w w" unfolding rejects_def halts_def by (rule hoare_true)
  from \<open>w \<in> L\<^sub>D\<close> show "time_bounded_word T M\<^sub>w w"
    unfolding M\<^sub>w_def LD_def Let_def mem_Collect_eq ..
qed

lemma L\<^sub>D'E[elim]:
  fixes w
  assumes "w \<in> L\<^sub>D'"
  defines "M\<^sub>w \<equiv> TM_decode_pad w"
    and "w' \<equiv> strip_al_prefix (strip_exp_pad w)"
  shows "rejects M\<^sub>w w'"
    and "halts M\<^sub>w w'"
    and "time_bounded_word T M\<^sub>w w'"
proof -
  from \<open>w \<in> L\<^sub>D'\<close> show "rejects M\<^sub>w w'" unfolding M\<^sub>w_def LD'_def w'_def Let_def by blast
  then show "halts M\<^sub>w w'" by (rule rejects_halts)
  from \<open>w \<in> L\<^sub>D'\<close> show "time_bounded_word T M\<^sub>w w'"
    unfolding M\<^sub>w_def LD'_def w'_def Let_def mem_Collect_eq ..
qed

theorem time_hierarchy: "L\<^sub>D \<in> DTIME(T) - DTIME(t)"
proof
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
    and *: "\<And>w. if L\<^sub>D_P w then accepts M w else rejects M w" sorry (* probably out of scope *)
  have "decides M L\<^sub>D" unfolding decides_altdef4 LD_def mem_Collect_eq L\<^sub>D_P_def[symmetric] using * ..
  with \<open>time_bounded T M\<close> show "L\<^sub>D \<in> DTIME(T)" by blast


  have "L \<noteq> L\<^sub>D" if "L \<in> DTIME(t)" for L
  proof -
    from \<open>L \<in> DTIME(t)\<close> obtain M where "decides M L" and "time_bounded t M" ..
    define w' where "w' = encode_TM M"

    let ?n = "length (encode_TM M) + 2"
    obtain l where "T(2*l) \<ge> t(2*l)" and "clog l \<ge> ?n"
    proof -
      from T_dominates_t obtain l\<^sub>1 :: nat where l1: "l \<ge> l\<^sub>1 \<Longrightarrow> T l \<ge> t l" for l sorry (* TODO *)
      obtain l\<^sub>2 :: nat where l2: "l \<ge> l\<^sub>2 \<Longrightarrow> clog l \<ge> ?n" for l sorry (* TODO *)

      let ?l = "max l\<^sub>1 l\<^sub>2"
      have "T (2*?l) \<ge> t (2*?l)" by (rule l1) force
      moreover have "clog ?l \<ge> ?n" by (rule l2) force

      ultimately show ?thesis by (intro that)
    qed

    have "tm_wf0 M" sorry (* ??? *)
    then obtain w where "length w = l" and "TM_decode_pad w = M"
      using \<open>clog l \<ge> ?n\<close> by (rule embed_TM_in_len)

    define M\<^sub>w where "M\<^sub>w \<equiv> TM_decode_pad w"
    have "M\<^sub>w = M" unfolding M\<^sub>w_def by (fact \<open>TM_decode_pad w = M\<close>)
    have "L(M\<^sub>w) = L" unfolding \<open>M\<^sub>w = M\<close> using \<open>decides M L\<close> by (rule decidesE)

    have "w \<in> L(M\<^sub>w) \<longleftrightarrow> w \<notin> L\<^sub>D"
    proof
      assume "w \<in> L(M\<^sub>w)"
      then have "w \<in> L" unfolding \<open>L(M\<^sub>w) = L\<close> .
      moreover from \<open>decides M L\<close> have "w \<notin> L \<longleftrightarrow> rejects M w" unfolding decides_def by blast
      ultimately have "\<not> rejects M w" by blast
  
      then show "w \<notin> L\<^sub>D" unfolding LD_def mem_Collect_eq
        unfolding \<open>TM_decode_pad w = M\<close> Let_def de_Morgan_conj ..
    next
      assume "w \<notin> L\<^sub>D"                                                                    
      moreover have "time_bounded_word T M w"
      proof (rule time_bounded_word_mono)
        from \<open>T(2*l) \<ge> t(2*l)\<close> show "real (T (tape_size <w>\<^sub>t\<^sub>p)) \<ge> real (t (tape_size <w>\<^sub>t\<^sub>p))"
          unfolding tape_size_input \<open>length w = l\<close> by (rule of_nat_mono)
        from \<open>time_bounded t M\<close> show "time_bounded_word t M w" ..
      qed
      ultimately have "\<not> rejects M\<^sub>w w" unfolding \<open>M\<^sub>w = M\<close>[symmetric]
        unfolding LD_def mem_Collect_eq Let_def M\<^sub>w_def by blast
      with \<open>decides M L\<close> show "w \<in> L(M\<^sub>w)" unfolding \<open>L(M\<^sub>w) = L\<close> decides_def
        unfolding \<open>M\<^sub>w = M\<close> by blast
    qed
    then show "L \<noteq> L\<^sub>D" unfolding \<open>L(M\<^sub>w) = L\<close> by blast
  qed
  then show "L\<^sub>D \<notin> DTIME(t)" by blast
qed

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

  have T_superlinear: "\<forall>N. \<exists>n'. \<forall>n\<ge>n'. T(n)/n \<ge> N"
  proof (intro allI exI impI)
    fix N :: real and n :: nat
    let ?n' = "nat \<lceil>N\<rceil>"
    assume "?n' \<le> n"

    have "N \<le> ?n'" by (rule real_nat_ceiling_ge)
    also have "... \<le> n" using \<open>?n' \<le> n\<close> by (rule of_nat_mono)
    also have "... \<le> n\<^sup>2" by (rule of_nat_mono) (rule power2_nat_le_imp_le, rule le_refl)
    also have "n\<^sup>2 = n powr (3 - 1)" by force
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

\<comment> \<open>Alternative proof for \<open>\<close> without the need for the Speed-Up Theorem.
  This version of @{thm DTIME_int} should work, if multiple tapes may be used.\<close>

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

end \<comment> \<open>\<^locale>\<open>tht_sq_assms\<close>\<close>

end
