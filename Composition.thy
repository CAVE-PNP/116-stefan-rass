theory Composition
  imports TM Complexity
begin

locale TM_switch = TM_abbrevs + M1: TM M1 for M1 :: "('q1, 's, 'l1) TM" +
  fixes f :: "'l1 \<Rightarrow> ('q2, 's, 'l2) TM"
  assumes f_tape_count[simp]: "\<And>l. l \<in> M1.labels \<Longrightarrow> TM.k (f l) = M1.k"
    and symbols_eq[simp]: "\<And>l. l \<in> M1.labels \<Longrightarrow> TM.\<Sigma> (f l) = M1.\<Sigma>"
begin

lemma tape_symbols_eq[simp]: "\<And>l. l \<in> M1.labels \<Longrightarrow> TM.\<Sigma>\<^sub>t\<^sub>p (f l) = M1.\<Sigma>\<^sub>t\<^sub>p" by simp

lemmas f_simps = f_tape_count symbols_eq tape_symbols_eq


abbreviation (input) "switch_TM_states \<equiv> Inl ` M1.Q \<union> Inr ` {(l,q). l \<in> M1.labels \<and> q \<in> TM.Q (f l)}"
abbreviation (input) "switch_TM_next_state q hds \<equiv>
  case q of Inl q1 \<Rightarrow>
    let q1' = M1.\<delta>\<^sub>q q1 hds in
    if q1' \<in> M1.F
    then let l = M1.label q1' in Inr (l, TM.q\<^sub>0 (f l))
    else Inl q1'
  | Inr (l, q2) \<Rightarrow> Inr (l, TM.\<delta>\<^sub>q (f l) q2 hds)"
abbreviation (input) "switch_TM_next_write q hds i \<equiv>
  case q of Inl q1 \<Rightarrow> M1.\<delta>\<^sub>w q1 hds i | Inr (l, q2) \<Rightarrow> TM.\<delta>\<^sub>w (f l) q2 hds i"
abbreviation (input) "switch_TM_next_move q hds i \<equiv>
  case q of Inl q1 \<Rightarrow> M1.\<delta>\<^sub>m q1 hds i | Inr (l, q2) \<Rightarrow> TM.\<delta>\<^sub>m (f l) q2 hds i"

definition switch_TM_rec :: "('q1 + ('l1 \<times> 'q2), 's, 'l2) TM_record"
  where "switch_TM_rec \<equiv> \<lparr>
    TM_record.tape_count = M1.k,
    symbols = M1.\<Sigma>,
    states = switch_TM_states,
    initial_state = if M1.q\<^sub>0 \<in> M1.F
                    then let l = M1.label M1.q\<^sub>0 in Inr (l, TM.q\<^sub>0 (f l))
                    else Inl M1.q\<^sub>0,
    final_states = Inr ` {(l,q). l \<in> M1.labels \<and> q \<in> TM.F (f l)},
    label = \<lambda>q. case q of Inr (l, q2) \<Rightarrow> TM.label (f l) q2,
    next_state = switch_TM_next_state,
    next_write = switch_TM_next_write,
    next_move  = switch_TM_next_move
  \<rparr>"

lemma valid_switch_TM: "valid_TM switch_TM_rec" unfolding switch_TM_rec_def
proof (intro valid_TM_I)
  let ?Q = switch_TM_states and ?\<delta>\<^sub>q = switch_TM_next_state and ?\<delta>\<^sub>w = switch_TM_next_write

  have h1: "{(l, q). l \<in> M1.labels \<and> q \<in> TM.Q (f l)} = (\<Union>l\<in>M1.labels. Pair l ` TM.Q (f l))" by blast
  have "finite (\<Union>l\<in>M1.labels. Pair l ` TM.Q (f l))" by blast
  then show "finite ?Q" unfolding h1 by blast

  show "(if M1.q\<^sub>0 \<in> M1.F then let l = M1.label M1.q\<^sub>0 in Inr (l, TM.q\<^sub>0 (f l)) else Inl M1.q\<^sub>0) \<in> ?Q"
    unfolding Let_def by (cases rule: ifI) blast+

  fix q hds
  assume q: "q \<in> ?Q"
  assume hds: "length hds = M1.k" "set hds \<subseteq> M1.\<Sigma>\<^sub>t\<^sub>p"

  show "?\<delta>\<^sub>q q hds \<in> ?Q" using q
  proof (induction q)
    case (Inl q1)
    then have q1: "q1 \<in> M1.Q" by blast
    with hds show ?case unfolding sum.case Let_def by (induction rule: ifI) blast+
  next
    case (Inr q2)
    then have "q2 \<in> {(l, q). l \<in> M1.labels \<and> q \<in> TM.Q (f l)}" by blast
    then show ?case unfolding sum.case
    proof (induction q2)
      case (Pair l q2')
      then have l: "l \<in> M1.labels" and q2': "q2' \<in> TM.Q (f l)" by blast+
      with hds have "TM.\<delta>\<^sub>q (f l) q2' hds \<in> TM.Q (f l)" by force
      with l show ?case unfolding prod.case by blast
    qed
  qed

  fix i
  assume i: "i < M1.k"

  show "?\<delta>\<^sub>w q hds i \<in> M1.\<Sigma>\<^sub>t\<^sub>p" using q
  proof (induction q)
    case (Inl q1)
    then have q1: "q1 \<in> M1.Q" by blast
    with hds i show ?case unfolding sum.case by blast
  next
    case (Inr q2)
    then have "q2 \<in> {(l, q). l \<in> M1.labels \<and> q \<in> TM.Q (f l)}" by blast
    then show ?case unfolding sum.case
    proof (induction q2)
      case (Pair l q2')
      then have l: "l \<in> M1.labels" and q2': "q2' \<in> TM.Q (f l)" by blast+
      with hds i have "TM.\<delta>\<^sub>w (f l) q2' hds i \<in> TM.\<Sigma>\<^sub>t\<^sub>p (f l)"
        by (intro TM.next_write_valid) (unfold f_simps[OF l])
      then show ?case using l by simp
    qed
  qed
qed (use M1.symbol_axioms(2) in blast)+


definition "M \<equiv> Abs_TM switch_TM_rec"

sublocale TM M .

lemma M_rec: "M_rec = switch_TM_rec" unfolding M_def using valid_switch_TM by (intro Abs_TM_inverse CollectI)
lemmas M_fields = TM_fields_defs[unfolded M_rec switch_TM_rec_def TM_record.simps Let_def]
lemmas [simp] = M_fields(1-6)


subsubsection\<open>Setup\<close>


definition cl :: "('q1, 's) TM_config \<Rightarrow> ('q1 + 'l1 \<times> 'q2, 's) TM_config"
  where "cl \<equiv> map_conf_state Inl"
definition cr :: "'l1 \<Rightarrow> ('q2, 's) TM_config \<Rightarrow> ('q1 + 'l1 \<times> 'q2, 's) TM_config"
  where "cr l \<equiv> map_conf_state (\<lambda>q2. Inr (l, q2))"

lemma cl_simps[simp]: "state (cl c) = Inl (state c)" "tapes (cl c) = tapes c" "cl (TM_config q tps) = TM_config (Inl q) tps" unfolding cl_def by auto
lemma cr_simps[simp]: "state (cr l c) = Inr (l, state c)" "tapes (cr l c) = tapes c" "cr l (TM_config q tps) = TM_config (Inr (l, q)) tps" unfolding cr_def by auto

lemma is_final_cl[simp]: "is_final (cl c) \<longleftrightarrow> False" by (auto simp: is_final_def)
lemma is_final_cr[simp]: "l \<in> M1.labels \<Longrightarrow> is_final (cr l c) \<longleftrightarrow> TM.is_final (f l) c" by (auto simp: is_final_def)


lemma wf_config_simps[simp]:
  shows wf_config_cl: "wf_config (cl c1) \<longleftrightarrow> M1.wf_config c1"
    and wf_config_cr: "l \<in> M1.labels \<Longrightarrow> wf_config (cr l c2) \<longleftrightarrow> TM.wf_config (f l) c2"
  by (fastforce elim!: TM.wf_config_transferI)+

lemma wf_config_transfer[intro,simp]:
  "l \<in> M1.labels \<Longrightarrow> M1.wf_config c \<Longrightarrow> TM.wf_config (f l) (TM_config (TM.q\<^sub>0 (f l)) (tapes c))"
  by (elim TM.wf_config_transferI) simp_all

(* the following two lemmas are pre-simplified (do not actually contain any mention of cl or cr)
   so that they will be applicable by simp *)
lemma next_fun_cl_simps[simp]:
  assumes [simp]: "M1.wf_config c"
  defines "q \<equiv> state c" and "hds \<equiv> heads c"
  defines "q' \<equiv> Inl (state c)"
  defines "l \<equiv> M1.label (M1.\<delta>\<^sub>q q hds)"
  shows "M1.\<delta>\<^sub>q q hds \<in> M1.F \<Longrightarrow> \<delta>\<^sub>q q' hds = Inr (l, TM.q\<^sub>0 (f l))"
    and "M1.\<delta>\<^sub>q q hds \<notin> M1.F \<Longrightarrow> \<delta>\<^sub>q q' hds = Inl (M1.\<delta>\<^sub>q q hds)"
    and "i < M1.k \<Longrightarrow> \<delta>\<^sub>m q' hds i = M1.\<delta>\<^sub>m q hds i"
    and "i < M1.k \<Longrightarrow> \<delta>\<^sub>w q' hds i = M1.\<delta>\<^sub>w q hds i"
  unfolding M_fields assms by auto

lemma next_fun_cr_simps[simp]:
  assumes [simp]: "TM.wf_config (f l) c"
  defines "q \<equiv> state c" and "hds \<equiv> heads c"
  defines "q' \<equiv> Inr (l, q)"
  shows "\<delta>\<^sub>q q' hds = Inr (l, TM.\<delta>\<^sub>q (f l) q hds)"
    and "i < M1.k \<Longrightarrow> \<delta>\<^sub>m q' hds i = TM.\<delta>\<^sub>m (f l) q hds i"
    and "i < M1.k \<Longrightarrow> \<delta>\<^sub>w q' hds i = TM.\<delta>\<^sub>w (f l) q hds i"
  unfolding M_fields assms by auto

lemma next_actions_simps[simp]:
  shows "M1.wf_config c1 \<Longrightarrow> \<delta>\<^sub>a (Inl (state c1)) (heads c1) = M1.\<delta>\<^sub>a (state c1) (heads c1)"
    and "l \<in> M1.labels \<Longrightarrow> TM.wf_config (f l) c2 \<Longrightarrow> \<delta>\<^sub>a (Inr (l, state c2)) (heads c2) = TM.\<delta>\<^sub>a (f l) (state c2) (heads c2)"
  unfolding TM.next_actions_altdef by auto


lemma comp_step1_not_final:
  assumes step_nf: "\<not> M1.is_final (M1.step c)"
    and [simp]: "M1.wf_config c"
  shows "step (cl c) = cl (M1.step c)" (is "step ?c = cl (M1.step c)")
proof -
  from step_nf have nf': "\<not> M1.is_final c" by blast
  then have "\<not> is_final ?c" by auto

  then have "step ?c = step_not_final ?c" by blast
  also have "... = cl (M1.step_not_final c)"
  proof (rule TM_config_eq)
    from step_nf have "M1.\<delta>\<^sub>q (state c) (heads c) \<notin> M1.F" using nf' by auto
    then show "state (step_not_final ?c) = state (cl (M1.step_not_final c))" by simp
    show "tapes (step_not_final ?c) = tapes (cl (M1.step_not_final c))" by simp
  qed
  also from nf' have "... = cl (M1.step c)" by simp
  finally show ?thesis .
qed

lemma comp_steps1_non_final:
  assumes "\<not> M1.is_final (M1.steps n c)"
    and [simp]: "M1.wf_config c"
  shows "steps n (cl c) = cl (M1.steps n c)"
proof -
  have "0 \<le> n" by (rule le0)
  then show "steps n (cl c) = cl (M1.steps n c)"
  proof (induction n rule: dec_induct)
    case (step n')
    have "steps (Suc n') (cl c) = step (steps n' (cl c))" unfolding funpow.simps comp_def ..
    also have "... = step (cl (M1.steps n' c))" unfolding step.IH ..
    also have "... = cl (M1.step (M1.steps n' c))"
    proof (rule comp_step1_not_final)
      from \<open>n' < n\<close> have "Suc n' \<le> n" by (rule Suc_leI)
      with assms have "\<not> M1.is_final (M1.steps (Suc n') c)" using M1.final_mono by blast
      then show "\<not> M1.is_final (M1.step (M1.steps n' c))" unfolding funpow.simps comp_def .
    qed fastforce
    also have "... = cl (M1.steps (Suc n') c)" by simp
    finally show *: "steps (Suc n') (cl c) = cl (M1.steps (Suc n') c)" .
  qed \<comment> \<open>case \<open>n = 0\<close> by\<close> simp
qed

corollary comp_steps1_non_final':
  assumes "n < M1.config_time c"
    and [simp]: "M1.wf_config c"
  shows "steps n (cl c) = cl (M1.steps n c)"
  using assms by (blast intro!: comp_steps1_non_final)

lemma comp_step1_next_final:
  assumes nf': "\<not> M1.is_final c"
    and step_final: "M1.is_final (M1.step c)"
    and [simp]: "M1.wf_config c"
  defines "l \<equiv> M1.label (state (M1.step c))"
  shows "step (cl c) = TM_config (Inr (l, TM.q\<^sub>0 (f l))) (tapes (M1.step c))"
  (is "step ?c = ?c\<^sub>0 (M1.step c)")
proof -
  from assms(2) have "\<not> is_final ?c" by simp

  then have "step ?c = step_not_final ?c" by blast
  also have "... = ?c\<^sub>0 (M1.step_not_final c)"
  proof (rule TM_config_eq, unfold TM_config.sel)
    from step_final have "M1.\<delta>\<^sub>q (state c) (heads c) \<in> M1.F" using nf' by fastforce
    with nf' show "state (step_not_final ?c) = Inr (l, TM.q\<^sub>0 (f l))" unfolding l_def by simp
    show "tapes (step_not_final ?c) = tapes (M1.step_not_final c)" by simp
  qed
  also from nf' have "... = ?c\<^sub>0 (M1.step c)" by simp
  finally show ?thesis .
qed

lemma comp_steps1_final:
  assumes "\<not> M1.is_final c"
    and "M1.halts_config c"
    and wfc[simp]: "M1.wf_config c"
  defines "n \<equiv> M1.config_time c"
  defines "l \<equiv> M1.label (state (M1.steps n c))"
  shows "steps n (cl c) = TM_config (Inr (l, TM.q\<^sub>0 (f l))) (tapes (M1.steps n c))"
proof -
  from \<open>\<not> M1.is_final c\<close> have "\<not> M1.is_final (M1.steps 0 c)" by simp
  with \<open>M1.halts_config c\<close> have "n > 0" unfolding n_def by blast
  then obtain n' where "n = Suc n'" by (rule lessE)
  then have "n' < n" by blast

  have *: "TM.steps M n c = TM.step M (TM.steps M n' c)" for M :: "('x, 'y, 'z) TM" and c
    unfolding \<open>n = Suc n'\<close> funpow.simps comp_def ..
  from \<open>n' < n\<close> and wfc have **: "steps n' (cl c) = cl (M1.steps n' c)"
    unfolding n_def by (rule comp_steps1_non_final')

  show ?thesis unfolding * ** l_def
  proof (intro comp_step1_next_final)
    from \<open>n' < n\<close> show "\<not> M1.is_final (M1.steps n' c)" unfolding n_def by blast
    from \<open>M1.halts_config c\<close> show "M1.is_final (M1.step (M1.steps n' c))"
      unfolding *[symmetric] n_def by blast
  qed fastforce
qed

lemma comp_step2:
  assumes [simp]: "l \<in> M1.labels"
    and [simp]: "TM.wf_config (f l) c"
  shows "step (cr l c) = cr l (TM.step (f l) c)"
proof (cases "TM.is_final (f l) c")
  assume nf: "\<not> TM.is_final (f l) c"
  then have "\<not> is_final (cr l c)" by fastforce

  then have "step (cr l c) = step_not_final (cr l c)" ..
  also have "... = cr l (TM.step_not_final (f l) c)" by (rule TM_config_eq) simp_all
  also from nf have "... = cr l (TM.step (f l) c)" by simp
  finally show ?thesis .
qed \<comment> \<open>case \<^term>\<open>TM.is_final (f l) c\<close> by\<close> simp

lemma comp_steps2:
  assumes "TM.wf_config (f l) c_init2"
    and "l \<in> M1.labels"
  shows "steps n2 (cr l c_init2) = cr l (TM.steps (f l) n2 c_init2)" using le0
proof (induction n2 rule: dec_induct)
  case (step n2)
  show ?case unfolding funpow.simps comp_def step.IH
    using assms by (blast intro: comp_step2)
qed \<comment> \<open>case \<open>n2 = 0\<close> by\<close> simp

lemma comp_steps_final:
  fixes c_init1 n1 n2
  defines "c_fin1 \<equiv> M1.steps n1 c_init1"
  defines "l \<equiv> M1.conf_label c_fin1"
  defines "c_init2 \<equiv> TM_config (TM.q\<^sub>0 (f l)) (tapes c_fin1)"
  defines "c_fin2 \<equiv> TM.steps (f l) n2 c_init2"
  assumes ci1_nf: "\<not> M1.is_final c_init1"
    and cf1: "M1.is_final c_fin1"
    and cf2: "TM.is_final (f l) c_fin2"
    and wfc1[simp]: "M1.wf_config c_init1"
  shows "steps (n1+n2) (cl c_init1) = cr l c_fin2" (is "steps ?n ?c0 = _")
proof -
  let ?n1' = "M1.config_time c_init1"
  from cf1 have "?n1' \<le> n1" unfolding c_fin1_def by blast
  from cf1 have c_fin1_altdef: "c_fin1 = M1.steps ?n1' c_init1" unfolding c_fin1_def by blast

  from ci1_nf cf1 wfc1 have "steps ?n1' ?c0 = TM_config (Inr (l, TM.q\<^sub>0 (f l))) (tapes (M1.steps ?n1' c_init1))"
    unfolding l_def c_fin1_altdef by (intro comp_steps1_final) blast+
  also from cf1 have "... = cr l c_init2" unfolding c_init2_def c_fin1_def cr_def by auto
  finally have steps_n1': "steps ?n1' ?c0 = cr l c_init2" .

  from cf1 have [intro, simp]: "l \<in> M1.labels" unfolding l_def by blast
  from wfc1 have wfc2[simp]: "TM.wf_config (f l) c_init2" unfolding c_init2_def c_fin1_def by blast

  from cf2 have "is_final (steps (n2 + ?n1') ?c0)"
    unfolding funpow_add comp_def unfolding steps_n1' c_fin2_def by (subst comp_steps2) auto
  moreover from \<open>?n1' \<le> n1\<close> have "n2 + ?n1' \<le> ?n" by simp
  ultimately have "steps ?n ?c0 = steps (n2 + ?n1') ?c0" by (rule final_le_steps)

  also have "... = steps n2 (cr l c_init2)" unfolding funpow_add comp_def steps_n1' ..
  also have "... = cr l c_fin2" unfolding c_fin2_def by (force simp: comp_steps2)
  finally show ?thesis .
qed


lemma comp_steps:
  fixes tps n1 n2
  defines "c_fin1 \<equiv> M1.steps n1 (TM_config M1.q\<^sub>0 tps)"
  assumes l_def: "l = M1.conf_label c_fin1"
  defines "c_init2 \<equiv> TM_config (TM.q\<^sub>0 (f l)) (tapes c_fin1)"
  defines "c_fin2 \<equiv> TM.steps (f l) n2 c_init2"
  assumes cf1: "M1.is_final c_fin1"
    and cf2: "TM.is_final (f l) c_fin2"
    and wf: "M1.wf_config (TM_config M1.q\<^sub>0 tps)"
  shows "steps (n1+n2) (TM_config q\<^sub>0 tps) = cr l c_fin2"
    (is "steps ?n ?c\<^sub>0 = _")
proof (cases "M1.q\<^sub>0 \<in> M1.F")
  let ?c_init1 = "TM_config M1.q\<^sub>0 tps"
  assume q0f: "M1.q\<^sub>0 \<in> M1.F"
  then have [simp]: "c_fin1 = ?c_init1" unfolding c_fin1_def by fastforce
  have [simp]: "M1.label M1.q\<^sub>0 = l" unfolding l_def by simp
  from cf1 have [simp, intro]: "l \<in> M1.labels" unfolding l_def by blast
  from wf have wf_c_init2: "TM.wf_config (f l) c_init2" unfolding \<open>c_fin1 = ?c_init1\<close> c_init2_def by blast

  from q0f have "?c\<^sub>0 = cr l c_init2" unfolding TM.initial_config_def cr_def c_init2_def by force
  then have "steps ?n ?c\<^sub>0 = steps ?n (cr l c_init2)" by (fact arg_cong)
  also have "... = cr l (TM.steps (f l) ?n c_init2)" using wf_c_init2 by (simp add: comp_steps2)
  also from cf2 have "... = cr l c_fin2" unfolding c_fin2_def by (subst TM.final_le_steps) fastforce+
  finally show ?thesis .
next
  assume nf: "M1.q\<^sub>0 \<notin> M1.F"
  then have *: "TM_config q\<^sub>0 tps = cl (TM_config M1.q\<^sub>0 tps)" by simp
  from nf have "\<not> M1.is_final (TM_config M1.q\<^sub>0 tps)" by (simp add: TM.is_final_def)
  with cf1 cf2 wf show ?thesis unfolding assms * by (intro comp_steps_final M1.wf_initial_config)
qed

end \<comment> \<open>\<^locale>\<open>TM_switch\<close>\<close>

end
