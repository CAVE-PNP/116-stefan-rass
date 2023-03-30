theory TM_While
  imports TM Complexity
begin

locale TM_while = base: TM M\<^sub>B for M\<^sub>B :: "('q, 's, 'l option) TM"
begin


abbreviation (input) "while_TM_next_state q hds \<equiv>
    if q \<in> base.F then q else
    let q' = base.next_state q hds in
    if q' \<in> base.F \<and> base.label q' = None then base.q\<^sub>0 else q'"

definition while_TM_rec :: "('q, 's, 'l) TM_record"
  where "while_TM_rec \<equiv> \<lparr>
    TM_record.tape_count = base.k,
    symbols = base.\<Sigma>,
    states = base.Q,
    initial_state = (\<lambda>TODO. TODO) base.q\<^sub>0,
    final_states = {q \<in> base.F. base.label q \<noteq> None},
    label = \<lambda>q. the (base.label q),
    next_state = while_TM_next_state,
    next_write = \<lambda>q hds i. if q \<in> base.F then hds ! i else base.next_write q hds i,
    next_move  = \<lambda>q hds i. if q \<in> base.F then No_Shift else base.next_move q hds i
  \<rparr>"

lemma valid_while_TM: "valid_TM while_TM_rec" unfolding while_TM_rec_def
  by (intro valid_TM_I) (auto simp: Let_def split: if_split)

definition "M \<equiv> Abs_TM while_TM_rec"

sublocale TM M .

lemma M_rec: "M_rec = while_TM_rec" unfolding M_def using valid_while_TM by (intro Abs_TM_inverse CollectI)
lemmas M_fields = TM_fields_defs[unfolded M_rec while_TM_rec_def TM_record.simps Let_def]
lemmas [simp] = M_fields(1-6)


subsubsection\<open>Setup\<close>

lemma wf_config_eq[simp]: "wf_config c \<longleftrightarrow> base.wf_config c" unfolding TM.wf_config_def by simp

lemma next_actions_eq: "\<not> base.is_final c \<Longrightarrow> \<delta>\<^sub>a (state c) (heads c) = base.\<delta>\<^sub>a (state c) (heads c)"
  unfolding TM.next_actions_altdef M_fields TM.is_final_def by presburger

lemma step_nf_tapes_eq[simp, intro]: "\<not> base.is_final c \<Longrightarrow> tapes (step_not_final c) = tapes (base.step_not_final c)"
  by (simp add: next_actions_eq)

lemma next_state_eq'[simp, intro]:
  assumes "\<not> base.is_final (base.step c)"
  shows "state (step_not_final c) = state (base.step_not_final c)"
proof -
  from assms have nf': "\<not> base.is_final c" by blast
  with assms have "base.\<delta>\<^sub>q (state c) (heads c) \<notin> base.F" by blast
  with nf' show ?thesis unfolding TM.is_final_def TM.step_not_final_simps M_fields by presburger
qed

lemma is_final_imp[dest]: "is_final c \<Longrightarrow> base.is_final c" unfolding TM.is_final_def by simp
lemma not_final_imp[dest]: "\<not> base.is_final c \<Longrightarrow> \<not> is_final c" by blast

lemma while_step_not_final:
  assumes step_nf: "\<not> base.is_final (base.step c)"
    and "base.wf_config c"
  shows "step c = base.step c"
proof -
  from step_nf have nf: "\<not> base.is_final c" by blast
  then have "step c = step_not_final c" by blast
  also from step_nf nf have "... = base.step_not_final c" by (blast intro: TM_config_eq)
  also from nf have "... = base.step c" by simp
  finally show ?thesis .
qed

lemma while_steps_not_final1:
  assumes steps_nf: "\<not> base.is_final (base.steps n c)"
    and wf: "base.wf_config c"
  shows "steps n c = base.steps n c"
proof (use steps_nf in \<open>induction n\<close>)
  case (Suc n')
  from Suc.prems have "base.is_not_final (base.steps n' c)" by force
  with Suc.IH have IH: "steps n' c = base.steps n' c" by blast

  have "steps (Suc n') c = step (steps n' c)" unfolding funpow.simps comp_def ..
  also have "... = step (base.steps n' c)" unfolding IH ..
  also have "... = base.step (base.steps n' c)"
  proof (rule while_step_not_final)
    from Suc.prems show "\<not> base.is_final (base.step (base.steps n' c))" unfolding funpow.simps comp_def .
    from wf show "base.wf_config (base.steps n' c)" by blast
  qed
  also have "... = base.steps (Suc n') c" by simp
  finally show "steps (Suc n') c = base.steps (Suc n') c" .
qed \<comment> \<open>case \<open>n = 0\<close> by\<close> simp

corollary while_steps_not_final2:
  assumes "n < base.config_time c"
    and [simp]: "base.wf_config c"
  shows "steps n c = base.steps n c"
  using assms by (blast intro!: while_steps_not_final1)

lemma while_steps_not_final3:
  assumes "\<not> base.is_final c"
    and "base.halts_config c"
    and wfc[simp]: "base.wf_config c"
  defines "n \<equiv> base.config_time c"
  defines "n' \<equiv> n - 1"
  shows "n = Suc n'"
    and "steps n' c = base.steps n' c"
    and "\<not> base.is_final (steps n' c)"
proof -
  from \<open>\<not> base.is_final c\<close> have "\<not> base.is_final (base.steps 0 c)" by simp
  with \<open>base.halts_config c\<close> have "n > 0" unfolding n_def by blast
  then show "n = Suc n'" unfolding n'_def by simp
  then have "n' < n" by blast
  then show g2: "steps n' c = base.steps n' c" using wfc
    unfolding n_def by (fact while_steps_not_final2)
  from \<open>n' < n\<close> show "\<not> base.is_final (steps n' c)" unfolding n_def g2 by blast
qed

lemma while_step_loop:
  assumes nf': "\<not> base.is_final c"
    and step_final: "base.is_final (base.step c)"
    and loop': "base.conf_label (base.step c) = None"
    and wf: "base.wf_config c"
  shows "step c = TM_config q\<^sub>0 (tapes (base.step c))"
  (is "step c = ?c\<^sub>0 (base.step c)")
proof -
  from nf' have nf: "\<not> is_final c" ..
  with loop' have loop: "base.label (base.\<delta>\<^sub>q (state c) (heads c)) = None"
    unfolding TM.step_not_final[OF nf'] by simp

  from nf have "step c = step_not_final c" by blast
  also have "... = ?c\<^sub>0 (base.step_not_final c)"
  proof (rule TM_config_eq, unfold TM_config.sel)
    from step_final have "base.\<delta>\<^sub>q (state c) (heads c) \<in> base.F" using nf' by fastforce
    with nf' loop show "state (step_not_final c) = q\<^sub>0" by (simp add: M_fields(7) TM.is_final_def)
    from nf' show "tapes (step_not_final c) = tapes (base.step_not_final c)" by blast
  qed
  also from nf' have "... = ?c\<^sub>0 (base.step c)" by simp
  finally show ?thesis .
qed

theorem while_steps_loop:
  fixes c
  defines "n \<equiv> base.config_time c"
  assumes nf: "\<not> base.is_final c"
    and halts: "base.halts_config c"
    and wfc[simp]: "base.wf_config c"
    and loop: "base.conf_label (base.steps n c) = None"
  shows "steps n c = TM_config q\<^sub>0 (tapes (base.steps n c))"
proof -
  define n' where "n' = n - 1"
  from nf halts wfc have "n = Suc n'" and steps_eq: "steps n' c = base.steps n' c"
    unfolding n'_def n_def by (fact while_steps_not_final3)+

  have *: "TM.steps M n c = TM.step M (TM.steps M n' c)" for M :: "('x, 'y, 'z) TM" and c
    unfolding \<open>n = Suc n'\<close> funpow.simps comp_def ..

  show ?thesis unfolding * steps_eq
  proof (rule while_step_loop)
    have "n' < n" unfolding \<open>n = Suc n'\<close> ..
    then show "\<not> base.is_final (base.steps n' c)" unfolding n_def ..
    from \<open>base.halts_config c\<close> show "base.is_final (base.step (base.steps n' c))"
      unfolding *[symmetric] n_def by blast
    from loop show "base.label (state (base.step (base.steps n' c))) = None"
      unfolding \<open>n = Suc n'\<close> funpow.simps comp_def .
  qed fastforce
qed

lemma while_step_done:
  assumes nf': "\<not> base.is_final c"
    and step_final: "base.is_final (base.step c)"
    and done': "base.conf_label (base.step c) \<noteq> None"
    and wf: "base.wf_config c"
  shows "step c = base.step c"
    and "is_final (step c)"
    and "conf_label (step c) = the (base.conf_label (base.step c))" (is "_ = the ?l")
proof -
  from nf' have nf: "\<not> is_final c" ..
  with done' have done'': "base.label (base.\<delta>\<^sub>q (state c) (heads c)) \<noteq> None"
    unfolding TM.step_not_final[OF nf'] by simp

  from nf have "step c = step_not_final c" by blast
  also have "... = base.step_not_final c"
  proof (rule TM_config_eq)
    from step_final have "base.\<delta>\<^sub>q (state c) (heads c) \<in> base.F" using nf' by fastforce
    with nf' done'' show "state (step_not_final c) = state (base.step_not_final c)"
      unfolding TM.step_not_final_simps M_fields TM.is_final_def by presburger
    from nf' show "tapes (step_not_final c) = tapes (base.step_not_final c)" by blast
  qed
  also from nf' have "... = base.step c" by simp
  finally show h1[simp]: "step c = base.step c" .

  show "conf_label (step c) = the ?l" by simp

  from done' obtain l where l: "?l = Some l" by blast
  with step_final show "is_final (step c)" by force
qed

theorem while_steps_done:
  fixes c
  defines "n \<equiv> base.config_time c"
  assumes nf: "\<not> base.is_final c"
    and halts: "base.halts_config c"
    and wfc[simp]: "base.wf_config c"
    and done': "base.conf_label (base.steps n c) \<noteq> None"
  shows "steps n c = base.steps n c"
    and "is_final (steps n c)"
    and "conf_label (steps n c) = the (base.conf_label (base.steps n c))" (is "_ = the ?l")
proof -
  define n' where "n' = n - 1"
  from nf halts wfc have "n = Suc n'"
    and steps_eq: "steps n' c = base.steps n' c"
    and steps_nf: "\<not> base.is_final (steps n' c)"
    unfolding n'_def n_def by (fact while_steps_not_final3)+

  note * = steps_eq \<open>n = Suc n'\<close> funpow.simps comp_def

  from halts have "base.is_final (base.steps n c)" unfolding n_def ..
  then have f: "base.is_final (base.step (steps n' c))" by (unfold *)
  from done' have done'': "base.label (state (base.step (steps n' c))) \<noteq> None" by (unfold *)
  from wfc have wfc': "base.wf_config (steps n' c)" unfolding steps_eq ..

  from steps_nf f done'' wfc' show "steps n c = base.steps n c" and "is_final (steps n c)"
    and "conf_label (steps n c) = the ?l" unfolding * by (fact while_step_done)+
qed

end \<comment> \<open>\<^locale>\<open>TM_while\<close>\<close>

end
