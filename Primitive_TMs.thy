theory Primitive_TMs
  imports Complexity
begin

definition read_TM_rec :: "nat \<Rightarrow> 's set \<Rightarrow> ('s option option, 's, 's option) TM_record"
  where "read_TM_rec k \<Sigma> \<equiv> \<lparr>
    TM_record.tape_count = k,
    symbols = \<Sigma>,
    states = options (options \<Sigma>),
    initial_state = None,
    final_states = Some ` options \<Sigma>,
    label = \<lambda>q. the q,
    next_state = \<lambda>q hds. Some (hd hds),
    next_write = \<lambda>q hds i. hds ! i,
    next_move  = \<lambda>q hds i. No_Shift
  \<rparr>"

lemma read_TM_rec_valid:
  assumes "k > 0"
    and "finite \<Sigma>"
    and "\<Sigma> \<noteq> {}"
  shows "valid_TM (read_TM_rec k \<Sigma>)" unfolding read_TM_rec_def
proof (intro valid_TM_I)
  fix q hds
  assume "length hds = k" and "set hds \<subseteq> options \<Sigma>"
  with \<open>k > 0\<close> show "Some (hd hds) \<in> options (options \<Sigma>)" by auto

  fix i
  assume "i < k"
  with \<open>length hds = k\<close> and \<open>set hds \<subseteq> options \<Sigma>\<close> show "hds ! i \<in> options \<Sigma>" by fastforce
qed (use assms in blast)+


definition "read_TM_M k \<Sigma> \<equiv> Abs_TM (read_TM_rec k \<Sigma>)"

locale read_TM = TM "Abs_TM (read_TM_rec k \<Sigma>)"
  for k :: nat and \<Sigma> :: "'s set" +
  assumes at_least_one_tape: "k > 0"
    and finite_symbols: "finite \<Sigma>"
    and nonempty_symbols: "\<Sigma> \<noteq> {}"
begin

lemma M_rec: "M_rec = read_TM_rec k \<Sigma>" using read_TM_rec_valid[OF at_least_one_tape finite_symbols nonempty_symbols]
  by (intro Abs_TM_inverse CollectI)

lemma M_fields:
  shows "tape_count \<equiv> k"
    and "symbols \<equiv> \<Sigma>"
    and "Q \<equiv> options (options \<Sigma>)"
    and "q\<^sub>0 \<equiv> None"
    and "F \<equiv> Some ` options \<Sigma>"
    and "label \<equiv> the"
    and "\<delta>\<^sub>q \<equiv> \<lambda>q hds. Some (hd hds)"
    and "\<delta>\<^sub>w \<equiv> \<lambda>q. (!)"
    and "\<delta>\<^sub>m \<equiv> \<lambda>q hds i. No_Shift"
  unfolding TM_fields_defs M_rec unfolding read_TM_rec_def TM_record.simps .

declare M_fields(1-6)[simp]


lemma step:
  assumes "state c = q\<^sub>0"
    and "wf_config c"
  shows "step c = TM_config (Some (head (hd (tapes c)))) (tapes c)"
  using assms
proof (induction c)
  case (TM_config q tps)
  let ?c = "TM_config q tps"
  let ?h = "head (hd tps)"

  assume "state ?c = q\<^sub>0"
  then have [simp]: "q = q\<^sub>0" by simp
  assume "wf_config ?c"
  from wf_configD(2)[OF this] have [simp]: "length tps = tape_count" by simp
  from \<open>wf_config ?c\<close> have "tps \<noteq> []" by force

  have "step ?c = step_not_final ?c" by force
  also have "... = TM_config (Some ?h) tps"
  proof (rule TM_config_eq, unfold step_not_final_simps TM_config.sel)
    show "\<delta>\<^sub>q q (map head tps) = Some ?h" unfolding M_fields list.map_sel[OF \<open>tps \<noteq> []\<close>] ..

    show "map2 tape_action (\<delta>\<^sub>a q (map head tps)) tps = tps"
    proof (rule step_not_final_eqI)
      fix i
      assume "i < tape_count"
      then have "i < length tps" by simp
      then show "tape_action (\<delta>\<^sub>w q (map head tps) i, \<delta>\<^sub>m q (map head tps) i) (tps ! i) = tps ! i"
        unfolding M_fields by simp
    qed auto
  qed
  also have "... = TM_config (Some (head (hd (tapes ?c)))) (tapes ?c)" by simp
  finally show ?case .
qed


lemma
  assumes "state c = q\<^sub>0"
    and "wf_config c"
  shows "is_final (step c)"
    and "conf_label (step c) = head (hd (tapes c))"
    and "tapes (step c) = tapes c"
proof -
  show [simp]: "tapes (step c) = tapes c" unfolding step[OF assms] by simp
  have [simp]: "state (step c) = Some (head (hd (tapes c)))" unfolding step[OF assms] by simp

  from \<open>wf_config c\<close> have "head (hd (tapes c)) \<in> \<Sigma>\<^sub>t\<^sub>p" by fastforce
  then show "is_final (step c)" unfolding is_final_def by simp

  show "conf_label (step c) = head (hd (tapes c))" by simp
qed

end \<comment> \<open>\<^locale>\<open>read_TM\<close>\<close>

end
