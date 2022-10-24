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

lemma M_rec: "M_rec = read_TM_rec k \<Sigma>"
  using read_TM_rec_valid[OF at_least_one_tape finite_symbols nonempty_symbols]
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
  shows "step c = TM_config (Some (head (hd (tapes c)))) (tapes c)" using assms
proof (induction c)
  case (TM_config q tps)
  let ?c = "TM_config q tps"
  let ?h = "head (hd tps)"

  from \<open>state ?c = q\<^sub>0\<close> have [simp]: "q = q\<^sub>0" by simp
  from wf_configD(2)[OF \<open>wf_config ?c\<close>] have [simp]: "length tps = tape_count" by simp
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


definition write_TM_rec :: "'s option \<Rightarrow> nat \<Rightarrow> 's set \<Rightarrow> (bool, 's, unit) TM_record"
  where "write_TM_rec \<sigma> k \<Sigma> \<equiv> \<lparr>
    TM_record.tape_count = k,
    symbols = \<Sigma>,
    states = UNIV,
    initial_state = False,
    final_states = {True},
    label = \<lambda>q. (),
    next_state = \<lambda>q hds. True,
    next_write = \<lambda>q hds i. if i = 0 then \<sigma> else hds ! i,
    next_move  = \<lambda>q hds i. No_Shift
  \<rparr>"

lemma write_TM_rec_valid:
  assumes "k > 0"
    and "finite \<Sigma>"
    and "\<Sigma> \<noteq> {}"
    and "\<sigma> \<in> options \<Sigma>"
  shows "valid_TM (write_TM_rec \<sigma> k \<Sigma>)" unfolding write_TM_rec_def
proof (intro valid_TM_I)
  show "finite (UNIV :: bool set)" by simp

  fix q hds i
  assume "hds ! i \<in> options \<Sigma>"
  with \<open>\<sigma> \<in> options \<Sigma>\<close> show "(if i = 0 then \<sigma> else hds ! i) \<in> options \<Sigma>" by (cases rule: ifI) blast
qed (use assms in blast)+



definition "write_TM_M \<sigma> k \<Sigma> \<equiv> Abs_TM (write_TM_rec \<sigma> k \<Sigma>)"

locale write_TM = TM "Abs_TM (write_TM_rec \<sigma> k \<Sigma>)"
  for \<sigma> :: "'s option" and k :: nat and \<Sigma> :: "'s set" +
  assumes at_least_one_tape: "k > 0"
    and finite_symbols: "finite \<Sigma>"
    and nonempty_symbols: "\<Sigma> \<noteq> {}"
    and write_valid: "\<sigma> \<in> options \<Sigma>"
begin

lemma M_rec: "M_rec = write_TM_rec \<sigma> k \<Sigma>"
  using write_TM_rec_valid[OF at_least_one_tape finite_symbols nonempty_symbols write_valid]
  by (intro Abs_TM_inverse CollectI)

lemma M_fields:
  shows "tape_count \<equiv> k"
    and "symbols \<equiv> \<Sigma>"
    and "Q \<equiv> UNIV"
    and "q\<^sub>0 \<equiv> False"
    and "F \<equiv> {True}"
    and "label \<equiv> \<lambda>q. ()"
    and "\<delta>\<^sub>q \<equiv> \<lambda>q hds. True"
    and "\<delta>\<^sub>w \<equiv> \<lambda>q hds i. (if i = 0 then \<sigma> else hds ! i)"
    and "\<delta>\<^sub>m \<equiv> \<lambda>q hds i. No_Shift"
  unfolding TM_fields_defs M_rec unfolding write_TM_rec_def TM_record.simps .

declare M_fields(2-6)[simp]


lemma step:
  assumes "state c = q\<^sub>0"
    and "wf_config c"
  shows "step c = TM_config True (tape_write \<sigma> (hd (tapes c)) # tl (tapes c))" using assms
proof (induction c)
  case (TM_config q tps)
  let ?c = "TM_config q tps"
    and ?h = "head (hd tps)"
    and ?tps' = "tape_write \<sigma> (hd tps) # tl tps"

  from \<open>state ?c = q\<^sub>0\<close> have [simp]: "q = q\<^sub>0" by simp
  from wf_configD(2)[OF \<open>wf_config ?c\<close>] have [simp]: "length tps = tape_count" by simp
  from \<open>wf_config ?c\<close> have "tps \<noteq> []" by force

  have "step ?c = step_not_final ?c" by force
  also have "... = TM_config True ?tps'"
  proof (rule TM_config_eq, unfold step_not_final_simps TM_config.sel)
    let ?hds = "map head tps"
    show "\<delta>\<^sub>q q ?hds = True" unfolding M_fields ..

    from \<open>tps \<noteq> []\<close> show "map2 tape_action (\<delta>\<^sub>a q ?hds) tps = ?tps'"
    proof (intro step_not_final_eqI, unfold length_Cons)
      from \<open>length tps = tape_count\<close> show "Suc (length (tl tps)) = tape_count" by simp

      fix i
      assume "i < tape_count"
      then show "tape_action (\<delta>\<^sub>w q ?hds i, \<delta>\<^sub>m q ?hds i) (tps ! i) = ?tps' ! i"
      proof (induction i)
        case 0
        with \<open>tps \<noteq> []\<close> show ?case unfolding M_fields by (simp add: if_P hd_conv_nth)
      next
        case (Suc i)
        from \<open>Suc i < tape_count\<close> have "Suc i < length tps" by simp
        then have "i < length (tl tps)" unfolding length_tl less_diff_conv by simp
        from nth_tl[OF this] and \<open>Suc i < length tps\<close> show ?case unfolding M_fields by simp
      qed
    qed auto
  qed
  finally show ?case unfolding TM_config.sel .
qed


lemma
  assumes "state c = q\<^sub>0"
    and "wf_config c"
  shows "is_final (step c)"
    and "head (hd (tapes (step c))) = \<sigma>"
proof -
  have [simp]: "tapes (step c) = tape_write \<sigma> (hd (tapes c)) # tl (tapes c)" unfolding step[OF assms] by simp
  have [simp]: "state (step c) = True" unfolding step[OF assms] by simp
  show "is_final (step c)" unfolding is_final_def by simp

  show "head (hd (tapes (step c))) = \<sigma>" by simp
qed

end \<comment> \<open>\<^locale>\<open>write_TM\<close>\<close>


definition move_TM_rec :: "nat \<Rightarrow> 's set \<Rightarrow> head_move \<Rightarrow> (bool, 's, unit) TM_record"
  where "move_TM_rec k \<Sigma> m \<equiv> \<lparr>
    TM_record.tape_count = k,
    symbols = \<Sigma>,
    states = UNIV,
    initial_state = False,
    final_states = {True},
    label = \<lambda>q. (),
    next_state = \<lambda>q hds. True,
    next_write = \<lambda>q hds i. hds ! i,
    next_move  = \<lambda>q hds i. if i = 0 then m else No_Shift
  \<rparr>"

lemma move_TM_rec_valid:
  assumes "k > 0"
    and "finite \<Sigma>"
    and "\<Sigma> \<noteq> {}"
  shows "valid_TM (move_TM_rec k \<Sigma> m)" unfolding move_TM_rec_def
proof (intro valid_TM_I)
  fix q hds i
  assume "length hds = k" and "set hds \<subseteq> options \<Sigma>" and "i < k"
  with \<open>length hds = k\<close> and \<open>set hds \<subseteq> options \<Sigma>\<close> show "hds ! i \<in> options \<Sigma>" by fastforce
qed (use assms finite_UNIV in blast)+


definition "move_TM_M k \<Sigma> m \<equiv> Abs_TM (move_TM_rec k \<Sigma> m)"

locale move_TM = TM "move_TM_M k \<Sigma> m"
  for k :: nat and \<Sigma> :: "'s set" and m :: head_move +
  assumes at_least_one_tape: "k > 0"
    and finite_symbols: "finite \<Sigma>"
    and nonempty_symbols: "\<Sigma> \<noteq> {}"
begin

lemma M_rec: "M_rec = move_TM_rec k \<Sigma> m" unfolding move_TM_M_def
  using move_TM_rec_valid[OF at_least_one_tape finite_symbols nonempty_symbols]
  by (intro Abs_TM_inverse CollectI)

lemma M_fields:
  shows "tape_count \<equiv> k"
    and "symbols \<equiv> \<Sigma>"
    and "Q \<equiv> UNIV"
    and "q\<^sub>0 \<equiv> False"
    and "F \<equiv> {True}"
    and "label \<equiv> \<lambda>q. ()"
    and "\<delta>\<^sub>q \<equiv> \<lambda>q hds. True"
    and "\<delta>\<^sub>w \<equiv> \<lambda>q. (!)"
    and "\<delta>\<^sub>m \<equiv> \<lambda>q hds i. if i = 0 then m else No_Shift"
  unfolding TM_fields_defs M_rec unfolding move_TM_rec_def TM_record.simps .

declare M_fields(1-6)[simp]


lemma step:
  assumes "state c = q\<^sub>0"
    and "wf_config c"
  shows "step c = TM_config True (tape_shift m (hd (tapes c)) # tl (tapes c))" using assms
proof (induction c)
  case (TM_config q tps)
  let ?c = "TM_config q tps"
  let ?h = "head (hd tps)"
  let ?tps' = "tape_shift m (hd tps) # tl tps"

  from \<open>state ?c = q\<^sub>0\<close> have [simp]: "q = q\<^sub>0" by simp
  from wf_configD(2)[OF \<open>wf_config ?c\<close>] have "length tps = tape_count" by simp
  from \<open>wf_config ?c\<close> have "tps \<noteq> []" by force

  have "step ?c = step_not_final ?c" by force
  also have "... = TM_config True ?tps'"
  proof (rule TM_config_eq, unfold step_not_final_simps TM_config.sel)
    show "\<delta>\<^sub>q q (map head tps) = True" unfolding M_fields ..

    show "map2 tape_action (\<delta>\<^sub>a q (map head tps)) tps = ?tps'"
    proof (rule step_not_final_eqI)
      show "length tps = tape_count" by fact
      then show "length (tape_shift m (hd tps) # tl tps) = tape_count"
        unfolding len_tl_Cons[OF \<open>tps \<noteq> []\<close>] .

      fix i
      assume "i < tape_count"
      then have "i < length tps" unfolding \<open>length tps = tape_count\<close> .
      then show "tape_action (\<delta>\<^sub>w q (map head tps) i, \<delta>\<^sub>m q (map head tps) i) (tps ! i) = ?tps' ! i"
        unfolding M_fields by (cases "i = 0" rule: ifI) (auto simp: hd_conv_nth nth_tl) (* TODO tune *)
    qed
  qed
  also have "... = TM_config True (tape_shift m (hd (tapes ?c)) # tl (tapes ?c))" by simp
  finally show ?case .
qed


lemma
  assumes "state c = q\<^sub>0"
    and "wf_config c"
  shows "is_final (step c)"
proof -
  have [simp]: "state (step c) = True" unfolding step[OF assms] by simp
  then show "is_final (step c)" unfolding is_final_def by simp
qed

end \<comment> \<open>\<^locale>\<open>move_TM\<close>\<close>




locale nop_TM = move_TM k \<Sigma> No_Shift for k :: nat and \<Sigma> :: "'s set"
begin

lemma
  assumes "state c = q\<^sub>0"
    and "wf_config c"
  shows "tapes (step c) = tapes c"
proof -
  have [simp]: "tapes (step c) = hd (tapes c) # tl (tapes c)" unfolding step[OF assms] by simp
  also from \<open>wf_config c\<close> have "... = tapes c" by force
  finally show ?thesis .
qed

end \<comment> \<open>\<^locale>\<open>nop_TM\<close>\<close>

abbreviation "nop_TM_M k \<Sigma> \<equiv> move_TM_M k \<Sigma> No_Shift"


end
