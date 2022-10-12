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

end
