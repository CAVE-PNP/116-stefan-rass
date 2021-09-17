theory TM
  imports Main
begin

record ('a, 'b) TM =
  k :: nat (*number of tapes*)

  states :: "'a set"
  start_state :: 'a
  final_states :: "'a set"

  symbols :: "'b set"
  blank :: 'b
  
  next_state :: "'a \<Rightarrow> (nat \<Rightarrow> 'b) \<Rightarrow> 'a"
  next_action:: "'a \<Rightarrow> (nat \<Rightarrow> 'b) \<Rightarrow> nat \<Rightarrow> int"
  next_write :: "'a \<Rightarrow> (nat \<Rightarrow> 'b) \<Rightarrow> nat \<Rightarrow> 'b"

record ('a, 'b) TM_config =
  state :: 'a
  head  :: "nat \<Rightarrow> int"
  tape  :: "nat \<Rightarrow> int \<Rightarrow> 'b"

locale wf_TM =
  fixes M :: "('a, 'b) TM" (structure)
  assumes "1 \<le> k M"
      and "finite (states M)" "start_state M \<in> states M" "final_states M \<subseteq> states M"
      and "finite (symbols M)" "blank M \<in> (symbols M)"
      and "\<forall>state\<in>states M. \<forall>head. next_state M state head \<in> states M"
      and "\<forall>state\<in>states M. \<forall>head. \<forall>tape<k M. next_write M state head tape \<in> symbols M"
      and "\<forall>state\<in>states M. \<forall>head. \<forall>tape<k M. next_action M state head tape \<in> {-1,0,1}"
begin
definition step :: "('a, 'b) TM_config \<Rightarrow> ('a, 'b) TM_config" where
  "step c = (let q=state c; w=(\<lambda>n. tape c n (head c n)) in \<lparr>
      state=next_state M q w,
      head=(\<lambda>n. head c n + next_action M q w n),
      tape=(\<lambda>n. fun_upd (tape c n) (head c n) (next_write M q w n))
   \<rparr>)"
end \<comment> \<open>\<^locale>\<open>wf_TM\<close>\<close>

end