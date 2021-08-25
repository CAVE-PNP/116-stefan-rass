theory imp_eq_of_bool_le
  imports Main
begin


lemma "(P \<longrightarrow> Q) \<longleftrightarrow> (of_bool P \<le> of_bool Q)" nitpick oops

lemma "of_bool False \<le> of_bool False" nitpick oops
lemma "of_bool False \<le> of_bool True" nitpick oops

\<comment> \<open>The statement does not hold (universally),
  so we need to "inject" the required type classes for \<^const>\<open>of_bool\<close>.

  \<^class>\<open>zero_neq_one\<close> is required as \<^const>\<open>of_bool\<close> is defined in this class.
  \<^class>\<open>zero_less_one\<close> for \<^term>\<open>of_bool False \<le> of_bool True\<close>.

  \<^class>\<open>preorder\<close> would be required for \<^term>\<open>of_bool P \<le> of_bool P\<close>,
  but is subsumed in \<^class>\<open>zero_less_one\<close> through \<^class>\<open>order\<close>.\<close>

lemma imp_eq_of_bool_le:
  "(P \<longrightarrow> Q) \<longleftrightarrow> (of_bool P \<le> (of_bool Q :: 'a :: {zero_neq_one, zero_less_one}))"
proof (induction P; induction Q; simp)
  from zero_less_one show "(0::'a) \<le> 1" "\<not> (1::'a) \<le> 0" unfolding less_le_not_le by blast+
qed


\<comment> \<open>A version where at least the goal is slightly more readable:\<close>

lemma imp_eq_of_bool_le':
  fixes P Q :: bool
  defines "(p :: 'a :: {zero_neq_one, zero_less_one}) \<equiv> of_bool P"
  defines "(q :: 'a) \<equiv> of_bool Q"
  shows "(P \<longrightarrow> Q) \<longleftrightarrow> (p \<le> q)"
  unfolding p_def q_def
  by (rule imp_eq_of_bool_le)


\<comment> \<open>For specific types, such as \<^typ>\<open>nat\<close> or \<^typ>\<open>int\<close>, showing this is substantially simpler.\<close>

lemma imp_eq_of_bool_le_nat:
  fixes P Q :: bool
  shows "(P \<longrightarrow> Q) \<longleftrightarrow> (of_bool P \<le> (of_bool Q :: nat))"
  by force


end
