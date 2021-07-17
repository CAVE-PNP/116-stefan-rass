theory Graph_Induct
  imports "Graph_Theory.Graph_Theory"
begin

lemma (in fin_digraph) arcs_induct [case_names empty insert]:
  assumes "P (G \<lparr>arcs:={}\<rparr>)"
      and "\<And>A a. A \<subseteq> arcs G \<Longrightarrow> a \<in> arcs G \<Longrightarrow> a \<notin> A \<Longrightarrow> P (G \<lparr> arcs := A \<rparr>) \<Longrightarrow> P (G \<lparr> arcs := insert a A \<rparr>)"
    shows "P G"
proof -
 have "\<forall>A \<subseteq> arcs G. P (G\<lparr>arcs := A\<rparr>)" proof safe
    fix A assume "A \<subseteq> arcs G"
    then have "finite A" using finite_subset[of A] by simp
    then show "P (G\<lparr>arcs:=A\<rparr>)" using \<open>A \<subseteq> arcs G\<close> assms by (induction rule: finite_induct; simp)
 qed
 thus ?thesis by fastforce
qed
    
end