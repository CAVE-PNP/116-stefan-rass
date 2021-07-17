theory Graph_Induct
  imports "Graph_Theory.Graph_Theory"
begin

lemma (in fin_digraph) arcs_induct [case_names empty delete]:
  assumes "\<And>H. arcs H = {} \<Longrightarrow> P H"
      and "\<And>H a. a \<in> arcs H \<Longrightarrow> P (H\<lparr> arcs := arcs H - {a} \<rparr>) \<Longrightarrow> P H"
    shows "P G"
proof -
  have "\<forall>A \<subseteq> arcs G. P (G\<lparr>arcs := A\<rparr>)" proof safe
    fix A assume "A \<subseteq> arcs G"
    then have "finite A" using finite_subset[of A] by simp
    then show "P (G\<lparr>arcs:=A\<rparr>)" using assms by (induction rule: finite_induct) force+
  qed
  thus ?thesis by fastforce
qed
    
end