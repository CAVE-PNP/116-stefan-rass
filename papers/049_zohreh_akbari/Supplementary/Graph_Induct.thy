theory Graph_Induct
  imports "Graph_Theory.Graph_Theory"
begin

subsubsection\<open>over Arcs\<close>

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


subsubsection\<open>over Vertices\<close>

definition (in pre_digraph) is_empty :: "bool"
  where "is_empty \<equiv> verts G = {}"

declare is_empty_def[simp] pre_digraph.is_empty_def[simp]


lemma (in fin_digraph) verts_induct [case_names empty delete]:
  assumes "\<And>G. pre_digraph.is_empty G \<Longrightarrow> P G"
    and "\<And>G v. P (G \<restriction> (verts G - {v})) \<Longrightarrow> P G"
  shows "P G"
  using finite_verts
proof (induction "verts G" arbitrary: G rule: finite_induct)
  case empty
  with assms(1) show "P G" by simp
next
  case (insert x F)
  let ?G = "G \<restriction> (verts G - {x})"

  from \<open>x \<notin> F\<close> have "F = verts ?G" by (fold \<open>insert x F = verts G\<close>) simp
  with \<open>\<And>G. F = verts G \<Longrightarrow> P G\<close> have "P ?G" .
  with assms(2) show "P G" .
qed

lemma card_singleton[simp]: "card {x} = 1" by simp
lemma finite_singleton[simp]: "finite {x}" by blast

lemma (in fin_digraph) verts_induct_non_empty [consumes 1, case_names singleton delete]:
  assumes "\<not> is_empty"
    and "\<And>G. is_singleton (verts G) \<Longrightarrow> P G"
    and "\<And>G v. P (G \<restriction> (verts G - {v})) \<Longrightarrow> P G"
  shows "P G"
  using assms(1) finite_verts (* these are required induction premises *)
proof (induction rule: verts_induct)
  case (delete G v) thus ?case
  proof (cases "card (verts G) > 1")
    case False (* G is singleton *)
    then have "card (verts G) = 1 \<or> card (verts G) = 0" by force
    with delete.prems have "card (verts G) = 1" by force
    then have "is_singleton (verts G)" by (unfold is_singleton_altdef)
    with assms(2) show "P G" .
  next
    let ?G = "G \<restriction> (verts G - {v})" and ?non_empty = "\<lambda>G. \<not> pre_digraph.is_empty G"
    case True (* G has at least two members *)
    then have "0 < card (verts G) - card {v}" by force
    also have "... \<le> card (verts G - {v})" using finite_singleton by (rule diff_card_le_card_Diff)
    finally have "verts G - {v} \<noteq> {}" unfolding card_gt_0_iff by blast
    then have "?non_empty ?G" by simp
    moreover have "finite (verts ?G)" using delete.prems by simp
    ultimately have "P ?G" by (rule delete.IH)
    with assms(3) show "P G" .
  qed
qed (* case "empty" by *) contradiction


end