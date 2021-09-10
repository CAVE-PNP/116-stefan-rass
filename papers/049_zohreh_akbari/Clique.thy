theory Clique
  imports "Graph_Theory.Graph_Theory"
    "Supplementary/Graph"
begin

subsection\<open>Clique\<close>

(*
undirected graph = graph (Digraph.thy)
complete graph = complete_digraph (Kuratowsky.thy)
clique
maximum clique
largest subgraph of G in which alpha exists
*)

definition (in pre_digraph) clique :: "'a set \<Rightarrow> bool"
  where "clique C \<equiv> C \<subseteq> verts G \<and> complete_digraph (card C) (G \<restriction> C)"

definition (in pre_digraph) max_clique :: "'a set"
  where "max_clique = (ARG_MAX card S. clique S)"

definition (in pre_digraph) least_degree_vertex :: "'a"
  where "least_degree_vertex = (ARG_MIN (out_degree G) \<alpha>. \<alpha> \<in> verts G)"

definition (in pre_digraph) neighbors :: "'a \<Rightarrow> 'a set"
  where "neighbors \<alpha> = {v. v = \<alpha> \<or> \<alpha> \<rightarrow>\<^bsub>G\<^esub> v \<or> v \<rightarrow>\<^bsub>G\<^esub> \<alpha>}"

definition (in pre_digraph) neighborhood :: "'a \<Rightarrow> ('a, 'b) pre_digraph"
  where "neighborhood \<alpha> = G \<restriction> neighbors \<alpha>"


lemma (in fin_digraph) least_degree_vertex_ex:
  assumes "verts G \<noteq> {}"
  shows "least_degree_vertex \<in> verts G"
  using arg_min_if_finite(1) finite_verts assms unfolding least_degree_vertex_def arg_min_on_def .


lemma (in pre_digraph) neighborI:
  shows neighbor_selfI: "\<alpha> \<in> verts (neighborhood \<alpha>)"
    and neighbor_inI: "\<alpha> \<rightarrow>\<^bsub>G\<^esub> v \<Longrightarrow> v \<in> verts (neighborhood \<alpha>)"
    and neighbor_outI: "v \<rightarrow>\<^bsub>G\<^esub> \<alpha> \<Longrightarrow> v \<in> verts (neighborhood \<alpha>)"
unfolding neighborhood_def neighbors_def by simp_all

lemma (in pre_digraph) neighborE:
  assumes "v \<in> verts (neighborhood \<alpha>)"
  shows "v = \<alpha> \<or> \<alpha> \<rightarrow>\<^bsub>G\<^esub> v \<or> v \<rightarrow>\<^bsub>G\<^esub> \<alpha>"
  using assms unfolding neighborhood_def neighbors_def by simp

lemma (in pre_digraph) nb_altdef: "neighbors \<alpha> = ({\<alpha>} \<union> {v. \<alpha> \<rightarrow>\<^bsub>G\<^esub> v} \<union> {v. v \<rightarrow>\<^bsub>G\<^esub> \<alpha>})"
  unfolding neighbors_def by auto

lemma (in pre_digraph) nbh_altdef: "neighborhood \<alpha> = G \<restriction> ({\<alpha>} \<union> {v. \<alpha> \<rightarrow>\<^bsub>G\<^esub> v} \<union> {v. v \<rightarrow>\<^bsub>G\<^esub> \<alpha>})"
  unfolding neighborhood_def using nb_altdef by simp


lemma (in graph) empty_clique: "clique {}" unfolding clique_def complete_digraph_def
proof (intro conjI)
  show "{} \<subseteq> verts G" by (rule empty_subsetI)

  let ?E = "G \<restriction> {}"
  have v: "verts ?E = {}" and a: "arcs ?E = {}" by auto
  then show "graph ?E" by (rule graph_emptyI)
  show "card (verts ?E) = card {}" unfolding v by simp
  show "arcs_ends ?E = {(u, v). (u, v) \<in> verts ?E \<times> verts ?E \<and> u \<noteq> v}"
    unfolding v arcs_ends_def induce_subgraph_arcs by simp
qed

lemma (in graph) singleton_clique: "v \<in> verts G \<Longrightarrow> clique {v}"
  unfolding clique_def complete_digraph_def
proof (intro conjI)
  assume "v \<in> verts G"
  then show "{v} \<subseteq> verts G" by blast

  let ?H = "G \<restriction> {v}"
  have *:"card (verts ?H) = 1" by simp
  then show "card (verts ?H) = card {v}" by simp

  from \<open>{v} \<subseteq> verts G\<close> have "induced_subgraph ?H G" by (rule induced_induce)
  then show "graph ?H"
    by (intro digraph.graphI digraphI_induced sym_digraph.sym_arcs induced_graph_imp_graph)
  have "arcs_ends ?H = {}"
    using wellformed_induce_subgraph no_loops by fastforce
  then show "arcs_ends ?H = {(u, w). (u, w) \<in> verts ?H \<times> verts ?H \<and> u \<noteq> w}"
    using * by simp
qed


end
