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
  where "clique C = complete_digraph (card C) (G \<restriction> C)"

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


end
