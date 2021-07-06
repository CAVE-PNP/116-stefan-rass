theory Clique
  imports "Graph_Theory.Graph_Theory" (* this requires a distribution of the AFP to be set up *)
begin

subsection\<open>Clique\<close>

(*
undirected graph = graph (Digraph.thy)
complete graph = complete_digraph (Kuratowsky.thy)
clique
maximum clique
largest subgraph of G in which alpha exists
*)

definition clique :: "('a, 'b) pre_digraph \<Rightarrow> 'a set \<Rightarrow> bool"
  where "clique G C = complete_digraph (card C) (G \<restriction> C)"

definition max_clique :: "('a, 'b) pre_digraph \<Rightarrow> 'a set"
  where "max_clique G = (ARG_MAX card S. (clique G S))"

definition least_degree_vertex :: "('a, 'b) pre_digraph \<Rightarrow> 'a"
  where "least_degree_vertex G = (ARG_MIN (\<lambda>\<alpha>. out_degree G \<alpha>) \<alpha>. (\<alpha> \<in> verts G))"

definition direct_neighborhood :: "('a, 'b) pre_digraph \<Rightarrow> 'a \<Rightarrow> ('a, 'b) pre_digraph"
  where "direct_neighborhood G \<alpha> = G \<restriction> {v\<in>verts G. v = \<alpha> \<or> \<alpha> \<rightarrow>\<^bsub>G\<^esub> v}"


subsection\<open>Helper lemmas\<close>

lemma pair_inj: "inj (Pair a)" by (intro injI) (rule Pair_inject)


lemma inj_on_arc_to_ends [simp]:
  assumes "graph G"
  shows "inj_on (arc_to_ends G) (arcs G)"
  using nomulti_digraph.inj_on_arc_to_ends and digraph.axioms(3) and graph.axioms(1) and \<open>graph G\<close> .

lemma (in graph) inj_on_arc_to_ends [simp]: (* apparently, defining this using the locale interferes with the [simp] annotation *)
  shows "inj_on (arc_to_ends G) (arcs G)"
  using local.inj_on_arc_to_ends .

lemma inj_imp_inj_on: "inj f \<Longrightarrow> inj_on f A"
  using subset_UNIV by (subst inj_on_subset) blast+

lemma complete_digraph_altdef:
  "complete_digraph n G \<longleftrightarrow> graph G \<and> n = card (verts G) \<and> (\<forall>v. v \<in> verts G \<longrightarrow> out_degree G v = n - 1)"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof (intro iffI)
  assume ?lhs
  then have lhs1: "graph G" and lhs2: "card (verts G) = n" and lhs3: "arcs_ends G = {(u, v). (u, v) \<in> verts G \<times> verts G \<and> u \<noteq> v}"
    unfolding complete_digraph_def by blast+

  let ?V = "verts G" and ?E = "arcs_ends G" and ?n = "card (verts G)"

  have "\<forall>v. v \<in> verts G \<longrightarrow> out_degree G v = n - 1"
  proof (intro allI impI)
    fix v
    assume "v \<in> verts G"

    have "out_degree G v = card (out_arcs G v)" unfolding out_degree_def ..

    also have "... = card (arc_to_ends G ` out_arcs G v)"
    proof -
      from \<open>graph G\<close> have "inj_on (arc_to_ends G) (arcs G)" by simp
      then have "inj_on (arc_to_ends G) (out_arcs G v)"
        unfolding out_arcs_def by (subst inj_on_subset) blast+
      with sym[OF card_image] show ?thesis .
    qed

    also have "... = card ((\<lambda>w. (v, w)) ` (?V - {v}))"
    proof -
      have "arc_to_ends G ` out_arcs G v = {(u, w) \<in> ?E. u = v}"
        unfolding out_arcs_def arc_to_ends_def arcs_ends_def by blast
      also have "... = {(u, w) \<in> {(u, v). (u, v) \<in> verts G \<times> verts G \<and> u \<noteq> v}. u = v}"
        unfolding lhs3 ..
      also have "... = {(u, w) \<in> verts G \<times> verts G. u \<noteq> w \<and> u = v}" by simp
      also have "... = {(v, w) | w. w \<in> ?V \<and> v \<noteq> w}" using \<open>v \<in> ?V\<close> by blast
      also have "... = {(v, w) | w. w \<in> ?V - {v}}" by blast
      also have "... = (\<lambda>w. (v, w)) ` (?V - {v})" by blast
      finally show ?thesis by (rule arg_cong)
    qed

    also have "... = card (?V - {v})"
      using pair_inj by (intro card_image) (rule inj_imp_inj_on)

    also have "... = card ?V - 1"
    proof -
      have "card {v} = 1" by simp
      have "finite {v}" and "{v} \<subseteq> ?V" using \<open>v \<in> ?V\<close> by blast+
      with card_Diff_subset[of "{v}"] show ?thesis unfolding \<open>card {v} = 1\<close> .
    qed

    finally show "out_degree G v = n - 1" unfolding \<open>card ?V = n\<close> .
  qed

  with lhs1 and lhs2 show ?rhs by blast
next
  assume ?rhs
  then have rhs1: "graph G" and rhs2: "n = card (verts G)" 
    and rhs3: "v \<in> verts G \<Longrightarrow> out_degree G v = n - 1" for v by blast+

  let ?V = "verts G" and ?E = "arcs_ends G" and ?n = "card (verts G)"

  (* show ?lhs unfolding complete_digraph_def sorry *)
  oops


end
