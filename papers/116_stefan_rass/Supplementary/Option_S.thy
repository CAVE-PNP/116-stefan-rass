theory Option_S
  imports HOL.Option Main
begin


(* Showing \<open>not_None_helper\<close> directly only works with \<open>meson\<close> and \<open>metis\<close>;
 * but when substituting \<open>y := None\<close>, many methods solve it instantly. *)
lemma not_None_helper[dest]: "None \<notin> A \<Longrightarrow> x \<in> A \<Longrightarrow> x \<noteq> None" by meson


lemma the_map_option_image: "None \<notin> A \<Longrightarrow> the ` map_option f ` A = f ` the ` A"
proof -
  assume "None \<notin> A"
  then have h1: "y = the (map_option f x) \<and> x \<in> A \<longleftrightarrow> y = f (the x) \<and> x \<in> A" for x y by auto

  have "the ` map_option f ` A = {the (map_option f x) |x. x\<in>A}" by blast
  also have "... = {f (the x) |x. x\<in>A}" unfolding h1 ..
  also have "... = f ` the ` A" by blast
  finally show ?thesis .
qed


lemma these_union[simp]: "Option.these (A \<union> B) = Option.these A \<union> Option.these B"
  unfolding Option.these_def by blast

lemma these_image[simp]: "f ` Option.these A = Option.these (map_option f ` A)"
proof -
  have "Option.these (map_option f ` A) = the ` {x \<in> map_option f ` A. x \<noteq> None}"
    by (fact Option.these_def)
  also have "... = the ` {map_option f x |x. x \<in> {x \<in> A. x \<noteq> None}}" by blast
  also have "... = the ` map_option f ` {x \<in> A. x \<noteq> None}" unfolding Setcompr_eq_image ..
  also have "... = f ` Option.these A" unfolding Option.these_def
    by (rule the_map_option_image) blast
  finally show ?thesis ..
qed

lemma these_id: "None \<notin> A \<Longrightarrow> Option.these A = the ` A" unfolding Option.these_def by fast


end
