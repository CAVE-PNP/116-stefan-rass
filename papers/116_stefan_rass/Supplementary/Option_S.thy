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

lemma these_altdef: "Option.these A = \<Union> (set_option ` A)" unfolding Option.these_def by force

lemma card_set_option[simp]: "card (set_option x) \<le> 1" by (induction x) auto
lemma finite_set_option[simp]: "finite (set_option x)" by (induction x) auto

lemma card_these:
  assumes "finite A"
  shows "card (Option.these A) \<le> card A"
proof -
  from assms have "card (Option.these A) \<le> (\<Sum>a\<in>A. card (set_option a))"
    unfolding these_altdef by (rule card_UN_le)
  also have "... \<le> (\<Sum>a\<in>A. 1)" using card_set_option by (rule sum_mono)
  also have "... \<le> card A" by simp
  finally show ?thesis .
qed

lemma case_option_same[simp]: "(case x of None \<Rightarrow> a | Some y \<Rightarrow> a) = a"
  by (simp add: option.case_eq_if)

lemma if_Some_P[elim_format]: "(if P then Some x else None) = Some y \<Longrightarrow> P" by (cases P) auto
lemma if_None_notP[elim_format]: "(if P then Some x else None) = None \<Longrightarrow> \<not>P" by (cases P) auto
lemma if_Some_notP[elim_format]: "(if P then None else Some x) = Some y \<Longrightarrow> \<not>P" by (cases P) auto
lemma if_None_P[elim_format]: "(if P then None else Some x) = None \<Longrightarrow> P" by (cases P) auto


lemma those_map_Some[simp]: "those (map Some xs) = Some xs" by (induction xs) auto

end
