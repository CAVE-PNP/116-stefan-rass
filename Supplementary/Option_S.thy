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


lemma these_empty_eq_subset: "Option.these A = {} \<longleftrightarrow> A \<subseteq> {None}"
  unfolding these_empty_eq subset_singleton_iff ..

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

lemma case_option_cases[case_names None Some]:
  assumes "x = None \<Longrightarrow> P a"
    and "\<And>y. x = Some y \<Longrightarrow> P (b y)"
  shows "P (case x of None \<Rightarrow> a | Some y \<Rightarrow> b y)"
  using assms unfolding option.split_sel by blast

lemma if_Some_P[elim_format]: "(if P then Some x else None) = Some y \<Longrightarrow> P" by (cases P) auto
lemma if_None_notP[elim_format]: "(if P then Some x else None) = None \<Longrightarrow> \<not>P" by (cases P) auto
lemma if_Some_notP[elim_format]: "(if P then None else Some x) = Some y \<Longrightarrow> \<not>P" by (cases P) auto
lemma if_None_P[elim_format]: "(if P then None else Some x) = None \<Longrightarrow> P" by (cases P) auto


lemma those_map_Some[simp]: "those (map Some xs) = Some xs" by (induction xs) auto

(* set of items which are not None *)
abbreviation "someset xs \<equiv> Option.these (set xs)"

lemma card_these_length: "card (someset xs) \<le> length xs"
proof -
  have "card (someset xs) \<le> card (set xs)" by (rule card_these) blast
  also have "... \<le> length xs" by (rule card_length)
  finally show ?thesis .
qed

definition "option_map f \<equiv> \<exists>g. f = map_option g"
lemma option_map_altdef: "option_map f \<longleftrightarrow> f None = None \<and> (\<forall>x. \<exists>y. f (Some x) = Some y)"
proof safe
  assume "option_map f"
  then obtain g where f_def: "f = map_option g" unfolding option_map_def ..
  show "f None = None" unfolding f_def by simp
  fix x show "\<exists>y. f (Some x) = Some y" unfolding f_def by simp
next
  assume fN: "f None = None" and fS: "\<forall>x. \<exists>y. f (Some x) = Some y"
  define g where "g \<equiv> \<lambda>x. the (f (Some x))"
  have "f = map_option g"
    by (rule ext) (metis fS fN g_def not_Some_eq option.sel option.simps(8) option.simps(9))
  thus "option_map f" unfolding option_map_def by blast
qed


definition options :: "'a set \<Rightarrow> 'a option set"
  where "options A = insert None (Some ` A)"

lemma options_altdef: "options A = {None} \<union> (Some ` A)" unfolding options_def by blast

lemma empty_options[simp]: "options {} = {None}"
  and UNIV_options[simp]: "options UNIV = UNIV"
  and None_in_options[intro]: "None \<in> options A"
  and Some_options_iff[iff]: "Some x \<in> options A \<longleftrightarrow> x \<in> A"
  unfolding options_def UNIV_option_conv by blast+

lemma options_UNIV_iff[iff]: "options A = UNIV \<longleftrightarrow> A = UNIV" by auto

lemma set_options_eq: "x \<in> options A \<longleftrightarrow> set_option x \<subseteq> A" by (induction x) blast+

lemma options_map_option[simp]: "map_option f ` options A = options (f ` A)"
proof (rule set_eqI)
  show "x \<in> map_option f ` options A \<longleftrightarrow> x \<in> options (f ` A)" for x
    by (induction x) (auto simp add: options_def comp_def image_image)
qed

lemma options_set_option[simp]: "\<Union> (set_option ` options A) = A" by blast


end
