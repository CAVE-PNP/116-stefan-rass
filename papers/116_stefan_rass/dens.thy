theory dens
  imports Main gn
begin

type_synonym lang = "word set"

(* language density function as defined in ch 3.2 *)
fun dens :: "lang \<Rightarrow> nat \<Rightarrow> nat" where
  "dens L x = card {w \<in> L. gn w \<le> x}"

(* "density of a word" for convenience *)
fun dens' :: "lang \<Rightarrow> word \<Rightarrow> nat" where
  "dens' L v = dens L (gn v)"

lemma lemma4_1: "\<forall>x>0. dens L x \<le> x"
proof (rule ccontr)
  assume "\<not> (\<forall>x>0. dens L x \<le> x)"
  then have "\<exists>x>0. dens L x > x" by (fold not_le) blast
  then obtain x0 where "x0 < dens L x0" by blast

  then have "Suc x0 \<le> card {w\<in>L. gn w \<le> x0}" by simp
  then obtain W where "W \<subseteq> {w\<in>L. gn w \<le> x0}" and Wcard: "card W = Suc x0"
    by (rule obtain_subset_with_card_n)

  then have "gn ` W \<subseteq> {0<..x0}" using gn_gt_0 by auto
  then have "card (gn ` W) \<le> x0" using card_mono card_greaterThanAtMost
    by (metis diff_zero finite_greaterThanAtMost)
  then show False using Wcard pigeonhole
    by (metis gn_inj inj_on_def le_imp_less_Suc)
qed

lemma lemma4_1':
  fixes L x
  assumes "x > 0"
  shows "dens L x \<le> x"
  using assms and lemma4_1 
  by blast

end
