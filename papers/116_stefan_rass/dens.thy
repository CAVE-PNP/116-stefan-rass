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

lemma lemma4_1: "dens L x \<le> x"
proof (rule ccontr)
  assume "\<not> dens L x \<le> x"
  then have "dens L x > x" by (fold not_le) blast

  then have "Suc x \<le> card {w\<in>L. gn w \<le> x}" by simp
  then obtain W where "W \<subseteq> {w\<in>L. gn w \<le> x}" and Wcard: "card W = Suc x"
    by (rule obtain_subset_with_card_n)

  then have "gn ` W \<subseteq> {0<..x}" using gn_gt_0 by auto
  then have "card (gn ` W) \<le> x" using card_mono card_greaterThanAtMost
    by (metis diff_zero finite_greaterThanAtMost)
  then show False using Wcard pigeonhole
    by (metis gn_inj inj_on_def le_imp_less_Suc)
qed

end
