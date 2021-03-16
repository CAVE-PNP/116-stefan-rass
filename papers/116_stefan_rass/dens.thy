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

  then have "card {w\<in>L. gn w \<le> x} \<ge> Suc x" by force
  then obtain W where "W \<subseteq> {w\<in>L. gn w \<le> x}" and Wcard: "card W = Suc x"
    by (rule obtain_subset_with_card_n)

  then have "gn ` W \<subseteq> {0<..x}" using gn_gt_0 by auto
  then have "card (gn ` W) \<le> x" using card_mono card_greaterThanAtMost
    by (metis diff_zero finite_greaterThanAtMost)
  then show False using Wcard pigeonhole
    by (metis gn_inj inj_on_def le_imp_less_Suc)
qed

lemma bounded_lang_finite : "finite {w\<in>L. gn w \<le> x}" by sorry

lemma dens_mono: "L \<subseteq> M \<Longrightarrow> dens L x \<le> dens M x"
proof -
  fix x
  assume "L \<subseteq> M"
  hence "{w \<in> L. gn w \<le> x} \<subseteq> {w \<in> M. gn w \<le> x}" by blast
  thus "dens L x \<le> dens M x"
    using card_mono bounded_lang_finite [of M x] by simp
qed

lemma dens_intersect_le: "dens (L1 \<inter> L2) x \<le> dens L1 x"
proof -
  from dens_mono show ?thesis by blast
qed

end
