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
  then obtain x where "x > 0" and "dens L x > x" by blast

  then show False sorry
qed

lemma lemma4_1':
  fixes L x
  assumes "x > 0"
  shows "dens L x \<le> x"
  using assms and lemma4_1 
  by blast

end
