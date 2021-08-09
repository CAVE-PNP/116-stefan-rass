theory Misc
  imports Main
begin

lemma inj_imp_inj_on: "inj f \<Longrightarrow> inj_on f A" by (simp add: inj_on_def)

(* Suppl_Set ? *)
lemma image_Collect_compose: "f ` {g x | x. P x} = {f (g x) | x. P x}" by blast

(* Suppl_Orderings ? *)
lemma nat_strict_mono_greatest:
  fixes f::"nat \<Rightarrow> nat" and N::nat
  assumes "strict_mono f" "f 0 \<le> N"
  obtains n where "f n \<le> N" and "\<forall>m. f m \<le> N \<longrightarrow> m \<le> n"
proof -
  define M where "M \<equiv> {m. f m \<le> N}"
  define n where "n = Max M"

  from \<open>strict_mono f\<close> have "\<And>n. n \<le> f n" by (rule strict_mono_imp_increasing)
  hence "finite M" using M_def finite_less_ub by simp
  moreover from M_def \<open>f 0 \<le> N\<close> have "M \<noteq> {}" by auto
  ultimately have "n \<in> M" unfolding n_def using Max_in[of M] by simp

  then have "f n \<le> N" using n_def M_def by simp
  moreover have "\<forall>m. f m \<le> N \<longrightarrow> m \<le> n"
    using Max_ge \<open>finite M\<close> n_def M_def by blast
  ultimately show thesis using that by simp
qed

lemma subset_card_eq: "finite B \<Longrightarrow> {A\<in>Pow B. card A = card B} = {B}"
  sorry

end
