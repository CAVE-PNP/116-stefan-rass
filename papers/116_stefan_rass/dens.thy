theory dens
  imports Main HOL.Num gn
begin

(* language density function as defined in ch 3.2 *)
definition dens :: "lang \<Rightarrow> nat \<Rightarrow> nat" where
  "dens L x = card {w \<in> L. gn w \<le> x}"

(* "density of a word" for convenience *)
definition dens' :: "lang \<Rightarrow> word \<Rightarrow> nat" where
  "dens' L v = dens L (gn v)"

declare dens_def[simp] dens'_def[simp]

lemma vim_nat_le:
  fixes x :: nat
  shows "{w. f w \<le> x} = f -` {0..x}"
  by fastforce

lemma vim_nat_le2:
  fixes x :: nat
  shows "{w \<in> A. f w \<le> x} = A \<inter> f -` {0..x}"
  using vim_nat_le[of f x] by blast

(* definition of dens is equivalent to using preimage of gn intersected with L *)
lemma dens_eq_card_vim_gn: "dens L x = card (L \<inter> gn -` {0..x})"
  using dens_def[of L x] unfolding vim_nat_le2[of L gn x] .


lemma inj_spec: "inj f \<Longrightarrow> inj_on f A" by (standard) (simp add: inj_def)

lemma lemma4_1: "dens L x \<le> x"
proof - (* shorter proof by Moritz Hiebler *)
  let ?A = "{w\<in>L. gn w \<le> x}"
  have gn_inj_on: "inj_on gn ?A"
    using gn_inj inj_spec by blast
  have "gn ` ?A \<subseteq> {0<..x}"
    using nat_of_num_pos by auto
  then have "card ?A \<le> card {0<..x}"
    using gn_inj_on card_inj_on_le by blast
  then show ?thesis by (unfold card_greaterThanAtMost dens_def minus_nat.diff_0)
qed


lemma bounded_lang_finite: "finite {w \<in> L. gn w \<le> x}"
proof -
  from gn_inj have "finite (gn -` {0..x})" using finite_vimageI[of "{0..x}" gn] by blast
  then have "finite (L \<inter> (gn -` {0..x}))" by blast
  then show "finite {w \<in> L. gn w \<le> x}" by (fold vim_nat_le2[of L gn x])
qed

lemma dens_mono: "L \<subseteq> M \<Longrightarrow> dens L x \<le> dens M x"
proof -
  assume "L \<subseteq> M"
  hence "{w \<in> L. gn w \<le> x} \<subseteq> {w \<in> M. gn w \<le> x}" by blast
  with card_mono bounded_lang_finite show ?thesis unfolding dens_def .
      (* interestingly, the unfold tactic does not work here *)
qed

lemma dens_intersect_le: "dens (L\<^sub>1 \<inter> L\<^sub>2) x \<le> dens L\<^sub>1 x"
  using dens_mono by blast

end
