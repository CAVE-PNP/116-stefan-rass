theory SQ
  imports Complex_Main dens "HOL-Library.Discrete"
begin

definition SQ :: lang where
  "SQ \<equiv> {w. \<exists>z. gn w = z ^ 2}"

lemma lemma_4_2: "dens SQ x = Discrete.sqrt x"
proof -
  have eq: "{w\<in>SQ. gn w \<le> x} = gninv ` power2 ` {0<..Discrete.sqrt x}"
  proof -
    have "{w\<in>SQ. gn w \<le> x} = {w. \<exists>z. (gn w = z^2 \<and> gn w \<le> x)}"
      using SQ_def by (smt (verit, best) Collect_cong mem_Collect_eq)
    also have "\<dots> = {w. \<exists>z. (gn w = z^2 \<and> z^2 \<le> x)}" by metis
    also have "\<dots> = {w. \<exists>z. (gn w = z^2 \<and> 0 < z^2 \<and> z^2 \<le> x)}"
      using gn_def nat_of_num_pos by metis
    also have "\<dots> = {gninv (z\<^sup>2) |z. 0 < z\<^sup>2 \<and> z\<^sup>2 \<le> x}"
      using gn_def gninv_def nat_of_num_inverse
      by (metis (no_types, lifting) num_of_nat_inverse)
    also have "\<dots> = {gninv (z\<^sup>2) |z. 0 < z \<and> z \<le> Discrete.sqrt x}"
      using le_sqrt_iff by force
    also have "\<dots> = gninv ` power2 ` {0<..Discrete.sqrt x}" by auto
    finally show ?thesis .
  qed
  have "inj_on gninv (power2 ` {0<..Discrete.sqrt x})"
    by (smt (verit, best) gninv_def greaterThanAtMost_iff imageE inj_on_def nat_zero_less_power_iff num_of_nat_inverse)
  then have "dens SQ x = card (power2 ` {0<..Discrete.sqrt x})"
    using eq card_image by auto
  also have "\<dots> = card {0<..Discrete.sqrt x}"
    by (simp add: card_image inj_on_def)
  also have "\<dots> = Discrete.sqrt x" by simp
  finally show ?thesis .
qed

end