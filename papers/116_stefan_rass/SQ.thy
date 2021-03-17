theory SQ
  imports Complex_Main dens "HOL-Library.Discrete"
begin

definition SQ :: lang where
  "SQ \<equiv> {w. \<exists>x. nat_of_num w = x ^ 2}"

lemma lemma_4_2: "dens SQ x = Suc (Discrete.sqrt x)"
proof -
  have "dens SQ x = card {w\<in>SQ. nat_of_num w \<le> x}" by simp
  also have "\<dots> = card {w. (\<exists>z. nat_of_num w = z^2) \<and> (nat_of_num w \<le> x)}"
    using SQ_def by (smt (verit, best) Collect_cong mem_Collect_eq)
  also have "\<dots> = card {z. z^2 \<le> x}" by sorry
  also have "\<dots> = card {z. z \<le> Discrete.sqrt x}"
    using le_sqrt_iff by presburger
  also have "\<dots> = card {..Discrete.sqrt x}" by simp
  also have "\<dots> = Suc (Discrete.sqrt x)" by simp
  finally show ?thesis .
qed

end