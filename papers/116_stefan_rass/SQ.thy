theory SQ
 imports Main gn dens
begin

definition SQ :: lang where
  "SQ \<equiv> {w. \<exists>x. gn w = x ^ 2}"

definition SQ_nat :: "nat set" where
  "SQ_nat \<equiv> {y. \<exists>x. y = x ^ 2}"

declare SQ_def[simp] SQ_nat_def[simp]

lemma SQ_nat_eq: "SQ = {w. gn w \<in> SQ_nat}" by simp

end