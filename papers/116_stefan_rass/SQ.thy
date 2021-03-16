theory SQ
 imports Complex_Main gn dens
begin

definition SQ :: lang where
  "SQ \<equiv> {w. \<exists>x. gn w = x ^ 2}"

definition SQ_nat :: "nat set" where
  "SQ_nat \<equiv> {y. \<exists>x. y = x ^ 2}"

declare SQ_def[simp] SQ_nat_def[simp]

lemma SQ_nat_eq: "SQ = {w. gn w \<in> SQ_nat}" by simp

(* floor of log\<^sub>2 n for easier access *)
fun log2 :: "nat \<Rightarrow> nat" where
  "log2 n = length (bin_of_nat n) - 1"

(* prove correctness of the shortcut (is this necessary?) *)
lemma 
  fixes n::nat
  assumes "n > 0"
  shows "log2 n = floor (log 2 (of_nat n))"
proof -
  let ?n = "of_nat n" let ?b = "bin_of_nat ?n" let ?l = "length ?b" let ?nbn = "nat_of_bin ?b"
  assume "n > 0"
  then have "?n = 2 powr (log 2 ?n)" using powr_log_cancel[of 2 ?n] by auto

  then have "?n \<ge> 2 powr (floor (log 2 ?n))" by (metis of_int_floor_le powr_mono one_le_numeral)
  then have "?n < 2 powr (floor (log 2 ?n) + 1)" by (simp add: assms less_powr_iff)

  (* lower bound: n \<ge> 2 ^ (?l - 1) *)
  from \<open>n > 0\<close> have "ends_in True ?b" using bin_of_nat_end_True by simp
  then have "2 ^ (?l - 1) \<le> ?nbn" by (rule nat_of_bin_min[of ?b])
  then have "(2::nat) ^ (?l - 1) \<le> ?n" unfolding nat_bin_nat[of ?n] .

  (* upper bound: n < 2 ^ ?l *)
  from nat_of_bin_max[of ?b] have "?n < (2::nat) ^ ?l" unfolding nat_bin_nat .
  
  

  find_theorems "_ powr _"

  thm floor_log2_div2
  thm powr_log_cancel
  thm powr_realpow

  oops

end