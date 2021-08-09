theory Threshold_Functions
  imports Main "HOL.Binomial" "HOL.Limits"
begin

definition mono
  where "mono Q \<equiv> \<forall>A B. A \<subseteq> B \<longrightarrow> Q A \<longrightarrow> Q B"

definition non_trivial
  where "non_trivial Q \<equiv> \<exists>A B. Q A \<and> ~ Q B"

(* probability of a random k-subset of {1..n} having Q *)
definition P_k
  where "P_k n k Q \<equiv> card {A\<in>Pow {1..n}. card A = k \<and> Q A} / (binomial n k)"

corollary mono_non_triv_0:
  assumes "mono Q" and "non_trivial Q"
  shows "P_k n 0 Q = 0"
  oops

corollary mono_non_triv_n:
  assumes "mono Q" and "non_trivial Q"
  shows "P_k n n Q = 1"
  oops

definition almost_every
  where "almost_every k Q \<equiv> (\<lambda>n. P_k n (k n) Q) \<longlonglongrightarrow> 1"

definition almost_none 
  where "almost_none k Q \<equiv> (\<lambda>n. P_k n (k n) Q) \<longlonglongrightarrow> 0"

definition threshold
  where "threshold M Q \<equiv>
    \<forall>m. let q=\<lambda>n. (m n)/of_nat (M n) in
      (q \<longlonglongrightarrow> 0) \<longrightarrow> almost_none m Q
    \<and> (q \<longlonglongrightarrow> 1) \<longrightarrow> almost_every m Q"

(*every non-trivial monotone increasing property has a threshold function *)
theorem mono_ex_th:
  fixes Q :: "nat set \<Rightarrow> bool"
  assumes "mono Q"
      and "non_trivial Q"
    obtains M where "threshold M Q"
sorry

end