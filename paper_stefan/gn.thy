theory gn
  imports Main HOL.HOL
begin

fun bin_to_nat :: "bool list \<Rightarrow> nat" where
  "bin_to_nat [] = 0" |
  (*"bin_to_nat (True # xs) = 1 + 2 * bin_to_nat xs" |
  "bin_to_nat (False # xs) = 2 * bin_to_nat xs" |*)
  "bin_to_nat (a # xs) = (if a then 1 else 0) + 2 * bin_to_nat xs"

value "even (0::nat)"

fun inc :: "bool list \<Rightarrow> bool list" where
  incNil: "inc [] = [True]" |
  incStep: "inc (a # xs) = (if a then (False # inc xs) else (True # xs))"

lemma bin_to_nat_inc_S: "Suc (bin_to_nat xs) = bin_to_nat (inc xs)"
  by (induction xs) auto

fun trim :: "bool list \<Rightarrow> bool list" where
  "trim [] = []" |
  "trim xs = (if last xs = False then trim (butlast xs) else xs)"

fun nat_to_bin :: "nat \<Rightarrow> bool list" where
  "nat_to_bin 0 = []" |
  "nat_to_bin (Suc n) = inc (nat_to_bin n)"

lemma "bin_to_nat (nat_to_bin (n)) = n"
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have "bin_to_nat (nat_to_bin (Suc n)) = bin_to_nat (inc (nat_to_bin n))" by simp
  also have "bin_to_nat (inc (nat_to_bin n)) = Suc (bin_to_nat (nat_to_bin n))" by (simp add: bin_to_nat_inc_S)
  also have "Suc (bin_to_nat (nat_to_bin n)) = Suc n" by (simp add: Suc.IH)
  finally show ?case .
qed

lemma inc_not_Nil: "inc xs \<noteq> []"
  by (induction xs rule: inc.induct) auto

(* gödel number and related *)
fun gn :: "bool list \<Rightarrow> nat" where
  "gn w = bin_to_nat (w @ [True])"

theorem "gn w > 0" 
  by (induction w) auto

theorem "gn w = bin_to_nat w + (2 ^ length w)"
  by (induction w) auto
