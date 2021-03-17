theory nat_bin
  imports Main
begin

type_synonym bin = "bool list"

abbreviation ends_in :: "'a \<Rightarrow> 'a list \<Rightarrow> bool" where
  "ends_in a xs \<equiv> (\<exists>ys. xs = ys @ [a])"


(* binary to natural number conversion *)
fun nat_of_bin :: "bin \<Rightarrow> nat" where
  "nat_of_bin [] = 0" |
  "nat_of_bin (a # xs) = (if a then 1 else 0) + 2 * nat_of_bin xs"

fun inc :: "bin \<Rightarrow> bin" where
  "inc [] = [True]" |
  "inc (a # xs) = (if a then (False # inc xs) else (True # xs))"

fun bin_of_nat :: "nat \<Rightarrow> bin" where
  "bin_of_nat 0 = []" |
  "bin_of_nat (Suc n) = inc (bin_of_nat n)"

(* what happens when a digit is appended *)
lemma nat_of_bin_app0: "nat_of_bin (xs @ [False]) = nat_of_bin xs"
  by (induction xs) auto

lemma nat_of_bin_app1: "nat_of_bin (xs @ [True]) = nat_of_bin xs + 2 ^ length xs"
  by (induction xs) auto

(* boundaries *)
lemma nat_of_bin_max: "nat_of_bin xs < 2 ^ (length xs)"
  by (induction xs) auto

lemma nat_of_bin_min: "ends_in True xs \<Longrightarrow> nat_of_bin xs \<ge> 2 ^ (length xs - 1)"
  by (auto simp add: nat_of_bin_app1)

(* nat to bin to nat*)
lemma nat_of_bin_inc_S: "Suc (nat_of_bin xs) = nat_of_bin (inc xs)"
  by (induction xs) auto

lemma nat_bin_nat[simp]: 
  "nat_of_bin (bin_of_nat (n)) = n" (is "?nbn n = n")
proof (induction n)
  case 0 thus ?case by simp
next
  case (Suc n)
  have "?nbn (Suc n) = nat_of_bin (inc (bin_of_nat n))" by simp
  also have "... = Suc (?nbn n)" using nat_of_bin_inc_S by simp
  also have "... = Suc n" using Suc.IH by simp
  finally show ?case .
qed

(* operations result in binary strings that end with a 1 bit *)
lemma inc_end_True:
  fixes xs
  assumes "ends_in True xs"
  shows "ends_in True (inc xs)"
  using assms
proof (induction xs)
  case Nil thus ?case by simp
next
  case (Cons a xs')
  from Cons.prems obtain ys where ysD: "a # xs' = ys @ [True]" ..
  then show ?case
  proof (cases ys)
    case Nil
    with ysD show ?thesis by simp
  next
    case (Cons b ys')
    with ysD have h1: "xs' = ys' @ [True]" by fastforce
    with Cons.IH obtain zs' where h2: "inc xs' = zs' @ [True]" by auto
    then show ?thesis by (cases a) (auto simp add: h1 h2)
  qed
qed

lemma bin_of_nat_end_True: "n > 0 \<Longrightarrow> ends_in True (bin_of_nat n)"
proof (induction n)
  case 0 thus ?case by simp
next
  case (Suc n) 
  then show ?case by (cases n) (auto simp add: inc_end_True)
qed


lemma inc_len: "length xs \<le> length (inc xs)"
  by (induction xs) auto

lemma bin_of_nat_len:
  assumes "n > 0"
  shows "length (bin_of_nat n) > 0"
  using assms 
proof (induction n rule: nat_induct_non_zero)
  case 1
  then show ?case by simp
next
  case (Suc n)
  let ?b = "\<lambda>n. bin_of_nat n" and ?l = "\<lambda>w. length w"

  (* also ... finally does not work in this case for some reason *)
  have 1: "?l (?b (Suc n)) = ?l (inc (?b n))" using nat_of_bin_inc_S by simp
  have 2: "?l (inc (?b n)) \<ge> ?l (?b n)" by (rule inc_len)
  have 3:  "?l (?b n) > 0" by (rule Suc.IH)
  from 1 2 3 show "0 < length (bin_of_nat (Suc n))" by fastforce
qed 

end