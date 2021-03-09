theory gn
  imports Main HOL.HOL
begin

(* binary to natural number conversion and related concepts *)
fun bin_to_nat :: "bool list \<Rightarrow> nat" where
  "bin_to_nat [] = 0" |
  "bin_to_nat (a # xs) = (if a then 1 else 0) + 2 * bin_to_nat xs"

fun inc :: "bool list \<Rightarrow> bool list" where
  "inc [] = [True]" |
  "inc (a # xs) = (if a then (False # inc xs) else (True # xs))"

(*
 * note: the auto-solvers seem to have difficulties with the split rules,
 * but can easily prove equivalence to the versions defined with "if ... then ... else"
 *)
fun bin_to_nat' :: "bool list \<Rightarrow> nat" where
  "bin_to_nat' [] = 0" |
  "bin_to_nat' (True # xs) = 1 + 2 * bin_to_nat' xs" |
  "bin_to_nat' (False # xs) = 2 * bin_to_nat' xs"

lemma "bin_to_nat' w = bin_to_nat w"
  by (induction w) auto

fun inc' :: "bool list \<Rightarrow> bool list" where
  "inc' [] = [True]" |
  "inc' (False # xs) = True # xs" |
  "inc' (True # xs) = False # (inc' xs)"

lemma "inc' w = inc w"
  by (induction w) auto

lemma bin_to_nat_inc_S: "Suc (bin_to_nat xs) = bin_to_nat (inc xs)"
  by (induction xs) auto

lemma inc_end_True:
  fixes xs
  assumes "\<exists>ys. xs = ys @ [True]"
  shows "\<exists>zs. inc xs = zs @ [True]"
  using assms
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs')
  from Cons.prems obtain ys where ysD: "a # xs' = ys @ [True]" ..
  thm Cons.IH
  thm Cons.prems

  then show ?case 
  proof (cases ys)
    case Nil
    with ysD show ?thesis by simp
  next
    case (Cons b ys')
    with ysD have h1: "xs' = ys' @ [True]" by fastforce
    with Cons.IH obtain zs' where h2: "inc xs' = zs' @ [True]" by auto

    then show ?thesis
    proof (cases a)
      case True
      with h2 have "inc (a # xs') = False # zs' @ [True]" by simp
      then show ?thesis by simp
    next
      case False
      then have "inc (a # xs') = True # xs'" by simp
      with h1 have "\<exists>zs. inc (a # xs') = True # zs @ [True]" by simp
      then show ?thesis by auto
    qed 
  qed
qed

lemma inc_rev_first_True:
  fixes xs
  assumes "\<exists>ys. rev xs = True # ys"
  shows "\<exists>zs. rev (inc xs) = True # zs"
proof -
  from assms have "\<exists>ys. xs = ys @ [True]" by fastforce
  then have "\<exists>zs. inc xs = zs @ [True]" by (rule inc_end_True)
  then show "\<exists>zs. rev (inc xs) = True # zs" by fastforce
qed

lemma inc_last_True:
  fixes xs
  assumes "xs \<noteq> []" and "last xs = True"
  shows "last (inc xs) = True"
proof -
  obtain ys where "ys = butlast xs" by simp
  with assms have "xs \<noteq> [] \<and> butlast xs = ys \<and> last xs = True" by simp
      (*find_theorems "?xs \<noteq> []" "last"
  thm snoc_eq_iff_butlast[of ys True xs]*)
  then have "xs = ys @ [True]"
    using snoc_eq_iff_butlast[of ys True xs] by simp

  then have "\<exists>ys. xs = ys @ [True]" ..
  then have "\<exists>zs. inc xs = zs @ [True]" by (rule inc_end_True)
  then show "last (inc xs) = True" by fastforce
qed

(* trim function: removes leading zeroes. currently unused *)
fun trim :: "bool list \<Rightarrow> bool list" where
  "trim [] = []" |
  "trim (a # xs) = (if last (a # xs) = False then trim (butlast (a # xs)) else a # xs)"

lemma trim_trimmed: "last xs = True \<Longrightarrow> trim xs = xs"
  by (induction xs) auto

lemma "trim xs \<noteq> [] \<Longrightarrow> xs \<noteq> []"
  by (induction xs) auto

(* continued conversion *)
fun nat_to_bin :: "nat \<Rightarrow> bool list" where
  "nat_to_bin 0 = []" |
  "nat_to_bin (Suc n) = inc (nat_to_bin n)"

lemma nat_to_bin_to_nat[simp]: "bin_to_nat (nat_to_bin (n)) = n"
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

(* lemma bin_to_nat_to_bin: "(last w = True) \<Longrightarrow> (nat_to_bin (bin_to_nat w)) = w" *)
(*lemma bin_to_nat_to_bin: 
  fixes xs
  assumes "\<exists>ys. xs = ys @ [True]"
  shows "(nat_to_bin (bin_to_nat xs)) = xs"
  using assms
proof (induction xs) *)

lemma inc_not_Nil[simp]: "inc xs \<noteq> []"
  by (induction xs rule: inc.induct) auto

(* gödel number and related *)
fun gn :: "bool list \<Rightarrow> nat" where
  "gn w = bin_to_nat (w @ [True])"

theorem gn_gt_0[simp]: "gn w > 0" 
  by (induction w) auto

theorem gnD: "gn w = bin_to_nat w + (2 ^ length w)"
  by (induction w) auto

find_theorems "_ \<Longrightarrow> inj _"
find_theorems "\<not>(inj _) \<Longrightarrow> _"
thm injD
thm injI

(* theorem bin_to_nat_inj: "last v = True \<Longrightarrow> last w = True \<Longrightarrow> (bin_to_nat v = bin_to_nat w) \<Longrightarrow> v = w" *)

theorem gn_inj: "inj gn"
proof (rule ccontr)
  assume "\<not> inj gn"
  then obtain v w where gn_eq: "gn v = gn w" and "v \<noteq> w" 
    using injI by metis (* proven (proudly) using try *)
  then have "length v = length w" sorry

  oops

(* is a number a gödel number *)
fun is_gn :: "nat \<Rightarrow> bool"
  where "is_gn n = (n > 0)"

(* inverse: retrieve word from gödel number, assuming it is a valid gn (is_gn n = True) *)
fun gn_inv :: "nat \<Rightarrow> bool list"
  where "gn_inv n = butlast (nat_to_bin n)"

theorem "is_gn n \<Longrightarrow> \<exists>w. gn w = n"
