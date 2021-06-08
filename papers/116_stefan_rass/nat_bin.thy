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

(* many of the following proofs can probably be replaced by references to similar lemmas for Num *)

(* what happens when a digit is appended *)
lemma nat_of_bin_app0: "nat_of_bin (xs @ [False]) = nat_of_bin xs"
  by (induction xs) auto

lemma nat_of_bin_app1: "nat_of_bin (xs @ [True]) = nat_of_bin xs + 2 ^ length xs"
  by (induction xs) auto

lemma nat_of_bin_0s [simp]: "nat_of_bin (replicate k False) = 0"
  by (induction k) auto

lemma nat_of_bin_app: "nat_of_bin (lo @ up) = (nat_of_bin up) * 2^(length lo) + (nat_of_bin lo)"
  by (induction lo) auto

corollary nat_of_bin_app_zs: "nat_of_bin (replicate k False @ up) = (nat_of_bin up) * 2^k"
  using nat_of_bin_app by simp

corollary nat_of_bin_leading_zs[simp]: "nat_of_bin (xs @ replicate k False) = nat_of_bin xs"
  using nat_of_bin_app by simp

lemma nat_of_bin_div2[simp]: "nat_of_bin (a # xs) div 2 = nat_of_bin xs" by force
lemma nat_of_bin_div2': "nat_of_bin xs div 2 = nat_of_bin (tl xs)" by (cases xs) auto

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

corollary nat_of_bin_surj: "surj nat_of_bin"
  using nat_bin_nat by (intro surjI)

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

lemma bin_of_nat_end_True[simp]: "n > 0 \<Longrightarrow> ends_in True (bin_of_nat n)"
proof (induction n)
  case 0 thus ?case by simp
next
  case (Suc n)
  then show ?case by (cases n) (auto simp add: inc_end_True)
qed


(* more lemmas about ends_in *)
lemma ends_in_last: "xs \<noteq> [] \<Longrightarrow> ends_in x xs \<longleftrightarrow> last xs = x"
proof (intro iffI)
  assume "last xs = x" and "xs \<noteq> []"
  then have "xs = butlast xs @ [last xs]" 
    using snoc_eq_iff_butlast[of "butlast xs" "last xs" "xs"] by force
  then show "ends_in x xs" unfolding \<open>last xs = x\<close> ..
qed (* direction "\<Longrightarrow>" by *) force

lemma ends_in_app: "ends_in a (xs @ ys) = (if ys = [] then ends_in a xs else ends_in a ys)"
proof (cases "ys = []")
  case False
  then have "xs @ ys \<noteq> []" by blast
  with ends_in_last have "ends_in a (xs @ ys) \<longleftrightarrow> last (xs @ ys) = a" .
  also have "... \<longleftrightarrow> last ys = a" unfolding \<open>ys \<noteq> []\<close>[THEN last_appendR] ..
  also have "... \<longleftrightarrow> ends_in a ys" using ends_in_last[symmetric] \<open>ys \<noteq> []\<close> .
  also have "... \<longleftrightarrow> (if ys = [] then ends_in a xs else ends_in a ys)" using \<open>ys \<noteq> []\<close> by simp
  finally show ?thesis .
qed (* case "ys = []" by *) simp


lemma inc_len: "length xs \<le> length (inc xs)"
  by (induction xs) auto

lemma bin_of_nat_len[simp]:
  assumes "n > 0"
  shows "length (bin_of_nat n) > 0"
  using assms
proof (induction n rule: nat_induct_non_zero)
  case 1 thus ?case by simp
next
  case (Suc n)
  have "0 < length (bin_of_nat n)" using Suc.IH .
  also have "... \<le> length (inc (bin_of_nat n))" by (rule inc_len)
  also have "... = length (bin_of_nat (Suc n))" by simp
  finally show ?case .
qed

lemma ends_in_True_Cons: "ends_in True (a # w) \<Longrightarrow> w \<noteq> [] \<Longrightarrow> ends_in True w"
  by (metis append_butlast_last_id last.simps last_ConsR last_snoc list.sel(3) tl_append2)

lemma double_inc: "xs \<noteq> [] \<Longrightarrow> inc (inc (x # xs)) = x # (inc xs)" by force 

lemma bin_of_nat_double: "n > 0 \<Longrightarrow> bin_of_nat (2 * n) = False # (bin_of_nat n)" 
proof (induction n rule: nat_induct_non_zero)
  case (Suc n)
  have "bin_of_nat (2 * Suc n) = inc (inc (bin_of_nat (2 * n)))" by simp
  also have "... = inc (inc (False # bin_of_nat n))" unfolding Suc.IH ..
  also have "... = False # inc (bin_of_nat n)" using double_inc by simp
  also have "... = False # bin_of_nat (Suc n)" by simp
  finally show ?case .
qed (* case 1 by *) (simp add: numeral_2_eq_2)

corollary bin_of_nat_double_p1: "bin_of_nat (2 * n + 1) = True # (bin_of_nat n)"
  using bin_of_nat_double by (cases "n > 0") auto

lemma ends_in_True_gt0:
  assumes eTw: "ends_in True w"
  shows "nat_of_bin w > 0"
proof -
  have "(0::nat) < 2 ^ 0" by (rule less_exp)
  also have "... \<le> 2 ^ (length w - 1)" by fastforce
  also have "... \<le> nat_of_bin w" using nat_of_bin_min eTw .
  finally show ?thesis .
qed

lemma bin_nat_bin[simp]: "ends_in True w \<Longrightarrow> bin_of_nat (nat_of_bin w) = w"
proof (induction w)
  case (Cons a w)
  note IH = Cons.IH and prems1 = Cons.prems
  show ?case
  proof (cases w)
    case Nil
    with \<open>ends_in True (a # w)\<close> have "a" (* == True *) by simp
    with Nil show ?thesis by simp
  next
    case (Cons a' w')
    with ends_in_True_Cons prems1 have "ends_in True w" by blast
    with ends_in_True_gt0 have "nat_of_bin w > 0" .
    show ?thesis
    proof (cases a)
      case True
      then have "bin_of_nat (nat_of_bin (a # w)) = inc (bin_of_nat (2 * nat_of_bin w))" by simp
      also have "... = inc (False # bin_of_nat (nat_of_bin w))" using bin_of_nat_double \<open>nat_of_bin w > 0\<close> by auto
      also have "... = inc (False # w)" using IH \<open>ends_in True w\<close> by presburger
      also have "... = a # w" using \<open>a\<close> by simp
      finally show ?thesis .
    next
      case False
      then have "bin_of_nat (nat_of_bin (a # w)) = bin_of_nat (2 * nat_of_bin w)" by simp
      also have "... = False # bin_of_nat (nat_of_bin w)" using bin_of_nat_double \<open>nat_of_bin w > 0\<close> by auto
      also have "... = False # w" using IH \<open>ends_in True w\<close> by presburger
      also have "... = a # w" using \<open>\<not>a\<close> by simp
      finally show ?thesis .
    qed
  qed
qed simp

lemma bin_of_nat_div2: "bin_of_nat (n div 2) = tl (bin_of_nat n)"
proof (cases "n > 1")
  case False
  then have "n = 0 \<or> n = 1" by (cases n) auto
  then show ?thesis by (elim disjE) auto
next
  case True

  define w where "w \<equiv> bin_of_nat n"
  then have "nat_of_bin w = nat_of_bin (bin_of_nat n)" by simp
  then have wI: "nat_of_bin w = n" by simp

  have eTw: "ends_in True w" unfolding w_def using bin_of_nat_end_True \<open>n > 1\<close> by simp

  (* TODO remove metis *)
  from \<open>n > 1\<close> have "length w \<ge> 2"
    by (metis (mono_tags, lifting) Suc_1 Suc_leI less_trans_Suc nat_of_bin_max one_less_numeral_iff power_one_right power_strict_increasing_iff semiring_norm(76) wI)
  then have "tl w \<noteq> []"
    by (metis Suc_1 Suc_le_length_iff butlast.simps(1) butlast_snoc butlast_tl dual_order.order_iff_strict eTw less_imp_Suc_add list.sel(3) not_Cons_self2 one_le_numeral plus_1_eq_Suc self_append_conv tl_append2)
  with eTw have "ends_in True (hd w # tl w)" by force
  with ends_in_True_Cons have eTtw: "ends_in True (tl w)" using \<open>tl w \<noteq> []\<close> .

  have "bin_of_nat (n div 2) = bin_of_nat (nat_of_bin w div 2)" unfolding wI ..
  also have "... = bin_of_nat (nat_of_bin (tl w))" using nat_of_bin_div2' by simp
  also have "... = tl w" using bin_nat_bin eTtw .
  finally show ?thesis unfolding w_def .
qed

corollary bin_of_nat_div2_times2: "n > 1 \<Longrightarrow> bin_of_nat (2 * (n div 2)) = False # tl (bin_of_nat n)"
  using bin_of_nat_div2 bin_of_nat_double by simp

lemma len_tl_Cons: "xs \<noteq> [] \<Longrightarrow> length (x # tl xs) = length xs" 
  unfolding length_Cons length_tl by simp

corollary bin_of_nat_div2_times2_len: "n > 1 \<Longrightarrow> length (bin_of_nat (2 * (n div 2))) =  length (bin_of_nat n)"
proof -
  assume "n > 1"
  then have l: "bin_of_nat n \<noteq> []" using bin_of_nat_len by simp
  
  have "length (bin_of_nat (2 * (n div 2))) = length (False # tl (bin_of_nat n))"
    using bin_of_nat_div2_times2 \<open>n > 1\<close> by presburger
  also have "... = length (bin_of_nat n)" using len_tl_Cons l .
  finally show ?thesis .
qed

corollary nat_of_bin_drop: "nat_of_bin (drop k xs) = (nat_of_bin xs) div 2 ^ k" 
proof (induction k)
  case 0
  then show ?case by simp
next
  case (Suc k)
  then show ?case
    by (metis Suc_eq_plus1 div_exp_eq drop_Suc nat_of_bin_div2' power_one_right tl_drop)
qed

lemma bin_of_nat_app_zs:
  assumes "n > 0"
  shows "bin_of_nat (n * 2^k) = replicate k False @ bin_of_nat n"
  (is "?lhs = ?zs @ ?n")
proof -
  from \<open>n > 0\<close> have "?n \<noteq> []" using bin_of_nat_len by simp
  moreover from \<open>n > 0\<close> have "ends_in True ?n" by simp
  ultimately have eTr: "ends_in True (?zs @ ?n)" unfolding ends_in_app by simp

  have "?lhs = bin_of_nat (nat_of_bin ?n * 2^k)" by simp
  also have "... = bin_of_nat (nat_of_bin (?zs @ ?n))" using nat_of_bin_app_zs by simp
  also have "... = ?zs @ ?n" using eTr by simp
  finally show ?thesis .
qed


lemma ends_in_drop:
  assumes "k < length w"
    and "ends_in True w"
  shows "ends_in True (drop k w)"
  using assms by force
  
end