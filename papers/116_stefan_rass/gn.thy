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

(* abbreviations are directly replaced and only displayed to the user *)
abbreviation ends_in :: "'a \<Rightarrow> 'a list \<Rightarrow> bool" where
  "ends_in a xs \<equiv> (\<exists>ys. xs = ys @ [a])"

(*
 * alternative definitions
 *
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


(* properties of inc *)
lemma bin_to_nat_inc_S: "Suc (bin_to_nat xs) = bin_to_nat (inc xs)"
  by (induction xs) auto

lemma inc_not_Nil[simp]: "inc xs \<noteq> []"
  by (induction xs rule: inc.induct) auto

lemma inc_end_True:
  fixes xs
  assumes "\<exists>ys. xs = ys @ [True]"
  shows "\<exists>zs. inc xs = zs @ [True]"
    (* assumes "ends_in True xs"
  shows "ends_in True (inc xs)" *)
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

lemma nat_to_bin_to_nat[simp]: 
  "bin_to_nat (nat_to_bin (n)) = n" (is "?nbn n = n")
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have "?nbn (Suc n) = bin_to_nat (inc (nat_to_bin n))" by simp
  also have "... = Suc (?nbn n)" using bin_to_nat_inc_S by simp
  also have "... = Suc n" using Suc.IH by simp
  finally show ?case .
qed

lemma nat_to_bin_end_True:
  fixes n
  assumes "n > 0"
  shows "ends_in True (nat_to_bin n)"
  using assms
  by (induction n rule: nat_induct_non_zero) 
    (auto simp add: inc_end_True)

(* lemma bin_to_nat_to_bin: "(last w = True) \<Longrightarrow> (nat_to_bin (bin_to_nat w)) = w" 
lemma bin_to_nat_to_bin: 
  fixes xs
  assumes "\<exists>ys. xs = ys @ [True]"
  shows "(nat_to_bin (bin_to_nat xs)) = xs"
  using assms
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  

  then show ?case
  proof (cases xs)
    case Nil
    with Cons.prems show ?thesis by simp
  next
    case (Cons a xs')
    then have 
    then show ?thesis sorry
  qed
qed
  oops *)

(* what happens when a digit is appended *)
lemma bin_to_nat_app0: "bin_to_nat (xs @ [False]) = bin_to_nat xs"
  by (induction xs) auto

lemma bin_to_nat_app1: "bin_to_nat (xs @ [True]) = bin_to_nat xs + 2 ^ length xs"
  by (induction xs) auto

(* boundaries *)
lemma bin_to_nat_max: "bin_to_nat xs < 2 ^ (length xs)"
  by (induction xs) auto

lemma bin_to_nat_min: "ends_in True xs \<Longrightarrow> bin_to_nat xs \<ge> 2 ^ (length xs - 1)"
  by (auto simp add: bin_to_nat_app1)

lemma bin_to_nat_len_eq:
  fixes xs ys
  assumes "bin_to_nat xs = bin_to_nat ys" (is "?nx = ?ny")
    and xsD: "ends_in True xs"
    and ysD: "ends_in True ys"
  shows "length xs = length ys" (is "?lx = ?ly") (* let ?lx = "length xs" and ?ly = "length ys" *)
proof (rule ccontr)
  (* 
   * at this point the mathematical way would be 
   * to assume ?lx < ?ly "without loss of generality".
   * it seems, this is not possible in isabelle, and tedious to work around. see:
  find_theorems name:wlog
  thm linorder_wlog 
   *)
  assume "?lx \<noteq> ?ly"
  then have "?lx < ?ly \<or> ?lx > ?ly" using less_linear by blast
  then have "?nx \<noteq> ?ny"
  proof (* standard determines "(elim disjE)" *)
    assume "?lx < ?ly"
    have "?nx < 2 ^ ?lx" by (rule bin_to_nat_max)
    also have "... \<le> 2 ^ (?ly - 1)" using \<open>?lx < ?ly\<close> by simp
    also have "... \<le> ?ny" using ysD by (rule bin_to_nat_min)
    finally show "?nx \<noteq> ?ny" by (rule less_imp_neq)
  next
    assume "?lx > ?ly"
    have "?ny < 2 ^ ?ly" by (rule bin_to_nat_max)
    also have "... \<le> 2 ^ (?lx - 1)" using \<open>?lx > ?ly\<close> by simp
    also have "... \<le> ?nx" using xsD by (rule bin_to_nat_min)
    finally have "?ny \<noteq> ?nx" by (rule less_imp_neq)
    then show "?nx \<noteq> ?ny" by (rule not_sym)
  qed

  with \<open>?nx = ?ny\<close> show False by contradiction
qed

lemma "bin_to_nat (a # xs) - bin_to_nat (b # xs) \<le> 1"
  by (induction xs arbitrary: a b) auto

lemma bin_to_nat_hd_eq: "bin_to_nat (x # xs) = bin_to_nat (y # xs) \<Longrightarrow> x = y"
  by (induction xs arbitrary: x y, auto, (metis One_nat_def zero_neq_one)+)
    (* the last part was generated by sledge and i have not found any replacement for it *)

lemma "even (bin_to_nat (x # xs)) = (x = False)" by simp

lemma bin_to_nat_msb_lt:
  fixes xs ys
  assumes "length xs = length ys"
  shows "bin_to_nat (xs @ [False]) < bin_to_nat (ys @ [True])"
  using assms 
  by (induction xs ys rule: list_induct2) auto

lemma bin_to_nat_lsb[simp]: "bin_to_nat (a # xs) div 2 = bin_to_nat xs"
  by (induction xs) auto

lemma bin_to_nat_split: "bin_to_nat (xs @ ys) = bin_to_nat xs + (2 ^ length xs) * bin_to_nat ys"
  by (induction xs) auto

find_theorems "?xs ! ?i " Nil
thm take_Suc_conv_app_nth


(* lemma "xs \<noteq> ys \<Longrightarrow> \<exists>xsH xsT x ysH ysT y. xs = xsH @ x # xsT \<and> ys = ysH @ y # ysT \<and> xsT = ysT \<and> x \<noteq> y" *)

(* lemma "bin_to_nat xs = (\<Sum>n::nat=1..(length xs). n)" *)

thm longest_common_suffix

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

thm injI

term UNIV

theorem gn_inj: "inj gn"
proof (rule ccontr)
  assume "\<not> inj gn"
  then obtain v w where gn_eq: "gn v = gn w" and "v \<noteq> w"
    using injI by metis (* proven (proudly) using try *)

  let ?v' = "v @ [True]" and ?w' = "w @ [True]"

  from \<open>gn v = gn w\<close> have "bin_to_nat ?v' = bin_to_nat ?w'" by simp

  moreover have "ends_in True ?v'" "ends_in True ?w'" by simp_all
  thm bin_to_nat_len_eq[of ?v' ?w']
  ultimately have "length ?v' = length ?w'" by (rule bin_to_nat_len_eq[of ?v' ?w'])
  then have lens: "length v = length w" by simp

  thm longest_common_suffix[of v w]
  thm conjE

  (* obtain prefixes *)
  obtain ss vp wp where vpD: "v = vp @ ss" and wpD: "w = wp @ ss" and last_vw: "vp = [] \<or> wp = [] \<or> last vp \<noteq> last wp"
    using longest_common_suffix[of v w] by blast
  (* prefixes are not empty *)
  with \<open>v \<noteq> w\<close> have "vp \<noteq> []" "wp \<noteq> []" using lens by fastforce+
  with last_vw have "last vp \<noteq> last wp" by fast
   (* by (metis append_eq_append_conv append_self_conv2 lens) *)

  thm bin_to_nat_hd_eq
  term take
        
  oops

(* is a number a gödel number *)
fun is_gn :: "nat \<Rightarrow> bool"
  where "is_gn n = (n > 0)"

(* inverse: retrieve word from gödel number, assuming it is a valid gn (is_gn n = True) *)
fun gn_inv :: "nat \<Rightarrow> bool list"
  where "gn_inv n = butlast (nat_to_bin n)"

lemma "is_gn n \<Longrightarrow> gn (gn_inv n) = n"
  oops

theorem "is_gn n \<Longrightarrow> \<exists>w. gn w = n"
  oops