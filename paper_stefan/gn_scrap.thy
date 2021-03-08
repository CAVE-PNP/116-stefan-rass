theory gn_scrap
  imports Main HOL.HOL
begin

lemma 
  fixes xs
  assumes "xs \<noteq> []" 
    and "last xs = True"
  shows "last (inc xs) = True"
  using assms
proof (induction xs)
  case Nil
  from \<open>[] \<noteq> []\<close> show ?case by simp
next
  case (Cons a ys)
  print_cases
  thm Cons
  thm \<open>last (a # ys) = True\<close>


  then show ?case
  proof (cases ys)
    case Nil
      (* with step show ?thesis by auto *)
    with Cons.prems have "a # ys = [True]" by simp
    then have "last (inc (a # ys)) = last (inc [True])" by simp
    also have "... = last [False, True]" by simp
    also have "... = True" by simp
    finally show ?thesis .
  next
    case (Cons b zs)
    then have "ys \<noteq> []" by simp
    with Cons.IH have IH_refined: "last ys = True \<Longrightarrow> last (inc ys) = True" .

    show ?thesis
    proof (cases a)
      case True
      then have "inc (a # ys) = False # inc ys" by simp
      then have "last (inc (a # ys)) = last (False # inc ys)" by simp
      find_theorems "last"
      thm last_ConsR
      also have "... = last (inc (ys))" using inc_not_Nil by simp
      finally have last_h: "last (inc (a # ys)) = last (inc (ys))" .

      have "last (a # ys) = last ys" using \<open>ys \<noteq> []\<close> by simp
      then have "last ys = True" using Cons.prems(2) by simp
      then have "last (inc ys) = True" using IH_refined by simp
      then show "last (inc (a # ys)) = True" using last_h by simp
    next
      case False
      then have ""
      then show ?thesis sorry
    qed
  qed
qed


  case 1
  then show ?case by simp
next
  case (2 a ys)
  print_cases

  note step = this
  note step_IH = step(1)
  note step_prems = step(2) step(3)

  from step show ?case
  proof (cases ys)
    case Nil
      (* with step show ?thesis by auto *)
    with step_prems have "a # ys = [True]" by simp
    then have "last (inc (a # ys)) = last (inc [True])" by simp
    also have "... = last [False, True]" by simp
    also have "... = True" by simp
    finally show ?thesis .
  next
    case (Cons b zs)
    then have "ys \<noteq> []" by simp
    then show ?thesis
    proof (cases a)
      case True
      with step_IH and \<open>ys \<noteq> []\<close> have "last ys = True \<Longrightarrow> last (inc ys) = True" by simp
      then show ?thesis sorry
    next
      case False
      then show ?thesis sorry
    qed
  qed
qed


(* lemma "xs \<noteq> [] \<Longrightarrow> last xs = True \<Longrightarrow> last (inc xs) = True" *)

lemma 
  fixes xs
  assumes "xs \<noteq> []" 
    and "last xs = True"
  shows "last (inc xs) = True"
  using assms
proof (induction xs rule: inc.induct)
  case 1
  then show ?case by simp
next
  case (2 a ys)
  print_cases

  note step = this
  note step_IH = step(1)
  note step_prems = step(2) step(3)

  from step show ?case
  proof (cases ys)
    case Nil
      (* with step show ?thesis by auto *)
    with step_prems have "a # ys = [True]" by simp
    then have "last (inc (a # ys)) = last (inc [True])" by simp
    also have "... = last [False, True]" by simp
    also have "... = True" by simp
    finally show ?thesis .
  next
    case (Cons b zs)
    then have "ys \<noteq> []" by simp
    then show ?thesis
    proof (cases a)
      case True
      with step_IH and \<open>ys \<noteq> []\<close> have "last ys = True \<Longrightarrow> last (inc ys) = True" by simp
      then show ?thesis sorry
    next
      case False
      then show ?thesis sorry
    qed
  qed
qed


(*
    with step have "a # ys = True # ys" by simp
    then have "inc (a # ys) = inc (True # ys)" by simp
    also have "inc (True # ys) = False # (inc ys)" by simp
    finally have "last (inc (a # ys)) = last (False # (inc ys))" by simp

    also have "last (False # (inc ys)) = last (inc ys)" using inc_not_Nil and last_ConsR by simp
    finally have "last (inc (a # ys)) = last (inc ys)" by simp
    then show ?thesis sorry
  qed*)


  have "last (inc xs) = last (inc ys)"
  proof (cases a)
    case True
    with step have "xs = True # ys" by simp
    then have "inc xs = inc (True # ys)" by simp
    also have "inc (True # ys) = False # (inc ys)" by simp
    finally have "last (inc xs) = last (False # (inc ys))" by simp

    thm last_ConsR
    find_theorems name:last_ConsR

    also have "last (False # (inc ys)) = last (inc ys)" using inc_not_Nil and last_ConsR by simp
    finally
    then have "inc xs = False # inc ys" by simp
    then show ?thesis sorry
  next
    case False
    then show ?thesis sorry
  qed




  then show "last (inc xs) = True"
  proof (cases ys)
    case Nil
    with step have "a # ys = [True]" by simp
    then have "inc (a # ys) = [False, True]" by simp
    then show ?thesis by simp
  next
    case (Cons b zs) (* ys = b # zs *)
    print_cases
    then show "last (inc (a # ys)) = True" sorry
  qed

  then show "last (inc xs) = True"


lemma "last (nat_to_bin (Suc n)) = True"
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have "nat_to_bin (Suc (Suc n)) = inc (nat_to_bin (Suc n))" by simp

  then show ?case sorry
qed

(*
lemma "xs \<noteq> [] \<Longrightarrow> last xs = True \<Longrightarrow> last (inc xs) = True"
proof -
  assume "xs \<noteq> []" and "last xs = True"
  then have "\<exists>a ys. xs = Cons a ys" by (induction xs) simp+
  then obtain a ys where "xs = Cons a ys" by blast

  then show ?thesis
  proof (cases "ys = []")
    case True
    then show ?thesis by blast
  next
    case False
    then show ?thesis sorry
  qed
  




lemma "last xs = True \<Longrightarrow> last (inc xs) = True"

lemma "trim (inc xs) = inc (trim xs)"
  apply (induction xs)
  apply simp
  try0

lemma "trim (nat_to_bin n) = nat_to_bin n"
proof (induction rule: nat_to_bin.induct)
  case 1
  then show ?case by simp
next
  case (2 n)
  then show ?case try0
qed


lemma "n > 0 \<Longrightarrow> 
  nat_to_bin n = 
  (if (even n) then False else True) # (nat_to_bin (n div 2))"
  oops

lemma "nat_to_bin (bin_to_nat (xs)) = trim (xs)"
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  thm Cons
  print_cases
  then show ?case sorry
qed

(* (if (even n) then False else True) # (nat_to_bin (n div 2)) *)

value "nat_to_bin (bin_to_nat ([True, False, True, True]))"
value "bin_to_nat (nat_to_bin (10))"

lemma "bin_to_nat (nat_to_bin (n)) = n"
proof (induction n)
case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case 
qed
*)

theorem 
  fixes n :: nat
  assumes "n > 0"
  shows "\<exists>w. gn w = n"
  using \<open>n > 0\<close>
proof (induction n rule: nat_induct_non_zero)
  case 1
  have "gn [] = 1" by simp
  then show ?case ..
next
  case (Suc n)
  have "n = bin_to_nat (nat_to_bin (n))"
    then show ?case sorry
  qed

qed

end
