theory ex2_3_no_auto
  imports Main HOL.HOL
begin

fun count::"'a \<Rightarrow> 'a list \<Rightarrow> nat" where
  "count a [] = 0" |
  "count a (b # lst) = (if a=b then Suc (count a lst) else (count a lst))"


lemma 
  fixes x xs
  shows "count x xs \<le> length xs"
  using [[rule_trace]]
proof (induction xs)
  case Nil
  have "count x [] = 0" by (rule count.simps(1))

  find_theorems "length [] = 0"
  also have "length [] = 0" by (rule list.size(3))

  thm sym
  finally have "count x [] = length []" by (rule sym)

  find_theorems "?a = ?b \<Longrightarrow> ?a \<le> ?b"
  then show "count x [] \<le> length []" by (rule eq_imp_le)
next
  case (Cons a xs)
  fix b
  thm Cons.IH
  from Cons.IH have "count x (a # xs) \<le> Suc (length xs)"
  proof (cases "x = a")
    case True

(*
    find_theorems "?a \<Longrightarrow> (?a = True)"
    then have ax: "(x = a) = True" by (rule HOL.eqTrueI)

    have "count x (a # xs) = (if True then Suc (count x xs) else count x xs)"
      unfolding count.simps
      by (subst ax) (rule refl)
    
    find_theorems "if _ then _ else _"
    also have "(if True then Suc (count x xs) else count x xs) = Suc (count x xs)" 
      by (rule HOL.if_True)
*)
(* the above section commented out can be replaced by this statement *)
    then have "count x (a # xs) = Suc (count x xs)"
      unfolding count.simps
      by (rule HOL.if_P)

    find_theorems "(Suc ?a) \<le> (Suc ?b)"
    also have "Suc (count x xs) \<le> Suc (length xs)" 
      using Cons.IH by (subst Suc_le_mono)

    finally show ?thesis .
  next
    case False
    then have "count x (a # xs) = count x xs"
      unfolding count.simps
      by (rule HOL.if_not_P)

(*
    have "count x (a # xs) = (if (x = a) then Suc (count x xs) else count x xs)"
      unfolding count.simps
      by (rule refl)

    find_theorems "if _ then _ else _"
    thm HOL.if_not_P
    also have "(if (x = a) then Suc (count x xs) else count x xs) = count x xs" 
      using \<open>x \<noteq> a\<close>
      by (rule HOL.if_not_P)
*)

    find_theorems "?a \<le> ?b \<Longrightarrow> ?a \<le> (Suc ?b)"
    also have "count x xs \<le> Suc (length xs)" 
      using Cons.IH by (rule le_SucI)

    finally show ?thesis .
  qed

  find_theorems "length (_ # _) = _"
  also have "Suc (length xs) = length (a # xs)"
  proof -
    thm Nat.add_0_right[of "length xs"]
    have "(length xs) = (length xs + 0)" by (rule sym) (rule Nat.add_0_right)
    then have "Suc (length xs) = Suc (length xs + 0)" ..
    then have "Suc (length xs) = length xs + Suc 0" by (subst Nat.add_Suc_right)
    also have "length xs + Suc 0 = length (a # xs)" by (rule sym) (rule list.size(4))
    finally show ?thesis .
  qed

  finally show ?case .
qed

lemma 
  fixes x a xs
  shows "count x (a # xs) \<ge> count x xs"
proof (cases "x = a")
  case True
  then have "count x (a # xs) = Suc (count x xs)"
    unfolding count.simps
    by (rule HOL.if_P)

  find_theorems "?a < Suc ?a"
  also have "Suc (count x xs) > count x xs" by (rule lessI)
  find_theorems "?a < ?b ==> ?a <= ?b"
  finally show ?thesis by (rule less_imp_le_nat)
next
  case False
  then have "count x (a # xs) = count x xs"
    unfolding count.simps
    by (rule HOL.if_not_P)
  then have "count x xs = count x (a # xs)" by (rule sym)
  then show ?thesis by (rule eq_imp_le)
qed

end