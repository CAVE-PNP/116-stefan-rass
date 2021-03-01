theory ex2_5_no_auto
  imports Main
begin

fun sum_upto::"nat \<Rightarrow> nat" where
  "sum_upto 0 = 0" |
  "sum_upto (Suc n) = Suc n + sum_upto n"


lemma gauss_sum [simp]: 
  fixes n::nat
  shows "sum_upto n = (n * (n+1)) div 2"
proof (induction n)
  case 0
  have "sum_upto 0 = 0" by (rule sum_upto.simps(1))

(* division is hard.. *)
  find_theorems "0 div ?a"
  thm div_0
  also have "0 = (0::nat) div 2" by (rule sym, rule div_0)

  find_theorems "0 * _ = 0"
  thm mult_0
  also have "0 div 2 = ((0::nat) * (0 + 1)) div 2" by (subst mult_0, rule refl)
  finally show ?case .
next
  case (Suc n)
  find_theorems "_ + 1"
  have "Suc n * (Suc n + 1) div 2 = Suc n * (Suc (Suc n)) div 2"
    unfolding Suc_eq_plus1 by (rule refl)

  find_theorems "Suc ?n * _ = _"
  find_theorems "_ * Suc ?n = _"
  also have "Suc n * (Suc (Suc n)) div 2 = (Suc n + (Suc n + n * Suc n)) div 2"
    by (unfold mult_Suc_right, fold mult_Suc, rule refl)

  find_theorems "(?a + ?b) + ?c = ?a + (?b + ?c)"
  thm add.assoc
  also have "(Suc n + (Suc n + n * Suc n)) div 2 = (Suc n + Suc n + n * Suc n) div 2"
    unfolding add.assoc by (rule refl)

  find_theorems "?a * ?b = ?b * ?a"
  thm mult.commute
  also have "(Suc n + Suc n + n * Suc n) div 2 = (Suc n * 2 + n * Suc n) div 2"
    (* the specification is necessary, because "unfolding" will not terminate otherwise *)
    unfolding mult.commute[of "Suc n" 2] mult_2 by (rule refl)

  find_theorems "(?c * ?b + ?a) div ?b"
  thm div_mult_self3
  find_theorems "_ \<noteq> 0"
  also have "(Suc n * 2 + n * Suc n) div 2 = Suc n + (n * Suc n) div 2"
    by (subst div_mult_self3, rule numeral_neq_zero, rule refl)

  thm Suc.IH
  also have "Suc n + (n * Suc n) div 2 = Suc n + sum_upto n"
    by (unfold Suc_eq_plus1, subst Suc.IH, rule refl)

  also have "Suc n + sum_upto n = sum_upto (Suc n)"
    by (fold sum_upto.simps(2), rule refl)

  finally show ?case by (rule sym)
qed

end