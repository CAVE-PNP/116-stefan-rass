theory induction_nonzero
  imports Main
begin

lemma this_will_not_work: 
  fixes n::nat
  assumes n0: "n > 0"
  shows "(\<Sum>i::nat=0..n. i) > 0"
proof (induction n)
  quickcheck
  (* Quickcheck found a counterexample: n = 1 *)
  oops

(* even though the expression is clearly True for n=1 *)
value "let n=1 in (\<Sum>i::nat=0..n. i) > 0"

(* 
 * it seems possible in isabelle to arrive at False,
 * even when starting with correct assumptions
 * see also: https://isabelle.in.tum.de/community/FAQ#If_I_do_auto.2C_it_leaves_me_a_goal_False._Is_my_theorem_wrong.3F
 *)


lemma this_does: 
  fixes n::nat
  assumes n0: "n > 0"
  shows "(\<Sum>i::nat=0..n. i) > 0"
  (* 
   * but not without this next line
   * (the definition of nat_induct_non_zero 
   *  states "[consumes 1...]" but now how)
   *)
  using n0
proof (induction n rule: nat_induct_non_zero)
  case 1
  then show ?case by simp
next
  case (Suc n)
  then show ?case by simp
qed

lemma interestingly_this_seems_to_work_too: 
  fixes n::nat
  assumes n0: "n > 0"
  shows "(\<Sum>i::nat=0..n. i) > 0"
  using n0 (* only different in this line from the first lemma *)
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case by simp
qed

(* 
 * induction seems to take the context into account 
 * but is seemingly not smart enough to include the assumptions
 *)

(* Stating the assumption as an implication works too *)
lemma "n > 0 \<Longrightarrow> (\<Sum>i::nat=0..n. i) > 0" by (induction n; simp)