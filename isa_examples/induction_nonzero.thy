theory induction_nonzero
  imports Main
begin

lemma this_will_not_work: 
  fixes n::nat
  assumes n0: "n > 0"
  shows "(\<Sum>i::nat=0..n. i) > 0"
  apply (induction n)
  quickcheck
  (* Quickcheck found a counterexample: n = 1 *)

  (* even though the expression is clearly True for n=1 *)
  value "let n=1 in (\<Sum>i::nat=0..n. i) > 0"

  apply auto
  (* Now the goal is "False", which in this case may be hard to show *)
  oops

(* 
 * it seems possible in Isabelle to arrive at a goal that is "False", 
 * even when starting with provable goals
 * see also: https://isabelle.in.tum.de/community/FAQ#If_I_do_auto.2C_it_leaves_me_a_goal_False._Is_my_theorem_wrong.3F
 *
 * the error in this case is that induction per default starts at zero 
 * (ignoring the assumption that "n > 0"),
 * thus the first sub-goal already states "0 < 0" when unfolded
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
  apply (induction n rule: nat_induct_non_zero)
  (* note that for the Isar route (proof ... qed) this results in the intuitive cases "1" and "Suc n" *)
  apply auto
  done

lemma interestingly_this_seems_to_work_too: 
  fixes n::nat
  assumes n0: "n > 0"
  shows "(\<Sum>i::nat=0..n. i) > 0"
  using n0 (* only different in this line from the first lemma *)
  apply (induction n)
  (* even more interestingly, this results in the default cases "0" and "Suc n" *)
  apply auto
  done

(* 
 * induction seems to take the context into account 
 * but is seemingly not smart enough to include the assumptions
 *
 * as the sub-goals are somewhat clearer with "rule: nat_induct_non_zero"
 * this method is probably preferable
 *)

(* Stating the assumption as an implication works too *)
lemma "n > 0 \<Longrightarrow> (\<Sum>i::nat=0..n. i) > 0" by (induction n; simp)