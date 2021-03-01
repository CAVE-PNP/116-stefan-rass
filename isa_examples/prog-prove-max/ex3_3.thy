theory ex3_3
  imports Main
begin

(* Reflexive Transitive Closure *)
inductive star :: "( 'a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
  refl: "star r x x" |
  step: "r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"

inductive star' :: "( 'a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
  refl': "star' r x x" |
  step': "star' r x y \<Longrightarrow> r y z \<Longrightarrow> star' r x z"


lemma h0: "r x y \<Longrightarrow> star r x y"
  by (auto simp add: refl step)

lemma h'0: "r x y \<Longrightarrow> star' r x y"
  apply (rule step')
   apply (auto simp add: refl' step')
  done

lemma h1: "star r x y \<Longrightarrow> r y z \<Longrightarrow> star r x z"
  by (induction rule: star.induct) (auto simp add: h0 step)

(* magic step: reorder assumptions *)
lemma h'1: "star' r y z \<Longrightarrow> r x y \<Longrightarrow> star' r x z"
  apply (induction rule: star'.induct)
   apply (auto simp add: h'0 step')
  done

theorem t1: "star' r x y \<Longrightarrow> star r x y"
  by (induction rule: star'.induct) (auto simp add: h1 refl)

theorem t2: "star r x y \<Longrightarrow> star' r x y"
  apply (induction rule: star.induct)
   apply (auto simp add: h'1 refl')
  done

end