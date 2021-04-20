theory proof_terms_example
  imports Main
begin

\<comment> \<open>the output of each command is included in comments. 
    to evaluate \<open>prf\<close> and \<open>full_prf\<close>, switch to the HOL-Proofs session image in the Theories panel 
    and restart Isabelle/jEdit\<close>

print_statement False_not_True
(* theorem False_not_True: shows "False \<noteq> True" *)

thm False_not_True
(* False \<noteq> True *)

prf False_not_True
(* notI \<cdot> _ \<bullet> (False_neq_True \<cdot> _) (* where \<cdot> is Pure.Appt and \<bullet> is Pure.AppP *) *)

full_prf False_not_True
(* notI \<cdot> False = True \<bullet> (False_neq_True \<cdot> False) *)



lemma example1: "1 + 1 = 2" by (rule one_add_one)

prf example1
(* one_add_one \<cdot> TYPE(?'a) \<bullet> (Pure.PClass numeral_class \<cdot> TYPE(?'a)) *)

lemma example2: "1 + 1 = 2" by simp

prf example2
(*
equal_elim \<cdot> _ \<cdot> _ \<bullet>
 (symmetric \<cdot> TYPE(prop) \<cdot> _ \<cdot> _ \<bullet>
   (combination \<cdot> TYPE(bool) \<cdot> TYPE(prop) \<cdot> Trueprop \<cdot> Trueprop \<cdot> _ \<cdot> _ \<bullet>
     (reflexive \<cdot> TYPE(bool \<Rightarrow> prop) \<cdot> _) \<bullet>
     (transitive \<cdot> TYPE(bool) \<cdot> _ \<cdot> _ \<cdot> _ \<bullet>
       (combination \<cdot> TYPE(?'a) \<cdot> TYPE(bool) \<cdot> (=) (1 + 1) \<cdot> (=) 2 \<cdot> _ \<cdot> _ \<bullet>
         (combination \<cdot> TYPE(?'a) \<cdot> TYPE(?'a \<Rightarrow> bool) \<cdot> (=) \<cdot> (=) \<cdot> _ \<cdot> _ \<bullet>
           (reflexive \<cdot> TYPE(?'a \<Rightarrow> ?'a \<Rightarrow> bool) \<cdot> _) \<bullet>
           (eq_reflection \<cdot> TYPE(?'a) \<cdot> _ \<cdot> _ \<bullet>
             (super \<cdot> TYPE(?'a) \<bullet> (super_1 \<cdot> TYPE(?'a) \<bullet> (Pure.PClass numeral_class \<cdot> TYPE(?'a)))) \<bullet>
             (equal_elim \<cdot> _ \<cdot> _ \<bullet>
               (combination \<cdot> TYPE(bool) \<cdot> TYPE(prop) \<cdot> Trueprop \<cdot> Trueprop \<cdot> _ \<cdot> _ \<bullet>
                 (reflexive \<cdot> TYPE(bool \<Rightarrow> prop) \<cdot> _) \<bullet>
                 (combination \<cdot> TYPE(?'a) \<cdot> TYPE(bool) \<cdot> (=) (1 + 1) \<cdot> (=) (1 + 1) \<cdot> _ \<cdot> _ \<bullet>
                   (reflexive \<cdot> TYPE(?'a \<Rightarrow> bool) \<cdot> _) \<bullet>
                   (combination \<cdot> TYPE(num) \<cdot> TYPE(?'a) \<cdot> numeral.numeral 1 (+) \<cdot> numeral \<cdot> _ \<cdot> _ \<bullet>
                     (symmetric \<cdot> TYPE(num \<Rightarrow> ?'a) \<cdot> _ \<cdot> _ \<bullet> (numeral_dict \<cdot> TYPE(?'a))) \<bullet>
                     (reflexive \<cdot> TYPE(num) \<cdot> _)))) \<bullet>
               (add_numeral_special_3 \<cdot> TYPE(?'a) \<cdot> (+) \<cdot> _ \<bullet>
                 (super \<cdot> TYPE(?'a) \<bullet> (super_1 \<cdot> TYPE(?'a) \<bullet> (Pure.PClass numeral_class \<cdot> TYPE(?'a)))) \<bullet>
                 (intro \<cdot> TYPE(?'a) \<cdot> _ \<bullet>
                   (super \<cdot> TYPE(?'a) \<bullet> (super_1 \<cdot> TYPE(?'a) \<bullet> (Pure.PClass numeral_class \<cdot> TYPE(?'a)))) \<bullet>
                   (axioms \<cdot> TYPE(?'a) \<bullet>
                     (super_2 \<cdot> TYPE(?'a) \<bullet> (Pure.PClass numeral_class \<cdot> TYPE(?'a))))))))) \<bullet>
         (reflexive \<cdot> TYPE(?'a) \<cdot> _)) \<bullet>
       (eq_reflection \<cdot> TYPE(bool) \<cdot> _ \<cdot> _ \<bullet> arity_type_bool \<bullet>
         (simp_thms_6 \<cdot> TYPE(?'a) \<cdot> _ \<bullet>
           (super \<cdot> TYPE(?'a) \<bullet> (super_1 \<cdot> TYPE(?'a) \<bullet> (Pure.PClass numeral_class \<cdot> TYPE(?'a))))))))) \<bullet>
 TrueI
*)

end