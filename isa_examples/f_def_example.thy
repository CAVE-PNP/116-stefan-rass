theory f_def_example
  imports Main
begin

fun fib :: "nat \<Rightarrow> nat" where
  fib0: "fib 0 = 0" |
  fib1: "fib (Suc 0) = Suc 0" |
  fibN: "fib (Suc (Suc n)) = fib n + fib (Suc n)"
(* the function definition rules can be given names for easier access, but are available in fib.simps anyways *)

(* use Ctrl+MouseOver in Isabelle/jEdit to see the full names/paths of facts *)
thm fib0
thm fib.simps(1)

thm fib.simps
thm fib.cases
thm fib.induct
thm fib.elims
thm fib.pelims

find_theorems name: "fib.*"

end