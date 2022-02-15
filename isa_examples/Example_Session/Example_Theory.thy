section\<open>Example\<close>

theory Example_Theory
  imports Main
begin

notation (latex output)
  "Set.empty" ("\<emptyset>")
notation (latex)
  card  ("|_|")

text\<open>Just some text.
  \LaTeX -commands are available,
  as well as references to Isabelle entities: @{thm card.empty}.\<close>

lemma some_lemma: "card {} = 0" by (fact card.empty)
    \<comment> \<open>Marginal comments allow short remarks on proof steps.\<close>

(* ML comments are not visible in the PDF *)

end




