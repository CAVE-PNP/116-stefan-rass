#Isabelle Q&A

Q: What's wrong with following function definition?
```
fun count :: "'a ⇒ 'a list ⇒ nat" where
"count _ nil = 0" | "count x (h#t) = count x t + (if x=h then 1 else 0)"
```
A: `nil` is not defined. Use `Nil` or `[]` instead of "nil".

Q: Coq `rewrite` tactic in Isabelle?
A: simp, auto
A: add new rewrite rules with `simp add: `

Q: "The definition of a function f is a theorem named f_def and can be added to a call of simp like any other theorem"... False?

Q: How to declare an inline function?
A: `\<lambda>` or its shorthand `%`

Q: How to require a type `'a` to be both of class times and plus?
A: `'a :: {times, plus}`
A: https://stackoverflow.com/a/65967607

Q: How to print generated proof terms?

Q: How to introduce variables in Isar?
A: `let ?t = ... `

Q: Coq Check
A: value / thm / term / ...?

Q: How to find definitions of a (function|datatype|class) (Coq Print)?
A: Use <kbd>Ctrl</kbd>+Click on the usage to get around.

Q: How to print definitions of rules or facts (e.g. `list.size(3)` or `Cons.IH`)?

Q: How to list all rules starting with `List.`?

Q: What exactly is the dot notation in `List.length_rev` ?

Q: In `assumes ... shows ... using assms` why do we need `using assms`?
