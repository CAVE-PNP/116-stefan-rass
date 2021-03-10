# Isabelle Q&A

<!-- markdownlint-disable MD001 -->

#### Q: What's wrong with following function definition?

```isabelle
fun count :: "'a ⇒ 'a list ⇒ nat" where
    "count _ nil = 0" |
    "count x (h#t) = count x t + (if x=h then 1 else 0)"
```

A: `nil` is not defined (as indicated by the green syntax/semantic highlighting). Use `Nil` or `[]` instead.

#### Q: Coq `rewrite` tactic in Isabelle?

A: use `subst` and instantiate rule explicitly using `<rule>[of "<var1>" "<var2>"]` when subst cannot find the correct instantiation on its own.
use `fold` and `unfold` to only apply rules in one direction.
(look these up in `isar-ref.pdf` for more information)

Recommendation: **use Isar to specify intermediate results instead** and use simp/auto (add new rewrite rules with `(simp add: <rules>)`).
Isabelle/Isar tries to focus on proofs that read like the ones in conventional mathematical papers.
Therefore the use of `apply`-style proofs is discouraged.

#### Q: "The definition of a function f is a theorem named f_def and can be added to a call of simp like any other theorem"... False?

A: yes, when defined with `definition`

Note: for functions defined like `fun g ...` the following facts are generated instead of g_def:
`g.simps`, `g.induct`, `g.cases`, `g.elims`, `g.pelims` to be used by the respective tactics.
`g.simps` contains the rules that induce the function.
See [isa_examples/f_def_example.thy](isa_examples/f_def_example.thy)

#### Q: How to declare an inline function?

A: `\<lambda>` or its shorthand `%`

Note: for the sake of readability, the use of `λ` is encouraged.
note that entering either of the ASCII versions will prompt replacing them with the unicode lambda in Isabelle/jEdit

#### Q: How to require a type `'a` to be both of class times and plus?

A: `'a :: {times, plus}` (source: <https://stackoverflow.com/a/65967607>)

#### Q: How to print generated proof terms?

#### Q: How to introduce variables in Isar?

A: `let ?t = ...`

#### Q: Coq Check

A: `term`/`value` (get type/value of expression resp.) / `thm` (print facts) / <kbd>Ctrl</kbd>+MouseOver in Isabelle/jEdit (display full name and kind of items)

#### Q: How to find definitions of a (function|datatype|class) (Coq Print)?

A: Use <kbd>Ctrl</kbd>+Click on the usage to jump to the definition.

#### Q: How to print definitions of rules or facts (e.g. `list.size(3)` or `Cons.IH`)?

A: `thm <fact>` (note that `thm list.size` will print multiple lines, as `list.size` is a collection of facts)

#### Q: How to list all rules starting with `List.`?

A: `find_theorems name:List` or `find_theorems name:"List.*"`

#### Q: What exactly is the dot notation in `List.length_rev` ?

A: informally, it specifies the "path" to the item.
since `length_rev` is defined in `/HOL/List.thy` (which is imported either implicitly with `Main` or explicitly as `HOL.List`), its full path is `List.length_rev`.
however, as long as there are no name conflicts, just specifying `length_rev` will suffice.

#### Q: In `assumes ... shows ... using assms` why do we need `using assms`?

A: informally, most tactics only have access to the "direct context".
Isar-style assumptions are not a part of this and instead are collected in `assms`.
`proof` (without an explicit opening)
will use the `standard` tactic to generate more useful goals, but will sometimes require the assumptions as prerequisites.
similarly, `induction` and `cases` can only provide assumptions in the `case.prems` when they are made available to the openings.

#### Q: How to make `simp` use specific facts by default?

A: add the attribute `[simp]` to the fact definition, or use `declare` to manually specify attributes. (see `tutorial.pdf` ch 3.1.2 _Simplification Rules_ and `isar-ref.pdf` ch 3.3.9 _Attributes and theorems_)

```isabelle
lemma MyLemma[simp]: "1 + 1 = 2" by simp
lemma [simp]: "1 + 2 = 3" by simp (* "anonymous" lemma *)

declare MyLemma[simp] (* add to simp *)
declare MyLemma[simp del] (* remove from simp *)
```
