# Isabelle Q&A

<!-- markdownlint-disable MD001 -->

#### What's wrong with following function definition?

```isabelle
fun count :: "'a ⇒ 'a list ⇒ nat" where
    "count _ nil = 0" |
    "count x (h#t) = count x t + (if x=h then 1 else 0)"
```

`nil` is not defined (as indicated by the green syntax/semantic highlighting). Use `Nil` or `[]` instead.

#### Coq `rewrite` tactic in Isabelle?

use `subst` and instantiate rule explicitly using `<rule>[of "<var1>" "<var2>"]` when subst cannot find the correct instantiation on its own.
use `fold` and `unfold` to only apply rules in one direction.
(look these up in `isar-ref.pdf` for more information)

Recommendation: **use Isar to specify intermediate results instead** and use simp/auto (add new rewrite rules with `(simp add: <rules>)`).
Isabelle/Isar tries to focus on proofs that read like the ones in conventional mathematical papers.
Therefore the use of `apply`-style proofs is discouraged.

#### "The definition of a function f is a theorem named f_def and can be added to a call of simp like any other theorem"... False?

yes, when defined with `definition`

Note: for functions defined like `fun g ...` the following facts are generated instead of g_def:
`g.simps`, `g.induct`, `g.cases`, `g.elims`, `g.pelims` to be used by the respective tactics.
`g.simps` contains the rules that induce the function.
See [isa_examples/f_def_example.thy](isa_examples/f_def_example.thy)

#### How to declare an inline function?

`\<lambda>` or its shorthand `%`

Note: for the sake of readability, the use of `λ` is encouraged.
note that entering either of the ASCII versions will prompt replacing them with the unicode lambda in Isabelle/jEdit

#### How to require a type `'a` to be both of class times and plus?

`'a :: {times, plus}` (source: <https://stackoverflow.com/a/65967607>)

#### How to print generated proof terms?

use `prf` and `full_prf` (see `isar-ref.pdf` ch 8.1.1)

Note: this will not work for most theorems, as proof terms are disabled by default (it seems for performance reasons).
[this answer](https://stackoverflow.com/a/31644559/9335596) suggests enabling proof terms by switching to `HOL-Proofs` in the _Theories_ panel and restarting jEdit.
this will cause all theories in HOL to be built (once), which may take a few minutes.
see [this answer](https://stackoverflow.com/a/30692248/9335596) explaining _why this may not be what you want_.
see [proof_terms_example.thy](isa_examples/proof_terms_example.thy) for a demonstration.

#### How to introduce variables in Isar?

`let ?t = ...`

#### Coq Check

`term`/`value` (get type/value of expression resp.) / `thm` (print facts) / <kbd>Ctrl</kbd>+MouseOver in Isabelle/jEdit (display full name and kind of items)

#### How to find definitions of a (function|datatype|class)?

Use <kbd>Ctrl</kbd>+Click on the usage to jump to the definition.

#### How to fix `Cannot update finished theory ...` in a non-painful way so I can jump to definitions with <kbd>Ctrl</kbd>+Click?

Start Isabelle using `/opt/Isabelle2021/bin/isabelle jedit -l Pure` and open the theory file.
This is equivalent to changing the loaded session in the Theories panel in Isabelle/jEdit to `Pure`.

Note that this will cause any imported or opened theories to be checked live, which may take a long time depending on the size of the theories.

#### How to print definitions of rules or facts (e.g. `list.size(3)` or `Cons.IH`)?

use `thm <fact>` (_Pure_ notation) or `print_statement <fact>` (_Isar_ notation)

Note: `thm list.size` will print multiple lines, as `list.size` is a collection of facts

#### How to list all rules starting with `List.`?

`find_theorems name:List` or `find_theorems name:"List.*"`

#### What exactly is the dot notation in `List.length_rev` ?

informally, it specifies the "path" to the item.
since `length_rev` is defined in `/HOL/List.thy` (which is imported either implicitly with `Main` or explicitly as `HOL.List`), its full path is `List.length_rev`.
however, as long as there are no name conflicts, just specifying `length_rev` will suffice.

#### In `assumes ... shows ... using assms` why do we need `using assms`?

informally, most tactics only have access to the "direct context".
Isar-style assumptions are not a part of this and instead are collected in `assms`.
`proof` (without an explicit opening)
will use the `standard` tactic to generate more useful goals, but will sometimes require the assumptions as prerequisites.
similarly, `induction` and `cases` can only provide assumptions in the `case.prems` when they are made available to the openings.

#### How to make `simp` use specific facts by default?

add the attribute `[simp]` to the fact definition, or use `declare` to manually specify attributes. (see `tutorial.pdf` ch 3.1.2 _Simplification Rules_ and `isar-ref.pdf` ch 3.3.9 _Attributes and theorems_)

```isabelle
lemma MyLemma[simp]: "1 + 1 = 2" by simp
lemma [simp]: "1 + 2 = 3" by simp (* "anonymous" lemma *)

declare MyLemma[simp] (* add to simp *)
declare MyLemma[simp del] (* remove from simp *)
```
