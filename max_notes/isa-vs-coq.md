# Comparison

- [Comparison](#comparison)
  - [Coq Overview](#coq-overview)
  - [Isabelle Overview](#isabelle-overview)
  - [Editors and Environments](#editors-and-environments)
  - [Readability of Proofs](#readability-of-proofs)
  - [Automation and Tools](#automation-and-tools)
    - [Term simplification](#term-simplification)
    - [Manual search for relevant lemmas](#manual-search-for-relevant-lemmas)
    - [Automagically find proofs](#automagically-find-proofs)
    - [More](#more)

## Coq Overview

- internals
  - calculus of inductive constructions (TODO..)
  - focus on backward reasoning
- pro
  - **proof structure is solid**
  - **more explicit handling of subgoals (less confusing)**
  - more supported IDEs
- contra
  - **weaker automation tools**
  - quickly becomes tedious when large formulas need to be reformed
  - primarily designed for constructive proofs,
    needs to be extended to include some widely accepted standards
    - excluded middle: $`A ∨ ¬A = True`$
    - proof by contradiction
  - theory files (`.v`) need to be compiled in order to import them
    - recompile necessary after Coq version update

## Isabelle Overview

- internals
  - minimalistic kernel supports only natural deduction
    (see also `talk:isa_intro`)
    - small means less room for errors in specification and implementation
    - natural deduction axioms are the "assembly" of isabelle
      - strategies/tactics submit calls to modify kernel state
  - focus on forward reasoning using Isabelle/Isar
- pro
  - **strong automation, powerful tools**
    - more compact proof scripts
    - simple goals are simple to prove
    - [sledgehammer](https://www.youtube.com/watch?v=5Cx7jzq2Bx4)
  - comparatively simple to use
- contra
  - **confusing goal structure and application rules**
  - automation sometimes leads to large leaps in reasoning, missing details
    - proofs are harder to follow
  - lack of good inspection tools (view step-by-step results from automatic solver)
  - lack of unified search/print tools
  - lack of concise documentation
    - everything in paper structure
    - searching terms in `isar-ref.pdf` is tedious and sometimes inconclusive

The language of Coq with the solvers of Isabelle would be an ideal combination.

## Editors and Environments

Both proof assistants include IDEs in their default distributions
(CoqIde and Isabelle/jEdit),
however those are not the most modern or streamlined.
The benefit of a preconfigured IDE is that it _just works™_
and does not have to be fiddled around with
in order to get it to work properly.

Coq provides a web interface (jsCoq) and the VSCode plugin (VSCoq)
works fairly well (comparable with the functionality of CoqIde,
but with all the added benefits of VSCode).

TODO test jsCoq with a bigger example

TODO emacs & proof general?

## Readability of Proofs

TODO overlap with simplification => merge?

Isabelle provides the Isabelle/Isar language extension
(the recommended way to write proofs \[citation needed]),
which enables proofs that state intermediate results
instead of just tactics for the proof assistant.

> A proof translator to natural language (English and French) contributed by
> Yann Coscoy could be used to write in a readable manner the proof terms
> that had been constructed by the tactics.
> This was an important advantage against competitor proof systems
> that did not construct explicit proofs,
> since it allowed auditing of the formal certifications.

TODO find the proof translator

> for improved readability of `.v` files one might use a tool like [Coqatoo](https://github.com/andrew-bedford/coqatoo)

TODO get coqatoo to work (i have not managed to get it to generate output so far)

## Automation and Tools

### Term simplification

TODO overlap with readability => merge?

Isabelle provides a host of tactics like `simp` and `auto` to automatically
apply fitting lemmas and perform rewrites.
Coq provides similarly named tactics `simpl` and `auto`
(as well variations of both), which are however not as powerful
as their Isabelle counterparts and are only able to solve trivial problems.

For arithmetic terms, the Coq tactics `ring_simplify`
(simplify using the properties of a (semi-)ring:
associativity, commutativity for addition, distributivity)
and `ring` (similar, tries to solve the current goal)
as well as their `field` counterparts can be used,
but lack extensibility and integration with more powerful tactics
compared to Isabelle.
_Note that over the naturals and integers,
division has to be handled manually, as **`field`** is not applicable
and **`ring`** is not capable of processing division._
(see the [Coq documentation on `ring` and `field`](https://coq.inria.fr/refman/addendum/ring.html)).
A more powerful option is `lia` (linear integer arithmetic),
a part of the `micromega` solver package that is to replace
the older strategies `omega` and `romega`
(see github issues [#7872](https://github.com/coq/coq/issues/7872) and [#7878](https://github.com/coq/coq/pull/7878)).

The process of applying automatic solvers is by default not very transparent
and can quickly become a guessing game of
which tactic will work with which arguments,
which in turn leads to a lack of understanding of what is actually going on.
Isabelle has a higher risk of becoming like this,
as the automation tools are more powerful.
Both proof assistants have solutions for this issue:
in Isabelle, one can enable tracing with `using [[simp_trace_new mode=full]]`;
in Coq, tactics can be prepended by `info_` (like `info_auto`)
and the command `Show Proof.` can be used inside proofs
to show the associated proof program.

![`trace_1_isa.png`: Isabelle shows the detailed steps taken to prove $`m+0=m`$ by induction on m](img/trace_1_isa.png)

### Manual search for relevant lemmas

Proving anything more than bare basics requires lemmas or proofs too large to be comprehensible.
Finding lemmas that can assist in finding the proof for a posed theorem can be tedious, though.
For this task, the Coq command `Search` and its Isabelle counterpart `find_theorems` can be used.
Both allow using wildcards and search for patterns in theorems.

![`search_1_coq.png`: Searching a lemma for cancelling terms in integer multiplication/division in Coq](img/search_1_coq.png)

![`search_1_isa.png`: Searching a lemma for cancelling terms in integer multiplication/division in Isabelle](img/search_1_isa.png)

Note that this function is not smart in the sense of being able
to compensate for typos and incompleteness,
and even slight mistakes can lead to wrong results or none at all.

![`search_2a_coq.png`: Searching a lemma for cancelling terms in integer addition in Coq](img/search_2a_coq.png)

![`search_2b_coq.png`: Rewriting the search term (without changing its meaning) results in another found lemma (for more complicated items, users may not be this lucky)](img/search_2b_coq.png)

![`search_2a_isa.png`: Searching a lemma for cancelling terms in integer addition in Isabelle](img/search_2a_isa.png)

![`search_2b_isa.png`: Rewriting the search term (without changing its meaning) results in not finding any lemma](img/search_2b_isa.png)

(Isabelle) See `tutorial.pdf` section 3.1.11 for more filters.

#### Finding theorems by name

Theorems whose names are known can be printed out using
the commands `thm <name>` and `Print <name>.` in Isabelle and Coq,
respectively.

The source file in which a specific theorem or similar is defined can be found
in Isabelle/jEdit by control-clicking (`Ctrl+LeftMouseButton`)
on the name of the entity.
No similar functionality exists in Coq \[citation needed],
the source file can instead be found by following the package import path
(obtained from `Locate <name>.`) starting from
`<Coq>/lib/coq/theories/` for the `Coq` root package,
where `<Coq>` is the Coq installation directory.

Example: `Nat.add_0_l` states $`0+n=n`$. Note that there are multiple versions
of `add_0_l` for different domains; `Nat.add_0_l` is stated over the naturals.
`Locate Nat.add_0_l.` yields `Constant Coq.Arith.PeanoNat.Nat.add_0_l`.
The path to the source file is therefore `<Coq>/lib/coq/theories/Arith/PeanoNat.v`.

### Automagically find proofs

`sledgehammer` is the most powerful of Isabelle's automation tools,
querying several automatic solvers in parallel and reporting
if one or more found a correct proof.
Some of the solvers automatically find relevant lemmas,
which simplifies the process immensely.
Sledgehammer is not a tactic, but a tool that searches for relevant tactics
and lemmas for a problem, and (if successful) outputs a sequence of steps
(normal Isabelle tactics) that solve the current goal.

This can be utilized to avoid large amounts of work finding proofs
for simple lemmas, but at the same time contributes to the readability problem,
as often the generated proofs contain (or are) obscure one-liners
that do not make sense at first glance.

The option to generate _Isar_ proofs has been included,
but this does not solve the problem of readability,
as these proofs again often contain obscure parts \[citation needed].
Coq has no comparable tools, so finding proofs that require only a few known
facts and techniques but a large number of steps can take a long time.

Sledgehammer is however not a complete substitute for
someone who knows what they are doing and will often fail
when confronted with seemingly simple problems.

![`isa_sledge_1.png`: sledgehammer bounces right off the famous integer sum formula](img/isa_sledge_1.png)

This however can quickly change when the right approach is chosen.

![`isa_sledge_2.png`: applying the tactic `induction` provides clear goals for sledgehammer to smash](img/isa_sledge_2.png)

### More

Another very useful gadget built into Isabelle is Quickcheck (`quickcheck`),
which automatically checks posed theorems for counterexamples.
This prevents unnecessary effort put into trying to prove theorems
with minor formulation errors.
A restricted version (Auto Quickcheck) that only finds trivial counterexamples
is executed automatically when a theorem is posed:

TODO find out in which way auto quickcheck is restricted. possible: number of variables to instantiate

![`isa_counter_example.png`: Isabelle automatically determines that the theorem is false and provides a counterexample](img/isa_counter_example.png)
