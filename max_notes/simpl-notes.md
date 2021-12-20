# Simpl

This guide will reference the associated thesis

- Norbert Schirmer.
  Verification of Sequential Imperative Programs in Isabelle/HOL (Dissertation, 2005).
  <https://d-nb.info/980343011/34>.

and generated proof outline

- Norbert Schirmer.
  A Sequential Imperative Programming Language Syntax, Semantics, Hoare Logics and Verification Environment (generated from Isabelle sources, 2021).
  <https://www.isa-afp.org/browser_info/current/AFP/Simpl/outline.pdf>.

## Introduction

An overview of the Simpl **language syntax** is given in
ch. [2.1 Abstract Syntax](https://d-nb.info/980343011/34#section.2.1)
(see [Def. 2.1](https://d-nb.info/980343011/34#definition.2.1)).
The **Isabelle syntax and abbreviations** are given in
ch. [2.4.2 Concrete Syntax for Simpl](https://d-nb.info/980343011/34#subsection.2.4.2).

It is worth noting that the type of $`Γ :: {}'p ⇀ ( {}'s, {}'p, {}'f) \text{ com}`$
in _Definition 2.4_ is a _map_-type ($`a ⇀ b`$ defined in `HOL.Map`),
which is different from the standard _function_-type ($`a ⇒ b`$)
in that its output is wrapped by `option` ($`a ⇀ b ≡ a ⇒ b \text{ option}`$).
Thus the environment $`Γ`$ is a collection of defined procedures (of type `com`)
that can be accessed using their "names" of type `'p`.
For undefined procedures, the environment will return `None`.
Note that in the thesis, $`⌊x⌋`$ denotes the option `Some x`.

**States** are modeled as either `statespace` or record types.
For alternative state space representations see ch. 2.4.1.
The basic **heap** model is described in ch. 2.4.9.
**Hoare logic in Simpl** is presented in ch. 3, with syntactic sugar introduced on p. 37.

### Nondeterministic

Simpl includes the command `Spec r` that is only defined in terms of a relation `r`.
The idea is that it represents procedures that are specified, but not implemented.
Since the relation can contain an arbitrary amount of entries $`(s, t)`$
for any given state `s`, the resulting state `t` is not uniquely defined.

### Big-Step and Small-Step Semantics

Big-step corresponds to a functional approach;
recursively referring to nested commands in top-down fashion.
Small-step corresponds to an imperative approach;
focusing on the next concrete instruction instead of abstraction.

This difference becomes apparent when comparing their definitions for Simpl:
Big-step semantics (Def. 2.4) relate a configuration (current state + program to be executed)
to a final state that is reached after evaluating the whole program.
Small-step semantics (Def. 3.13) relate a configuration
to its "next" configuration that is reached after executing one step.

### Notation and Basic Definitions

The notation is somewhat complex, but the main definitions are easy to understand.
The rules are given in diagrams in
[inference rule "standard-form"](https://en.wikipedia.org/wiki/Rule_of_inference#Standard_form).

`Normal` corresponds to "normal" execution states,
as opposed to `Fault` (from failing `Guard`),
`Stuck` (from missing procedures in `Call` or missing results in `Spec`)
and `Abrupt` (from `Throw` exceptions).

The following definitions may be annotated with one or more of the following contexts:
$`Γ,Θ⊢_{/F} ⋯`$.

- `Γ` is the _procedure environment_,
  mapping defined procedure names to their associated _body_.
- `Θ` is the _specification context_,
  containing assumptions about procedures (in the style of Hoare triples),
  "that are taken as granted" in this context.
  - Can be omitted if empty.
- `F` ($`{}_{/F}`$) is the set of _admitted faults_.
  Guards that may produce this fault are assumed (not verified) to hold.
  Ideally, `F` is empty.
  - Can be omitted if empty.

#### Simpl Verification Predicates

- Big-step semantics: $`Γ⊢ ⟨c,s⟩ ⇒ t`$

  - "the execution of command/program `c` on initial state `s` results in new state `t`"
  - $`Γ⊢`$ can be read as "in procedure environment $`Γ`$",
    but can be treated as implicit in most contexts
  - defined as `Semantic.exec` in Isabelle with notation `Γ⊢⟨c, s⟩ ⇒ t`
  - see Def. 2.4, Fig. 2.1
  - Variants:
    - with limit on nested procedure calls (Def. 3.4, Fig. 3.2, `execn`)
      $`Γ⊢ ⟨c,s⟩ \xRightarrow{n} t`$ / `Γ⊢⟨c, s⟩ =n⇒ t`

- Guaranteed termination: $`Γ⊢c ↓ s`$

  - "the execution of command/program `c` on initial state `s` terminates
    (does not run indefinitely)"
  - Termination "rules out infinite computations",
    therefore any procedures containing `Spec` must terminate
    on all possible execution paths to be considered terminating
  - defined as `Termination.terminates` in Isabelle with notation `Γ⊢c↓s`
  - see Def. 2.5, Fig. 2.2 in the thesis

- Small-step semantics: $`Γ⊢(c,s) → (c',s')`$

  - "executing one step of command/program `c` on state `s` results in
    new state `s'` and pending/next command `c'`"
  - defined as `SmallStep.step` in Isabelle with notation `Γ⊢(c, s) → (c', s')`
  - not included in the thesis, seems to have been developed after it was published
  - The new version seems to combine aspects of the old version and big-step semantics,
    avoiding the need for continuations.
  - Alternative version: $`Γ⊢ ⟨cs,css,s⟩ → ⟨cs',css',s⟩`$
    - The alternative/old version is presented in the thesis,
      but has been replaced by the new version in the Simpl Isabelle session.
    - Complex operations, such as `Seq c1 c2` are broken up
      into concrete instructions `[c1, c2]`, until the first one can be executed
    - to allow `THROW` and `CATCH` structures, the list of continuations `css`
      contains lists of steps to be executed in case of `Normal` and `Abrupt` states
      (see Fig. 3.4, rules ExitBlockAbrupt and ExitBlockNormal).
    - defined as `AlternativeSmallStep.step` in Isabelle
      - includes analogous definitions of big-step semantics (`execs`)
        and Termination (`terminatess`) that use continuation lists
    - see Def. 3.13, Fig. 3.4 in the thesis

- Hoare logic (partial correctness): $`Γ,Θ⊢_{/F} P \text{ } c \text{ } Q,A`$

  - "if pre-condition `P` hold, then after executing command `c`,
    the post-condition `Q,A` holds"
    - the post condition consists of two parts `Q` and `A`
      such that the resulting state is either a `Normal` state for which `Q` holds,
      or an `Abrupt` state for which `A` holds  
      (`Normal t ∈ Q ∨ Abrupt t ∈ A` for result state `t`)
  - the difference between total and partial correctness is
    that total correctness requires guaranteed termination
  - defined as `HoarePartialDef.hoarep` in Isabelle
    - with notation `Γ,Θ⊢⇘/F⇙ P c Q,A` where `,Θ` and `⇘/F⇙` may be omitted if empty
  - see Def. 3.1, Fig. 3.1 in the thesis
  - shown to be equivalent to (partial) validity: $`Γ⊨_{/F} P \text{ } c \text{ } Q,A`$
    - defined in terms of big-step semantics,
      to demonstrate that (partial) Hoare logic is sound and complete for Simpl
    - defined as `HoarePartialDef.valid` in Isabelle with notation `Γ⊨⇘/F⇙ P c Q,A`
    - Variants
      - with context (Def. 3.3, `cvalid`):
        $`Γ,Θ⊨_{/F} P \text{ } c \text{ } Q,A`$ / `Γ,Θ⊨⇘/F⇙ P c Q,A`
      - with limited call depth (Def. 3.5, `nvalid`):
        $`Γ\overset{n}⊨_{/F} P \text{ } c \text{ } Q,A`$ / `Γ⊨n:⇘/F⇙ P c Q,A`
      - with both (Def. 3.6, `cnvalid`):
        $`Γ,Θ\overset{n}⊨_{/F} P \text{ } c \text{ } Q,A`$ / `Γ,Θ⊨n:⇘/F⇙ P c Q,A`

- Hoare logic (total correctness)
  - defined as `HoareTotalDef.hoaret` in Isabelle with notation `Γ,Θ⊢⇩t⇘/F⇙ P c Q,A`
  - shown to be quivalent to (total) validity: `validt`, `cvalidt`

## Time Complexity with Simpl

### Limitations

The usage of `Spec` may introduce non-determinism
(for non-univalent (isa: `single_valued`) relations)
or cause programs to get `Stuck` (for non-surjective relations).
While both can be avoided by carefully designing the relations
(and the drawbacks possibly mitigated by proving the relations to be one-to-one),
the usefulness of `Spec` for time-conscious programs seems limited.

There are several commands besides `Spec` that may be used to "hide" complexity,
since they are defined using Isabelle code, and are otherwise unrestricted.

- The command `Basic f` allows arbitrary modification of the current state in one step.
- Boolean conditions for `IF` and `WHILE` are implemented
  as subsets of all possible states or equivalently as predicates on states.
  This allows one to evaluate arbitrary decisions on the current state (all accessible variables in the current scope).
- The command `DynCom c_s` allows executing an arbitrary command
  depending on the current state (`c_s` is a function that outputs a command).

A possible example of how this may introduce unwanted effects is the procedure `´h :== halts' ´m ´t`,
where `halts'` is a predicate that is true iff the TM encoded by `´m`
will eventually halt on the input word encoded by `´t`.
This procedure provably solves the halting problem
in any way it could be defined in Isabelle in one step,
since any definition can be turned into a deciding function,
regardless of whether it is actually computable.
Isabelle code for this example can be found in [Simpl_Notes.thy](../isa_examples/Simpl_Notes.thy).

#### Mitigation

Restricting the Simpl language to make its procedures fulfill
common assumptions in complexity theory seems difficult,
without making Simpl code overcomplicated.

- avoid `Spec`
  - replace by `Basic`
  - replace by a procedure call (requires implementing the function)
- avoid unnecessary usages of `DynCom`
  - use specific (restricted) shortcuts, such as `bind`, `block` or `call` (Defs. 2.6-2.8, resp.)
- for commands that allow arbitrary (Isabelle) definitions (`Basic`, `IF`, `WHILE`),
  restrict usage to computations that are considered to require only one unit of time
  - this can quickly become tricky, considering that for random access machines with unit multiplication $`P = PSPACE`$ holds

### Possible Time Measures

- _Small-step semantics_ (Def. 3.13) unfold the program
  into a list of pending concrete computation steps and execute the head of this list.
  - The length of a fully unfolded program could be used as time measure.
    - It is currently unclear whether it is viable to fully unfold a program prior to "execution"
      - Only the head of the list is examined and processed, then removed;
        the continuation is only processed if no main commands are left
    - Evaluation of boolean conditions (and `Spec` relations as well as guards)
      are not implemented as Simpl operations and thus not added as pending steps
  - Augmenting the reflexive transitive closure ($`Γ⊢ \_ →^* \_`$) with a counter
    could result in a viable time measure.
- _Big-step semantics with limit on nested procedure calls_ (Def. 3.4)
  could be used to bound recursion depth.
  - This approach requires additional attention towards
    Simpl language features other than procedures, such as `WHILE`,
    which could be used to introduce arbitrarily long computations.
  - While this approach effectively limits recursion depth,
    it does not discriminate different procedures,
    so any additional nested calls have to be factored into the total depth.

## Generating Simpl Code

- from JML annotated code
  - Chalin et al. (2008)
    [Using Isabelle/HOL for Static Program Verification in JML4](http://users.encs.concordia.ca/~tphols08/TPHOLs2008/ET/1-8.pdf)
  - Karabotsos et al. (2008)
    [Total Correctness of Recursive Functions using JML4 FSPV](https://www.cs.ucf.edu/~leavens/SAVCBS/2008/papers/Karabotsos-etal.pdf)

## Notes

### On the Intended Use-Case of Simpl

Simpl is designed to verify code written in conventional programming languages.
The inclusion of commands like `Spec` and the implementation
of the commands listed in [Limitations](#limitations) seem reasonable
from this perspective, since time complexity is not a main concern.
Any shortcuts taken in Simpl would have to be implemented
in a programming language manually anyway.

## TODO

- update this document incorporating the user guide (ch. 26 in the AFP proof outline)
- give an overview over library structure
  - Hoare.thy contains syntax and translations between notation
