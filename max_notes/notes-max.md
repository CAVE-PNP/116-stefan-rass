# Notes PNP

The first challenge will be the selection of a suitable proof assistant.
Initial research by Stefan Rass resulted in the two preliminary candidates
Isabelle/HOL and Coq.
They seem similar in many respects, both having a refined set of features
and both having been in development for more than 30 years,
with an active community and steady support.

As outlined in the [Comparison](#Comparison), Coq is easier to use
for small scale precise manipulation (for example, rewriting the current
proof goals) and Isabelle provides powerful automatic solvers that
help prevent small scale manipulations from being necessary.

## Contents

- [Notes PNP](#notes-pnp)
  - [Contents](#contents)
  - [Isabelle](#isabelle)
    - [Getting Started](#getting-started)
    - [Structure (work in progress)](#structure-work-in-progress)
    - [Versions](#versions)
    - [IDEs](#ides)
    - [Proof methods (work in progress)](#proof-methods-work-in-progress)
    - [General](#general)
  - [Coq](#coq)
    - [Coq IDEs](#coq-ides)
  - [Comparison](#comparison)
    - [Coq Overview](#coq-overview)
    - [Isabelle Overview](#isabelle-overview)
    - [Editors and Environments](#editors-and-environments)
    - [Readability of Proofs](#readability-of-proofs)
    - [Automation and Tools](#automation-and-tools)
  - [Proofs](#proofs)
    - [Barriers](#barriers)
    - [more](#more)
  - [Ongoing Work](#ongoing-work)
  - [Sources and Literature](#sources-and-literature)
    - [Isabelle/HOL related](#isabellehol-related)
    - [Coq related](#coq-related)
    - [General Quotes](#general-quotes)
  - [Additional reading](#additional-reading)
    - [Comparison of proof assistants](#comparison-of-proof-assistants)
    - [Inspecting solver steps](#inspecting-solver-steps)

## Isabelle

### Getting Started

The best option to start working with Isabelle seems to be reading `prog-prove.pdf`
(pdf in seafile [desktop](seafile://openfile?repo_id=d3f2bfd0-b877-47a7-a7ca-4af40c3d18d4&path=/Isabelle/manuals/prog-prove.pdf)/[web](https://seafile.aau.at/smart-link/eb40beb8-30e4-4485-bc89-2636ec1e8349/),
online lecture available from the [TU München's course page](https://www21.in.tum.de/teaching/semantik/WS20/#material))
and trying to solve as many of the exercises as possible.

### Structure (work in progress)

Terms like "Isabelle/\<name>" denote "\<name> in the context of Isabelle".
For instance, Isabelle/jEdit is the bundled IDE,
Isabelle/HOL is the specification for constructing higher-order logic
and Isabelle/ML is the use of ML in the Isabelle environment.

Notable components:

- Isabelle/Pure: logical framework, the "kernel" of Isabelle
  - the "assembly" of Isabelle; basically only supports natural deduction,
    everything else (including advanced tactics) is just a layer of abstraction
    constructing terms for Isabelle/Pure
  - written in [Standard ML](https://standardml.org)
    (SML '97, Isabelle uses the [PolyML](https://www.polyml.org/) implementation)
- [Isabelle/HOL](https://isabelle.in.tum.de/doc/logics.pdf):
  formalization of higher order logic
- [Isabelle/Isar](https://isabelle.in.tum.de/library/Doc/Implementation/implementation.pdf)
  abstracts ML commands in an effort to create more readable proofs
  - proof commands are reminiscent of natural language proofs,
    e.g. `from A have B using C`
- Isabelle/PIDE is a protocol for communication between a language kernel and an IDE
  - this is used with Isabelle/jEdit and, through an abstraction layer, with Isabelle/VSCode

### Versions

There are multiple options for using Isabelle. One can download and build
the sources (see [Mercurial repo](https://isabelle.sketis.net/repos/isabelle)
or [this view](https://isabelle-dev.sketis.net/source/isabelle/)
with a more modern UI), download a
["nightly" repository snapshot](https://isabelle.sketis.net/devel/release_snapshot/),
or download a release version
(see [Installation guide](https://isabelle.in.tum.de/installation.html)).

Release versions do not receive patches, but are community tested with
release candidates before going live (this then is the last chance to request
features for a release). Release versions are scheduled to release every
8-10 months

Note that for most of this section is mentioned nowhere on the official sites.
Instead this information is scraped together from multiple sources,
mainly [`talk:isa-news` (at ~1min)](https://youtu.be/MpJZI1M_uVs?t=67).
See also the section on [Isabelle resources](#Isabelle-resources).

### IDEs

The available options seem to be:

- _Isabelle/jEdit_, the modified and preconfigured distribution of _jEdit_
  bundled with Isabelle installers
- _emacs_ with the _Proof General_ plugin
- _Visual Studio Code_ with the _Isabelle_ plugin

Deprecated or not supported:

- [Isabelle/Eclipse](http://andriusvelykis.github.io/isabelle-eclipse/),
  latest commit from 2013
- Isabelle/IntelliJ ?

#### Isabelle/jEdit

This IDE feels old and clunky if one is used to more modern,
cutting edge solutions like JetBrains IntelliJ or Microsoft Visual Studio Code.
_However_, considering all options, this seems to be the most promising one
with the best user experience.
Isabelle/jEdit comes ready for use, preconfigured,
and bundled with the Isabelle installer.

Note: Makarius Wenzel, one of the main contributors to Isabelle,
also contributes to jEdit.

TODO Isabelle/PIDE

##### Adjusting abbreviations

TODO: verify that the following statements (changing symbol settings)
also work for other editors than Isabelle/jEdit

As Isabelle uses many symbols of traditional mathematical notation
(for instance `∧`, the logical AND),
internally represented by their ASCII names (e.g. `\<and>`),
quick shortcuts for entering symbols are very convenient.
Many shortcuts are provided by default (e.g. `==>` for `⟹`),
however, some of them are also cumbersome to enter (e.g., `/\` for `∧`).

> A symbol abbreviation that is a plain word, like `ALL`,
> is treated like a syntax keyword.
> Non-word abbreviations like `-->` are inserted more aggressively,
> except for single-character abbreviations like `!` above.
>
> \-- `jedit.pdf` chapter 3.7.1.3 Isabelle symbols (p34)

Abbreviations can be added or removed by (creating and) editing the file `$ISABELLE_USER_HOME/etc/symbols`,
following the syntax of `$ISABELLE_HOME/etc/symbols`.

_Note: **`$ISABELLE_HOME`** is the location of the Isabelle installation,
and **`$ISABELLE_USER_HOME`** typically is **`$USER_HOME/.isabelle/Isabelle20xx`**.
For Windows, **`$USER_HOME`** is **`%USERPROFILE%`**._

For instance, starting Isabelle the following `symbols` file (in the user settings directory)
adds the abbreviations `&&` for `∧` and `||` for `∨`.

_Note: the lines are copied and modified from the system version of **`symbols`**._

```ps
# add new abbreviation for logical and: &&
\<and>       code: 0x002227  group: logic  abbrev: /\  abbrev: &  abbrev: &&
# and for logical or: ||
\<or>        code: 0x002228  group: logic  abbrev: \/  abbrev: |  abbrev: ||

# remove || as abbreviation of these three symbols
# as only then || will be directly replaced
\<parallel>  code: 0x002225  group: punctuation
\<bar>       code: 0x0000a6  group: punctuation
\<bbar>      code: 0x002aff  group: punctuation

```

#### Isabelle/VSCode

Does provide a less streamlined experience than Isabelle/jEdit,
as the user has to manually install the IDE and extensions in addition to
Isabelle itself.

##### Support and trends

According to [`talk:isa-news` (at ~22min)](https://youtu.be/MpJZI1M_uVs?t=1342),
Isabelle/VSCode is more of an experiment (to learn from the VSCode platform),
and there are no intentions of making this a supported and recommended
main platform for Isabelle.
This attitude towards VSCode is due to it being somewhat resource-inefficient
(since it is an [Electron](https://www.electronjs.org/) app with a different
language server interface than PIDE, the one built for Isabelle/jEdit),
but providing many benefits that are not (yet) available in jEdit that stem
from its open framework and large community (see also `talk:isa-vscode`).

##### Isabelle/VSCode Setup

Install and configure extensions:

1. extension corresponding to the Isabelle version
   - for [Isabelle20xx releases](https://isabelle.in.tum.de/),
     use [`makarius.isabelle20xx`](https://marketplace.visualstudio.com/search?term=Isabelle20*&target=VSCode),
   - for [development builds](https://isabelle.sketis.net/devel/release_snapshot/),
     use [`makarius.isabelle`](https://marketplace.visualstudio.com/items?itemName=makarius.isabelle)
   - for a list of Isabelle/VSCode extensions, see
     [extensions published by Makarius Wenzel](https://marketplace.visualstudio.com/publishers/makarius).
2. install [_Prettify Symbols Mode_](https://marketplace.visualstudio.com/items?itemName=siegebell.prettify-symbols-mode)
3. configure extensions
   1. in particular, set the `isabelle.home` variable:
      - enter settings via `File > Preferences > Settings` or `Ctrl+,`
      - enter `isabelle.home` in the search bar or navigate to
        `Extensions > Isabelle > Isabelle: Home`
      - enter the directory in which Isabelle is installed
   2. \[optional] configure _Prettify Symbols Mode_
      - `"prettifySymbolsMode.adjustCursorMovement": true`
      - `"prettifySymbolsMode.revealOn": "cursor"` or `"never"`

##### Working environment

- open an Isabelle/HOL `.thy` file
- show output
  - select `View > Output` (`Ctrl+Shift+U`)
  - there, select the `Isabelle Output` channel in the dropdown menu
- show the state
  - select `View > Command Palette` (`Ctrl+Shift+P`)
  - enter `Isabelle: Show State`
    - wait until the Isabelle backend has launched (will display a message),
      as executing _show state_ before that will have no effect

##### Weird symbol representation

Symbols, (like `⟹`) are only visually inserted and the
background representations (like `\<Longrightarrow>`) are hidden
(unlike in jEdit where the ASCII representations are replaced
by Unicode symbols in the editor buffer).
This leads to strange behavior when trying to edit or remove such symbols.

The best way to cope with this seems to be setting the defaults
for _Prettify Symbols Mode_ as stated in the setup instructions.
It does not seem to be possible to set these as _Isabelle specific_,
since the Isabelle extension manages those.

#### Proof General (work in progress)

Based on emacs. Seems to be the primarily recommended editor for Isabelle
(and other proof assistant software, hence the name).

I did not manage to start proof general in windows.
the normal way of opening proof general is calling `isabelle emacs`
(see [this](https://proofgeneral.github.io/doc/master/userman/Isabelle-Proof-General/))
however, the `isabelle` binary is not usable in windows.
`Isabelle2020.exe emacs` opens a new file called `emacs` in the Isabelle/jEdit IDE.

TODO

- try through the bundled, integrated cygwin console
  - `Cygwin-Setup.bat`, then in `Cygwin-Terminal.bat` launch `isabelle`
- try the binaries in WSL

##### Support

From the [Proof General GitHub repo](https://github.com/ProofGeneral/PG/#more-info) (accessed 2020-11-30):

> Proof General used to support other proof assistants, but those
> instances are no longer maintained nor available in the MELPA package:
>
> - Legacy support of [Isabelle](https://www.cl.cam.ac.uk/research/hvg/Isabelle/)

Latest changes in [`/isar/` directory](https://github.com/ProofGeneral/PG/tree/master/isar)
are two years old, explicitly states support for _Isabelle2011_.

### Proof methods (work in progress)

**_TODO_** induct/induction

- induction by function rules, as opposed to "normal" induction
  following the rules of the function `Suc`/`S`.
  See `prog-prove.pdf`, 4.4.3 Computation Induction
- other induction rules like `nat_induct_non_zero` and `nat_induct_at_least`

**_TODO_** \[intro]/introduction rules

**_TODO_** sorry

listed from ~weak to strong

**_TODO_** the `..` ("default") and `.` ("immediate") tactics. something like:

- `.` proves an already known result
  (including rewriting constant abbreviations)
- `..` proves a goal through a single application of one of
  the natural deducation axioms

**_TODO_** unfold (acts on all subgoals)

_simp_. (Acts on all subgoals?)
Simplifies terms as much as possible using a set of predefined
simplification rules. Will apply simplifications to both sides of equations
until equality is reached, or no more rules are applicable.
Lemmas/Theorems can be added to the list of simplifications by

```isabelle
lemma <name> [simp]: "<lemma>"

```

however care needs to be taken as `simp` will blindly apply matching rules,
which can easily result in infinite loops.
A far more robust option is to add or suppress rules for proofs as needed:

```isabelle
apply(simp add: <additional rule names>
           del: <rules to suppress>)

```

Alternatively, `simp` can be instructed to only use a given set of rules
with `simp only: <rules>`.

Sources: `prog-prove.pdf`, `tutorial.pdf` chapter 3.1.4

**_TODO_** auto (acts on all subgoals)

### General

> Remember that `f t u` means `(f t) u` and not `f (t u)`!
>
> equality has a high priority \[...] `¬ ¬ P = P` means `¬ ¬ (P = P)` and
> not `(¬ ¬ P) = P`. When using `=` to mean logical equivalence,
> enclose both operands in parentheses, as in `(A ^ B) = (B ^ A)`

## Coq

Seems more focused on functional aspect and proving the correctness of programs
(including generating certified programs from proofs of correctness for said programs).

### Coq IDEs

The available options seem to be:

- _CoqIde_, a part of the Coq project
- _jsCoq_, a web-based environment
- _Jupyter_ with the _coq_jupyter_ kernel
- _emacs_ with the _Proof General_ and _Company-Coq_ plugins
- _Visual Studio Code_ with the _VSCoq_ plugin
- _Vim_ with the _Coqtail_ plugin

#### CoqIde

Similar to Isabelle/jEdit, feels even more old and clunky.

#### jsCoq

Web-based, interactive. See

- [jsCoq demo](https://jscoq.github.io/)
- [jsCoq scratchpad](https://jscoq.github.io/scratchpad.html) (local storage)
- [CollaCoq](https://x80.org/collacoq/), "the Coq pastebin"

#### VSCoq (VSCode)

Seems to work well.

For basic use see the [plugin page](https://marketplace.visualstudio.com/items?itemName=maximedenes.vscoq#basic-usage).

Note: if commands do not work, restart VSCode
(do not close the tab of the opened `.v` file, just close VSCode and launch it again).

##### Settings

configure at `Settings` (`Ctrl+,`) > `Extensions` > `Coq configuration`

###### required

- `Coqtop: Bin Path` enter path to `Coq/bin` dir
- (for Windows) for `Coqtop: Coqidetop Exe` and `Coqtop: Coqtop Exe`, add `.exe`

###### recommended

- `Coq: Auto Reveal Proof State At Cursor`: enable
- `Coqtop: Start On`: set to `open-script`

## Comparison

### Coq Overview

- internals
  - calculus of inductive constructions (TODO..)
  - focus on backward reasoning
- pro
  - **proof structure is solid**
  - **more explicit handling of subgoals (less confusing)**
- contra
  - **weaker automation tools**
  - quickly becomes tedious when large formulas need to be reformed
  - primarily designed for constructive proofs,
    needs to be extended to include some widely accepted standards
    - excluded middle: `A || !A == true`
    - proof by contradiction
  - theory files (`.v`) need to be compiled in order to import them
    - recompile necessary after Coq version update

### Isabelle Overview

- internals
  - minimalistic kernel supports only natural deduction
    (see also `talk:isa_intro`)
    - small means less room for errors in specification and implementation
    - strategies/tactics submit calls to modify kernel state
  - focus on forward reasoning
- pro
  - **strong automation, powerful tools**
    - more compact proof scripts
    - simple goals are simple to prove
    - [sledgehammer](https://www.youtube.com/watch?v=5Cx7jzq2Bx4)
  - comparatively simple to use
- contra
  - **confusing goal structure and application rules**
  - automation sometimes leads to large leaps in reasoning, missing details => harder to follow
  - lack of good inspection tools (view step-by-step results from automatic solver)

The language of Coq with the solvers of Isabelle would be an ideal combination.

### Editors and Environments

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

### Readability of Proofs

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

### Automation and Tools

#### Term simplification

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

! [`trace_1_isa.png`: Isabelle shows the detailed steps taken to prove `m+0=m` by induction on m](https://seafile.aau.at/lib/d3f2bfd0-b877-47a7-a7ca-4af40c3d18d4/file/examples/img/trace_1_isa.png?raw=1)

#### Manual search for relevant lemmas

Proving anything more than bare basics requires lemmas or proofs too large to be comprehensible.
Finding lemmas that can assist in finding the proof for a posed theorem can be tedious, though.
For this task, the Coq command `Search` and its Isabelle counterpart `find_theorems` can be used.
Both allow using wildcards and search for patterns in theorems.

! [`search_1_coq.png`: Searching a lemma for cancelling terms in integer multiplication/division in Coq](https://seafile.aau.at/lib/d3f2bfd0-b877-47a7-a7ca-4af40c3d18d4/file/examples/img/search_1_coq.png?raw=1)

! [`search_1_isa.png`: Searching a lemma for cancelling terms in integer multiplication/division in Isabelle](https://seafile.aau.at/lib/d3f2bfd0-b877-47a7-a7ca-4af40c3d18d4/file/examples/img/search_1_isa.png?raw=1)

Note that this function is not smart in the sense of being able
to compensate for typos and incompleteness,
and even slight mistakes can lead to wrong results or none at all.

! [`search_2a_coq.png`: Searching a lemma for cancelling terms in integer addition in Coq](https://seafile.aau.at/lib/d3f2bfd0-b877-47a7-a7ca-4af40c3d18d4/file/examples/img/search_2a_coq.png?raw=1)

! [`search_2b_coq.png`: Rewriting the search term (without changing its meaning) results in another found lemma (for more complicated items, users may not be this lucky)](https://seafile.aau.at/lib/d3f2bfd0-b877-47a7-a7ca-4af40c3d18d4/file/examples/img/search_2b_coq.png?raw=1)

! [`search_2a_isa.png`: Searching a lemma for cancelling terms in integer addition in Isabelle](https://seafile.aau.at/lib/d3f2bfd0-b877-47a7-a7ca-4af40c3d18d4/file/examples/img/search_2a_isa.png?raw=1)

! [`search_2b_isa.png`: Rewriting the search term (without changing its meaning) results in not finding any lemma](https://seafile.aau.at/lib/d3f2bfd0-b877-47a7-a7ca-4af40c3d18d4/file/examples/img/search_2b_isa.png?raw=1)

(Isabelle) See `tutorial.pdf` section 3.1.11 for more filters.

##### Finding theorems by name

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

Example: `Nat.add_0_l` states `0+n=n`. Note that there are multiple versions
of `add_0_l` for different domains; `Nat.add_0_l` is stated over the naturals.
`Locate Nat.add_0_l.` yields `Constant Coq.Arith.PeanoNat.Nat.add_0_l`.
The path to the source file is therefore `<Coq>/lib/coq/theories/Arith/PeanoNat.v`.

#### Automagically find proofs

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

! [`isa_sledge_1.png`: sledgehammer bounces right off the famous integer sum formula](https://seafile.aau.at/lib/d3f2bfd0-b877-47a7-a7ca-4af40c3d18d4/file/examples/img/isa_sledge_1.png?raw=1)

This however can quickly change when the right approach is chosen.

! [`isa_sledge_2.png`: applying the tactic `induction` provides clear goals for sledgehammer to smash](https://seafile.aau.at/lib/d3f2bfd0-b877-47a7-a7ca-4af40c3d18d4/file/examples/img/isa_sledge_2.png?raw=1)

#### More

Another very useful gadget built into Isabelle is Quickcheck (`quickcheck`),
which automatically checks posed theorems for counterexamples.
This prevents unnecessary effort put into trying to prove theorems
with minor formulation errors.
A restricted version (Auto Quickcheck) that only finds trivial counterexamples
is executed automatically when a theorem is posed:

TODO find out in which way auto quickcheck is restricted. possible: number of variables to instantiate

! [`isa_counter_example.png`: Isabelle automatically determines that the theorem is false and provides a counterexample](https://seafile.aau.at/lib/d3f2bfd0-b877-47a7-a7ca-4af40c3d18d4/file/examples/img/isa_counter_example.png?raw=1)

## Proofs

A lot of meta-results about `P vs NP` have been published;
some general properties of proofs and techniques that must be fulfilled,
some more concrete showing that certain techniques are doomed to fail.

### Barriers

#### Relativization

##### Oracle Machines

In most definitions, an oracle machine is a TM that is given access
to an _oracle_, a mechanism that answers a specific, predefined
kind of question instantaneously (in one operation/costing one unit of time).
The oracle is often modeled as a separate tape onto which the TM
can write queries and receive answers.
The resulting classes are often written as `C^A`,
where `C` is a complexity class and `A` is an oracle.

This leads to classes like `P^NP` (the class of all problems solvable in
polynomial time by a TM with access to an oracle that can solve an NP-complete
problem, like `SAT`, since this extends to all problems in NP via polynomial
reduction), which can be shown to include `NP` (`NP ⊆ P^NP`).
These concepts enable more constructions, like the polynomial hierarchy `PH`.

##### Basic Idea

It can then be shown, that oracles `A` and `B` exist, such that
`P^A = NP^A` and `P^B ≠ NP^B` hold
(see [Baker-Gill-Solovay-1975](doi.org/10.1137/0204037)).
In other words, `P = NP` holds _relative to oracle `A`_,
but fails _relative to oracle `B`_.

A very quick introduction to relativization would be the following question
from [David Harris](https://mathoverflow.net/questions/75890/definition-of-relativization-of-complexity-class):

> Is there any general definition, for a class `C` of languages,
> what is the relativized class `C^A` for an oracle `A`?

and the answer by [Timothy Chow](https://mathoverflow.net/a/76021):

> The short answer is no.
> The simplest way to see that `C^A` cannot possibly depend only on `C` and `A`
> as sets of strings is the following spurious argument that has confused
> generations of students.
> Assume that `P = NP`. Then for all oracles `A`, `P^A = NP^A`.
> But by Baker–Gill–Solovay, we know that there exists an oracle A
> such that `P^A ≠ NP^A`. This is a contradiction. Hence `P ≠ NP`. Q.E.D.,
> and I await my $1 million check.

Note: the flaw in this argument as noted by the author himself
is the assumption that `P = NP` implies `P^A = NP^A`.
Even though the sets of languages captured in the definitions
of the two complexity classes match, the definitions themselves differ,
and so may also the effects of giving access to an oracle.

When working with relativizations, special care needs to be taken,
as even small changes in definitions of classes
(see `IP vs IPP` in [Chang1994](<https://doi.org/10.1016/S0022-0000(05)80084-4>))
and oracle access mechanisms (see `relative.pdf`) can change results.

##### Notation

It is said that a statement `B ~ C` _relativizes_
if `B^A ~ C^A` remains true for all oracles `A`. \[citation needed]

Similarly, a proof technique is said to _relativize_
if it is unaffected by the addition of an oracle.

A _positive relativization_ of a statement `B ~ C`
is an example of an oracle `A` for which `B^A ~ C^A` holds.
A _negative relativization_ of a statement `B ~ C`
is an example of an oracle `A` for which `B^A ≁ B^A` (`¬(B^A ~ C^A)`) holds.

##### Remark (Stefan)

as it stands, I would agree with all that you noted; perhaps adding only two thoughts:
first: the concept of an oracle TM is rarely defined to the final extent of rigor, since several aspects go unexplained in most
instances where oracles are used: for example, does the space on the oracle tape count or does it not count towards the overall space
complexity? Does the time that I need to write the query on the oracle tape add to the running time of the TM? Can the oracle take
queries that are exponentially long (it can, if the time for writing the query is not counted). Do I write the query on a separate tape
or could I also "mark" a region on any tape and declare this region as the query to the oracle? The first method would practically be a
"call by value", whereas the second method would model a "call by reference" in real life programming languages.

Second, and more personally, I believe that reasoning under relativization is the same as adding one more axiom to the underlying
maths (speaking computer-science vocabulary, I would add one more instruction to my assembly in the machine that I consider).
Formally, we have worked on showing that by adding certain instructions to the machine model, we end up contradicting
well known (and proven as correct) facts, since the resulting machines are instantly more powerful than the original ones. Thus,
what is true without the oracle can be wrong with the oracle, say, the halting problem could even become solveable.
More formally, we used the forcing technique (unpublished work) to prove this - something that I will share with you along the lines
of looking into independence proofs (the third category that yet went without a paper selected, as they were all wrong :-))

##### Relevance in Complexity Theory

Relativization can be used to determine if certain proof techniques
are applicable to a problem.
For example, since `P vs NP` does not relativize (in either direction),
**any technique solving the problem must not relativize either**.
This is described as the barrier of relativization
that any proof for `P vs NP` has to overcome.

Great care needs to be taken when drawing conclusions from
relativization-related results; a particularly problematic topic are
space-bound complexity classes, as the use of the oracle tape provides
room for interpretation. TODO extend

It is noted that most known proof techniques relativize (see `relative.pdf`).
Conversely, it can also serve as a heuristic
for the difficulty and solvability of a problem;
if there are no known negative relativizations for a statement,
a relativizing proof may yet be possible. (see `relative.pdf`)

An often cited result regarding relativization is that `IP = PSPACE` holds
(see [Shamir1992](https://doi.org/10.1145/146585.146609))
even though there exist contradictory relativizations
`IP^A = PSPACE^A` and `IP^B ≠ PSPACE^B`
(see [Fortnow1988](<https://doi.org/10.1016/0020-0190(88)90199-8>))
and `IP ≠ PSPACE` holds for almost all oracles
(see [Chang1994](<https://doi.org/10.1016/S0022-0000(05)80084-4>)).
(all cited in [this answer](https://cs.stackexchange.com/a/41562))

##### Arithmetization and Algebrization

The technique that was used to prove `IP = PSPACE`
([Shamir1992](https://doi.org/10.1145/146585.146609))
transforms quantified formulas over boolean values into arithmetic formulas
over a field like the integers and reasons about the resulting polynomials
in a process that was coined _arithmetization_
by [Babai1991](https://doi.org/10.1007/BF01200057).

[Aaronson2009](https://doi.org/10.1145/1490270.1490272) expand this idea
to include oracle access to _field extensions **`A'`** of boolean oracles `A`_
(all polynomials over finite fields
(1) that match the boolean oracle's output if the query length matches and
(2) with degree bound by a constant)
and name the resulting barrier _algebrization_.

Note that a _boolean oracle_ in this context is a function `A: {0,1}^n → {0,1}`.

An inclusion `C ⊆ D` _algebrizes_ if `C^A ⊆ D^A'`
holds for all oracles `A` and extensions `A'`.
A separation `C ⊄ D` _algebrizes_ if `C^A' ⊄ D^A`
holds for all oracles `A` and extensions `A'`.

The asymmetry in the definition seems integral for the desired property
of the constructed barrier to separate previously shown results
that do not relativize (like `IP = PSPACE`, which algebrizes)
from those that seem harder to achieve
(like `P vs NP`, which is shown not to algebrize).

##### Local Checkability

[Arora1992](https://www.researchgate.net/publication/267777944_Relativizing_versus_Nonrelativizing_Techniques_The_Role_of_Local_Checkability)
formalize the notion that _"checking the correctness of a computation
is simpler than performing the computation itself"_ by introducing
two similar "proof checker" complexity classes with different definitions
`PF-CHK(t(n))` and `WPF-CHK(t(n))`.

The _Local Checkability Theorem (LCT)_ is introduced as `NP = PF-CHK(log n)`,
and similarly, the _weak LCT_ as `NP = WPF-CHK(log n)`.
Both results are true in the "real world" but do not relativize.
Further, it is shown that if an oracle `O` exists,
relative to which the _LCT_ or _weak LCT_ holds, such that `P^O ≠ NP^O`,
then `P ≠ NP` holds in the "real world".

The _Relativizing Complexity Theory (RCT)_ is introduced as a set of axioms,
from which all\* (complexity-theoretic) relativizing statements follow.
Adding the LCT results in a stronger set of axioms (`RCT + LCT`),
since the LCT does not relativize.
It is shown that "if any interesting facts (like `P ≠ NP`) are provable
in normal mathematics, then essentially the same facts are provable
with `RCT + LCT`".

_\* all complexity-theoretic statements that relativize and in which time is specified
within polynomial bounds and space within constant bounds._

(some) more at <https://cstheory.stackexchange.com/a/20515>

#### Natural Proofs

[Razborov1997](https://doi.org/10.1006/jcss.1997.1494) introduce the notion
of _natural proofs_ which define (explicitly or implicitly)
and reason about _useful and natural combinatorial properties_
which are defined as follows:

`F_n` is the set of _boolean functions_ with `n` parameters (`f_n: {0,1}^n → {0,1}`).
`|F_n| = 2^2^n`, since every `2^n` long string of bits can be interpreted as a truth table of a boolean function with `n` parameters.
A _combinatorial property_ `C_n` is a subset of all boolean functions
with `n` parameters (`C_n ⊆ F_n`).
A combinatorial property is _natural_ if there exists a sub-property `C*_n ⊆ C_n` that satisfies two conditions:
`C*_n` is decidable in polynomial time ("constructivity")
and its size is non-negligible (<!--`|C*_n| / |F_n| ≥ 1 / 2^O(n)` or `|C*_n| ≥ 2^(2^n - O(n))`, -->"largeness").
A combinatorial property is _useful against `P/poly`_ if the circuit size
of any family of functions `{f_1, ..., f_n, ...}` with `f_n ∈ C_n`
is super-polynomial.

Under the assumption that _pseudo random generators (PRG)
with exponential hardness_ exist, it is shown that no useful natural proof
can prove lower bounds of complexity classes.
Since the useful natural combinatorial property defined in such a proof
could be used to create a statistical test against a PRG, which,
by definition of PRGs, is not possible, posing a contradiction.

Since proving `P ≠ NP` would prove a lower bound for `NP` \[always?],
there can be no natural proof for this statement.
Proofs that employ [diagonalization](https://complexityzoo.net/Complexity_Dojo/Diagonalization) are inherently non-natural
\[[Aaronson2009](https://doi.org/10.1145/1490270.1490272)].

### more

sources

- given an oracle `A` such that `P^A = NP^A`,
  one could construct an oracle `B` such that `P^A,B ≠ NP^A,B`,
  which would mean that `P^A = NP^A` does not relativize. (see [Hartmanis1985](https://scholar.google.com/scholar_lookup?title=Solvable%20problems%20with%20conflicting%20relativizations&author=J..%20Hartmanis&journal=Bulletin%20of%20the%20European%20Association%20for%20Theoretical%20Computer%20Science&volume=27&pages=40-49&publication_year=1985) as cited in [Allender1990](https://doi.org/10.1007/3-540-52921-7_54))
- [Hartmanis1985. J Hartmanis: Solvable problems with conflicting relativizations](https://scholar.google.com/scholar_lookup?title=Solvable%20problems%20with%20conflicting%20relativizations&author=J..%20Hartmanis&journal=Bulletin%20of%20the%20European%20Association%20for%20Theoretical%20Computer%20Science&volume=27&pages=40-49&publication_year=1985) (paper frequently quoted but nowhere to be found)
- <https://cs.stackexchange.com/questions/41501/relativization-results-in-class-separation>
- <https://mathoverflow.net/questions/75890/definition-of-relativization-of-complexity-class>
- <https://cstheory.stackexchange.com/questions/1388/proofs-barriers-and-p-vs-np>
- <https://www.cs.toronto.edu/~toni/Courses/PvsNP/Lectures/lecture11.pdf>

TODO:

- linear programming, see work of Mihalis Yannakakis (tl;dr expressing NP problems as linear programs ~always results in exponential size)
- random-access machine with unit multiplication
- some believe that "\[statements that do not relativize] may fall outside the axioms of set theory" (see [Hartmanis1985](https://scholar.google.com/scholar_lookup?title=Solvable%20problems%20with%20conflicting%20relativizations&author=J..%20Hartmanis&journal=Bulletin%20of%20the%20European%20Association%20for%20Theoretical%20Computer%20Science&volume=27&pages=40-49&publication_year=1985) as quoted in `relative.pdf`)

## Ongoing Work

**_TODO_** Blum axioms

**_TODO_** random access machine formalization

look into papers

- Bohua Zhan et al.: [Verifying Asymptotic Time Complexity of Imperative Programs in Isabelle](https://arxiv.org/abs/1802.01336) (see also [github repo](https://github.com/bzhan/Imperative_HOL_Time))
- Tobias Nipkow: [Amortized Complexity Verified](http://www21.in.tum.de/~nipkow/pubs/itp15.html)
- Maximilian Haslbeck et al.: [Refinement with Time - Refining the Run-time of Algorithms in Isabelle/HOL](https://www21.in.tum.de/~haslbema/documents/Haslbeck_Lammich-Refinement_with_Time.pdf)

## Sources and Literature

- `pvsnp.pdf`: Stephen Cook: [The P versus NP Problem](https://www.claymath.org/sites/default/files/pvsnp.pdf). 2006. <!-- laut PDF Metadaten wurde es 2006 erstellt -->
- `relative.pdf`: Lance Fortnow: [The Role of Relativization in Complexity Theory](https://people.cs.uchicago.edu/~fortnow/papers/relative.pdf). 1994.

### Isabelle/HOL related

- `tm.pdf`: Jian Xu and Xingyuan Zhang and Christian Urban: [Mechanising Turing Machines and Computability Theory in Isabelle/HOL](https://nms.kcl.ac.uk/christian.urban/Publications/tm.pdf). Springer 2013.
  - Turing machine alphabet is `{Bk,Oc}` (for **B**lan**k** and **Oc**cupied, resp., amounts to unary encoding)
- GitHub repo: [The Archive of Graph Formalizations](https://github.com/wimmers/archive-of-graph-formalizations)
- Jeremy Avigad and Kevin Donnelly: [Formalizing `O` notation in Isabelle/HOL](http://www.andrew.cmu.edu/user/avigad/Papers/bigo.pdf)
- Robin Eßmann and Tobias Nipkow and Simon Robillard: [Verified Approximation Algorithms](https://www21.in.tum.de/~nipkow/pubs/ijcar20-approx.html)
  - Using Hoare logic (implemented in HOL)

#### Isabelle Tutorials

Note: _Markus Wenzel_ seems to be using the name _Makarius Wenzel_ since ~2007
as can be seen in the
[list of his publications](https://www21.in.tum.de/~wenzelm/papers/)
on his page on the website of the _Technische Universität München_.

Many of the sources provided here are taken from the [Documentation page](https://isabelle.in.tum.de/documentation.html) on the isabelle homepage,
and the [homepage](https://isabelle.in.tum.de/community/Main_Page#Getting_started)
as well as the page [Course Material](https://isabelle.in.tum.de/community/Course_Material) of the community wiki.

- [Getting Started with Isabelle/jEdit in 2018](https://arxiv.org/abs/1208.1368)
  - very short introduction of how to set up and work with Isabelle/jEdit
- Thomas Genet: [A Short Isabelle/HOL Tutorial for the Functional Programmer](https://hal.inria.fr/hal-01208577)
  - very short "depth-first" look into Isabelle
  - many concepts explained on-the-fly
  - requires an understanding of functional programming
- `concrete_semantics.pdf`: Tobias Nipkow and Gerwin Klein: [Concrete Semantics](http://www.concrete-semantics.org/)
  - full book as PDF available on the [homepage](http://www.concrete-semantics.org/concrete-semantics.pdf)
  - full lecture (from Tobias Nipkow, follows the book) available from the
    [course page](https://www21.in.tum.de/teaching/semantik/WS20/)
  - `prog-prove.pdf` is _Part I_ of this book
    - Tobias Nipkow: [Programming and Proving in Isabelle/HOL](https://isabelle.in.tum.de/doc/prog-prove.pdf). 2020.
    - this is the top entry in the [list of documentation items](https://isabelle.in.tum.de/documentation.html) on the isabelle homepage
    - gives a solid introduction into the basics of using Isabelle/Isar
- `tutorial.pdf`: Tobias Nipkow and Lawrence C. Paulson and Markus Wenzel: [Isabelle/Hol: A Proof Assistant for Higher-Order Logic](https://isabelle.in.tum.de/doc/tutorial.pdf). Springer 2020.
  - this is an updated version of the [book of the same name](https://permalink.obvsg.at/UKL/AC03403462)
    (published by Springer, 2002) that is available in the AAU library
    (see [here](https://www21.in.tum.de/~nipkow/LNCS2283/))
  - there was a lecture based on this book with materials available
    [here](https://isabelle.in.tum.de/coursematerial/PSV2009-1/)
- `jedit.pdf`: Makarius Wenzel: [Isabelle/jEdit](https://isabelle.in.tum.de/doc/jedit.pdf). 2020.
  - more in depth overview of the features of Isabelle/jEdit
- Christian Urban et al.: [The Isabelle Cookbook](https://web.cs.wpi.edu/~dd/resources_isabelle/isabelle_programming.urban.pdf)
  - Tutorial about programming on the ML level of Isabelle
    for users who are already familiar with Isabelle
- Course: Thomas Genet: [ACF: Software Formal Analysis and Design](http://people.irisa.fr/Thomas.Genet/ACF/),
  6 lectures and 10 lab sessions, WS20
  - full course materials publicly available (including lectures in french)
  - > Disclaimer: this is a course on formal software design and not on proof design. Students are given a limited set of proof tactics that is enough to prove properties defined during the lab sessions. However, resulting proofs can be long and cumbersome. As a result, it is accepted that properties are not proven but only checked using Isabelle/HOL powerful counter-example finders.
- Course: Clemens Ballarin and Gerwin Klein:
  [Introduction to the Isabelle Proof Assistant](https://isabelle.in.tum.de/coursematerial/IJCAR04/)
  - one-day introduction to Isabelle
  - materials (slides, exercises) available
  - starts by formally introducing syntax, explaining inner workings
    \-> not recommended for starters
- Course: Holger Gast: [Interactive Software Verification](https://www21.in.tum.de/teaching/isv/SS13/)
  - materials (slides, exercises & solutions) available online
  - introduction and working with Isabelle
  - focus on software verification (small C-like language)

#### Isabelle Resources

- [Homepage of Isabelle](https://isabelle.in.tum.de/index.html)
  - [Documentation](https://isabelle.in.tum.de/documentation.html)
    - Tutorials (excerpts included in the section above)
    - Reference Manuals
      - `system.pdf` extensive manual for the `isabelle` CLI (backend)
      - `implementation.pdf`
  - some interesting resources are hard to find, or are not linked to
    - specific versions of the homepage (e.g. Isabelle2019) can be accessed
      by inserting `website-Isabelle20xx/` between host and path
      (see also [version history](https://isabelle.in.tum.de/download_past.html))
      for example, viewing an old version of the documentation overview:
      - current: <https://isabelle.in.tum.de/documentation.html>
      - archive: <https://isabelle.in.tum.de/website-Isabelle2008/documentation.html>
    - all files of a distribution can be accessed through the [`dist/` path](https://isabelle.in.tum.de/dist/)
- [Isabelle community Wiki](https://isabelle.in.tum.de/community)
  - seems to consist of [33 pages in total](https://isabelle.in.tum.de/community/Special:AllPages) with most not being very long (2021-02-06)
  - custom `isa-*:` links are broken (2021-08-02)
    - fix by inserting url of isabelle homepage. example:
      - broken: [isa-current:doc/tutorial.pdf](https://isabelle.in.tum.de/community/Isa-current:doc/tutorial.pdf)
      - fixed: <https://isabelle.in.tum.de/doc/tutorial.pdf>
- [Sketis](https://sketis.net/) - Homepage of Makarius Wenzel,
  also hosts most Isabelle development related resources, services and tools
  - Overview: [Isabelle Development](https://isabelle-dev.sketis.net/home/menu/view/20/)
    - Blog: [Isabelle NEWS](https://isabelle-dev.sketis.net/phame/blog/view/1/)
    - Blog: [Isabelle Release](https://isabelle-dev.sketis.net/phame/blog/view/2/)
      - Post: [Release Candidates for Isabelle2021](https://isabelle-dev.sketis.net/phame/post/view/28/release_candidates_for_isabelle2021/)
- Mailing Lists
  - for users: [The Cl-isabelle-users Archives](https://lists.cam.ac.uk/pipermail/cl-isabelle-users/index.html)
  - for devs: [The isabelle-dev Archives](https://mailman46.in.tum.de/pipermail/isabelle-dev/)
- Talks from Makarius Wenzel (hosted on YouTube)
  - `talk:isa-news` [Makarius Wenzel: Isabelle NEWS and trends in 2020 (Isabelle 2020)](https://www.youtube.com/watch?v=MpJZI1M_uVs)
    - new features in Isabelle2020
    - development trends (where will time be invested)
  - `talk:isa-vscode` [Makarius über Isabelle/VSCode](https://www.youtube.com/watch?v=ScOcpPS1zzo) (in German)
    - the inner workings of Isabelle/VSCode
    - benefits and drawbacks when compared to Isabelle/jEdit (the main platform)
  - `talk:isa_intro` [Makarius Wenzel: Einführung in Isabelle](https://www.youtube.com/watch?v=dIwZSoZlUfw)
    - inner workings and structure of Isabelle/HOL
      - Pure (just natural deduction)
      - HOL (definition of `theorem`, `rule`, `datatype`)
      - Isar (`fix`, `assume`, `from`, `with`, `have`, `show`)
    - examples
      - the concept that proof "by auto" is less valuable/informative
        than one where the intermediate steps are enumerated
        - i.e. only using the `..` ("default") and `.` ("immediate") tactics
        - these tactics and the concept are not mentioned in `prog-prove.pdf`

### Coq related

- Maximilian Wuttke: [Verified Programming Of Turing Machines In Coq](https://www.ps.uni-saarland.de/~wuttke/bachelor.php). Bachelor's Thesis 2018.

#### Coq Tutorials

- `sf1`: Benjamin C. Pierce et al.: [Software Foundations, Volume 1: Logical Foundations](http://softwarefoundations.cis.upenn.edu). Online book. I consider this to be the best Coq introduction.

#### Coq Resources

- [Coq Documentation](https://coq.inria.fr/refman/index.html)
  - recommended reading: [Built-in decision procedures and programmable tactics](https://coq.inria.fr/refman/proofs/automatic-tactics/index.html)

### General Quotes

- Manuel Herold, realizing that the solution is trivial,
  mere seconds after asking whether `P` is `NP`:

  > `P = NP` genau dann, wenn `P = 0` oder `N = 1`.

  \-- Manuel Herold, Personal communcations (Max), 2021-01-08.

- The quote in the section on [Relativization (Basic Idea)](#Basic-Idea)
- From the preface of Concrete Semantics (cited above), on theorem proving assistents:
  - > The beauty is that this includes checking the logical correctness of all proof text. No more 'proofs' that look more like LSD trips than coherent chains of logical arguments.
  - > But only recently have proof assistants become mature enough for inflicting them on students without causing the students too much pain.

## Additional reading

### Comparison of proof assistants

- [Stackoverflow: What are the strengths and weaknesses of the Isabelle proof assistant compared to Coq?](https://stackoverflow.com/questions/30152139/what-are-the-strengths-and-weaknesses-of-the-isabelle-proof-assistant-compared-t)

### Inspecting solver steps

- [Stackoverflow: How to see step-by-step reasoning of Isabelle 'proofs'](https://stackoverflow.com/questions/30688177/how-to-see-step-by-step-reasoning-of-isabelle-proofs)
  - has a somewhat unsatisfying answer of why we can "trust" Isabelle and that the actual list of steps (pure natural deduction) would be too long to comprehend
- [Stackoverflow: Can resolution proofs be traced in Isabelle?](https://stackoverflow.com/questions/62728693/can-resolution-proofs-be-traced-in-isabelle)
  - [Isabelle mailing list: Unfold short tactics in Isar.](https://lists.cam.ac.uk/pipermail/cl-isabelle-users/2020-August/msg00008.html)
  - [Isabelle mailing list: Tracing intro and elim in auto](https://lists.cam.ac.uk/mailman/htdig/cl-isabelle-users/2015-March/msg00065.html)
  - [Stackoverflow: Printing out / showing detailed steps of proof methods (like simp) in a proof in isabelle](https://stackoverflow.com/questions/26825747/printing-out-showing-detailed-steps-of-proof-methods-like-simp-in-a-proof-in)
