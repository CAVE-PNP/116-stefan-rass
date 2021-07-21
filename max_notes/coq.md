# Coq

Seems more focused on functional aspect and proving the correctness of programs
(including generating certified programs from proofs of correctness for said programs).

- [Coq](#coq)
  - [Mathematical Foundations](#mathematical-foundations)
    - [Additional Reading](#additional-reading)
  - [Coq IDEs](#coq-ides)
    - [CoqIde](#coqide)
    - [jsCoq](#jscoq)
    - [VSCoq (VSCode)](#vscoq-vscode)

## Mathematical Foundations

Coq is based on the Calculus of Inductive Constructions (CIC),
defined in the [section on Typing rules](https://coq.inria.fr/distrib/current/refman/language/cic.html)
in the [Coq Reference Manual](https://coq.inria.fr/distrib/current/refman/).
The CIC is an instance of type theory; the base of Coq is a type checker.

Using the [Curry-Howard correspondence](https://en.wikipedia.org/wiki/Curry%E2%80%93Howard_correspondence) (_propositions as types_)
logic can be expressed in type theory, constituting the foundation of mathematics in Coq.
This means that proving a proposition $`P : Prop`$ is the same as providing a term $`t : P`$ (witness) of type $`P`$.
The question of whether a proposition $`P`$ is provable is thus the same as whether the type $`P`$ is _inhabited_ (has instances/terms).
The [section on Proof Objects](https://softwarefoundations.cis.upenn.edu/lf-current/ProofObjects.html)
in the [Logical Foundations](https://softwarefoundations.cis.upenn.edu/lf-current/index.html) book
shows how logical operators can be defined as types.
Their actual definitions in Coq are in the library [Coq.Init.Logic](https://coq.inria.fr/library/Coq.Init.Logic.html)
(see the file `lib/coq/theories/Init/Logic.v` in the Coq distribution for proofs).

Coq's core logic is _intuitionistic/constructive_,
which means that to prove a proposition, an explicit witness of it must be constructed.
For instance, a proof for $`A ∨ B`$ (a term $`t : A ∨ B`$) must be either a proof for $`A`$ ($`t : A`$) or a proof for $`B`$ ($`t : B`$).
This means that some non-constructive arguments traditionally used in _classical logic_ (like the _excluded middle_ $`A ∨ ¬A`$) must be added as axioms.
For more information see the sections on the [Logic of Coq](https://github.com/coq/coq/wiki/The-Logic-of-Coq)
and [useful Axioms](https://github.com/coq/coq/wiki/CoqAndAxioms)
in the [Coq Wiki on GitHub](https://github.com/coq/coq/wiki).

### Additional Reading

- For the canonical definition of the CIC see
  - [coqref:Sorts](https://coq.inria.fr/distrib/current/refman/language/core/sorts.html)
    for an explanation of the base of the type hierarchy
  - [coqref:Typing rules](https://coq.inria.fr/distrib/current/refman/language/cic.html)
    for the main definitions
  - [coqref:Theory of inductive definitions](https://coq.inria.fr/distrib/current/refman/language/core/inductive.html#inductive-definitions)
    for inductive types
- [wiki:Intuitionistic type theory](https://en.wikipedia.org/wiki/Intuitionistic_type_theory)
  explains some of the type theoretic basics.
  Note that this is not exactly how CIC is defined.
  - the entry on [Intuitionistic Type Theory](https://plato.stanford.edu/entries/type-theory-intuitionistic/)
    in the _Stanford Encyclopedia of Philosophy_
    discusses the concept more broadly
- Philip Wadler: [Propositions as types](https://homepages.inf.ed.ac.uk/wadler/papers/propositions-as-types/propositions-as-types.pdf) ([doi:10.1145/2699407](https://doi.org/10.1145/2699407)) gives a short history and overview of the concept and its uses.

## Coq IDEs

The available options seem to be:

- _CoqIde_, a part of the Coq project
- _jsCoq_, a web-based environment
- _Jupyter_ with the _coq_jupyter_ kernel
- _emacs_ with the _Proof General_ and _Company-Coq_ plugins
- _Visual Studio Code_ with the _VSCoq_ plugin
- _Vim_ with the _Coqtail_ plugin

### CoqIde

Similar to Isabelle/jEdit, feels even more old and clunky.

### jsCoq

Web-based, interactive. See

- [jsCoq demo](https://jscoq.github.io/)
- [jsCoq scratchpad](https://jscoq.github.io/scratchpad.html) (local storage)
- [CollaCoq](https://x80.org/collacoq/), "the Coq pastebin"

### VSCoq (VSCode)

Seems to work well.

For basic use see the [plugin page](https://marketplace.visualstudio.com/items?itemName=maximedenes.vscoq#basic-usage).

Note: if commands do not work, restart VSCode
(do not close the tab of the opened `.v` file, just close VSCode and launch it again).

#### Settings

configure at `Settings` (`Ctrl+,`) > `Extensions` > `Coq configuration`

##### required

- `Coqtop: Bin Path` enter path to `Coq/bin` dir
- (for Windows) for `Coqtop: Coqidetop Exe` and `Coqtop: Coqtop Exe`, add `.exe`

##### recommended

- `Coq: Auto Reveal Proof State At Cursor`: enable
- `Coqtop: Start On`: set to `open-script`
