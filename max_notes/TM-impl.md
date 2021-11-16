# Considerations for Implementing (a Theory of) Turing Machines in Isabelle

## Contents

- [Considerations for Implementing (a Theory of) Turing Machines in Isabelle](#considerations-for-implementing-a-theory-of-turing-machines-in-isabelle)
  - [Contents](#contents)
  - [Aspects/Questions](#aspectsquestions)
    - [Modelling Higher-Level Concepts](#modelling-higher-level-concepts)
    - [States](#states)
    - [Tapes](#tapes)
    - [Naming](#naming)
  - [Existing (Formal) TM Definitions](#existing-formal-tm-definitions)

## Aspects/Questions

- Policy for generality
  - Do we develop a library that we also use ourselves (general),
    or do we define TMs as part of our project (specific)
  - Where is the border? Should we consider aspects
    that are not relevant to us directly?
    - Proposal 1: Develop only directly relevant aspects,
      but with extensibility for other common aspects in mind
- Is space-complexity relevant?
  - Probably not, see previous item
- How to (explicitly) encode TMs as (binary?) strings?
  - Highly relevant for the universal TM (since it needs to support arbitrary alphabets)
  - Should encode alphabet and number of tapes explicitly

### Modelling Higher-Level Concepts

- Languages
  - What is a language?
    - Proposal 1: a set of words ("language") and a set of symbols ("alphabet")
      - the words of the language must contain exclusively symbols from the alphabet
      - avoids the ambiguity in questions like:  
        "is the word "2" contained in the complement of $`{w. w = 1^n}`$?"
      - the alphabet could be modelled as type,
        but the set-approach grants more flexibility
  - Deciding languages ("The TM $`M`$ decides the language $`L`$, iff ...")
    - Proposal 1: _accepting states_ as subset of final states;
      a TM accepts an input word, iff it terminates in an accepting state.
  - Is the blank symbol of a TM an admissible symbol in input words?
    - Proposal 1: No, since otherwise, TMs can never know how long a word is.
- Realization/Computation of functions
  ("The TM $`M`$ computes the function $`f`$, iff ...")
  - necessary for reductions
- Composition of TMs
  - combine TMs with different alphabets
    - use union?
  - combine TMs with different numbers of tapes
  - use output of one TM as input for another
    - TM program may assume that all tapes are empty;
      need to reset after execution of first TM?
    - Proposal 1: "stack" tapes
      - for TMs $`M_1, M_2`$ with $`k_1, k_2`$ tapes resp.
      - construct $`M`$ with $`k := k_1 + k_2 + 1`$ tapes
      - execute $`M_1`$ on tapes $`1..k_1`$  
        using $`M`$'s input-tape as input-tape for $`M_1`$,  
        and tape $`k_1 + 1`$ as output-tape for $`M_1`$  
        (until $`M_1`$ terminates)
      - execute $`M_2`$ on tapes $`k_1 + 2..k`$  
        using tape $`k_1 + 1`$ as input-tape for $`M_2`$,  
        and $`M`$'s output-tape as output-tape for $`M_2`$  
        (until $`M_2`$ terminates, at which point $`M`$ terminates)
    - Proposal 2: add "cleaner" TM in between TMs
      - probably more effort/harder to work with than (1)
      - would require extra measures to guarantee clean tapes
        - measure space-usage
        - introduce 2 extra tapes to "mask" tape usage in both directions
          - is this even possible?

### States

- How to model final states?
  - In terms of the states
    - as subset of all possible states
  - In terms of transition function $`δ`$
    - Proposal 1: required to result in `Nop` (no operation) for final states
    - Proposal 2: only defined for non-final states
    - Proposal 3: `step`-function only considers $`δ`$ for non-final states

### Tapes

- Should TMs have a (read-only) input tape? A (sequential-write-only) output tape?
  - How does composition work?
  - Compatibility/Equivalence to TMs without those?
    - for off-line TMs (from `hopcroft`, off-line TMs are TMs with an additional read-only input tape):
      - simulate a k-tape TM on a k-tape off-line TM by first copying the input-tape to the first tape, then executing the TM normally
      - simulate a k-tape off-line TM trivially on a k+1-tape TM
    - for TMs with output-tapes:
      - how is the "output" of a normal TM defined?
        - Proposal 1: The content of tape $`k`$ when the TM terminates
  - Do the "extra" tapes count in terms of $`k`$ (tape_count)?

### Naming

- Proposal: call the _main_ notion (definition/type/locale/?) `TM` for readability
  - the _main_ notion is the one that is expected to be used most frequently
    in theories that _use_ TMs (i.e. related to complexity theory)

## Existing (Formal) TM Definitions

- `AlgoKomp`: **Deterministic _k_-tape-TM**  
  from the [lecture slides of Algorithmen und Komplexitätstheorie](https://gitlab.aau.at/teamtewi/alk/-/raw/master/VO/AuK_WS2019_05.pdf#page=4)
  held at the AAU
  - see Defs. 5.1ff
  - has extra input and output tapes (do not count for $`k`$)
  - transition function only defined for non-final states
  - built with complexity theory in mind
    - may lack desirable properties for required computability results
  - Defs and proofs are semi-rigorous
    - contains proofs for almost all theorems relevant for this project
  - cites further sources:
    - `AB09` Sanjeev Arora and Boaz Barak:  
      _Computational Complexity: A Modern Approach_ (2009)
      - [draft (2006)](https://theory.cs.princeton.edu/complexity/) available freely
      - uses a similar notion of TM, see [ch. 1.2.1, p15ff](https://theory.cs.princeton.edu/complexity/book.pdf#subsection.1.2.1)
    - `hopcroft*`/`HMU06` John E. Hopcroft, Rajeev Motwani, and Jeffrey D. Ullman:  
      Introduction to Automata Theory, Languages, and Computation (3rd Edition, 2006)
      - [pdf can be found on google](<http://ce.sharif.edu/courses/94-95/1/ce414-2/resources/root/Text%20Books/Automata/John%20E.%20Hopcroft,%20Rajeev%20Motwani,%20Jeffrey%20D.%20Ullman-Introduction%20to%20Automata%20Theory,%20Languages,%20and%20Computations-Prentice%20Hall%20(2006).pdf>)
      - Basic TM (single-tape): [ch. 8.2.2, p326ff](<http://ce.sharif.edu/courses/94-95/1/ce414-2/resources/root/Text%20Books/Automata/John%20E.%20Hopcroft,%20Rajeev%20Motwani,%20Jeffrey%20D.%20Ullman-Introduction%20to%20Automata%20Theory,%20Languages,%20and%20Computations-Prentice%20Hall%20(2006).pdf#page=342>),
        Multitape TM: [ch. 8.4.1, p344ff](<http://ce.sharif.edu/courses/94-95/1/ce414-2/resources/root/Text%20Books/Automata/John%20E.%20Hopcroft,%20Rajeev%20Motwani,%20Jeffrey%20D.%20Ullman-Introduction%20to%20Automata%20Theory,%20Languages,%20and%20Computations-Prentice%20Hall%20(2006).pdf#page=360>)
      - no dedicated input or output tapes
    - `Pap94` Christos H. Papadimitriou:  
      Computational Complexity (1994)
    - `Rei99` R. Reischuk:  
      Komplexitätstheorie (Bd. 1, 1999)
- `hopcroft` from John E. Hopcroft and Jeffrey D. Ullman:  
  Introduction to Automata Theory, Languages, and Computation (1st Edition, 1979)
  - [pdf can be found on archive.org](https://archive.org/download/HopcroftUllman_cinderellabook/Intro%20to%20Automata%20Theory%2C%20Languages%20and%20Computation%20_%20John%20E%20Hopcroft%2C%20Jeffrey%20D%20Ullman.pdf)
  - Basic TM (one-way infinite single-tape): ch. 7.2, p147ff,
    Multitape TM: ch. 7.5, p161ff
    - no dedicated input or output tapes, but definition of _off-line TMs_, that are multitape TM with a read-only input tape
    - The single-tape TM requires the tape head to move on every step. The rationale for this is only given in the 3rd ed.:
      > This restriction does not constrain what a Turing machine can compute since any sequence of moves with a stationary head could be condensed, along with the next tape-head move, into a single state change, a new tape symbol, and a move left or right.
    - multitape TMs are only sketched.:
      > We shall not define the device more formally, as the formalism is cumbersome and a straightforward generalization of the notation for single-tape TM's.
- `CoqTM` from the _Coq Library of Undecidability Proofs_
  - see the published paper [Verified Programming of Turing Machines in Coq](https://www.ps.uni-saarland.de/Publications/documents/ForsterEtAl_2019_VerifiedTMs.pdf) and the [bachelor's thesis with the same title](https://www.ps.uni-saarland.de/~wuttke/bachelor/downloads/thesis.pdf)
  - fully modelled in Coq, allows reasoning about time and space requirements
    - Complexity theoretic lemmas seem to prefer the _weak call-by-value lambda calculus_ $`L`$ as model of computation.
      $`L`$ and TMs are shown to simulate each other with polynomial overload.
      - see [THT](https://github.com/uds-psl/coq-library-complexity/blob/coq-8.12/theories/HierarchyTheorem/TimeHierarchyTheorem.v#L132)
        and [space_bounds_time](https://github.com/uds-psl/coq-library-complexity/blob/coq-8.12/theories/Complexity/SpaceBoundsTime.v#L240)
        (~`space <= 25^time`)
  - based on defs. from [A Formalization of Multi-tape Turing Machines](https://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.1085.7296&rep=rep1&type=pdf)
    - defined in Matita, a project attempting to improve upon Coq while keeping the core functionality
  - n-tape TM: [thesis, ch. 2.2, p7](https://www.ps.uni-saarland.de/~wuttke/bachelor/downloads/thesis.pdf#section.2.2)
    - no dedicated input/output tapes
    - final ("halting") states implemented as predicate over states
    - accepting states can be modelled through labelling (function) of states
      - "[the label] is irrelevant for non-terminating states."
    - dependent types allow elegant usage of vectors for defining the transition function
    - the tape does not contain blank cells
    - reading blank tape cells are modelled using _option_ types
    - the tape type is "symmetric": the symbol currently under the tape head is a separate entity, and not the first element of the symbols right of the tape head
      - this allows efficient construction of "mirrored" TMs that perform mirrored subroutines (cf. shift-left and shift-right)
- `isabelle-UTM` from Isabelle session `Universal_Turing_Machine`
  - see the associated paper [Mechanising Turing Machines and Computability
    Theory in Isabelle/HOL](https://nms.kcl.ac.uk/christian.urban/Publications/tm.pdf)
  - based on defs. from [Boolos et al.: Computability and Logic](<http://alcom.ee.ntu.edu.tw/system/privatezone/uploads/Logic/20090928151927_George_S._Boolos,_John_P._Burgess,_Richard_C._Jeffrey_-_Computability_and_Logic_(5Ed,Cambridge,2007).pdf>)
    - single-tape TM with alphabet `{Bk, Oc}`
      - authors claim that their proofs work for arbitrary alphabets and TMs working on a 2D grid rather than a single 1D tape, but no explicit proofs are given
    - focus on computability, not complexity

TODO: look into other sources quoted in `AlgoKomp`
