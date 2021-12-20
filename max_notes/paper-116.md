# Formalizing Paper #116

Author: Stefan Rass  
Title: On the Existence of Weak One-Way Functions

The paper is available as preprint [1609.01575](https://arxiv.org/abs/1609.01575) on `arXiv.org`.
Currently, the discussion addresses [version 3](https://arxiv.org/abs/1609.01575v3) (2017),
the most recent one during the time working on it (Dec 2020 - Dec 2021).

## Contents

- [Formalizing Paper #116](#formalizing-paper-116)
  - [Contents](#contents)
  - [Overview](#overview)
    - [Summary](#summary)
    - [Structure](#structure)
  - [Results](#results)
    - [Pre-Formalization Work](#pre-formalization-work)
    - [Formalization](#formalization)

## Overview

### Summary

<!-- markdownlint-disable MD037 -->

The paper establishes the existence of weak one way functions by mapping bits to sets of words
that either almost certainly\* contain a word of the constructed language $`L_0`$ (for 1-bits)
or almost certainly\* do not (for 0-bits).
$`L_0`$ is constructed to have a given time complexity to ensure the "other-way" difficulty.
To evaluate the function quicker than deciding $`L_0`$,
the _threshold_ property of the mapped sets is used to achieve the desired properties\*,
by sampling from sets that are constructed in such a way
that the fixed size of the output-sets is above or below the threshold\*\*.
The existence of OWFs implies $`P \ne NP`$.

<!-- markdownlint-enable MD037 -->

\* the probability of the mapped sets containing a word of $`L_0`$
asymptotically tends to 1 and 0\*\* as the set size tends to infinity.

\*\* for input bits 1 and 0, resp.

### Structure

Sections 1 to 3 give an overview of the paper, introduce definitions
and pose the main theorem (Thm. 2.4: Weak OWFs exist).
Section 4 is the proof of the main theorem, and section 5 discusses implications
(Cor. 5.1: $`P \ne NP`$) and possible threats to validity.

## Results

### Pre-Formalization Work

The first task for this project was reading and understanding the paper,
including the literature required.
During this process, a few issues were discovered.
However, no serious threats to the validity of the paper arose,
as consultation with the author revealed them to be
either spelling mistakes ("typos") or misunderstandings.

### Formalization

#### Gödel Numbering, Density Functions and the Language of Squares

The first milestone in formalizing the paper were Lemmas 4.1 ($`dens_L(x) \le x`$)
and 4.2 ($`dens_{SQ}(x) \in \Theta(\sqrt{x})`$).

Proving these required modeling the concepts needed to express them. These include:

- formal _languages_ and _words_
- $`gn(w)`$, the Gödel numbering function and its required properties
- $`dens_L(x)`$, the Language density function
- $`SQ`$, the language of non-zero integer squares

The initial definition of _words_ and the _Gödel numbering function_ `gn` proved non-trivial.
The first approach was to model words as lists of boolean values
(`list bool`, following the paper's definition as binary strings)
instead of using the predefined type `num` (theory `HOL.Num`), since in its original purpose,
`num` cannot express the empty string `""`, zero `"0"`, or leading zeroes `"0..."`.
The development of an elegant workaround by Stefan Haan led to the adoption
of `num` as the primary definition of words,
which allowed for unobstructed usage of many pre-existing results proven for `num`.
This was later partly reverted, as `num` turned out to be tedious to use in proofs
concerning sub-strings, concatenation and similar concepts usually associated with lists.

During modelling of `SQ` and the formalization of Lemma 4.2,
an encoding for `SQ` was found by Stefan Haan
that is isomorphic to the one from the paper but allows
for a more intuitive proof of Lemma 4.2 (adapted for the new encoding).
The new encoding differs only in omitting the leading 1-bit,
which is always present in the old encoding,
as zero and any binary strings that have leading zeroes are not included.
This causes the Gödel number of words in `SQ` to be the encoded natural number,
which in turn causes the density of `SQ` to be equal to the discrete square root
($`dens_{SQ}(x) = \lfloor \sqrt{x} \rfloor`$).

<!-- https://gitlab.aau.at/cave-pnp/self/-/commit/768dbbc50a53af291b5934b3be94026d7c1fb284 -->

#### Adjacent Squares and Shared Prefixes

The next result in the paper was Theorem 4.5 /deterministic time hierarchy theorem (THT)),
which we chose to ignore for the time being due to its established status in complexity theory,
and admit it (using `sorry`) as soon as we actually needed it in the implementation.
Instead, Lemma 4.6 was selected as milestone,
which requires defining basic terms in complexity theory, up to `DTIME`.
To finish the parts directly related to `SQ`
and to avoid directly referencing TMs before the prerequisites were proven,
we first looked into the internals of Lemma 4.6,
specifically proving that the '"square approximation" $`w'`$
will eventually have an identical lot of $`⌈\text{log }ℓ⌉`$ most significant bits'.
For this we first proved the stated inequalities.

While trying to prove this "shared prefix", we discovered a flaw in the proof;
The square approximation was constructed as $`w' := ⌈ \sqrt w ⌉ ^ 2`$,
which for some values crosses a power of two
resulting in a shorter-than-required shared prefix.
(for instance `w = 63 = 0b0111111, w' = 64 = 0b1000000`)
We were still able to complete the proof for a modified square approximation
that mitigated this issue.

<!-- https://gitlab.aau.at/cave-pnp/self/-/commit/2d729f825a5e5be4cbbdba2087cb74e4cd33c422 -->

#### Complexity Theory and Foundations

The next steps, including the somewhat involved encoding of TMs detailed in ch. 4.2,
required an formal implementation of Turing Machines (TM).

##### Selecting a TM framework

Since formalizing TMs has been assessed as a "daunting prospect"
(from _Michael Norrish: Mechanised Computability Theory_;
a quote included in every paper on formalizing TMs),
we chose the existing Isabelle session (~library) `Universal_Turing_Machine`
(see [Xu et al.: Mechanising Turing Machines and Computability Theory in Isabelle/HOL],
[code in the AFP](https://foss.heptapod.net/isa-afp/afp-devel/-/tree/branch/default/thys/Universal_Turing_Machine)).
A severe limitation of `Universal_Turing_Machine` is its focus on pure computation theory;
The authors construct and verify a universal TM (UTM),
but only consider single-tape TMs over the alphabet $`\{\texttt{\#}, 1\}`$ ("blank", "occupied"),
and no time measure is defined.
Some famous theorems in complexity theory utilize additional tapes and extended alphabets,
for instance the (deterministic) linear time speed-up theorem (Thm. 12.3 in Hopcroft)
which we suspected to be necessary for our work at the time (this turned out to be true).
Additionally, some parts of the paper directly use multiple tapes.

As a promising alternative we considered the
[Coq Library of Undecidability Proofs](https://github.com/uds-psl/coq-library-undecidability)
in which multi-tape TMs over arbitrary finite alphabets are defined
and halting problems of various models of computation are shown to be equivalent.
It is complemented by the [Coq Library of Complexity Theory](https://github.com/uds-psl/coq-library-complexity),
which contains among others the results of [Forster et al: Verified Programming of Turing Machines in Coq],
which in turn includes a powerful TM time/space complexity framework and
a single-tape UTM that can simulate multi-tape TMs with polynomial time overhead
(and constant space overhead).
This is significantly closer to our requirements than the Isabelle library
but the gap between this and the theorems used in the paper is still substantial,
and considered out-of-scope for our project.
Since we had already chosen Isabelle as our main platform for this project
(mostly for its readability and strong automation)
and to be able to return to the main project focus (the paper's content)
we continued with `Universal_Turing_Machine`.

##### Complexity Theory and the TM Encoding Scheme

Towards finishing Lemma 4.6 the next step was to build a vocabulary of
basic terms in complexity theory as well as implementing the definitions
from ch. 4.2 (TM encoding) and proving desired properties thereof.
During the work on this, we got a more detailed understanding
of the inner workings of `Universal_Turing_Machine`.
Specifically, the encoding of TMs as input for the UTM (see function `UF.code`)
uses a system close to the original Gödel numbering scheme
(encoding a list of natural numbers as product of consecutive prime powers)
to encode a TM's transition function.
Combined with the unary encoding used throughout the library,
this lead to severe doubts that the UTM
and most other results would be of use for our project.

This sparked efforts to create a framework that was more suited for our requirements.
In particular we need multi-tape TMs over arbitrary (finite) alphabets
and an injective encoding into binary strings.
