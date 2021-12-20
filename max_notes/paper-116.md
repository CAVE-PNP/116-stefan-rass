# Formalizing Paper #116

Author: Stefan Rass  
Title: On the Existence of Weak One-Way Functions

The paper is available as preprint [1609.01575](https://arxiv.org/abs/1609.01575) on arXiv.org.
Currently, the discussion addresses [version 3](https://arxiv.org/abs/1609.01575v3) (2017),
the most recent one during the time working on it (Dec 2020 - Mar 2021).

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
by sampling from sets that are constructed such
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

During modelling of `SQ` and the formalization of Lemma 4.2,
an encoding for `SQ` was found by Stefan Haan,
that is isomorphic to the one from the paper but allows
for a more intuitive proof of Lemma 4.2 (adapted for the new encoding).
The new encoding differs only in omitting the leading 1-bit,
which is always present in the old encoding,
as zero and any binary strings that have leading zeroes are not included.
This causes the Gödel number of words in `SQ` to be the encoded natural number,
which in turn causes the density of `SQ` to be equal to the discrete square root
($`dens_{SQ}(x) = \lfloor \sqrt{x} \rfloor`$).
