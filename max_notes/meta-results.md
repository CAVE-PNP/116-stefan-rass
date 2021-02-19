# Meta Results on Proofs surrounding `P vs NP`

A lot of meta-results about `P vs NP` have been published;
some general properties of proofs and techniques that must be fulfilled,
some more concrete showing that certain techniques are doomed to fail.

## Contents

- [Meta Results on Proofs surrounding `P vs NP`](#meta-results-on-proofs-surrounding-p-vs-np)
  - [Contents](#contents)
  - [Barriers](#barriers)
    - [Relativization](#relativization)
    - [Natural Proofs](#natural-proofs)
  - [TODO](#todo)

## Barriers

### Relativization

#### Oracle Machines

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

#### Basic Idea

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

#### Notation

It is said that a statement `B ~ C` _relativizes_
if `B^A ~ C^A` remains true for all oracles `A`. \[citation needed]

Similarly, a proof technique is said to _relativize_
if it is unaffected by the addition of an oracle.

A _positive relativization_ of a statement `B ~ C`
is an example of an oracle `A` for which `B^A ~ C^A` holds.
A _negative relativization_ of a statement `B ~ C`
is an example of an oracle `A` for which `B^A ≁ B^A` (`¬(B^A ~ C^A)`) holds.

#### Remark (Stefan)

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

#### Relevance in Complexity Theory

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

#### Arithmetization and Algebrization

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

#### Local Checkability

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

### Natural Proofs

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

## TODO

- linear programming, see work of Mihalis Yannakakis (tl;dr expressing NP problems as linear programs ~always results in exponential size)
- random-access machine _with unit multiplication_
  - allows encoding arbitrarily many values into one _cell_
    and processing in O(1) time and space
  - the same applies to some other operations including bitwise logical operators
- Blum axioms
