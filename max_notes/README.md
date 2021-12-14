# Project Notes

The first challenge will be the selection of a suitable proof assistant.
Initial research by Stefan Rass resulted in the two preliminary candidates
Isabelle/HOL and Coq.
They seem similar in many respects, both having a refined set of features
and both having been in development for more than 30 years,
with an active community and steady support.

As outlined in the [Comparison](isa-isa-vs-coq.md), Coq is easier to use
for small scale precise manipulation (for example, rewriting the current
proof goals) and Isabelle provides powerful automatic solvers that
help prevent small scale manipulations from being necessary.

## Contents

- Proof Assistants
  - [Isabelle Overview](isabelle.md)
    - [Simpl](simpl-notes.md)
      (imperative program verification framework for Isabelle)
  - [Coq Overview](coq.md)
  - [Comparison of Isabelle and Coq](isa-vs-coq.md)
- P vs NP
  - [Claimed Solutions of $`P`$ vs $`NP`$](papers.md)
  - [Meta Results on Proofs Surrounding $`P`$ vs $`NP`$](meta-results.md)
- [Sources, Resources, Literature and Further Reading](sources.md)

## Meta

### Math Markup in Markdown

GitLab supports $`\LaTeX`$ math markdown using [$`\KaTeX`$](https://katex.org/)
for [some time](https://gitlab.com/gitlab-org/gitlab/-/commit/2d170a20dc4cd3423ac7994c797cae8fbed263ba) now.
See the examples [here](https://git-ainf.aau.at/help/user/markdown.md#math).
