# Sources and Literature

- [Sources and Literature](#sources-and-literature)
  - [P vs NP and related Topics](#p-vs-np-and-related-topics)
  - [Isabelle/HOL related](#isabellehol-related)
    - [Isabelle Tutorials](#isabelle-tutorials)
    - [Isabelle Resources](#isabelle-resources)
  - [Coq related](#coq-related)
    - [Coq Tutorials](#coq-tutorials)
    - [Coq Resources](#coq-resources)
  - [General Quotes](#general-quotes)
  - [Additional reading](#additional-reading)
    - [Comparison of proof assistants](#comparison-of-proof-assistants)
    - [Inspecting solver steps](#inspecting-solver-steps)
    - [Unsorted Resources](#unsorted-resources)
  - [Missing/Hard-to-Find Resources](#missinghard-to-find-resources)

## P vs NP and related Topics

- `pvsnp.pdf`: Stephen Cook: [The P versus NP Problem](https://www.claymath.org/sites/default/files/pvsnp.pdf). 2006. <!-- laut PDF Metadaten wurde es 2006 erstellt -->
- `relative.pdf`: Lance Fortnow: [The Role of Relativization in Complexity Theory](https://people.cs.uchicago.edu/~fortnow/papers/relative.pdf). 1994.

## Isabelle/HOL related

- `tm.pdf`: Jian Xu and Xingyuan Zhang and Christian Urban: [Mechanising Turing Machines and Computability Theory in Isabelle/HOL](https://nms.kcl.ac.uk/christian.urban/Publications/tm.pdf). Springer 2013.
  - Turing machine alphabet is `{Bk,Oc}` (for **B**lan**k** and **Oc**cupied, resp., amounts to unary encoding)
- GitHub repo: [The Archive of Graph Formalizations](https://github.com/wimmers/archive-of-graph-formalizations)
- Robin Eßmann and Tobias Nipkow and Simon Robillard: [Verified Approximation Algorithms](https://www21.in.tum.de/~nipkow/pubs/ijcar20-approx.html)
  - Using Hoare logic (implemented in HOL)
- Jeremy Avigad and Kevin Donnelly: [Formalizing `O` notation in Isabelle/HOL](http://www.andrew.cmu.edu/user/avigad/Papers/bigo.pdf)
- Bohua Zhan et al.: [Verifying Asymptotic Time Complexity of Imperative Programs in Isabelle](https://arxiv.org/abs/1802.01336)
  - see also [GitHub repo](https://github.com/bzhan/Imperative_HOL_Time)
- Tobias Nipkow: [Amortized Complexity Verified](http://www21.in.tum.de/~nipkow/pubs/itp15.html)
  - focus on data structures
  - uses invariant aproach with an additional property for amortized _potential_

### Isabelle Tutorials

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

### Isabelle Resources

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

## Coq related

- Maximilian Wuttke: [Verified Programming Of Turing Machines In Coq](https://www.ps.uni-saarland.de/~wuttke/bachelor.php). Bachelor's Thesis 2018.

### Coq Tutorials

- `sf1`: Benjamin C. Pierce et al.: [Software Foundations, Volume 1: Logical Foundations](http://softwarefoundations.cis.upenn.edu). Online book. I consider this to be the best Coq introduction.

### Coq Resources

- [Coq Documentation](https://coq.inria.fr/refman/index.html)
  - recommended reading: [Built-in decision procedures and programmable tactics](https://coq.inria.fr/refman/proofs/automatic-tactics/index.html)

## General Quotes

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

### Unsorted Resources

These are everything from blog posts to stackexchange questions that _may_ be of use at some point.

- <https://cs.stackexchange.com/questions/41501/relativization-results-in-class-separation>
- <https://mathoverflow.net/questions/75890/definition-of-relativization-of-complexity-class>
- <https://cstheory.stackexchange.com/questions/1388/proofs-barriers-and-p-vs-np>
- <https://www.cs.toronto.edu/~toni/Courses/PvsNP/Lectures/lecture11.pdf>

## Missing/Hard-to-Find Resources

- [Hartmanis1985. J Hartmanis: Solvable problems with conflicting relativizations](https://scholar.google.com/scholar_lookup?title=Solvable%20problems%20with%20conflicting%20relativizations&author=J..%20Hartmanis&journal=Bulletin%20of%20the%20European%20Association%20for%20Theoretical%20Computer%20Science&volume=27&pages=40-49&publication_year=1985)
  - paper is frequently quoted in works on relativization but nowhere to be found
  - given an oracle `A` such that `P^A = NP^A`,
    one could construct an oracle `B` such that `P^A,B ≠ NP^A,B`,
    which would mean that `P^A = NP^A` does not relativize.
    (see [Hartmanis1985] as cited in [Allender1990](https://doi.org/10.1007/3-540-52921-7_54))
  - some believe that "\[statements that do not relativize] may fall outside the axioms of set theory"
    (see [Hartmanis1985](https://scholar.google.com/scholar_lookup?title=Solvable%20problems%20with%20conflicting%20relativizations&author=J..%20Hartmanis&journal=Bulletin%20of%20the%20European%20Association%20for%20Theoretical%20Computer%20Science&volume=27&pages=40-49&publication_year=1985) as quoted in `relative.pdf`)
