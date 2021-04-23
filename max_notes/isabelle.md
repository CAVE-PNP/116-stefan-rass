# Isabelle

- [Isabelle](#isabelle)
  - [Getting Started](#getting-started)
    - [Imports](#imports)
  - [Proof methods (work in progress)](#proof-methods-work-in-progress)
  - [General](#general)
  - [Technical Overview](#technical-overview)
    - [Structure](#structure)
    - [Versions](#versions)
    - [IDEs](#ides)

## Getting Started

The best option to start working with Isabelle seems to be reading `prog-prove.pdf`
(pdf in seafile [desktop](seafile://openfile?repo_id=d3f2bfd0-b877-47a7-a7ca-4af40c3d18d4&path=/Isabelle/manuals/prog-prove.pdf)/[web](https://seafile.aau.at/smart-link/eb40beb8-30e4-4485-bc89-2636ec1e8349/),
online lecture available from the [TU München's course page](https://www21.in.tum.de/teaching/semantik/WS20/#material))
and trying to solve as many of the exercises as possible.

Even through working with Isar (the proof abstraction language of Isabelle) feels mostly imperative, most mathematical definitions resemble a _functional_ style.
Therefore for those not already familiar with functional programming, a short introduction of its main concepts (like currying) and way of thinking may be beneficial.

### Imports

A sort of minimal working example of a theory file is the following. Note that the file name needs to match the theory name or Isabelle will not run any code, so this example file must be named `Example.thy`.

```isabelle
theory Example
  imports Main
begin

end
```

Note that files missing an `end` will execute without warnings but cannot be imported, as Isabelle will complain about a `Bad theory import`.

Importing `Main` (a part of `HOL`) gives access to many classical mathematical definitions and results, including the natural numbers, sets, and lists.
`Complex_Main` is an extension including the real numbers and beyond.
In the absense of reasons against it, importing one of these is highly recommended as a baseline (see `prog-prove.pdf`).

#### Standard Libraries

Standard libraries (those `.thy` files bundled with Isabelle releases in the `src/` directory) can be imported using a package-like syntax:

| Theory file path                    | Import name                   |
| ----------------------------------- | ----------------------------- |
| `src/HOL/List.thy`                  | `HOL.List`                    |
| `src/ZF/ZFC.thy`                    | `ZF.ZFC`                      |
| `src/HOL/Library/BigO.thy`          | `"HOL-Library.BigO"`          |
| `src/HOL/Data_Structures/Heaps.thy` | `"HOL-Data_Structures.Heaps"` |

Imports containing special characters, like dashes `-`, must be surrounded by double quotes.

Note that collections of theories are referred to as _sessions_ (~projects) in the context of Isabelle (see `system.pdf` _ch. 2 Isabelle sessions and build management_).
The session `HOL` is active per default (see [Mechanics](#mechanics-and-session-images) below), such that the theory `src/HOL/Main.thy` can be imported using just `Main`.

#### Local Files

Files in the same directory as the importing file can be accessed by just the theory name.
So for instance a session called `OtherExample.thy` can be imported as `OtherExample`, or (in case of name conflicts) through its qualified name in the virtual package `Draft` as `Draft.OtherExample`.

See also [Creating Sessions](#creating-sessions) below for a way to make theories available for import in other sessions.

#### AFP

The Archive of Formal Proofs is a growing collection of sessions.
It is not included with Isabelle distributions per default, so using the libraries requires prior setup:

Download the version of the AFP that corresponds to the version of Isabelle from the [downloads section](https://www.isa-afp.org/download.html).
Note that downloading the wrong version may result in errors and warnings in the underlying proofs.

Follow the instructions at [Referring to AFP Entries](https://www.isa-afp.org/using.html).
Note that for Windows, the command has to be entered in the cygwin terminal (`<isa install dir>/Cygwin-Terminal.bat`).
Alternatively, the file `%userprofile%\.isabelle\Isabelle20xx\ROOTS` can be edited manually.
Also, the path to the AFP installation has to be adapted to fit the cygwin scheme `/cygdrive/<drive letter>/path/to/afp/thys`.

After setup, AFP entries can be accessed like standard libraries.

#### Mechanics and Session Images

When importing sessions, all stated results and proofs will be checked in the same way that code is executed live in the Isabelle/jEdit.
This may take some time depending on the size of the sessions.
The import progress can be tracked in the _Theories_ panel in Isabelle/jEdit, docked on the right by default, otherwise accessible via `Plugins > Isabelle > Theories panel` (see also `jedit.pdf` _ch. 3.1.2 Theories_).
Additionally, all loaded sessions will be displayed there.

Members of the sessions `HOL` (like `Main`) are exceptions to this as they are part of the pre-compiled _session image_ `HOL` which is loaded per default at startup (the same applies to the session `Pure`).
The loaded session image can be changed in the _Theories_ panel in Isabelle/jEdit (changes will take effect after a restart of Isabelle/jEdit).
If a session image is not yet compiled or out of date (newer sources available), it will be rebuilt on startup.
Session images that are included with the distribution are stored in `<isa install dir>/heaps/` and user compiled ones in `~/.isabelle/Isabelle20xx/heaps/`.

Note that while changing the session image may result in faster startup times, it prevents the semantic highlighting in Isabelle/jEdit to work properly for any theories of the loaded session
(indicated by the warning `Cannot update finished theory ...`).
To work around this, change the session image to `Pure` (pre-compiled) and restart Isabelle/jEdit.

The session `HOL-Proofs` is special in that the image includes the full proof terms of the entire `HOL-Library`.

#### Creating Sessions

In order for Isabelle to recognize a session, it has to be defined in a `ROOT` file (defines sessions), that in turn has to be referred to in a `ROOTS` file (points to `ROOT` files or further `ROOTS`).
There are two main `ROOTS` for each Isabelle installation: one in the installation directory (`ISABELLE_HOME`), and one in `~/.isabelle/Isabelle20xx/` (`ISABELLE_HOME_USER`).
Isabelle/jEdit provides semantic highlighting and checking for `ROOT` files.
See `system.pdf` _ch. 2.1 Session ROOT specifications_ for `ROOT` file structure and syntax.

During development of a session, it is advisable to only include _finalized_ theories when loading the session image at startup,
as any files included in the image cannot be live-checked in Isabelle/jEdit
(they can however, be imported as [local files](#local-files)).

## Proof methods (work in progress)

The cookbook's section on [Proof Methods](https://isabelle.systems/cookbook/src/proofs/methods/) is recommended reading.
For more information see the `isar-ref.pdf` _ch. 9 Generic tools and packages_, especially _chs. 9.2.1-9.2.2, 9.3.1, 9.4.3-9.4.4_.
Refer to _chs. 12.1-12.2_ for more tools (see also _chs. 12.4-12.8_ for some more uncommon tactics).
See _chs. 9.3.2, 9.4.2_ for theorem attributes that allow the automatic tools to use them effectively.

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
  the natural deduction axioms

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

## General

> Remember that `f t u` means `(f t) u` and not `f (t u)`!
>
> equality has a high priority \[...] `¬ ¬ P = P` means `¬ ¬ (P = P)` and
> not `(¬ ¬ P) = P`. When using `=` to mean logical equivalence,
> enclose both operands in parentheses, as in `(A ^ B) = (B ^ A)`

## Technical Overview

### Structure

Terms like "Isabelle/\<name>" denote "\<name> in the context of Isabelle".
For instance, Isabelle/jEdit is the bundled IDE,
Isabelle/HOL is the specification for constructing higher-order logic
and Isabelle/ML is the use of (a dialect of standard) ML in the Isabelle environment.

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

The available options include:

- _Isabelle/jEdit_, the modified and preconfigured distribution of _jEdit_
  bundled with Isabelle installers
- _emacs_ with the _Proof General_ plugin
- _Visual Studio Code_ with the _Isabelle_ plugin

Deprecated or not supported:

- [Isabelle/Eclipse](http://andriusvelykis.github.io/isabelle-eclipse/)
  - latest commit from 2013
  - states that support for Isabelle2013-1 is planned

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

_Note: **`$ISABELLE_HOME`** is the location of the Isabelle installation
(this is set by `isabelle` on startup and should not be modified, see `system.pdf`),
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
