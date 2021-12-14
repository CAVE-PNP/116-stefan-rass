# Isabelle/jEdit Settings Guide

Access options in `Utilities > Global Options`

## Content

- [Isabelle/jEdit Settings Guide](#isabellejedit-settings-guide)
  - [Content](#content)
  - [Editor](#editor)
  - [Isabelle-specific](#isabelle-specific)
  - [Shortcuts](#shortcuts)
  - [Abbreviations](#abbreviations)
  - [Non-recommended options](#non-recommended-options)

## Editor

- Display line numbers
  - enable `Global Options > jEdit > Gutter > Line numbers`
- Open most recently visited directory in file browser at startup
  - select `Most recently visited directory`
    in `Global Options > File System Browser > General`

## Isabelle-specific

- reduce Tooltip Delay (snappier `Ctrl+Mouseover` popup)
  - `Plugin Options > Isabelle > Tooltip Delay`
- configure Code Completion
  - in `Plugin Options > Isabelle > Completion`
  - adjust delay, choose selection key (`Tab` and/or `Enter`)
- enable auto-tools (run tools without user interactions when cursor is over a goal)
  - `Plugin Options > Isabelle > General > Automatically tried tools`
  - recommended (quick and useful)
    - `quickcheck` (and/or `nitpick`) automatically check for counterexamples
    - `solve_direct`
  - not recommended (slow, may impact performance); use manually instead
    - `methods` is similar to `try0`
    - `sledgehammer`
- select a session to load at start-up (if there are many slow imports in the project)
  - in `Theories` panel (docked on the right by default, alternatively activate using `Plugins > Isabelle > Theories panel`)  
    or in `Plugin Options > Isabelle > Logic`
  - restart to apply
    - compiles at first launch and on changes to the imported libraries
    - significantly reduces start-up time on subsequent launches
  - `HOL-Library` is a good start, see the section on [Session Images](isabelle.md#mechanics-and-session-images)

## Shortcuts

Edit shortcuts in `Global Options > jEdit > Shortcuts`.

Some particularly useful actions with suggested shortcuts:

- Navigation
  - _Back_ `Alt+Left` <!-- (by default assigned to _Shift Indent Left_) -->
  - _Forward_ `Alt+Right` <!-- (by default assigned to _Shift Indent Right_) -->
  - _Go to Previous Buffer_ `Ctrl+Shift+Tab`
  - _Go to Next Buffer_ `Ctrl+Tab`
- Code Completion
  - _Complete Isabelle text_ `Ctrl+Space` <!-- (by default assigned to _Repeat Last Action_) -->
    <!-- - there are some similarly named commands that perform different actions:
      - _Complete Word_ (Built-in Commands) is not context aware, and will suggest any word found in the current document
      - _Complete word_ (Plugin: Isabelle) and _Show Completion Popup_ (Plugin: SideKick)
        have no observable effect -->

## Abbreviations

These are configured in `$ISABELLE_USER_HOME/etc/symbols` (see `max_notes/isabelle.md#adjusting-abbreviations`).  
Note that jEdit provides built-in support for abbreviations (`Global Options > jEdit > Abbreviations`),
however those are independent of the standard Isabelle symbol abbreviations
(such as `==>` being replaced by `⟹` immediately after typing it).

Some useful additions are presented here:

```isabelle-symbols
# all additional modifies may be dropped, but `code: 0x...` should remain
# (for single character entries) as otherwise symbol replacement will be broken

# quick access to (single-character) sub-script and super-script
\<^sup> code: 0x0021e7 abbrev: ;;
\<^sub> code: 0x0021e9 abbrev: ,,

# abbreviations for pairs of brackets; sometimes more convenient than using the individual ones
# cartouches
\<open>\<close> abbrev: ``
# floor (`⌊ ⌋`) and ceiling (`⌈ ⌉`) brackets
\<lfloor>\<rfloor> abbrev: [_]
\<lceil>\<rceil> abbrev: [-]

# abbreviation `===` for `Pure.eq` (`≡`)
# omitting `abbrev: ==` will break this, as `==` will immediately be replaced by `\<rightleftharpoons>`
\<equiv> code: 0x002261 abbrev: == abbrev: ===
```

## Non-recommended options

Options that may sound interesting but should not be touched

- `Plugin Options > Isabelle > General > ML System > ML System 64`
  - enables `x86_64` (true 64-bit) version of PolyML instead of the [default `x86_64_32`](https://mailmanbroy.informatik.tu-muenchen.de/pipermail/isabelle-dev/2019-January/008176.html)
    - `x86_64_32` implements 32-bit values on a 64-bit system, increasing effective memory bandwidth
    - `x86_64` is in most cases slower (see [benchmarks](https://mailmanbroy.informatik.tu-muenchen.de/pipermail/isabelle-dev/2019-January/016637.html))
