# Coq

Seems more focused on functional aspect and proving the correctness of programs
(including generating certified programs from proofs of correctness for said programs).

- [Coq](#coq)
  - [Coq IDEs](#coq-ides)
    - [CoqIde](#coqide)
    - [jsCoq](#jscoq)
    - [VSCoq (VSCode)](#vscoq-vscode)

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
