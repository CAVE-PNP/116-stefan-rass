session "116_stefan_rass" = "HOL-Library" +
  options [document = pdf, document_output = "output"]
  sessions
    Universal_Turing_Machine
    "HOL-Computational_Algebra"
    Intro_Dest_Elim
    "HOL-Eisbach"
  directories
    (* This allows unqualified imports (\<open>Misc\<close> instead of \<open>"Supplementary/Misc"\<close>),
     * but only if this session is registered in Isabelle's component list.
     * To avoid inconsistent behaviour for users inspecting the code,
     * we hence use qualified imports where applicable. *)
    Supplementary
  theories [quick_and_dirty] (* allow `sorry` *)
    (* Supplementary theories *)
    "Supplementary/Misc"
    "Supplementary/Lists"
    "Supplementary/Sublists"
    "Supplementary/Discrete_Log"
    "Supplementary/Discrete_Sqrt"
    "Supplementary/Asymptotic"
    "Supplementary/UF_Code"
    (* Definitions and Preliminaries *)
    Binary
    Goedel_Numbering
    Language_Density
    (* A Hard Language with a Known Density Bound *)
    SQ
    TM_Encoding
    Complexity
    L0
  document_files
    "root.tex"
    "root.bib"
