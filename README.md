🧊 Hurricane
============

[![Actions](https://github.com/groupoid/hurricane/workflows/opam/badge.svg)](https://github.com/groupoid/hurricane/actions)

Minimal Implementation of HoTT-I Type System with definitional Path-β

```OCaml
type exp =
  | EKan of Z.t | EVar of name | EHole                                        (* cosmos *)
  | EPi of exp * (name * exp) | ELam of exp * (name * exp) | EApp of exp * exp     (* Π *)
  | ESig of exp * (name * exp) | EPair of exp * exp | EFst of exp | ESnd of exp    (* Σ *)
  | EI | ELeft | ERight | ECoe of exp                                       (* interval *)
  | EPathP of exp | EPLam of exp | EAppFormula of exp * exp                     (* path *)
  | EIso of exp                                                           (* univalence *)
  | EN | EZero | ESucc | ENInd of exp                                              (* N *)
  | EZ | EPos | ENeg | EZInd of exp | EZSucc | EZPred                              (* Z *)
  | EBot | EBotRec of exp                                                          (* ⊥ *)
```

HoTT-I
------

Hurricane was built by strictly following these publications:

* <a href="https://arxiv.org/pdf/2004.14195.pdf">Models of Homotopy Type Theory with an Interval Type</a> [Valery Isaev]

Authors
-------

* Siegmentation Fault
