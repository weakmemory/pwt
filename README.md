# Pomsets w/ Transformers (a Coq formalization)

This repository contains Coq code supplementing the paper _Leaky Semicolon: Compositional Semantic Dependencies for Relaxed-Memory Concurrency_ by 
Alan Jeffrey, James Riely, Mark Batty, Simon Cooksey, Anton Podkopaev, and Ilya Kaysin.

## Building the Project

### Requirements
* [Coq 8.13.1](https://coq.inria.fr)
* [Hahn library](https://github.com/vafeiadis/hahn) (`coq-hahn`)
* [Intermediate Memory Model](https://github.com/weakmemory/imm) (`coq-imm.1.3`)

All required dependencies can be installed via package manager [`opam`](https://opam.ocaml.org/). 

```bash
opam repo add coq-released https://coq.inria.fr/opam/released
opam remote add coq-weakmemory-local -k git https://github.com/weakmemory/local-coq-opam-archive
opam install coq-hahn coq-imm.1.3
```

### Building Manually

To build the project just use `make -j` command (assuming all dependencies were installed as described above). 

## Description of the project's files

### Basic definitions of the semantics
- `Events.v` – a definition of events (§4.1)
- `Language.v` – definitions of statements _S_ and expressions _M_ (§4.1)
- `Formula.v` – a language of formulas Φ (§4.1)
- `Action.v` — a definition of actions and related notions (§4.2)
- `PredTransformer.v` — a definition of predicate transformers (§4.3, Def. 4.2)
- `Pomset.v` — a definition of pomsets with predicate transformers (§4.3, Def. 4.4)
- `Semantics.v` — the PwT semantics extended to allow if-closure (§4.3, Fig. 1 and §9.4, Def. 9.6)

### Properties of the semantics
- `SeqSkipId.v` — `skip` as an identity element for the semicolon operator (§4.3, Lemma 4.5a)
- `SeqAssoc.v` — associativity of the semicolon operator (§4.3, Lemma 4.5b)
- `IfClosure.v` — distribution of the if operator over semicolon (§4.3, Lemma 4.6e)

### Auxiliary definitions and lemmas
- `AuxDef.v`, `AuxRel.v`, `SeqBuilder.v`
