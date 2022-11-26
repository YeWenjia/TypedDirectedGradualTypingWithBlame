# Type-Directed Operational Semantics for Gradual Typing (artifact)

## Abstract

This artifact contains the Coq formulation of \B, \Bg, \Bgl and \E calculus associated with 
the paper "Type-Directed Operational Semantics for Gradual Typing". This document 
explains how to run the Coq formulations and Coq files briefly. 


# 1) Build from Scratch #

This section explains how to build the artifact from scratch

### Prerequisites

1. Install Coq 8.10.2.
   The recommended way to install Coq is via `OPAM`. Refer to
   [here](https://coq.inria.fr/opam/www/using.html) for detailed steps. Or one could
   download the pre-built packages for Windows and MacOS via
   [here](https://github.com/coq/coq/releases/tag/V8.10.2). Choose a suitable installer
   according to your platform.

2. Make sure `Coq` is installed (type `coqc` in the terminal, if you see "command
   not found" this means you have not properly installed Coq), then install `Metalib`:
   1. Open terminal
   2. `git clone https://github.com/plclub/metalib`
   3. `cd metalib/Metalib`
   5. `make install`


### Build and Compile the Proofs

1. Enter  `\Bg/coq`, `\Bg(label)/coq` or ``\E/coq``  directory.

2. Please make sure to run the command `eval \$(opam env)` before running make if 
   you installed the Coq via opam. 

3. Type `make` in the terminal to build and compile the proofs.


## Proof Structure

- `\Bg/coq` directory contains the definition and proofs of \B and \Bg
- `\Bg(label)/coq` directory contains the definition and proofs of \B with blame labels and \Bg with blame labels  
- `\E/coq` directory contains the definition and proofs of \e
- `\Bg/coq/syntax_ott.v` contains the locally nameless definitions of \Bg.
- `\Bg/coq/syntaxb_ott.v` contains the locally nameless definitions of \B.
- `\Bg(label)/coq/syntax_ott.v` contains the locally nameless definitions of \Bg with blame labels.
- `\Bg(label)/coq/syntaxb_ott.v` contains the locally nameless definitions of \B with blame labels.
- `\E/coq/syntax_ott.v` contains the locally nameless definitions of \Bg.
- `rules_inf.v` and `rulesb_inf.v` contains the `lngen` generated code.
- `Infrastructure.v` contains the type systems of the calculi and some lemmas.
- `Infrastructure_b.v` contains the type systems of the blame calculi and some lemmas.
- `Deterministic.v` contains the proofs of the determinism property.
- `Typing.v` contains the proofs of some typing lemmas.
- `Typing_b.v` contains the proofs of some blame calculus typing lemmas.
- `ttyping.v` contains the proofs of some elaboration typing lemmas.
- `criteria.v` contains the proofs of gradual guarantee theorem.
- `Type_Safety.v` contains the proofs of the type preservation and progress properties.
- `\Bg/coq/soundness.v` contains the proofs of the soundness theorem with respect to blame calculus without blame label.
- `\Bg/coq/soundness_blame.v` contains the proofs of the soundness theorem with respect to blame calculus without blame label.
- `\Bg(label)/coq/soundness_completeness.v` contains the proofs of the soundness and completeness theorems with respect to blame calculus with  blame   label.
- `\Bg(label)/coq/soundness_completeness_blame.v` contains the proofs of the soundness and completeness theorems with respect to blame calculus with blame label.
- `\Bg(label)/coq/safe_theorem.v` contains the proofs of blame theorems.


## Correspondence

There are three folders and we show some important definitions and theorems correspondence with the coq formalization. 

### \Bg/coq folder :

| Theorems    | Description           | Files           | Name in Coq               |
|-------------|-----------------------|-----------------|---------------------------|
| Lemma 3.5   | Preservation(casting) | Type\_Safety.v  | TypedReduce\_preservation |
| Lemma 3.6   | Progress(casting)     | Type\_Safety.v  | TypedReduce\_progress     |
| Lemma 3.7   | Determinism(casting)  | Deterministic.v | TypedReduce\_unique       |
| Lemma 3.7   | Consistency(casting)  | Type\_Safety.v  | TypedReduce\_sim          |
| Theorem 3.1 | Determinism           | Deterministic.v | step\_unique              |
| Theorem 3.2 | Preservation          | Type\_Safety.v  | preservation              |
| Theorem 3.3 | Progress              | Type\_Safety.v  | progress                  |
| Theorem 4.1 | Relation(labels)      | Label.v         | bgl\_to\_bg               |
| Theorem 4.1 | Relation(labels)      | Label.v         | bgl\_to\_bg\_typing       |
| Theorem 4.4 | Embedding             | embed.v         | dynamic\_typing           |
| Theorem 4.5 | Equivalence           | embed.v         | static\_Typing\_dyn       |
| Theorem 4.5 | Equivalence           | embed.v         | static\_dtyping\_dyn      |


### \Bg(label)/coq folder :

| Theorems    | Description           | Files                     | Name in Coq                  |
|-------------|-----------------------|---------------------------|------------------------------|
| Theorem 4.2 | Elaboration           | ttyping.v                 | elaboration\_soundness       |
| Theorem 4.2 | Elaboration           | soundness\_completeness.v | btyping\_typing              |
| Lemma 4.1   | Soundness(cast)       | soundness\_completeness.v | Tred\_soundness              |
| Lemma 4.2   | Soundness(cast)       | sound\_complete\_blame.v  | Tred\_blame\_soundness       |
| Lemma 4.3   | Completeness(cast)    | soundness\_completeness.v | typedReduce\_completeness    |
| Lemma 4.4   | Completeness(cast)    | sound\_complete\_blame.v  | tTypedReduce\_completeness   |
| Theorem 4.3 | Sound,complete        | soundness\_completeness.v | soundness                    |
| Theorem 4.3 | Sound,complete        | soundness\_completeness.v | ttyping\_completeness        |
| Theorem 4.3 | Sound,complete        | sound\_complete\_blame.v  | soundness2                   |
| Theorem 4.3 | Sound,complete        | sound\_complete\_blame.v  | ttyping\_completeness\_blame |
| Theorem 4.6 | SGG                   | criteria.v                | SGG\_both                    |
| Lemma 4.5   | DGG(casting)          | criteria.v                | tdynamic\_guarantee          |
| Theorem 4.7 | DGG1                  | criteria.v                | dynamic\_guarantee\_dir      |
| Theorem 4.8 | DGG2                  | criteria.v                | dynamic\_guarantee\_less     |
| Theorem 4.8 | DGG2                  | criteria.v                | dynamic\_guarantees\_blame   |
| Theorem 4.9 | DGG                   | criteria.v                | dynamic\_guarantees          |
| Theorem 4.9 | DGG                   | criteria.v                | dynamic\_guarantees\_less    |
| Lemma 4.6   | Fractoring(subtype)   | safe\_theorem.v           | ssub\_factoring\_right       |
| Lemma 4.6   | Fractoring(subtype)   | safe\_theorem.v           | ssub\_factoring              |
| Lemma 4.7   | Fractoring(precision) | safe\_theorem.v           | ttpre\_factoring             |
| Lemma 4.7   | Fractoring(precision) | safe\_theorem.v           | ttpre\_factoring\_right      |
| Lemma 4.8   | Preservation(safe)    | safe\_theorem.v           | Safe\_preservation           |
| Lemma 4.9   | Progress(safe)        | safe\_theorem.v           | Safe\_progress               |


### \E/coq folder :

| Theorems    | Description           | Files           | Name in Coq               |
|-------------|-----------------------|-----------------|---------------------------|
| Lemma 5.3   | Inference unique      | Typing.v        | inference\_unique         |
| Lemma 5.4   | Casting transitivity  | Type\_safety.v  | TypedReduce\_trans        |
| Lemma 5.4   | Casting transitivity  | Type\_safety.v  | TypedReduce\_transr       |
| Lemma 5.5   | Preservation(casting) | Deterministic.v | TypedReduce\_preservation |
| Lemma 5.6   | Progress(casting)     | Type\_safety.v  | TypedReduce\_progress     |
| Lemma 5.7   | Determinism(casting)  | Deterministic.v | TypedReduce\_unique       |
| Theorem 5.1 | Determinism           | Deterministic.v | step\_unique              |
| Theorem 5.2 | Preservation          | Type\_Safety.v  | preservation              |
| Theorem 5.3 | Progress              | Type\_Safety.v  | progress                  |
| Theorem 5.4 | SGG                   | criteria.v      | SGG\_both                  |
| Lemma 5.8   | DGG(casting)          | criteria.v      | tdynamic\_guarantee       |
| Theorem 5.5 | DGG                   | criteria.v      | dynamic\_guarantee        |
| Theorem 5.6 | DGG                   | criteria.v      | DGG                       |
