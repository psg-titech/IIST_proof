# Mechanized Formalization of Invertible Incremental Sequence Transformations

This repository contains mechanized formalizations of the paper "Invertible Incremental Sequence Transformations" by Shirai (JSSST 2023), implemented in both Coq and Agda (the latter is currently in progress).

## Overview

**Invertible Incremental Sequence Transformations (IISTs)** are a class of stream/list processors that are both incremental and invertible. Given more input, they produce more output; given more output, their inverse can reconstruct more of the original input.

The paper presents a formal framework for IISTs and proves properties such as invertibility through pen-and-paper proofs. This repository mechanizes those proofs using interactive theorem provers to rigorously verify their correctness. In addition, it extends the original framework to support infinite sequences, which were not covered in the paper.

## Formalizations

This repository contains two formalizations:

1. **Coq Formalization** (`Coq/`): A complete formalization of the paper's results in Coq.
2. **Agda Formalization** (`Agda/`): A work-in-progress formalization in Agda.

## Paper Reference

Mizuki Shirai, Sosuke Moriguchi & Takuo Watanabe, **Construction of Inverse Computation in Synchronous Dataflow Programming**, Computer Software, Vol. 41, No. 3, pp. 34-40, Japan Society for Software Science and Technology, DOI: [10.11309/jssst.41.3_34](https://doi.org/10.11309/jssst.41.3_34), Jul., 2024 (in Japanese).

## License

MIT License
