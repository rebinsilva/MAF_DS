# Maximum Agreement Forest (MAF) Solver with Deltasearch

This repository contains a high-performance C++ implementation for solving the **Maximum Agreement Forest (MAF)** problem on rooted phylogenetic trees. The MAF problem is a fundamental computational challenge in phylogenetics, serving as the core mathematical model for calculating the **rooted Subtree Prune and Regraft (rSPR)** distance.

The solver is contained in a single unified C++ file: `maf_combined.cpp`.

---

## Overview

Calculating the rSPR distance is an NP-hard problem. To address this challenge, this project integrates three state-of-the-art algorithmic strategies to provide exact solutions and high-quality approximations:

1. **A Duality-Based 2-Approximation Algorithm**\
   Based on the paper *"A duality based 2-approximation algorithm for maximum agreement forest"*. This is a quadratic-time combinatorial algorithm that establishes a 2-approximation guarantee using a novel linear programming formulation and its dual.

2. **Faster Exact and Approximation Computations**\
   Based on the paper *"Faster Exact Computation of rSPR Distance via Better Approximation"*. This leverages efficient bounded search trees and tree reduction techniques to compute tight upper and lower bounds on the rSPR distance, greatly reducing the computational search space.

3. **Deltasearch**\
   Our custom search algorithm designed to optimize the exploration of the agreement forest search space. By combining systematic reductions and heuristics, Deltasearch rapidly refines the cut-set boundaries to find minimal agreement forests.

By unifying these three methodologies, the solver provides robust, high-performance execution on large-scale phylogenetic trees.

---

## Requirements

To build and run the solver, your system must have:

* A modern C++ compiler (such as `g++` or `clang++`).

* Support for the **C++17** standard (compiled with the `-std=c++17` flag).

* GNU `make` utility.

---

## Building the Executable

The codebase includes a `Makefile` configured to automate the build pipeline.

To compile `maf_combined.cpp` and generate the executable named `maf`, run the following command in the repository's root directory:

```
make
```

---

## Usage

This projects follows the same input and output format as [PACE 2027 challenge format](https://pacechallenge.org/2026/format/).

---

## References

* **Neil Olver, Frans Schalekamp, Suzanne van der Ster, Leen Stougie, Anke van Zuylen.** *"A duality based 2-approximation algorithm for maximum agreement forest."* Mathematical Programming, 2023.

* **Zhi-Zhong Chen, Y. Harada, Y. Nakamura, L. Wang.** *"Faster Exact Computation of rSPR Distance via Better Approximation."* IEEE/ACM Transactions on Computational Biology and Bioinformatics, 2020.
  
* **Steven Kelk, Simone Linz, Ruben Meuwese.** "Cyclic generators and an improved linear kernel for the rooted subtree prune and regraft distance." Information Processing Letters, 180:106336, 2023.
