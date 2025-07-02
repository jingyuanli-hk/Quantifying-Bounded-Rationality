# Quantifying Bounded Rationality

This repository contains formal mathematical and computational work on the quantification of bounded rationality, with a focus on stochastic dominance in decision theory and its formalization in Lean 4.

## Overview

Bounded rationality is a foundational concept in economics and decision theory, describing how agents make decisions under informational, computational, and cognitive constraints. This repository explores new ways to quantify bounded rationality using flexible forms of stochastic dominance, and provides rigorous, machine-checked formalizations in Lean 4. The project also contains accompanying theoretical documents and source code.

## Contents

- **FFSD_2025_0701.pdf**  
  A comprehensive theoretical document detailing flexible first-order stochastic dominance (FFSD), robust Riemann-Stieltjes integrals, and their role in modeling bounded rationality.  
  [View PDF](https://github.com/jingyuanli-hk/Quantifying-Bounded-Rationality/blob/main/FFSD_2025_0701.pdf)

- **FFSD_0701.lean**  
  Lean 4 formalization of the main one-dimensional results, including:
  - Robust Riemann-Stieltjes integral with tolerance for approximation.
  - Uniqueness lemma for the indicator threshold under small tolerance.
  - Characterization of flexible first-order stochastic dominance (FFSD) via expected utility inequalities.
  - All proofs are machine-checked in Lean 4.

- **MultiFFSD_0701.lean**  
  Lean 4 formalization of the N-dimensional generalization:
  - N-dimensional vectors, rectangles, and product measures.
  - N-dimensional robust Riemann-Stieltjes integrals and survival probabilities.
  - Uniqueness and integral lemmas for indicator functions of upper-right orthants.
  - Main theorem: Equivalence of N-dimensional FFSD and expected utility inequalities for functions close to orthant indicators.

## Getting Started

### Requirements

- [Lean 4](https://leanprover.github.io)
- [Mathlib4](https://github.com/leanprover-community/mathlib4) (for real analysis, calculus, etc.)

### Building

1. Clone the repository:
   ```sh
   git clone https://github.com/jingyuanli-hk/Quantifying-Bounded-Rationality.git
   cd Quantifying-Bounded-Rationality
   ```

2. Install dependencies:
   ```sh
   lake update
   ```

3. Check the Lean files:
   ```sh
   lake build
   ```

4. Open in your favorite Lean editor (e.g., VS Code with Lean extension).

### File guide

- `FFSD_0701.lean`: One-dimensional formal proofs and definitions.
- `MultiFFSD_0701.lean`: N-dimensional generalization and formal proofs.
- `FFSD_2025_0701.pdf`: Theoretical background and mathematical exposition.

## Citation

If you use this work or build on it in academic research, please cite the authors as indicated in the source files.

## License

This project is licensed under the Apache 2.0 License. See the `LICENSE` file for details.

## Authors

- Jingyuan Li
- Lin Zhou

## Acknowledgments

This work uses [Lean 4](https://leanprover.github.io) and [mathlib4](https://github.com/leanprover-community/mathlib4).

---

*For questions or collaboration, please open an issue or contact the repository owner.*
