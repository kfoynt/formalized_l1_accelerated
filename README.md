# Formal Verification of "Complexity of Classical Acceleration for ℓ₁-Regularized PageRank"

A Lean 4 + Mathlib formalization of the main results from:

> **Complexity of Classical Acceleration for ℓ₁-Regularized PageRank**
> Kimon Fountoulakis and David Martínez-Rubio
> [arXiv:2602.21138](https://arxiv.org/abs/2602.21138)

## Overview

This project provides machine-checked proofs (in Lean 4) for the theoretical results in the paper, which studies the degree-weighted work required to compute ℓ₁-regularized PageRank using the accelerated proximal-gradient method (FISTA). The formalization covers the main work bound, the boundary confinement theorem, supporting lemmas, and the lower-bound construction showing FISTA can be worse than ISTA on star graphs.

## What is formalized

### Core results (Sections 3--4 and Appendix A)

| # | Result | Statement |
|---|--------|-----------|
| 1 | **Lemma A.1** | Initial gap: F(0) = 0 and Δ₀ ≤ α/(2d_v) |
| 2 | **Fact A.2** | FISTA convergence rate: F(x_k) − F(x\*) ≤ 2Δ₀·(1−√α)^k |
| 3 | **Corollary A.3** | FISTA iterate bounds: ‖y_k − x\*‖² ≤ M·(1−√α)^{k−1} with M ≤ 20 |
| 4 | **Lemma 4.1** | Coordinate jump: spurious activation implies forward-step deviation exceeds KKT slack |
| 5 | **Lemma A.4** | Path monotonicity: x\*(ρ') ≤ x\*(ρ) coordinatewise for ρ' > ρ |
| 6 | **Lemma A.5** | Proximal gradient monotonicity |
| 7 | **Lemma 4.2** | Two-tier split: small-margin inactive nodes lie in the less-regularized support |
| 8 | **Theorem 4.3** | Work bound: O(1/(ρ√α)·log(α/ε) + √vol(B)/(ρα^{3/2})) |
| 9 | **Theorem 4.4** | Boundary confinement: supp(x_k) ⊆ S ∪ ∂S under a checkable graph condition |
| 10 | **Proposition A.8** | Degree cutoff: high-degree nodes are never activated |

### Lower bound (Appendix D) and bad instances (Appendix C)

| Result | Statement |
|--------|-----------|
| **Lemma D.1** | Star graph (seed at leaf): unique minimizer, margin formula, zero-margin breakpoint |
| **Lemma D.2** | Activation criterion at the breakpoint |
| **Lemma D.3** | FISTA overshoot at k=2: exact identity y_{2,v} = x\*_v·(1 + (1−α)β²/2) |
| **Proposition D.4** | FISTA total work ≥ 2D vs. ISTA total work O(1/α · log(1/ε)) |
| **Lemma C.1** | Star graph (seed at center): unique minimizer + breakpoint algebra |
| **Lemma C.2** | Path graph (seed at endpoint): unique minimizer + breakpoint algebra |

## File structure

| File | Contents |
|------|----------|
| `RequestProject/Defs.lean` | All definitions: graph, objective function, proximal map, FISTA iterates, etc. |
| `RequestProject/Helpers.lean` | Axioms and auxiliary lemmas (FISTA iterate properties, KKT helpers, Cauchy--Schwarz) |
| `RequestProject/Results.lean` | Main theorems from Sections 3--4 and Appendix A |
| `RequestProject/LowerBound.lean` | Lower bound construction (Appendix D) and bad instances (Appendix C) |

## Axiomatized results

Nine foundational results are taken as axioms (not proved from first principles in this formalization):

- `fObj_expansion` — quadratic Taylor identity
- `minimizer_strong_convexity` — strong-convexity gap bound
- `minimizer_is_prox_fixed_point` — minimizer implies proximal fixed point (Beck 2017, Thm 10.16)
- `rppr_support_volume_bound` — vol(supp(x\*)) ≤ 1/ρ (Fountoulakis et al. 2019, Thm 2)
- `minimizer_nonneg` — minimizer has nonnegative coordinates
- `kkt_inactive_upper` — ∇f(x\*)_i ≤ 0 at inactive coordinates
- `fista_convergence_rate` — FISTA convergence rate (Beck & Teboulle 2009)
- `ista_support_subset_optimal` — ISTA iterates have support contained in optimal support (Fountoulakis 2019, Thm 1)
- `ista_convergence_rate` — ISTA convergence rate (Beck & Teboulle 2009)

Everything else is proved from these axioms and the Mathlib library.

## Building

Requires Lean 4.28.0 and Mathlib v4.28.0.

```bash
# Build the full project
lake build

# Check a single file
lake env lean RequestProject/Results.lean
```

## Status

All files compile with **0 sorries, 0 errors, and 0 warnings**.
