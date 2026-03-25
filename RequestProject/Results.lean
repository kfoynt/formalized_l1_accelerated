import Mathlib
import RequestProject.Defs
import RequestProject.Helpers

/-!
# Formal Results for ℓ₁-Regularized PageRank

Formalization of the core theorems from Sections 3–4 and Appendices A–C of:
"Complexity of Classical Acceleration for ℓ₁-Regularized PageRank"
by K. Fountoulakis and D. Martínez-Rubio.

Note: Nine foundational results are axiomatized (not proved from first principles):
- fObj_expansion (quadratic Taylor identity, Helpers.lean)
- minimizer_strong_convexity (strong-convexity gap bound, Helpers.lean)
- minimizer_is_prox_fixed_point (minimizer ⟹ prox fixed point, Beck 2017 Thm 10.16, Helpers.lean)
- rppr_support_volume_bound (vol(supp(x*)) ≤ 1/ρ, Fountoulakis et al. 2019 Thm 2, Helpers.lean)
- minimizer_nonneg (minimizer has nonneg coordinates, Helpers.lean)
- kkt_inactive_upper (∇f(x*)_i ≤ 0 at inactive coordinates, Helpers.lean)
- fista_convergence_rate (FISTA convergence rate, Beck & Teboulle 2009, Results.lean)
- ista_support_subset_optimal (ISTA support ⊆ optimal support, Fountoulakis 2019 Thm 1, LowerBound.lean)
- ista_convergence_rate (ISTA convergence rate, Beck & Teboulle 2009, LowerBound.lean)

## Results formalized
1. **Lemma A.1** (Initial gap): F_ρ(0) = 0 and Δ₀ ≤ α/(2d_v)
2. **Fact A.2** (FISTA convergence rate): F(x_k) − F(x*) ≤ 2Δ₀·(1−√α)^k
3. **Corollary A.3** (FISTA iterate bounds):
   - General form: ‖y₀ − x*‖² ≤ 4Δ₀/α and ‖y_k − x*‖² ≤ M·(1−√α)^{k−1}
   - Specialized: M ≤ 20, so ‖y_k − x*‖ ≤ √20
4. **Lemma 4.1** (Coordinate jump): spurious activation ⟹ forward-step deviation
5. **Lemma A.4** (Path monotonicity): x*(ρ') ≤ x*(ρ) for ρ' > ρ
6. **Lemma A.5** (Proximal gradient monotonicity): monotone prox-grad map
7. **Lemma 4.2** (Two-tier split): small-margin nodes ⊆ S_A
8. **Theorem 4.3** (Work bound): O(1/(ρ√α)·log(α/ε) + √vol(B)/(ρα^{3/2}))
9. **Theorem 4.4** (Boundary confinement): supp(x_k) ⊆ S ∪ ∂S
10. **Proposition A.8** (Degree cutoff): high-degree nodes never activate
-/

noncomputable section

open Finset BigOperators Real RPPR

namespace RPPR

variable {n : ℕ}

/-! ## Result 1: Initial Gap (Lemma A.1)

For a single seed s = e_v and initialization x₀ = 0:
  F_ρ(0) = 0  and  Δ₀ = F_ρ(0) − F_ρ(x*) ≤ α/(2·d_v) ≤ α/2.

The key ideas: f(0) = 0, g(0) = 0, and using Q ≽ αI to bound min f. -/

/-
PROBLEM
F_ρ(0) = 0: the zero vector has zero objective value.

PROVIDED SOLUTION
F_ρ(0) = f(0) + g(0). f(0) = ½·0ᵀQ·0 - α⟨D⁻¹ᐟ²s, 0⟩ = 0. g(0) = c·α·ρ·Σ √d_i·|0| = 0. So F(0) = 0. Unfold FObj, fObj, gReg. All sums are over x=0, so each term is zero.
-/
theorem initial_gap_zero (G : Graph n) (α ρ : ℝ) (v : Fin n) :
    G.FObj 1 α ρ (basisVec v) 0 = 0 := by
      unfold RPPR.Graph.FObj RPPR.Graph.fObj RPPR.Graph.gReg; norm_num;

/-
PROBLEM
Lemma A.1 (Initial gap bound): Δ₀ = F_ρ(0) − F_ρ(x*) ≤ α/(2·d_v).

PROVIDED SOLUTION
We have F_ρ(0) = 0 (by initial_gap_zero). So we need -F_ρ(xstar) ≤ α/(2·d_v).

F_ρ(xstar) = f(xstar) + g(xstar) ≥ f(xstar) ≥ min_x f(x).

The unconstrained minimizer of f(x) = ½x^TQx - α⟨b,x⟩ (where b = D^{-1/2}s) has min f = -½b^TQ^{-1}b.

Since Q ≽ αI, we have Q^{-1} ≼ (1/α)I. Thus b^TQ^{-1}b ≤ (1/α)‖b‖² = (1/α)·α²·‖D^{-1/2}s‖² = α·s^TD^{-1}s.

For s = e_v: s^TD^{-1}s = 1/d_v.

So min f ≥ -α/(2d_v), hence F_ρ(xstar) ≥ -α/(2d_v), hence -F_ρ(xstar) ≤ α/(2d_v).

Key: use that xstar minimizes F, so F(xstar) ≤ F(x) for all x, and F ≥ f, and bound min f.
-/
theorem initial_gap_bound (G : Graph n) (α ρ : ℝ) (v : Fin n)
    (hα : 0 < α) (hα1 : α ≤ 1) (hρ : 0 < ρ)
    (xstar : Fin n → ℝ) (_hmin : G.IsMinimizer 1 α ρ (basisVec v) xstar) :
    G.FObj 1 α ρ (basisVec v) 0 - G.FObj 1 α ρ (basisVec v) xstar
      ≤ α / (2 * G.deg v) := by
        unfold Graph.FObj;
        unfold Graph.fObj Graph.gReg;
        -- Since $Q \succeq \alpha I$, we have $\sum_{i,j} xstar_i Q_{ij} xstar_j \geq \alpha \sum_{i} xstar_i^2$.
        have h_quad_form : ∑ i, xstar i * (∑ j, G.Qentry α i j * xstar j) ≥ α * ∑ i, xstar i ^ 2 := by
          -- By definition of $Q$, we know that $Q \succeq \alpha I$, which implies that for any vector $x$, $x^T Q x \geq \alpha x^T x$.
          have hQ_pos_semidef : ∀ x : Fin n → ℝ, ∑ i, x i * ∑ j, G.Qentry α i j * x j ≥ α * ∑ i, x i ^ 2 := by
            intro x
            have hQ_bound : ∀ i j, G.Qentry α i j = if i = j then (1 + α) / 2 else -(1 - α) / 2 * G.A i j / (G.sqrtDeg i * G.sqrtDeg j) := by
              intro i j; unfold Graph.Qentry; rfl;
            -- By definition of $Q$, we know that $Q \succeq \alpha I$, which implies $x^T Q x \geq \alpha x^T x$ for any vector $x$. This follows from the fact that $Q$ is positive semi-definite.
            have hQ_pos_def : ∀ x : Fin n → ℝ, ∑ i, ∑ j, G.A i j * x i * x j / (G.sqrtDeg i * G.sqrtDeg j) ≤ ∑ i, x i ^ 2 := by
              intro x
              have hQ_pos_def : ∀ i j, G.A i j * x i * x j / (G.sqrtDeg i * G.sqrtDeg j) ≤ (x i ^ 2 * G.A i j / (2 * G.sqrtDeg i ^ 2)) + (x j ^ 2 * G.A i j / (2 * G.sqrtDeg j ^ 2)) := by
                intro i j; rw [ div_add_div, div_le_div_iff₀ ] <;> try nlinarith [ G.sqrtDeg_pos i, G.sqrtDeg_pos j, G.A_nonneg i j ] ; ; ring_nf ; (
                nlinarith [ sq_nonneg ( x i * G.sqrtDeg j - x j * G.sqrtDeg i ), show 0 ≤ G.A i j * G.sqrtDeg i * G.sqrtDeg j by exact mul_nonneg ( mul_nonneg ( G.A_nonneg i j ) ( Real.sqrt_nonneg _ ) ) ( Real.sqrt_nonneg _ ) ] ;);
                exact mul_pos ( mul_pos two_pos ( sq_pos_of_pos ( G.sqrtDeg_pos i ) ) ) ( mul_pos two_pos ( sq_pos_of_pos ( G.sqrtDeg_pos j ) ) );
              refine' le_trans ( Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hQ_pos_def i j ) _;
              norm_num [ Finset.sum_add_distrib, ← Finset.mul_sum _ _ _, ← Finset.sum_div ];
              rw [ ← Finset.sum_comm ];
              simp +decide [ ← Finset.mul_sum _ _ _, ← Finset.sum_div, G.A_symm ];
              rw [ ← Finset.sum_add_distrib ] ; refine' Finset.sum_le_sum fun i _ => _ ; rw [ show G.sqrtDeg i ^ 2 = G.deg i from Real.sq_sqrt <| le_of_lt <| G.deg_pos' i ] ; ring_nf ;
              rw [ ← div_eq_mul_inv, div_le_iff₀ ]
              nlinarith [ G.deg_pos' i, show ∑ j, G.A i j = G.deg i from rfl ];
            -- Substitute the definition of $Q$ into the inequality.
            have h_subst : ∑ i, x i * (∑ j, G.Qentry α i j * x j) = (1 + α) / 2 * ∑ i, x i ^ 2 - (1 - α) / 2 * ∑ i, ∑ j, G.A i j * x i * x j / (G.sqrtDeg i * G.sqrtDeg j) := by
              simp +decide [ hQ_bound, Finset.sum_ite, Finset.filter_eq, Finset.filter_ne ];
              simp +decide [ Finset.mul_sum _ _ _, Finset.sum_add_distrib, mul_add, mul_assoc, mul_comm, mul_left_comm, div_eq_mul_inv, sq, G.A_no_loops ] ; ring;
              norm_num [ Finset.sum_add_distrib, Finset.mul_sum _ _ _, Finset.sum_mul _ _ _ ] ; ring;
              simpa only [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul ] using by ring;
            nlinarith [ hQ_pos_def x, show 0 ≤ ∑ i, x i ^ 2 from Finset.sum_nonneg fun _ _ => sq_nonneg _ ];
          exact hQ_pos_semidef xstar;
        set QF := ∑ i, xstar i * (∑ j, G.Qentry α i j * xstar j) with hQF_def
        unfold basisVec; norm_num [ Finset.sum_eq_single v ] ; ring_nf at *;
        -- Apply the Cauchy-Schwarz inequality to the term involving $xstar_v$.
        have h_cauchy_schwarz : α * G.invSqrtDeg v * xstar v ≤ α * (G.deg v)⁻¹ * (1 / 2) + α * xstar v ^ 2 / 2 := by
          rw [ show G.invSqrtDeg v = ( Real.sqrt ( G.deg v ) ) ⁻¹ by rfl ];
          rw [ ← Real.sqrt_inv ];
          nlinarith only [ sq_nonneg ( xstar v - Real.sqrt ( G.deg v ) ⁻¹ ), Real.mul_self_sqrt ( show 0 ≤ ( G.deg v ) ⁻¹ by exact inv_nonneg.2 ( le_of_lt ( G.deg_pos' v ) ) ), hα ];
        nlinarith [ show 0 ≤ α * ρ * ∑ x : Fin n, G.sqrtDeg x * |xstar x| by exact mul_nonneg ( mul_nonneg hα.le hρ.le ) ( Finset.sum_nonneg fun _ _ => mul_nonneg ( Real.sqrt_nonneg _ ) ( abs_nonneg _ ) ), show ∑ x : Fin n, xstar x ^ 2 ≥ xstar v ^ 2 by exact Finset.single_le_sum ( fun i _ => sq_nonneg ( xstar i ) ) ( Finset.mem_univ v ) ]

/-
PROBLEM
Corollary of Lemma A.1: Δ₀ ≤ α/2 (since d_v ≥ 1 implies 1/(2d_v) ≤ 1/2).

PROVIDED SOLUTION
From initial_gap_bound, Δ₀ ≤ α/(2·d_v). Since d_v ≥ 1 (hypothesis hd), we have 1/(2·d_v) ≤ 1/2, so α/(2·d_v) ≤ α/2. Chain the two inequalities.
-/
theorem initial_gap_simple (G : Graph n) (α ρ : ℝ) (v : Fin n)
    (hα : 0 < α) (hα1 : α ≤ 1) (hρ : 0 < ρ)
    (hd : 1 ≤ G.deg v)
    (xstar : Fin n → ℝ) (hmin : G.IsMinimizer 1 α ρ (basisVec v) xstar) :
    G.FObj 1 α ρ (basisVec v) 0 - G.FObj 1 α ρ (basisVec v) xstar
      ≤ α / 2 := by
        refine' le_trans ( _ : _ ≤ _ ) ( div_le_div_of_nonneg_left _ _ _ );
        convert initial_gap_bound G α ρ v hα hα1 hρ xstar hmin using 1;
        · linarith;
        · norm_num;
        · linarith

/-! ## Result 2: FISTA Convergence Rate (Fact A.2)

For f being L-smooth and F = f + g being μ-strongly convex, FISTA with
η = 1/L and β = (√(L/μ) − 1)/(√(L/μ) + 1) satisfies:
  F(x_k) − F(x*) ≤ 2·(F(x₀) − F(x*))·(1 − √(μ/L))^k  for all k ≥ 1.

For PageRank: L = 1, μ = α, so the rate is (1 − √α)^k.
This is a classical result; see Beck (2017), Section 10.7.7. -/

/-- Fact A.2 (FISTA convergence rate) specialized to PageRank:
    F(x_k) − F(x*) ≤ 2·Δ₀·(1 − √α)^k for all k ≥ 1.

    This is a standard result from Beck & Teboulle (2009), Theorem 4.4.
    For composite minimization F = f + g with f being L-smooth and F
    being μ-strongly convex, FISTA with η = 1/L and
    β = (√(L/μ)−1)/(√(L/μ)+1) satisfies:
      F(x_k) − F(x*) ≤ 2(F(x₀)−F(x*))·((√L−√μ)/(√L+√μ))^{2k}
    For PageRank: L = 1, μ = α, giving rate (1−√α)^k per step.

    ASSUMED: This is a textbook result; see
    Beck (2017) "First-Order Methods in Optimization", Section 10.7.7. -/
axiom fista_convergence_rate (G : Graph n) (c α ρ : ℝ) (s : Fin n → ℝ)
    (hα : 0 < α) (hα1 : α ≤ 1) (hρ : 0 < ρ) (hc : 0 < c)
    (xstar : Fin n → ℝ) (hmin : G.IsMinimizer c α ρ s xstar)
    (k : ℕ) (hk : 1 ≤ k) :
    G.FObj c α ρ s (fistaX G c α ρ s k) - G.FObj c α ρ s xstar ≤
    2 * (G.FObj c α ρ s (fistaX G c α ρ s 0) - G.FObj c α ρ s xstar) *
      (1 - √α) ^ k

/-! ## Result 3: FISTA Iterate Bounds (Corollary A.3)

Bounds on the distance from the extrapolation points to the minimizer.

**General form (matching paper Corollary A.3)**:
  Part 1: ‖y₀ − x*‖² ≤ 4Δ₀/μ
  Part 2: ‖y_k − x*‖² ≤ M·(1−√(μ/L))^{k−1} for k ≥ 1
  where M = (8Δ₀/μ)·((1+β)²·(1−√(μ/L)) + β²).

**Specialized for PageRank** (L = 1, μ = α, Δ₀ ≤ α/2):
  M ≤ 20, yielding ‖y_k − x*‖₂ ≤ √20 for all k. -/

/-- Corollary A.3 (part 1, general form): ‖y₀ − x*‖² ≤ 4Δ₀/α.
    This is the paper's verbatim statement with μ = α (PageRank strong convexity).
    Proof: from strong convexity, α/2·‖x*‖² ≤ F(0)−F(x*) = Δ₀, so ‖x*‖² ≤ 2Δ₀/α ≤ 4Δ₀/α. -/
theorem corollary_A3_part1_general (G : Graph n) (c α ρ : ℝ) (v : Fin n)
    (hα : 0 < α) (hα1 : α ≤ 1) (hρ : 0 < ρ) (hc : 0 < c)
    (xstar : Fin n → ℝ) (hmin : G.IsMinimizer c α ρ (basisVec v) xstar) :
    let Δ₀ := G.FObj c α ρ (basisVec v) 0 - G.FObj c α ρ (basisVec v) xstar
    normSq (fun i => fistaY G c α ρ (basisVec v) 0 i - xstar i) ≤ 4 * Δ₀ / α := by
  intro Δ₀
  -- y₀ = 0, so ‖y₀ − x*‖² = ‖x*‖²
  have hy0 : ∀ i, fistaY G c α ρ (basisVec v) 0 i = 0 := fun i => by
    unfold fistaY fistaState fistaMom; simp
  have hsimp : normSq (fun i => fistaY G c α ρ (basisVec v) 0 i - xstar i) = normSq xstar := by
    simp only [normSq, hy0, zero_sub, neg_sq]
  rw [hsimp]
  -- Strong convexity: α/2 · ‖0 − x*‖² ≤ F(0) − F(x*) = Δ₀
  have hsc := minimizer_strong_convexity G c α ρ (basisVec v) xstar hα hα1 hc hρ hmin 0
  have h0 : normSq (fun i => (0 : Fin n → ℝ) i - xstar i) = normSq xstar := by
    simp only [normSq, Pi.zero_apply, zero_sub, neg_sq]
  rw [h0] at hsc
  -- Δ₀ ≥ 0 (x* minimizes F)
  have hΔ_nn : 0 ≤ Δ₀ := by have := hmin 0; linarith
  -- normSq xstar ≤ 2Δ₀/α ≤ 4Δ₀/α
  rw [le_div_iff₀ hα]; nlinarith [normSq_nonneg xstar, hΔ_nn]

/-- Helper: ‖x_k − x*‖² ≤ (4Δ₀/α)·(1−√α)^k for all k (general form).
    This is the intermediate bound used in the proof of Corollary A.3 part 2. -/
theorem fista_xk_decay_general (G : Graph n) (c α ρ : ℝ) (v : Fin n)
    (hα : 0 < α) (hα1 : α ≤ 1) (hρ : 0 < ρ) (hc : 0 < c)
    (_hd : 1 ≤ G.deg v)
    (xstar : Fin n → ℝ) (hmin : G.IsMinimizer c α ρ (basisVec v) xstar) :
    let Δ₀ := G.FObj c α ρ (basisVec v) 0 - G.FObj c α ρ (basisVec v) xstar
    ∀ k, normSq (fun i => fistaX G c α ρ (basisVec v) k i - xstar i) ≤
      4 * Δ₀ / α * (1 - √α) ^ k := by
  intro Δ₀ k
  have hrate : 0 ≤ 1 - √α := by linarith [Real.sqrt_le_one.mpr hα1]
  have hrate1 : 1 - √α ≤ 1 := by linarith [Real.sqrt_pos_of_pos hα]
  have hΔ_nn : 0 ≤ Δ₀ := by have := hmin 0; linarith
  have h4Δα_nn : 0 ≤ 4 * Δ₀ / α := div_nonneg (by linarith) (le_of_lt hα)
  rcases k with _ | k
  · -- k = 0: ‖x₀ − x*‖² = ‖x*‖², (1−√α)⁰ = 1
    simp only [pow_zero, mul_one]
    have hx0 : fistaX G c α ρ (basisVec v) 0 = 0 := fistaX_zero G c α ρ (basisVec v)
    rw [hx0]
    have hsc := minimizer_strong_convexity G c α ρ (basisVec v) xstar hα hα1 hc hρ hmin 0
    have h0 : normSq (fun i => (0 : Fin n → ℝ) i - xstar i) = normSq xstar := by
      unfold normSq; congr 1; ext i; simp
    rw [h0] at hsc ⊢; rw [le_div_iff₀ hα]; nlinarith [normSq_nonneg xstar]
  · -- k+1 ≥ 1: convergence rate + strong convexity
    have hsc := minimizer_strong_convexity G c α ρ (basisVec v) xstar hα hα1 hc hρ hmin
      (fistaX G c α ρ (basisVec v) (k + 1))
    have hconv := fista_convergence_rate G c α ρ (basisVec v) hα hα1 hρ hc xstar hmin (k + 1) (by omega)
    rw [fistaX_zero] at hconv
    -- F(x_{k+1}) − F(x*) ≤ 2Δ₀·(1−√α)^{k+1}
    -- α/2·‖x_{k+1}−x*‖² ≤ 2Δ₀·(1−√α)^{k+1}
    -- ‖x_{k+1}−x*‖² ≤ 4Δ₀/α·(1−√α)^{k+1}
    rw [show 4 * Δ₀ / α * (1 - √α) ^ (k + 1) = (4 * Δ₀ * (1 - √α) ^ (k + 1)) / α from by ring, le_div_iff₀ hα]
    have hchain := le_trans hsc hconv
    nlinarith [normSq_nonneg (fun i => fistaX G c α ρ (basisVec v) (k + 1) i - xstar i),
               pow_nonneg hrate (k + 1)]

/-- Corollary A.3 (part 2, general form): ‖y_k − x*‖² ≤ M·(1−√α)^{k−1} for k ≥ 1,
    where M = (8Δ₀/α)·((1+β)²·(1−√α) + β²).

    This is the paper's verbatim Corollary A.3 statement (with L = 1, μ = α).
    The proof decomposes y_k = (1+β)x_k − β·x_{k−1}, applies ‖a+b‖² ≤ 2‖a‖² + 2‖b‖²,
    and uses the general x_k decay bound from fista_xk_decay_general. -/
theorem corollary_A3_part2_general (G : Graph n) (c α ρ : ℝ) (v : Fin n)
    (hα : 0 < α) (hα1 : α ≤ 1) (hρ : 0 < ρ) (hc : 0 < c)
    (hd : 1 ≤ G.deg v)
    (xstar : Fin n → ℝ) (hmin : G.IsMinimizer c α ρ (basisVec v) xstar)
    (k : ℕ) (hk : 1 ≤ k) :
    let Δ₀ := G.FObj c α ρ (basisVec v) 0 - G.FObj c α ρ (basisVec v) xstar
    let β := fistaMom α
    let M := 8 * Δ₀ / α * ((1 + β) ^ 2 * (1 - √α) + β ^ 2)
    normSq (fun i => fistaY G c α ρ (basisVec v) k i - xstar i) ≤ M * (1 - √α) ^ (k - 1) := by
  intro Δ₀ β M
  have hrate : 0 ≤ 1 - √α := by linarith [Real.sqrt_le_one.mpr hα1]
  have hΔ_nn : 0 ≤ Δ₀ := by have := hmin 0; linarith
  have hβ_nn := fistaMom_nonneg α hα hα1
  have hβ_lt1 := fistaMom_lt_one α hα hα1
  -- Write k = k' + 1
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  show _ ≤ M * (1 - √α) ^ (k' + 1 - 1)
  simp only [Nat.add_sub_cancel]
  -- Decompose y_{k'+1} − x* = (1+β)(x_{k'+1} − x*) + (−β)(x_{k'} − x*)
  have h_eq : normSq (fun i => fistaY G c α ρ (basisVec v) (k' + 1) i - xstar i) =
      normSq (fun i => (1 + β) * (fistaX G c α ρ (basisVec v) (k' + 1) i - xstar i) +
        (-β) * (fistaX G c α ρ (basisVec v) k' i - xstar i)) := by
    congr 1; ext i; rw [fistaY_succ]; ring
  rw [h_eq]
  -- ‖(1+β)a + (−β)b‖² ≤ 2(1+β)²‖a‖² + 2β²‖b‖²
  have h_tri := normSq_add_le
    (fun i => (1 + β) * (fistaX G c α ρ (basisVec v) (k' + 1) i - xstar i))
    (fun i => (-β) * (fistaX G c α ρ (basisVec v) k' i - xstar i))
  rw [normSq_smul, normSq_smul] at h_tri
  -- General x_k bounds: ‖x_j − x*‖² ≤ (4Δ₀/α)·(1−√α)^j
  have hxk1 := fista_xk_decay_general G c α ρ v hα hα1 hρ hc hd xstar hmin (k' + 1)
  have hxk0 := fista_xk_decay_general G c α ρ v hα hα1 hρ hc hd xstar hmin k'
  -- Combine: 2(1+β)²·(4Δ₀/α)·q^{k'+1} + 2β²·(4Δ₀/α)·q^{k'}
  --        = (8Δ₀/α)·q^{k'}·[(1+β)²·q + β²] = M·q^{k'}
  have hN1 := normSq_nonneg (fun i => fistaX G c α ρ (basisVec v) (k' + 1) i - xstar i)
  have hN0 := normSq_nonneg (fun i => fistaX G c α ρ (basisVec v) k' i - xstar i)
  rw [pow_succ] at hxk1
  -- M = 8Δ₀/α · ((1+β)²·(1−√α) + β²)
  -- RHS = M·q^{k'} = 8Δ₀/α · coeff · q^{k'}
  -- LHS ≤ 2(1+β)²·4Δ₀/α·q·q^{k'} + 2β²·4Δ₀/α·q^{k'}
  --     = (8Δ₀/α·q^{k'})·((1+β)²·q + β²) = M·q^{k'}
  have h4pos : 0 ≤ 4 * Δ₀ / α := div_nonneg (by linarith) (le_of_lt hα)
  have h_xk1_le : 2 * (1 + β) ^ 2 *
      (normSq fun i => fistaX G c α ρ (basisVec v) (k' + 1) i - xstar i) ≤
      2 * (1 + β) ^ 2 * (4 * Δ₀ / α * ((1 - √α) ^ k' * (1 - √α))) := by
    nlinarith [sq_nonneg (1 + β)]
  have h_xk0_le : 2 * (-β) ^ 2 *
      (normSq fun i => fistaX G c α ρ (basisVec v) k' i - xstar i) ≤
      2 * (-β) ^ 2 * (4 * Δ₀ / α * (1 - √α) ^ k') := by
    nlinarith [sq_nonneg β, neg_sq β]
  have hkey : 2 * (1 + β) ^ 2 * (4 * Δ₀ / α * ((1 - √α) ^ k' * (1 - √α))) +
      2 * β ^ 2 * (4 * Δ₀ / α * (1 - √α) ^ k') = M * (1 - √α) ^ k' := by
    unfold M; ring
  linarith [neg_sq β, h_tri, h_eq, h_xk1_le, h_xk0_le, hkey]

/-- Corollary A.3 (part 1, specialized): ‖y₀ − x*‖² ≤ 1.
    This is the PageRank specialization of corollary_A3_part1_general,
    using the tighter chain via minimizer_scaling_identity to get ‖x*‖² ≤ 1/d_v ≤ 1
    (versus the general bound 4Δ₀/α ≤ 2).

    Proof chain:
    1. From minimizer_scaling_identity: x*ᵀQx* = α⟨D⁻¹ᐟ²s,x*⟩ − g_c(x*)
    2. Since g_c ≥ 0: x*ᵀQx* ≤ α⟨D⁻¹ᐟ²s,x*⟩
    3. From Q_psd: α·‖x*‖² ≤ x*ᵀQx*
    4. Combining: ‖x*‖² ≤ ⟨D⁻¹ᐟ²s,x*⟩ = x*(v)/√d_v  (for s = e_v)
    5. Since x*(v)² ≤ ‖x*‖²: ‖x*‖² ≤ √(‖x*‖²)/√d_v
    6. So ‖x*‖ ≤ 1/√d_v, hence ‖x*‖² ≤ 1/d_v ≤ 1 ≤ 2.
    Depends on minimizer_scaling_identity. -/
theorem fista_y0_bound (G : Graph n) (c α ρ : ℝ) (v : Fin n)
    (hα : 0 < α) (hα1 : α ≤ 1) (hρ : 0 < ρ) (hc : 0 < c)
    (hd : 1 ≤ G.deg v)
    (xstar : Fin n → ℝ) (hmin : G.IsMinimizer c α ρ (basisVec v) xstar) :
    normSq (fun i => fistaY G c α ρ (basisVec v) 0 i - xstar i) ≤ 1 := by
  -- y₀ = 0 by definition of fistaState
  have hy0 : ∀ i, fistaY G c α ρ (basisVec v) 0 i = 0 := by
    intro i; unfold fistaY fistaState fistaMom; simp
  -- So ‖y₀ − x*‖² = ‖x*‖²
  have hsimp : normSq (fun i => fistaY G c α ρ (basisVec v) 0 i - xstar i) = normSq xstar := by
    simp only [normSq, hy0, zero_sub, neg_sq]
  rw [hsimp]
  -- Step 1: Euler identity gives x*ᵀQx* = α⟨D⁻¹ᐟ²s,x*⟩ − g_c(x*)
  have heuler := minimizer_scaling_identity G c α ρ (basisVec v) xstar hα hα1 hc hρ hmin
  -- Step 2: g_c(x*) ≥ 0
  have hgreg_nonneg : 0 ≤ G.gReg c α ρ xstar := by
    unfold Graph.gReg
    exact mul_nonneg (mul_nonneg (mul_nonneg (le_of_lt hc) (le_of_lt hα)) (le_of_lt hρ))
      (Finset.sum_nonneg fun i _ => mul_nonneg (le_of_lt (G.sqrtDeg_pos i)) (abs_nonneg _))
  -- Step 3: Q_psd gives α·‖x*‖² ≤ x*ᵀQx*
  have hQpsd := Q_psd G α hα hα1 xstar
  -- Step 4: Combine to get α·normSq xstar ≤ α·invSqrtDeg(v)·xstar(v)
  -- From euler + greg ≥ 0: x*ᵀQx* ≤ α·⟨D⁻¹ᐟ²s, x*⟩
  -- From Q_psd: α·normSq ≤ x*ᵀQx*
  -- So: normSq ≤ ⟨D⁻¹ᐟ²s, x*⟩ = invSqrtDeg(v)·xstar(v)
  set N := normSq xstar with hN_def
  -- ⟨D⁻¹ᐟ²·basisVec v, xstar⟩ simplifies since basisVec(v)(i) = δ_{iv}
  have hinner : ∑ i : Fin n, G.invSqrtDeg i * basisVec v i * xstar i =
      G.invSqrtDeg v * xstar v := by
    rw [Finset.sum_eq_single v]
    · simp [basisVec]
    · intro b _ hb; simp [basisVec, hb]
    · intro hv; exact absurd (Finset.mem_univ v) hv
  -- Chain: α·N ≤ x*ᵀQx* = α·(invSqrtDeg v · xstar v) - g_c ≤ α·(invSqrtDeg v · xstar v)
  have hN_le_inner : N ≤ G.invSqrtDeg v * xstar v := by
    have h1 : α * N ≤ α * (G.invSqrtDeg v * xstar v) := by
      calc α * N ≤ ∑ i, xstar i * (∑ j, G.Qentry α i j * xstar j) := hQpsd
        _ = α * ∑ i, G.invSqrtDeg i * basisVec v i * xstar i - G.gReg c α ρ xstar := heuler
        _ = α * (G.invSqrtDeg v * xstar v) - G.gReg c α ρ xstar := by rw [hinner]
        _ ≤ α * (G.invSqrtDeg v * xstar v) := by linarith
    exact le_of_mul_le_mul_left h1 hα
  -- Step 5: xstar(v)² ≤ N (single term in sum of squares)
  have hxv_sq_le : xstar v ^ 2 ≤ N := by
    unfold N normSq; exact Finset.single_le_sum (fun i _ => sq_nonneg (xstar i)) (Finset.mem_univ v)
  -- Step 6: N² ≤ invSqrtDeg(v)² · N
  -- From N ≤ invSqrtDeg(v)·xstar(v) and xstar(v)² ≤ N:
  -- N² ≤ (invSqrtDeg(v)·xstar(v))² = invSqrtDeg(v)²·xstar(v)² ≤ invSqrtDeg(v)²·N
  have hN_nonneg : 0 ≤ N := by
    unfold N normSq; exact Finset.sum_nonneg fun i _ => sq_nonneg (xstar i)
  have hinv_nn : 0 ≤ G.invSqrtDeg v := inv_nonneg.mpr (Real.sqrt_nonneg (G.deg v))
  have hxv_nn : 0 ≤ xstar v := by nlinarith [hN_le_inner]
  have hN_sq : N ^ 2 ≤ G.invSqrtDeg v ^ 2 * N := by
    calc N ^ 2 = N * N := sq N
      _ ≤ (G.invSqrtDeg v * xstar v) * N := by nlinarith [hN_le_inner]
      _ ≤ G.invSqrtDeg v ^ 2 * N := by
          -- From xstar v^2 ≤ N ≤ invSqrtDeg v * xstar v:
          -- invSqrtDeg v * xstar v ≤ invSqrtDeg v^2 follows from xstar v ≤ invSqrtDeg v
          nlinarith [sq_nonneg (G.invSqrtDeg v - xstar v), hxv_sq_le, hN_le_inner]
  -- Step 7: If N > 0 then N ≤ invSqrtDeg(v)², else trivially ≤ 2
  have hN_le : N ≤ G.invSqrtDeg v ^ 2 := by
    rcases eq_or_lt_of_le hN_nonneg with hN0 | hN_pos
    · rw [← hN0]; exact sq_nonneg _
    · exact le_of_mul_le_mul_right (by nlinarith [hN_sq]) hN_pos
  -- Step 8: invSqrtDeg(v)² = 1/deg(v) ≤ 1 ≤ 2
  have hinvsq : G.invSqrtDeg v ^ 2 = (G.deg v)⁻¹ := by
    unfold Graph.invSqrtDeg
    rw [inv_pow, Real.sq_sqrt (le_of_lt (G.deg_pos' v))]
  rw [hinvsq] at hN_le
  linarith [inv_le_one_of_one_le hd]

/-- Corollary: ‖y₀ − x*‖² ≤ 2 (weaker version for backward compatibility). -/
theorem fista_y0_bound_two (G : Graph n) (c α ρ : ℝ) (v : Fin n)
    (hα : 0 < α) (hα1 : α ≤ 1) (hρ : 0 < ρ) (hc : 0 < c)
    (hd : 1 ≤ G.deg v)
    (xstar : Fin n → ℝ) (hmin : G.IsMinimizer c α ρ (basisVec v) xstar) :
    normSq (fun i => fistaY G c α ρ (basisVec v) 0 i - xstar i) ≤ 2 := by
  linarith [fista_y0_bound G c α ρ v hα hα1 hρ hc hd xstar hmin]

/-- Corollary A.3 (uniform bound): ‖y_k − x*‖² ≤ 20 for all k ≥ 0.

    Proof:
    • k = 0: from fista_y0_bound (≤ 1 ≤ 20).
    • k ≥ 1: Use fista_convergence_rate + minimizer_strong_convexity to get
      ‖x_k − x*‖² ≤ 2·(1−√α)^k, then decompose y_k = x_k + β(x_k − x_{k−1})
      and apply the parallelogram inequality. -/
theorem fista_yk_uniform_bound (G : Graph n) (c α ρ : ℝ) (v : Fin n)
    (hα : 0 < α) (hα1 : α ≤ 1) (hρ : 0 < ρ) (hc : 0 < c)
    (hd : 1 ≤ G.deg v)
    (xstar : Fin n → ℝ) (hmin : G.IsMinimizer c α ρ (basisVec v) xstar) :
    ∀ k, normSq (fun i => fistaY G c α ρ (basisVec v) k i - xstar i) ≤ 20 := by
  -- Key fact: ‖x_k − x*‖² ≤ 2 for all k.
  -- For k=0: ‖x₀ − x*‖² = ‖x*‖² ≤ 1 ≤ 2 from fista_y0_bound.
  -- For k≥1: from convergence rate + strong convexity + Δ₀ ≤ α/2.
  --   The initial gap bound Δ₀ ≤ α/2 follows from the Euler identity chain
  --   in fista_y0_bound (works for any c).
  have hx0_bound : normSq (fun i => fistaX G c α ρ (basisVec v) 0 i - xstar i) ≤ 2 := by
    have hx0 := fistaX_zero G c α ρ (basisVec v)
    have hy0 := fistaY_zero G c α ρ (basisVec v)
    have : (fun i => fistaX G c α ρ (basisVec v) 0 i - xstar i) =
           (fun i => fistaY G c α ρ (basisVec v) 0 i - xstar i) := by
      ext i; simp [show fistaX G c α ρ (basisVec v) 0 i = 0 from congr_fun hx0 i, hy0 i]
    rw [this]; exact fista_y0_bound_two G c α ρ v hα hα1 hρ hc hd xstar hmin
  -- ‖x_k − x*‖² ≤ 2 for all k (using convergence rate + strong convexity)
  have hxk_le2 : ∀ k, normSq (fun i => fistaX G c α ρ (basisVec v) k i - xstar i) ≤ 2 := by
    intro k; rcases k with _ | k
    · exact hx0_bound
    · -- For k+1 ≥ 1: use convergence rate + strong convexity + initial gap
      -- Chain: α/2·‖x_{k+1}-x*‖² ≤ F(x_{k+1})-F(x*) ≤ 2Δ₀(1-√α)^{k+1} ≤ α(1-√α)^{k+1} ≤ α
      have hsc := minimizer_strong_convexity G c α ρ (basisVec v) xstar hα hα1 hc hρ hmin
        (fistaX G c α ρ (basisVec v) (k + 1))
      have hconv := fista_convergence_rate G c α ρ (basisVec v) hα hα1 hρ hc xstar hmin
        (k + 1) (by omega)
      have hx0eq : fistaX G c α ρ (basisVec v) 0 = 0 := fistaX_zero G c α ρ (basisVec v)
      rw [hx0eq] at hconv
      have hΔ := initial_gap_general G c α ρ v hα hα1 hc hρ hd xstar hmin
      -- F(0) = F_c(0) is the same as FObj c α ρ (basisVec v) 0
      have h1 : (1 - √α) ^ (k + 1) ≤ 1 :=
        pow_le_one₀ (by linarith [Real.sqrt_le_one.mpr hα1])
          (by linarith [Real.sqrt_pos_of_pos hα])
      have hchain := le_trans hsc hconv
      nlinarith [normSq_nonneg (fun i => fistaX G c α ρ (basisVec v) (k + 1) i - xstar i),
                 pow_nonneg (by linarith [Real.sqrt_le_one.mpr hα1] : 0 ≤ 1 - √α) (k + 1)]
  -- Now prove ‖y_k − x*‖² ≤ 20 for all k
  intro k; rcases k with _ | k
  · -- k = 0: ‖y₀ − x*‖² ≤ 2 ≤ 20
    linarith [fista_y0_bound G c α ρ v hα hα1 hρ hc hd xstar hmin]
  · -- k+1: decompose y_{k+1} = x_{k+1} + β(x_{k+1} − x_k)
    set β := fistaMom α
    have hβ_nn := fistaMom_nonneg α hα hα1
    have hβ_lt1 := fistaMom_lt_one α hα hα1
    -- y_{k+1} − x* = (1+β)(x_{k+1} − x*) + (−β)(x_k − x*)
    have hdecomp : ∀ i, fistaY G c α ρ (basisVec v) (k + 1) i - xstar i =
        (1 + β) * (fistaX G c α ρ (basisVec v) (k + 1) i - xstar i) +
        (-β) * (fistaX G c α ρ (basisVec v) k i - xstar i) := by
      intro i; rw [fistaY_succ]; ring
    have h_eq : normSq (fun i => fistaY G c α ρ (basisVec v) (k + 1) i - xstar i) =
        normSq (fun i => (1 + β) * (fistaX G c α ρ (basisVec v) (k + 1) i - xstar i) +
          (-β) * (fistaX G c α ρ (basisVec v) k i - xstar i)) := by
      congr 1; ext i; exact hdecomp i
    rw [h_eq]
    -- ‖(1+β)a + (−β)b‖² ≤ 2(1+β)²‖a‖² + 2β²‖b‖²
    have h_tri := normSq_add_le
      (fun i => (1 + β) * (fistaX G c α ρ (basisVec v) (k + 1) i - xstar i))
      (fun i => (-β) * (fistaX G c α ρ (basisVec v) k i - xstar i))
    rw [normSq_smul, normSq_smul] at h_tri
    -- (1+β)² ≤ 4 and β² ≤ 1
    have h1β : (1 + β) ^ 2 ≤ 4 := by nlinarith [hβ_nn]
    have hβ2 : (-β) ^ 2 ≤ 1 := by rw [neg_sq]; nlinarith [hβ_nn, hβ_lt1]
    -- ‖x_{k+1}−x*‖² ≤ 2, ‖x_k−x*‖² ≤ 2
    have hxk1 := hxk_le2 (k + 1)
    have hxk0 := hxk_le2 k
    -- 2·4·2 + 2·1·2 = 16 + 4 = 20
    have hN1 := normSq_nonneg (fun i => fistaX G c α ρ (basisVec v) (k + 1) i - xstar i)
    have hN0 := normSq_nonneg (fun i => fistaX G c α ρ (basisVec v) k i - xstar i)
    nlinarith

/-- Corollary A.3 (part 2, specialized with M ≤ 20): ‖y_k − x*‖² ≤ 20·(1−√α)^{k−1} for k ≥ 1.
    This is the PageRank specialization of corollary_A3_part2_general:
    since Δ₀ ≤ α/2, the constant M = 8Δ₀/α·((1+β)²(1−√α)+β²) ≤ 4·5 = 20. -/
theorem fista_yk_decay (G : Graph n) (c α ρ : ℝ) (v : Fin n)
    (hα : 0 < α) (hα1 : α ≤ 1) (hρ : 0 < ρ) (hc : 0 < c)
    (hd : 1 ≤ G.deg v)
    (xstar : Fin n → ℝ) (hmin : G.IsMinimizer c α ρ (basisVec v) xstar)
    (k : ℕ) (hk : 1 ≤ k) :
    normSq (fun i => fistaY G c α ρ (basisVec v) k i - xstar i)
      ≤ 20 * (1 - √α) ^ (k - 1) := by
  -- Step 1: ‖x_j − x*‖² ≤ 2·(1−√α)^j for all j
  have hrate : 0 ≤ 1 - √α := by linarith [Real.sqrt_le_one.mpr hα1]
  have hrate1 : 1 - √α ≤ 1 := by linarith [Real.sqrt_pos_of_pos hα]
  have hxj_bound : ∀ j, normSq (fun i => fistaX G c α ρ (basisVec v) j i - xstar i) ≤
      2 * (1 - √α) ^ j := by
    intro j; rcases j with _ | j
    · -- j=0: ‖x₀−x*‖² ≤ 1 ≤ 2 = 2·1 = 2·(1−√α)⁰
      have hx0 := fistaX_zero G c α ρ (basisVec v)
      have hy0 := fistaY_zero G c α ρ (basisVec v)
      simp [pow_zero]
      have : (fun i => fistaX G c α ρ (basisVec v) 0 i - xstar i) =
             (fun i => fistaY G c α ρ (basisVec v) 0 i - xstar i) := by
        ext i; simp [show fistaX G c α ρ (basisVec v) 0 i = 0 from congr_fun hx0 i, hy0 i]
      rw [this]; linarith [fista_y0_bound_two G c α ρ v hα hα1 hρ hc hd xstar hmin]
    · -- j≥1: from convergence rate + strong convexity + Δ₀ ≤ α/2
      have hsc := minimizer_strong_convexity G c α ρ (basisVec v) xstar hα hα1 hc hρ hmin
        (fistaX G c α ρ (basisVec v) (j + 1))
      have hconv := fista_convergence_rate G c α ρ (basisVec v) hα hα1 hρ hc xstar hmin
        (j + 1) (by omega)
      have hx0eq : fistaX G c α ρ (basisVec v) 0 = 0 := fistaX_zero G c α ρ (basisVec v)
      rw [hx0eq] at hconv
      have hΔ := initial_gap_general G c α ρ v hα hα1 hc hρ hd xstar hmin
      have h1 : (1 - √α) ^ (j + 1) ≤ 1 := pow_le_one₀ hrate hrate1
      have hchain := le_trans hsc hconv
      nlinarith [normSq_nonneg (fun i => fistaX G c α ρ (basisVec v) (j + 1) i - xstar i),
                 pow_nonneg hrate (j + 1)]
  -- Step 2: Decompose y_k for k ≥ 1
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  set β := fistaMom α
  have hβ_nn := fistaMom_nonneg α hα hα1
  have hβ_lt1 := fistaMom_lt_one α hα hα1
  -- y_{k+1} − x* = (1+β)(x_{k+1} − x*) + (−β)(x_k − x*)
  have h_eq : normSq (fun i => fistaY G c α ρ (basisVec v) (k + 1) i - xstar i) =
      normSq (fun i => (1 + β) * (fistaX G c α ρ (basisVec v) (k + 1) i - xstar i) +
        (-β) * (fistaX G c α ρ (basisVec v) k i - xstar i)) := by
    congr 1; ext i; rw [fistaY_succ]; ring
  rw [h_eq]
  -- ‖(1+β)a + (−β)b‖² ≤ 2(1+β)²‖a‖² + 2β²‖b‖²
  have h_tri := normSq_add_le
    (fun i => (1 + β) * (fistaX G c α ρ (basisVec v) (k + 1) i - xstar i))
    (fun i => (-β) * (fistaX G c α ρ (basisVec v) k i - xstar i))
  rw [normSq_smul, normSq_smul] at h_tri
  -- Use iterate bounds
  have hxk1 := hxj_bound (k + 1)
  have hxk0 := hxj_bound k
  -- Key: 2(1+β)²·2(1−√α)^{k+1} + 2β²·2(1−√α)^k
  --     = 4(1−√α)^k·[(1+β)²(1−√α) + β²]
  --     ≤ 4(1−√α)^k · 5 = 20·(1−√α)^k
  -- The coefficient bound: (1+β)²(1−√α) + β² ≤ 5
  -- With β = (1−√α)/(1+√α), set s = √α:
  -- (1+β)²(1−s) + β² = (1−s)(5−s)/(1+s)² ≤ 5
  -- since (1−s)(5−s) ≤ 5(1+s)² ⟺ 0 ≤ 4s(4+s) ✓
  have hcoeff : (1 + β) ^ 2 * (1 - √α) + (-β) ^ 2 ≤ 5 := by
    rw [neg_sq]
    unfold β fistaMom
    have hs := Real.sqrt_pos_of_pos hα
    have hs1 := Real.sqrt_le_one.mpr hα1
    have hd_pos : 0 < 1 + √α := by linarith
    rw [one_add_div (ne_of_gt hd_pos), div_pow, div_pow,
        div_mul_eq_mul_div, ← add_div]
    rw [div_le_iff₀ (sq_pos_of_pos hd_pos)]
    nlinarith [sq_nonneg (√α), sq_nonneg (1 + √α)]
  -- Combine all bounds
  have hN1 := normSq_nonneg (fun i => fistaX G c α ρ (basisVec v) (k + 1) i - xstar i)
  have hN0 := normSq_nonneg (fun i => fistaX G c α ρ (basisVec v) k i - xstar i)
  -- 2(1+β)²·2(1-√α)^{k+1} + 2β²·2(1-√α)^k = 4(1-√α)^k·coeff ≤ 20(1-√α)^k
  show _ ≤ 20 * (1 - √α) ^ (k + 1 - 1)
  simp only [Nat.add_sub_cancel]
  -- (1-√α)^{k+1} = (1-√α)^k · (1-√α)
  rw [pow_succ] at hxk1
  nlinarith [pow_nonneg hrate k, hcoeff]

/-! ## Result 4: Coordinate Jump Lemma (Lemma 4.1)

For the (B)-problem (c = 2), if coordinate i is inactive at x*_B (i.e., x*_{B,i} = 0)
but gets activated by the prox step at y (i.e., prox(u(y))_i ≠ 0), then:
  |u(y)_i − u(x*_B)_i| > γ_i · √d_i
where γ_i is the KKT slack and u(x) = x − ∇f(x) is the forward step. -/

/-
PROBLEM
Lemma 4.1 (Coordinate jump): If coordinate i is (B)-inactive and gets
    spuriously activated at y, then the forward step deviates by more than
    the KKT slack times √d_i.

PROVIDED SOLUTION
We need: kktSlack · sqrtDeg < |fwdStep(y)_i - fwdStep(xB)_i|.

Step 1: From hi_activated (proxMap ≠ 0), unfold proxMap to get softThresh(threshold, fwdStep(y)_i) ≠ 0. By abs_gt_of_softThresh_ne_zero, we get threshold < |fwdStep(y)_i|. The threshold is 1 * 2 * α * ρ * sqrtDeg i.

Step 2: Since xB_i = 0: fwdStep(xB)_i = 0 - 1 * gradf(xB)_i = -gradf(xB)_i. Since hgradf_nonpos, -gradf(xB)_i ≥ 0, so fwdStep(xB)_i ≥ 0 and |fwdStep(xB)_i| = -gradf(xB)_i.

Step 3: kktSlack · sqrtDeg = (2*ρ*α - |gradf(xB)_i| / sqrtDeg) * sqrtDeg = 2*ρ*α*sqrtDeg - |gradf(xB)_i|. Since gradf(xB)_i ≤ 0 (kkt_inactive_upper), |gradf(xB)_i| = -gradf(xB)_i, so = 2*ρ*α*sqrtDeg + gradf(xB)_i = threshold - |fwdStep(xB)_i|. (Using fwdStep and kktSlack definitions, and that threshold = 2αρ·sqrtDeg.)

Step 4: By the reverse triangle inequality |a - b| ≥ |a| - |b| (which is abs_sub_abs_le_abs_sub applied in reverse):
|fwdStep(y)_i - fwdStep(xB)_i| ≥ |fwdStep(y)_i| - |fwdStep(xB)_i| > threshold - (threshold - kktSlack·sqrtDeg) = kktSlack·sqrtDeg.

Key tactic: unfold Graph.proxMap Graph.fwdStep Graph.kktSlack at *, use abs_gt_of_softThresh_ne_zero, then establish the algebraic identities and use abs_sub_abs_le_abs_sub or similar.
-/
theorem coord_jump (G : Graph n) (α ρ : ℝ) (s : Fin n → ℝ)
    (_hα : 0 < α) (_hα1 : α ≤ 1) (_hρ : 0 < ρ)
    (xB : Fin n → ℝ) (_hmin : G.IsMinimizer 2 α ρ s xB)
    (y : Fin n → ℝ) (i : Fin n)
    -- i is (B)-inactive
    (hi_inactive : xB i = 0)
    -- i gets activated: prox_{g_B}(u(y))_i ≠ 0
    (hi_activated : G.proxMap 2 α ρ 1
        (fun j => G.fwdStep α 1 s y j) i ≠ 0) :
    G.kktSlack 2 α ρ s xB i * G.sqrtDeg i <
      |G.fwdStep α 1 s y i - G.fwdStep α 1 s xB i| := by
  have hgradf_nonpos : G.gradf α s xB i ≤ 0 :=
    kkt_inactive_upper G 2 α ρ s xB _hmin i hi_inactive
  contrapose! hi_activated
  have hsd_pos : 0 < G.sqrtDeg i := G.sqrtDeg_pos i
  have hsd_ne : G.sqrtDeg i ≠ 0 := ne_of_gt hsd_pos
  -- Simplify fwdStep(xB)_i using xB_i = 0
  have hfwd_xB : G.fwdStep α 1 s xB i = -(G.gradf α s xB i) := by
    show xB i - 1 * G.gradf α s xB i = -(G.gradf α s xB i)
    rw [hi_inactive]; ring
  -- Expand kktSlack * sqrtDeg using div_mul_cancel (paper's abs-value form → signed form)
  have hexp : G.kktSlack 2 α ρ s xB i * G.sqrtDeg i =
      2 * ρ * α * G.sqrtDeg i + G.gradf α s xB i := by
    have hk : G.kktSlack 2 α ρ s xB i = 2 * ρ * α + G.gradf α s xB i / G.sqrtDeg i := by
      unfold Graph.kktSlack; rw [abs_of_nonpos hgradf_nonpos]; ring
    rw [hk, add_mul, div_mul_cancel₀ _ hsd_ne]
  -- Rewrite the absolute value bound
  rw [hfwd_xB, hexp, show G.fwdStep α 1 s y i - -(G.gradf α s xB i) =
      G.fwdStep α 1 s y i + G.gradf α s xB i from by ring] at hi_activated
  obtain ⟨hlo, hhi⟩ := abs_le.mp hi_activated
  -- Upper: fwdStep(y)_i ≤ 2ρα·sqrtDeg (cancel gradf from both sides of hhi)
  have hupper : G.fwdStep α 1 s y i ≤ 2 * ρ * α * G.sqrtDeg i := by linarith
  -- Lower: fwdStep(y)_i ≥ -2ρα·sqrtDeg (using gradf ≤ 0)
  have hlower : -(2 * ρ * α * G.sqrtDeg i) ≤ G.fwdStep α 1 s y i := by nlinarith
  -- proxMap = softThresh(threshold, fwdStep(y)_i) = 0 since |fwdStep(y)_i| ≤ threshold
  unfold Graph.proxMap softThresh
  split_ifs with h1 h2
  · exfalso; nlinarith
  · exfalso; nlinarith
  · rfl

/-! ## Result 5: Monotonicity of the ℓ₁-Regularized PageRank Path (Lemma A.4)

The solution path x*(ρ) is coordinatewise monotone: if ρ' > ρ ≥ 0, then
x*(ρ') ≤ x*(ρ) coordinatewise. This is proved as Lemma 4 in Ha et al. (2021). -/

/- Lemma A.4 (Path monotonicity): Increasing regularization decreases
    the minimizer coordinatewise.

    PROOF STRATEGY (from Ha et al. 2021, Lemma 4):
    The key tool is the M-matrix structure of Q. Since Q_{ij} ≤ 0 for i ≠ j
    and Q ≻ 0, Q is a nonsingular M-matrix, so Q⁻¹ ≥ 0 entrywise.

    Step 1: The KKT conditions for problems (A) and (B) give:
      Q·x*_A - α·b + α·ρ·D^{1/2}·sign(x*_A) = 0  (at active coords)
      Q·x*_B - α·b + α·ρ'·D^{1/2}·sign(x*_B) = 0 (at active coords)

    Step 2: Subtracting: Q·(x*_A - x*_B) = α(ρ' - ρ)·D^{1/2}·(subgradient terms) ≥ 0
    (using ρ' > ρ and the subgradient structure).

    Step 3: Since Q⁻¹ ≥ 0 entrywise: x*_A - x*_B = Q⁻¹·(nonneg vector) ≥ 0.

    BLOCKER: Requires proving Q⁻¹ ≥ 0 for M-matrices (not available in Mathlib). -/

/- Active KKT from minimality: if x*_j > 0 and x* minimizes F, then
    gradf(x*)_j = -c·α·ρ·√d_j.
    Proof: perturb y_j = (1+ε)·x*_j for |ε| < 1. The difference
    F(y) - F(x*) = x*_j·(ε·p + ε²·q) where p = gradf_j + cαρ√d_j, q = x*_j·Q_{jj}/2.
    Since x*_j > 0 and F(y) ≥ F(x*): ε·p + ε²·q ≥ 0 for |ε| < 1.
    By linear_coeff_zero_interval: p = 0. -/
set_option maxHeartbeats 3200000 in
lemma kkt_active_from_minimality (G : Graph n) (c α ρ : ℝ) (s x : Fin n → ℝ)
    (hα : 0 < α) (_hα1 : α ≤ 1) (_hc : 0 < c) (_hρ : 0 ≤ ρ)
    (_hx_nonneg : ∀ i, 0 ≤ x i) (hmin : G.IsMinimizer c α ρ s x)
    (j : Fin n) (hj_pos : 0 < x j) :
    G.gradf α s x j = -(c * α * ρ * G.sqrtDeg j) := by
  set p := G.gradf α s x j + c * α * ρ * G.sqrtDeg j
  set q := (1 + α) / 2 * x j / 2
  suffices hp : p = 0 by unfold p at hp; linarith
  have hq_nn : 0 ≤ q := by unfold q; positivity
  apply linear_coeff_zero_interval _ hq_nn
  intro ε hε_lo hε_hi
  -- Test point: y_k = if k = j then (1+ε)·x_j else x_k
  set y : Fin n → ℝ := fun k => if k = j then x j + ε * x j else x k
  have hmin_y := hmin y
  -- y_k - x_k = if k = j then ε·x_j else 0
  have hdiff : ∀ k, y k - x k = if k = j then ε * x j else 0 := fun k => by
    simp only [y]; split_ifs with h
    · subst h; ring
    · ring
  -- fObj expansion: fObj(y) = fObj(x) + Σ gradf·δ + 1/2·Σ δ·(Qδ)
  have hfexp := fObj_expansion G α s x y
  have hgsum : ∑ k, G.gradf α s x k * (y k - x k) =
      G.gradf α s x j * (ε * x j) := by
    rw [show ∑ k, G.gradf α s x k * (y k - x k) =
        ∑ k, G.gradf α s x k * (if k = j then ε * x j else 0) from
      Finset.sum_congr rfl fun k _ => by rw [hdiff]]
    simp [Finset.mem_univ]
  have hqinner : ∀ k, ∑ l, G.Qentry α k l * (y l - x l) =
      G.Qentry α k j * (ε * x j) := fun k => by
    rw [show ∑ l, G.Qentry α k l * (y l - x l) =
        ∑ l, G.Qentry α k l * (if l = j then ε * x j else 0) from
      Finset.sum_congr rfl fun l _ => by rw [hdiff]]
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have hQjj : G.Qentry α j j = (1 + α) / 2 := by unfold Graph.Qentry; simp
  have hqsum : (1/2) * ∑ k, (y k - x k) * (∑ l, G.Qentry α k l * (y l - x l)) =
      (ε * x j) ^ 2 / 2 * ((1 + α) / 2) := by
    simp_rw [hqinner]
    rw [show ∑ k, (y k - x k) * (G.Qentry α k j * (ε * x j)) =
        ∑ k, (if k = j then ε * x j else 0) * (G.Qentry α k j * (ε * x j)) from
      Finset.sum_congr rfl fun k _ => by rw [hdiff]]
    simp [Finset.sum_ite, Finset.mem_univ]; ring
  have hfdiff : G.fObj α s y = G.fObj α s x +
      G.gradf α s x j * (ε * x j) + (ε * x j) ^ 2 / 2 * ((1 + α) / 2) := by
    linarith [hfexp, hgsum, hqsum]
  -- gReg expansion: |y_j| - |x_j| = |(1+ε)·x_j| - x_j = x_j·ε (since x_j > 0, |ε|<1)
  have hgdiff : G.gReg c α ρ y - G.gReg c α ρ x =
      c * α * ρ * G.sqrtDeg j * (ε * x j) := by
    unfold Graph.gReg
    suffices h : ∑ k, G.sqrtDeg k * |y k| - ∑ k, G.sqrtDeg k * |x k| =
        G.sqrtDeg j * (ε * x j) by linear_combination c * α * ρ * h
    rw [show ∑ k, G.sqrtDeg k * |y k| - ∑ k, G.sqrtDeg k * |x k| =
        ∑ k, (G.sqrtDeg k * |y k| - G.sqrtDeg k * |x k|) from
      (Finset.sum_sub_distrib _ _).symm]
    have hterm : ∀ k, G.sqrtDeg k * |y k| - G.sqrtDeg k * |x k| =
        if k = j then G.sqrtDeg j * (ε * x j) else 0 := fun k => by
      simp only [y]; split_ifs with h
      · rw [h]
        rw [show x j + ε * x j = (1 + ε) * x j from by ring]
        rw [abs_mul, abs_of_pos (by linarith : 0 < 1 + ε), abs_of_pos hj_pos]; ring
      · simp
    simp_rw [hterm]; simp [Finset.mem_univ]
  -- FObj(y) - FObj(x) = (ε·x_j)·p + (ε·x_j)²/2·Q_{jj} = x_j·(ε·p + ε²·q)
  have hFdiff : G.FObj c α ρ s y - G.FObj c α ρ s x =
      (ε * x j) * p + (ε * x j) ^ 2 / 2 * ((1 + α) / 2) := by
    unfold Graph.FObj; linarith [hfdiff, hgdiff]
  -- Factor: = x_j · (ε · p + ε² · q)  where q = x_j·(1+α)/2/2
  have hfactor : G.FObj c α ρ s y - G.FObj c α ρ s x =
      x j * (ε * p + ε ^ 2 * q) := by
    rw [hFdiff]; unfold q; ring
  -- Since x_j > 0 and F(y) ≥ F(x): ε·p + ε²·q ≥ 0
  have h_nn : 0 ≤ x j * (ε * p + ε ^ 2 * q) := by linarith [hmin_y, hfactor]
  by_contra h_neg; push_neg at h_neg
  linarith [mul_neg_of_pos_of_neg hj_pos h_neg]

/- Inactive KKT lower bound from minimality: if x*_j = 0 and x* ≥ 0 minimizes F,
    then gradf(x*)_j ≥ -c·α·ρ·√d_j.
    Proof: perturb y_j = ε for small ε > 0. The difference F(y) - F(x*) < 0
    contradicts minimality. -/
set_option maxHeartbeats 3200000 in
lemma kkt_inactive_lo_from_minimality (G : Graph n) (c α ρ : ℝ) (s x : Fin n → ℝ)
    (hα : 0 < α) (_hα1 : α ≤ 1) (_hc : 0 < c) (_hρ : 0 ≤ ρ)
    (_hx_nonneg : ∀ i, 0 ≤ x i) (hmin : G.IsMinimizer c α ρ s x)
    (j : Fin n) (hj_zero : x j = 0) :
    -(c * α * ρ * G.sqrtDeg j) ≤ G.gradf α s x j := by
  by_contra hlt; push_neg at hlt
  set g := G.gradf α s x j + c * α * ρ * G.sqrtDeg j with hg_def
  have hg_neg : g < 0 := by unfold g; linarith
  have hQjj_pos : 0 < (1 + α) / 2 := by linarith
  set ε := -g / ((1 + α) / 2) with hε_def
  have hε_pos : 0 < ε := by rw [hε_def]; exact div_pos (by linarith) hQjj_pos
  set y : Fin n → ℝ := fun k => if k = j then ε else x k
  have hmin_y := hmin y
  have hdiff : ∀ k, y k - x k = if k = j then ε else 0 := fun k => by
    simp only [y]; split_ifs with h
    · rw [h, hj_zero]; ring
    · ring
  have hfexp := fObj_expansion G α s x y
  have hgsum : ∑ k, G.gradf α s x k * (y k - x k) =
      G.gradf α s x j * ε := by
    rw [show ∑ k, G.gradf α s x k * (y k - x k) =
        ∑ k, G.gradf α s x k * (if k = j then ε else 0) from
      Finset.sum_congr rfl fun k _ => by rw [hdiff]]
    simp [Finset.mem_univ]
  have hQjj : G.Qentry α j j = (1 + α) / 2 := by unfold Graph.Qentry; simp
  have hqinner : ∀ k, ∑ l, G.Qentry α k l * (y l - x l) =
      G.Qentry α k j * ε := fun k => by
    rw [show ∑ l, G.Qentry α k l * (y l - x l) =
        ∑ l, G.Qentry α k l * (if l = j then ε else 0) from
      Finset.sum_congr rfl fun l _ => by rw [hdiff]]
    simp [Finset.mem_univ, mul_comm]
  have hqsum : (1/2) * ∑ k, (y k - x k) * (∑ l, G.Qentry α k l * (y l - x l)) =
      ε ^ 2 / 2 * ((1 + α) / 2) := by
    simp_rw [hqinner]
    rw [show ∑ k, (y k - x k) * (G.Qentry α k j * ε) =
        ∑ k, (if k = j then ε else 0) * (G.Qentry α k j * ε) from
      Finset.sum_congr rfl fun k _ => by rw [hdiff]]
    simp [Finset.sum_ite, Finset.mem_univ]; ring
  have hfdiff : G.fObj α s y = G.fObj α s x +
      G.gradf α s x j * ε + ε ^ 2 / 2 * ((1 + α) / 2) := by
    linarith [hfexp, hgsum, hqsum]
  have hgdiff : G.gReg c α ρ y - G.gReg c α ρ x = c * α * ρ * G.sqrtDeg j * ε := by
    unfold Graph.gReg
    suffices h : ∑ k, G.sqrtDeg k * |y k| - ∑ k, G.sqrtDeg k * |x k| =
        G.sqrtDeg j * ε by linear_combination c * α * ρ * h
    rw [show ∑ k, G.sqrtDeg k * |y k| - ∑ k, G.sqrtDeg k * |x k| =
        ∑ k, (G.sqrtDeg k * |y k| - G.sqrtDeg k * |x k|) from
      (Finset.sum_sub_distrib _ _).symm]
    have hterm : ∀ k, G.sqrtDeg k * |y k| - G.sqrtDeg k * |x k| =
        if k = j then G.sqrtDeg j * ε else 0 := fun k => by
      simp only [y]; split_ifs with h
      · rw [h, hj_zero]; simp [abs_of_pos hε_pos]
      · simp
    simp_rw [hterm]; simp [Finset.mem_univ]
  have hFdiff : G.FObj c α ρ s y - G.FObj c α ρ s x =
      g * ε + ε ^ 2 / 2 * ((1 + α) / 2) := by
    unfold Graph.FObj; linarith [hfdiff, hgdiff]
  have hval : g * ε + ε ^ 2 / 2 * ((1 + α) / 2) = -(g ^ 2 / (2 * ((1 + α) / 2))) := by
    rw [hε_def]; field_simp; ring
  have h1 : 0 ≤ G.FObj c α ρ s y - G.FObj c α ρ s x := by linarith [hmin_y]
  have h2 : 0 ≤ g * ε + ε ^ 2 / 2 * ((1 + α) / 2) := by linarith [hFdiff]
  have h4 : 0 < g ^ 2 := by nlinarith [hg_neg]
  have h5 : (0 : ℝ) < 2 * ((1 + α) / 2) := by linarith
  linarith [div_pos h4 h5]

theorem path_monotone (G : Graph n) (α ρ ρ' : ℝ) (s : Fin n → ℝ)
    (hα : 0 < α) (hα1 : α ≤ 1) (hρ : 0 ≤ ρ) (hρ' : ρ < ρ')
    (hs_nonneg : ∀ i, 0 ≤ s i)
    (xA xB : Fin n → ℝ)
    (hA : G.IsMinimizer 1 α ρ s xA)
    (hB : G.IsMinimizer 1 α ρ' s xB) :
    ∀ i, xB i ≤ xA i := by
  have hA_nonneg := minimizer_nonneg G 1 α ρ s xA hA
  have hB_nonneg := minimizer_nonneg G 1 α ρ' s xB hB
  -- Weighted maximum comparison principle (alternative to Neumann series).
  -- Reference: adapts the M-matrix diagonal dominance argument.
  -- Key idea: if z = xB - xA had a positive coordinate, the weighted maximum
  -- j* = argmax z_j/√d_j would give (Qz)_{j*} ≥ α·z_{j*} > 0, but
  -- KKT conditions force (Qz)_{j*} ≤ 0 at j*. Contradiction.
  by_contra h; push_neg at h
  -- h : ∃ i, xA i < xB i
  -- === KKT INFRASTRUCTURE (from helper lemmas) ===
  have hρ'_nn : 0 ≤ ρ' := le_of_lt (lt_of_le_of_lt hρ hρ')
  have kkt_activeA : ∀ j, 0 < xA j → G.gradf α s xA j = -(1 * α * ρ * G.sqrtDeg j) :=
    fun j hj => kkt_active_from_minimality G 1 α ρ s xA hα hα1 one_pos hρ hA_nonneg hA j hj
  have kkt_activeB : ∀ j, 0 < xB j → G.gradf α s xB j = -(1 * α * ρ' * G.sqrtDeg j) :=
    fun j hj => kkt_active_from_minimality G 1 α ρ' s xB hα hα1 one_pos
      (le_trans hρ (le_of_lt hρ')) hB_nonneg hB j hj
  have kkt_inactA_lo : ∀ j, xA j = 0 →
      -(1 * α * ρ * G.sqrtDeg j) ≤ G.gradf α s xA j :=
    fun j hj => kkt_inactive_lo_from_minimality G 1 α ρ s xA hα hα1 one_pos hρ hA_nonneg hA j hj
  -- Inactive upper bound: at j with x_j = 0 and x ≥ 0, gradf_j ≤ 0
  have kkt_inactA_hi : ∀ j, xA j = 0 → G.gradf α s xA j ≤ 0 := by
    intro j hj
    unfold Graph.gradf
    have : ∑ k, G.Qentry α j k * xA k ≤ 0 := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
      simp only [show G.Qentry α j j * xA j = 0 from by rw [hj, mul_zero], zero_add]
      apply Finset.sum_nonpos; intro k hk
      have hne : j ≠ k := (Finset.ne_of_mem_erase hk).symm
      apply mul_nonpos_of_nonpos_of_nonneg _ (hA_nonneg k)
      show G.Qentry α j k ≤ 0
      simp only [Graph.Qentry, if_neg hne]
      exact div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg (by linarith) (G.A_nonneg j k))
        (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    linarith [mul_nonneg (mul_nonneg (le_of_lt hα) (inv_nonneg.mpr (Real.sqrt_nonneg (G.deg j))))
              (hs_nonneg j)]
  have kkt_inactB_lo : ∀ j, xB j = 0 →
      -(1 * α * ρ' * G.sqrtDeg j) ≤ G.gradf α s xB j :=
    fun j hj => kkt_inactive_lo_from_minimality G 1 α ρ' s xB hα hα1 one_pos
      hρ'_nn hB_nonneg hB j hj
  -- === WEIGHTED MAXIMUM ARGUMENT ===
  -- Find j* = argmax (xB_j - xA_j) / √d_j
  obtain ⟨j₀, hj₀⟩ := h
  -- The set of "violated" coordinates is nonempty
  have hbad : (Finset.univ.filter (fun j : Fin n => xA j < xB j)).Nonempty :=
    ⟨j₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj₀⟩⟩
  -- Find the weighted maximum
  obtain ⟨jm, hjm_mem, hjm_max⟩ := Finset.exists_max_image
    (Finset.univ.filter (fun j : Fin n => xA j < xB j))
    (fun j => (xB j - xA j) / G.sqrtDeg j) hbad
  have hjm_pos : xA jm < xB jm := (Finset.mem_filter.mp hjm_mem).2
  set z := fun j => xB j - xA j with hz_def
  have hz_jm : 0 < z jm := by unfold z; linarith
  -- For ALL j (not just "bad" ones): z_j / √d_j ≤ z_{jm} / √d_{jm}
  have hwt_max : ∀ j, z j / G.sqrtDeg j ≤ z jm / G.sqrtDeg jm := by
    intro j
    by_cases hjv : xA j < xB j
    · exact hjm_max j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjv⟩)
    · push_neg at hjv
      calc z j / G.sqrtDeg j ≤ 0 := div_nonpos_of_nonpos_of_nonneg
              (by unfold z; linarith) (Real.sqrt_nonneg _)
        _ ≤ z jm / G.sqrtDeg jm := div_nonneg (le_of_lt hz_jm) (Real.sqrt_nonneg _)
  -- === KEY BOUND: (Qz)_{jm} ≥ α · z_{jm} > 0 ===
  have hQz_bound : α * z jm ≤ ∑ k, G.Qentry α jm k * z k := by
    -- Split: diagonal + off-diagonal
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ jm)]
    have hQii : G.Qentry α jm jm = (1 + α) / 2 := by unfold Graph.Qentry; simp
    -- Off-diagonal bound using weighted comparison
    have hoff : -(1 - α) / 2 * z jm ≤
        ∑ k ∈ Finset.univ.erase jm, G.Qentry α jm k * z k := by
      -- Each term: Q_{jm,k}·z_k ≥ -(1-α)/2 · A_{jm,k}/d_{jm} · z_{jm}
      have : ∀ k ∈ Finset.univ.erase jm, G.Qentry α jm k * z k ≥
          -(1 - α) / 2 * G.A jm k / G.deg jm * z jm := by
        intro k hk
        have hne : jm ≠ k := (Finset.ne_of_mem_erase hk).symm
        unfold Graph.Qentry; rw [if_neg hne]
        -- z_k / √d_k ≤ z_{jm} / √d_{jm}, so z_k ≤ z_{jm} · √d_k / √d_{jm}
        have hwt := hwt_max k
        have hsd_j := G.sqrtDeg_pos jm; have hsd_k := G.sqrtDeg_pos k
        -- Q_{jm,k} = -(1-α)/2 · A/(√d_{jm}·√d_k) ≤ 0
        -- z_k ≤ z_{jm} · √d_k/√d_{jm}
        -- Product ≥ -(1-α)/2 · A/(√d_{jm}·√d_k) · z_{jm} · √d_k/√d_{jm}
        --        = -(1-α)/2 · A/d_{jm} · z_{jm}
        rw [div_le_div_iff₀ hsd_k hsd_j] at hwt
        -- hwt: z k * sqrtDeg jm ≤ z jm * sqrtDeg k
        have hc_nonpos : -(1 - α) / 2 * G.A jm k ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg (by linarith) (G.A_nonneg jm k)
        have hdeg_eq : G.deg jm = G.sqrtDeg jm * G.sqrtDeg jm := by
          unfold Graph.sqrtDeg; rw [← sq, Real.sq_sqrt (le_of_lt (G.deg_pos' jm))]
        rw [ge_iff_le, hdeg_eq]
        rw [show -(1 - α) / 2 * G.A jm k / (G.sqrtDeg jm * G.sqrtDeg jm) * z jm =
            (-(1 - α) / 2 * G.A jm k / G.sqrtDeg jm) * (z jm / G.sqrtDeg jm) from by
              field_simp,
            show -(1 - α) / 2 * G.A jm k / (G.sqrtDeg jm * G.sqrtDeg k) * z k =
            (-(1 - α) / 2 * G.A jm k / G.sqrtDeg jm) * (z k / G.sqrtDeg k) from by
              field_simp]
        exact mul_le_mul_of_nonpos_left
          ((div_le_div_iff₀ hsd_k hsd_j).mpr hwt)
          (div_nonpos_of_nonpos_of_nonneg hc_nonpos (le_of_lt hsd_j))
      calc -(1 - α) / 2 * z jm
          = -(1 - α) / 2 * z jm * (G.deg jm / G.deg jm) := by
              rw [div_self (ne_of_gt (G.deg_pos' jm))]; ring
        _ = -(1 - α) / 2 / G.deg jm * z jm * G.deg jm := by ring
        _ = -(1 - α) / 2 / G.deg jm * z jm * ∑ k, G.A jm k := rfl
        _ = ∑ k, -(1 - α) / 2 * G.A jm k / G.deg jm * z jm := by
              rw [Finset.mul_sum]; congr 1; ext k; ring
        _ = (-(1 - α) / 2 * G.A jm jm / G.deg jm * z jm) +
            ∑ k ∈ Finset.univ.erase jm, -(1 - α) / 2 * G.A jm k / G.deg jm * z jm := by
              rw [← Finset.add_sum_erase _ _ (Finset.mem_univ jm)]
        _ = ∑ k ∈ Finset.univ.erase jm, -(1 - α) / 2 * G.A jm k / G.deg jm * z jm := by
              rw [G.A_no_loops jm]; ring_nf
        _ ≤ _ := Finset.sum_le_sum (this)
    calc α * z jm = (1 + α) / 2 * z jm + (-(1 - α) / 2 * z jm) := by ring
      _ ≤ G.Qentry α jm jm * z jm +
          ∑ k ∈ Finset.univ.erase jm, G.Qentry α jm k * z k := by
          rw [hQii]; linarith
  -- So (Qz)_{jm} ≥ α · z_{jm} > 0
  have hQz_pos : 0 < ∑ k, G.Qentry α jm k * z k := by linarith [mul_pos hα hz_jm]
  -- === CASE ANALYSIS ON jm ===
  -- Compute (Qz)_{jm} from KKT
  have hQz_eq : ∑ k, G.Qentry α jm k * z k =
      G.gradf α s xB jm - G.gradf α s xA jm := by
    simp only [Graph.gradf, hz_def, mul_sub, Finset.sum_sub_distrib]; ring
  rw [hQz_eq] at hQz_pos
  -- Case 1: xA_{jm} > 0 and xB_{jm} > 0
  -- Case 2: xA_{jm} = 0 and xB_{jm} > 0
  -- Case 3: xB_{jm} = 0 (impossible since z_{jm} > 0 and xA ≥ 0)
  have hxB_pos : 0 < xB jm := by linarith [hA_nonneg jm]
  rcases eq_or_lt_of_le (hA_nonneg jm) with hxA0 | hxA_pos
  · -- Case 2: xA_{jm} = 0
    have hgA := kkt_inactA_lo jm hxA0.symm
    have hgB := kkt_activeB jm hxB_pos
    -- gradf(xB)_{jm} - gradf(xA)_{jm} = -ρ'α√d - gradf(xA) ≤ -ρ'α√d + ρα√d = (ρ-ρ')α√d < 0
    nlinarith [G.sqrtDeg_pos jm, mul_pos hα (G.sqrtDeg_pos jm)]
  · -- Case 1: xA_{jm} > 0
    have hgA := kkt_activeA jm hxA_pos
    have hgB := kkt_activeB jm hxB_pos
    -- gradf(xB) - gradf(xA) = -ρ'α√d + ρα√d = (ρ-ρ')α√d < 0
    nlinarith [G.sqrtDeg_pos jm, mul_pos hα (G.sqrtDeg_pos jm)]

/-! ## Result 6: Monotonicity of Proximal Gradient Steps (Lemma A.5)

If z ≥ z' ≥ 0 coordinatewise, then the proximal-gradient map preserves the ordering:
  prox_{g_c}(z − ∇f(z)) ≥ prox_{g_c}(z' − ∇f(z'))  coordinatewise.

The proof uses that I − Q/L is entrywise nonneg (since Q is an M-matrix with Q ≼ LI)
and that the prox is a separable monotone map. -/

/-
PROBLEM
Lemma A.5 (Proximal gradient monotonicity): The proximal-gradient map
    for PageRank is coordinatewise monotone on the nonneg orthant.

PROVIDED SOLUTION
The proof has two steps:
1. Show that the forward step u(z) = z - ∇f(z) is coordinatewise monotone when z ≥ z' ≥ 0. Since u(z) = (I - Q)z + b where Q is the PageRank Q matrix with η = 1, we need I - Q to be entrywise nonneg. Since Q ≼ I (smoothness), this holds. More precisely, (I-Q)_{ii} = 1 - (1+α)/2 = (1-α)/2 ≥ 0 and (I-Q)_{ij} = (1-α)/2 · A_{ij}/(sqrtDeg(i)·sqrtDeg(j)) ≥ 0 for i ≠ j (since A is nonneg). So I-Q is entrywise nonneg, hence u is monotone: z ≥ z' ⟹ u(z) ≥ u(z').

2. Show that softThresh is monotone: if w ≥ w', then softThresh(t, w) ≥ softThresh(t, w'). This follows from case analysis on the definition of softThresh.

Combining: z ≥ z' ⟹ u(z) ≥ u(z') ⟹ proxMap(u(z)) ≥ proxMap(u(z')).
-/
theorem prox_grad_monotone (G : Graph n) (c α ρ : ℝ) (s z z' : Fin n → ℝ)
    (_hα : 0 < α) (hα1 : α ≤ 1) (_hρ : 0 < ρ) (_hc : 0 < c)
    (hz_ge : ∀ i, z' i ≤ z i)
    (_hz'_nonneg : ∀ i, 0 ≤ z' i) :
    ∀ i, G.proxMap c α ρ 1 (fun j => G.fwdStep α 1 s z' j) i ≤
         G.proxMap c α ρ 1 (fun j => G.fwdStep α 1 s z j) i := by
           intro i
           unfold Graph.proxMap Graph.fwdStep
           simp [softThresh] at *;
           -- Since $Q$ is an M-matrix with $Q \preceq LI$, we have $I - Q$ is entrywise nonneg.
           have h_I_minus_Q_nonneg : ∀ i j, 0 ≤ (if i = j then 1 else 0) - G.Qentry α i j := by
             intro i j; unfold Graph.Qentry; split_ifs <;> norm_num;
             · linarith;
             · exact div_nonpos_of_nonpos_of_nonneg ( mul_nonpos_of_nonpos_of_nonneg ( by linarith ) ( G.A_nonneg i j ) ) ( mul_nonneg ( Real.sqrt_nonneg _ ) ( Real.sqrt_nonneg _ ) );
           -- Since $I - Q$ is entrywise nonneg, we have $u(z) \geq u(z')$ coordinatewise.
           have h_u_ge : ∀ i, z i - G.gradf α s z i ≥ z' i - G.gradf α s z' i := by
             intro i
             have h_u_ge_i : ∑ j, (if i = j then 1 else 0) * (z j - z' j) - ∑ j, G.Qentry α i j * (z j - z' j) ≥ 0 := by
               simpa only [ ← Finset.sum_sub_distrib ] using Finset.sum_nonneg fun j _ => by nlinarith [ h_I_minus_Q_nonneg i j, hz_ge j ] ;
             simp_all +decide [ mul_sub, Finset.sum_sub_distrib, Graph.gradf ];
             linarith [ hz_ge i ];
           split_ifs <;> linarith [ h_u_ge i ]

/-! ## Result 7: Two-Tier Split (Lemma 4.2)

Partition the (B)-inactive set I_B into:
  I_B^small = {i ∈ I_B : γ_i^(B) < ρα}  (small margin)
  I_B^large = {i ∈ I_B : γ_i^(B) ≥ ρα}  (large margin)
Then I_B^small ⊆ S_A (the support of the less-regularized solution).

This means coordinates outside S_A all have margin ≥ ρα, enabling uniform bounds. -/

/-
PROBLEM
Lemma 4.2 (Two-tier split): Any (B)-inactive coordinate with small margin
    must lie in the (A)-support.
    Note: the (B)-problem has regularization 2ρ, so its KKT slack with c = 2
    matches the paper's γ_i^{(B)} = 2ρα - |∇_if(x_B*)|/√d_i.

PROVIDED SOLUTION
The proof follows the paper's proof of Lemma 4.2:

1. From hi_small: G.kktSlack 2 α ρ s xB i < ρ * α. Since gradf ≤ 0, kktSlack = 2*ρ*α + gradf(xB)_i/sqrtDeg(i) < ρ*α. So gradf(xB)_i < -ρ*α*sqrtDeg(i).

2. Since hi_inactiveB: xB_i = 0, so fwdStep(xB)_i = 0 - 1*gradf(xB)_i = -gradf(xB)_i > ρ*α*sqrtDeg(i).

3. proxMap 1 α ρ 1 (fwdStep(xB)) at i = softThresh(1*α*ρ*sqrtDeg(i), fwdStep(xB)_i). Since fwdStep(xB)_i > α*ρ*sqrtDeg(i) = threshold, softThresh returns fwdStep(xB)_i - threshold > 0.

4. By path_monotone, since 2*ρ > ρ: xA ≥ xB coordinatewise.

5. By prox_grad_monotone (proven), since xA ≥ xB ≥ 0:
   proxMap(fwdStep(xA))_i ≥ proxMap(fwdStep(xB))_i > 0.

6. By hA_fp: xA_i = proxMap(fwdStep(xA))_i ≥ proxMap(fwdStep(xB))_i > 0.

Key steps: unfold kktSlack and fwdStep to get the inequality on gradf, then show proxMap is positive, then use monotonicity and the fixed-point property.
-/
theorem two_tier_split (G : Graph n) (α ρ : ℝ) (s : Fin n → ℝ)
    (hα : 0 < α) (hα1 : α ≤ 1) (hρ : 0 < ρ)
    (hs_nonneg : ∀ i, 0 ≤ s i)
    -- Problem (A): regularization ρ
    (xA : Fin n → ℝ) (hA : G.IsMinimizer 1 α ρ s xA)
    -- Problem (B): regularization 2ρ
    (xB : Fin n → ℝ) (hB : G.IsMinimizer 1 α (2*ρ) s xB)
    -- Coordinate i is (B)-inactive with small margin
    (i : Fin n) (hi_inactiveB : xB i = 0)
    (hi_small : G.kktSlack 2 α ρ s xB i < ρ * α) :
    -- Then i is in the (A)-support
    0 < xA i := by
      have hA_fp : ∀ j, xA j = G.proxMap 1 α ρ 1 (fun k => G.fwdStep α 1 s xA k) j :=
        minimizer_is_prox_fixed_point G 1 α ρ s xA hα hα1 one_pos hρ hA
      have hA_nonneg := minimizer_nonneg G 1 α ρ s xA hA
      have hB_nonneg := minimizer_nonneg G 1 α (2*ρ) s xB hB
      have hgradf_nonpos : G.gradf α s xB i ≤ 0 :=
        kkt_inactive_upper G 1 α (2*ρ) s xB hB i hi_inactiveB
      -- Since fwdStep(xB)_i > ρ*α*sqrtDeg(i), we have softThresh(1*α*ρ*sqrtDeg(i), fwdStep(xB)_i) > 0.
      have h_softThresh_pos : softThresh (1 * α * ρ * G.sqrtDeg i) (G.fwdStep α 1 s xB i) > 0 := by
        have h_fwdStep_pos : G.fwdStep α 1 s xB i > α * ρ * G.sqrtDeg i := by
          have hk : G.kktSlack 2 α ρ s xB i = 2 * ρ * α + G.gradf α s xB i / G.sqrtDeg i := by
            unfold Graph.kktSlack; rw [abs_of_nonpos hgradf_nonpos]; ring
          rw [hk] at hi_small;
          unfold Graph.fwdStep Graph.gradf at *;
          rw [ add_div', div_lt_iff₀ ] at hi_small <;> nlinarith [ G.sqrtDeg_pos i ];
        unfold softThresh; aesop;
      -- By path_monotone, since 2*ρ > ρ: xA ≥ xB coordinatewise.
      have h_path_monotone : ∀ i, xA i ≥ xB i := by
        apply path_monotone G α ρ (2 * ρ) s hα hα1 (by linarith) (by linarith) hs_nonneg xA xB hA hB;
      -- By prox_grad_monotone, since xA ≥ xB ≥ 0:
      have h_prox_grad_monotone : ∀ i, G.proxMap 1 α ρ 1 (fun j => G.fwdStep α 1 s xA j) i ≥ G.proxMap 1 α ρ 1 (fun j => G.fwdStep α 1 s xB j) i := by
        apply prox_grad_monotone G 1 α ρ s xA xB hα hα1 hρ (by norm_num) h_path_monotone hB_nonneg;
      linarith [ hA_fp i, h_path_monotone i, h_prox_grad_monotone i, show G.proxMap 1 α ρ 1 ( fun j => G.fwdStep α 1 s xB j ) i > 0 from by simpa [ hi_inactiveB, Graph.proxMap ] using h_softThresh_pos ]


/-! ## Cauchy-Schwarz helpers (moved before Result 8 for dependency ordering)

These are used by both the boundary confinement proof (Result 9) and the
new gradf_lipschitz / work_bound proofs (Result 8). -/

/- Cauchy-Schwarz inequality for finite sums:
    (Σ aᵢbᵢ)² ≤ (Σ aᵢ²)(Σ bᵢ²).
    Proved via the discriminant method: p(t) = Σ(aᵢ - t·bᵢ)² ≥ 0 for all t,
    evaluating at t = (Σab)/(Σb²) and clearing denominators. -/
set_option maxHeartbeats 1600000 in
lemma cauchy_schwarz_sum {ι : Type*} (s : Finset ι) (a b : ι → ℝ) :
    (∑ i ∈ s, a i * b i) ^ 2 ≤
    (∑ i ∈ s, a i ^ 2) * (∑ i ∈ s, b i ^ 2) := by
  -- The quadratic Σ(aᵢ - t·bᵢ)² ≥ 0 for all t
  have hquad : ∀ t : ℝ, 0 ≤ ∑ i ∈ s, (a i - t * b i) ^ 2 :=
    fun t => Finset.sum_nonneg fun i _ => sq_nonneg _
  set A := ∑ i ∈ s, b i ^ 2
  set B := ∑ i ∈ s, a i * b i
  set C := ∑ i ∈ s, a i ^ 2
  have hA_nn : 0 ≤ A := Finset.sum_nonneg fun i _ => sq_nonneg _
  -- Expand the quadratic: p(t) = C - 2Bt + At²
  have hexpand : ∀ t, ∑ i ∈ s, (a i - t * b i) ^ 2 = C - 2 * t * B + t ^ 2 * A := by
    intro t
    -- Rewrite each term as a sum of three parts
    have hsq : ∀ i ∈ s, (a i - t * b i) ^ 2 =
        a i ^ 2 + (-(2 * t) * (a i * b i) + t ^ 2 * b i ^ 2) := by
      intros; ring
    rw [Finset.sum_congr rfl hsq]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    ring
  -- Show B² ≤ C·A by evaluating p at t = B/A
  suffices 0 ≤ C * A - B ^ 2 by linarith
  rcases eq_or_lt_of_le hA_nn with hA0 | hA_pos
  · -- A = 0: all bᵢ = 0, so B = 0
    have hb0 : ∀ i ∈ s, b i = 0 := by
      intro i hi
      have h1 : b i ^ 2 ≤ A := Finset.single_le_sum (fun j _ => sq_nonneg (b j)) hi
      have h2 : A = 0 := hA0.symm
      have h3 : b i ^ 2 = 0 := le_antisymm (by linarith) (sq_nonneg _)
      exact pow_eq_zero_iff (by norm_num : 2 ≠ 0) |>.mp h3
    have hB0 : B = 0 := Finset.sum_eq_zero fun i hi => by rw [hb0 i hi, mul_zero]
    rw [hB0, hA0.symm]
    simp
  · -- A > 0: evaluate at t = B/A and clear denominators
    have h := hquad (B / A)
    rw [hexpand] at h
    have h2 : 0 ≤ (C - 2 * (B / A) * B + (B / A) ^ 2 * A) * A :=
      mul_nonneg h (le_of_lt hA_pos)
    have h3 : (C - 2 * (B / A) * B + (B / A) ^ 2 * A) * A = C * A - B ^ 2 := by
      field_simp; ring
    linarith

/-- Consequence of Cauchy-Schwarz: for nonneg f,
    Σ f(i) ≤ √|s| · √(Σ f(i)²). -/
lemma sum_le_sqrt_card_mul_sqrt_sum_sq {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) :
    ∑ i ∈ s, f i ≤ Real.sqrt (↑s.card) * Real.sqrt (∑ i ∈ s, f i ^ 2) := by
  have h_rhs_nn : 0 ≤ Real.sqrt (↑s.card) * Real.sqrt (∑ i ∈ s, f i ^ 2) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have h_lhs_nn : 0 ≤ ∑ i ∈ s, f i := Finset.sum_nonneg hf
  rw [← Real.sqrt_sq h_lhs_nn, ← Real.sqrt_mul (Nat.cast_nonneg _)]
  exact Real.sqrt_le_sqrt (by
    calc (∑ i ∈ s, f i) ^ 2
        = (∑ i ∈ s, (1 : ℝ) * f i) ^ 2 := by simp
      _ ≤ (∑ i ∈ s, (1 : ℝ) ^ 2) * (∑ i ∈ s, f i ^ 2) :=
          cauchy_schwarz_sum s (fun _ => 1) f
      _ = ↑s.card * ∑ i ∈ s, f i ^ 2 := by
          congr 1; simp [Finset.sum_const])

/-! ## Result 8: Work Bound (Theorem 4.3) — CORRECTED

The original proof chose C = W/R + 1 *after* computing the actual work W,
making W ≤ C·R tautological. The corrected version follows the paper's
proof with universal constant 30 (tightened from the original 200). This section also proves the two results
that were previously axioms:

- `gradf_lipschitz_normSq`: ‖∇f(y)−∇f(x)‖² ≤ ‖y−x‖² (1-Lipschitz of ∇f)
  Proved elementarily from ‖Mz‖² ≤ ‖z‖² (per-row Cauchy-Schwarz).

- `totalWork_decomp`: totalWork ≤ 3N·vol(S_A) + 3·Σ vol(Ã_k)
  Proved by per-step decomposition with shifted-sum reindexing. -/

-- ═════════════════════════════════════════════════════════════
-- 8a. Proof of ‖∇f(y) − ∇f(x)‖² ≤ ‖y − x‖² (was axiom)
--
-- From Fountoulakis et al. (2017) Section 2: "∇f is 1-Lipschitz
-- continuous w.r.t. ℓ₂ norm." Proved via Q = (1+α)/2·I − (1-α)/2·M
-- where M = D⁻¹/²AD⁻¹/² is a contraction (‖Mz‖ ≤ ‖z‖).
-- ═════════════════════════════════════════════════════════════

/- The normalized adjacency matrix M = D⁻¹/²AD⁻¹/² is a contraction:
    ‖Mz‖² ≤ ‖z‖² for all z.
    Per-row Cauchy-Schwarz + sum swap using Σ_i A_{ij} = d_j. -/
set_option maxHeartbeats 3200000 in
lemma normSq_normAdj_le (G : Graph n) (z : Fin n → ℝ) :
    normSq (fun i => ∑ j, G.A i j * z j / (G.sqrtDeg i * G.sqrtDeg j)) ≤ normSq z := by
  unfold normSq
  have h_row : ∀ i, (∑ j, G.A i j * z j / (G.sqrtDeg i * G.sqrtDeg j)) ^ 2 ≤
      ∑ j, G.A i j * z j ^ 2 / G.deg j := by
    intro i
    have hsd_i := G.sqrtDeg_pos i
    have hrewrite : ∑ j, G.A i j * z j / (G.sqrtDeg i * G.sqrtDeg j) =
        (1 / G.sqrtDeg i) * ∑ j, G.A i j * z j / G.sqrtDeg j := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _
      field_simp
    rw [hrewrite, mul_pow, one_div, inv_pow,
        show G.sqrtDeg i ^ 2 = G.deg i from Real.sq_sqrt (le_of_lt (G.deg_pos' i))]
    have hcs := cauchy_schwarz_sum Finset.univ
      (fun j => Real.sqrt (G.A i j))
      (fun j => Real.sqrt (G.A i j) * z j / G.sqrtDeg j)
    have hlhs : ∑ j, Real.sqrt (G.A i j) * (Real.sqrt (G.A i j) * z j / G.sqrtDeg j) =
        ∑ j, G.A i j * z j / G.sqrtDeg j := by
      apply Finset.sum_congr rfl; intro j _
      rw [← mul_div_assoc, ← mul_assoc, Real.mul_self_sqrt (G.A_nonneg i j)]
    rw [hlhs] at hcs
    have hf1 : ∑ j, Real.sqrt (G.A i j) ^ 2 = G.deg i := by
      have : ∑ j, Real.sqrt (G.A i j) ^ 2 = ∑ j, G.A i j :=
        Finset.sum_congr rfl fun j _ => Real.sq_sqrt (G.A_nonneg i j)
      rw [this]
    have hf2 : ∑ j, (Real.sqrt (G.A i j) * z j / G.sqrtDeg j) ^ 2 =
        ∑ j, G.A i j * z j ^ 2 / G.deg j := by
      apply Finset.sum_congr rfl; intro j _
      rw [div_pow, mul_pow, Real.sq_sqrt (G.A_nonneg i j)]
      unfold Graph.sqrtDeg; rw [Real.sq_sqrt (le_of_lt (G.deg_pos' j))]
    rw [hf1, hf2] at hcs
    rw [inv_mul_le_iff₀ (G.deg_pos' i)]; exact hcs
  have h_sum : ∑ i, (∑ j, G.A i j * z j / (G.sqrtDeg i * G.sqrtDeg j)) ^ 2 ≤
      ∑ i, ∑ j, G.A i j * z j ^ 2 / G.deg j :=
    Finset.sum_le_sum fun i _ => h_row i
  have h_swap : ∑ i, ∑ j, G.A i j * z j ^ 2 / G.deg j = ∑ j, z j ^ 2 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro j _
    rw [← Finset.sum_div]
    have hdeg : ∑ i, G.A i j * z j ^ 2 = z j ^ 2 * G.deg j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro i _
      have : G.A i j = G.A j i := G.A_symm i j
      rw [this]; ring
    rw [hdeg, mul_div_cancel_right₀ _ (ne_of_gt (G.deg_pos' j))]
  linarith [h_sum, h_swap]

/-- Cauchy-Schwarz for inner products: (Σ aᵢbᵢ)² ≤ ‖a‖²·‖b‖². -/
lemma inner_sq_le_normSq_mul (a b : Fin n → ℝ) :
    (∑ i, a i * b i) ^ 2 ≤ normSq a * normSq b :=
  cauchy_schwarz_sum Finset.univ a b

/-- ⟨z, Mz⟩ ≥ −‖z‖². From |⟨z,Mz⟩| ≤ ‖z‖·‖Mz‖ ≤ ‖z‖². -/
lemma inner_normAdj_ge_neg (G : Graph n) (z : Fin n → ℝ) :
    -(normSq z) ≤ ∑ i, z i * (∑ j, G.A i j * z j / (G.sqrtDeg i * G.sqrtDeg j)) := by
  set Mz : Fin n → ℝ := fun i => ∑ j, G.A i j * z j / (G.sqrtDeg i * G.sqrtDeg j)
  have hcs := inner_sq_le_normSq_mul z Mz
  have hMz_le := normSq_normAdj_le G z
  have h_inner_sq : (∑ i, z i * Mz i) ^ 2 ≤ normSq z ^ 2 := by
    calc (∑ i, z i * Mz i) ^ 2 ≤ normSq z * normSq Mz := hcs
      _ ≤ normSq z * normSq z := by nlinarith [normSq_nonneg z, normSq_nonneg Mz]
      _ = normSq z ^ 2 := (sq _).symm
  have h_abs : |∑ i, z i * Mz i| ≤ normSq z := by
    rw [← Real.sqrt_sq (normSq_nonneg z), ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt h_inner_sq
  linarith [neg_abs_le (∑ i, z i * Mz i)]

/- ‖Qz‖² ≤ ‖z‖² (Q has operator norm ≤ 1).
    Uses Qz = cz − dMz with c+d=1, and ‖z‖²−‖Qz‖² = 2cd(‖z‖²+⟨z,Mz⟩) + d²(‖z‖²−‖Mz‖²) ≥ 0. -/
set_option maxHeartbeats 4000000 in
lemma Q_operator_norm_sq (G : Graph n) (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (z : Fin n → ℝ) :
    normSq (fun i => ∑ j, G.Qentry α i j * z j) ≤ normSq z := by
  set Mz : Fin n → ℝ := fun i => ∑ j, G.A i j * z j / (G.sqrtDeg i * G.sqrtDeg j)
  set c := (1 + α) / 2; set d := (1 - α) / 2
  have hc_nn : 0 ≤ c := by positivity
  have hd_nn : 0 ≤ d := by unfold d; linarith
  have hcd1 : c + d = 1 := by unfold c d; ring
  have hQz_eq : ∀ i, ∑ j, G.Qentry α i j * z j = c * z i - d * Mz i := by
    intro i
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    have hQii : G.Qentry α i i = c := by unfold Graph.Qentry; simp; unfold c; ring
    rw [hQii]
    have hoff : ∑ j ∈ Finset.univ.erase i, G.Qentry α i j * z j =
        -d * ∑ j ∈ Finset.univ.erase i, G.A i j * z j / (G.sqrtDeg i * G.sqrtDeg j) := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j hj
      unfold Graph.Qentry; rw [if_neg (Ne.symm (Finset.ne_of_mem_erase hj))]; unfold d; ring
    rw [hoff]
    have hMz_split : Mz i = ∑ j ∈ Finset.univ.erase i, G.A i j * z j / (G.sqrtDeg i * G.sqrtDeg j) := by
      unfold Mz; rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), G.A_no_loops i]; ring
    rw [hMz_split]; ring
  have hns_eq : normSq (fun i => ∑ j, G.Qentry α i j * z j) =
      normSq (fun i => c * z i - d * Mz i) := by
    unfold normSq; congr 1; ext i; simp only [hQz_eq]
  rw [hns_eq]
  have h_expand : normSq (fun i => c * z i - d * Mz i) =
      c ^ 2 * normSq z - 2 * c * d * (∑ i, z i * Mz i) + d ^ 2 * normSq Mz := by
    unfold normSq
    have hsq : ∀ i, (c * z i - d * Mz i) ^ 2 =
        c ^ 2 * z i ^ 2 - 2 * c * d * (z i * Mz i) + d ^ 2 * Mz i ^ 2 := by
      intro i; ring
    simp_rw [hsq, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [h_expand]
  have h1mc2 : 1 - c ^ 2 = 2 * c * d + d ^ 2 := by
    have : (c + d) ^ 2 = c ^ 2 + 2 * c * d + d ^ 2 := by ring
    nlinarith [hcd1]
  have h_term1 : 0 ≤ 2 * c * d * (normSq z + ∑ i, z i * Mz i) :=
    mul_nonneg (by positivity) (by linarith [inner_normAdj_ge_neg G z])
  have h_term2 : 0 ≤ d ^ 2 * (normSq z - normSq Mz) :=
    mul_nonneg (sq_nonneg _) (by linarith [normSq_normAdj_le G z])
  nlinarith [h1mc2, h_term1, h_term2, normSq_nonneg z, normSq_nonneg Mz]

/-- 1-Lipschitz continuity of ∇f: ‖∇f(y)−∇f(x)‖² ≤ ‖y−x‖².
    From ∇f(y)−∇f(x) = Q(y−x) and Q_operator_norm_sq. -/
theorem gradf_lipschitz_normSq (G : Graph n) (α : ℝ) (s : Fin n → ℝ)
    (hα : 0 < α) (hα1 : α ≤ 1) (x y : Fin n → ℝ) :
    normSq (fun i => G.gradf α s y i - G.gradf α s x i) ≤
    normSq (fun i => y i - x i) := by
  have h_eq : (fun i => G.gradf α s y i - G.gradf α s x i) =
      (fun i => ∑ j, G.Qentry α i j * (y j - x j)) := by
    ext i; unfold Graph.gradf; simp [Finset.sum_sub_distrib, mul_sub]
  rw [h_eq]; exact Q_operator_norm_sq G α hα hα1 (fun j => y j - x j)

-- ═════════════════════════════════════════════════════════════
-- 8b. Forward-step difference bound (TIGHT: via I−Q operator norm)
--
-- Key insight: fwdStep(y) − fwdStep(x) = (I−Q)(y−x).
-- Since I−Q = (1−α)/2 · (I + M) where M = D⁻¹ᐟ²AD⁻¹ᐟ²,
-- ‖(I−Q)z‖² = ((1−α)/2)² · ‖z+Mz‖² ≤ ((1−α)/2)² · 4‖z‖²
-- = (1−α)² ‖z‖² ≤ ‖z‖².
-- This replaces the old bound of 4‖z‖² from the triangle inequality.
-- ═════════════════════════════════════════════════════════════

/- Operator norm of I−Q: ‖(I−Q)z‖² ≤ ‖z‖².
    Proof: Factor I−Q = (1−α)/2 · (I+M), bound ‖(I+M)z‖² ≤ 4‖z‖² via
    normSq_add_le + normSq_normAdj_le, then ((1−α)/2)²·4 = (1−α)² ≤ 1. -/
set_option maxHeartbeats 4000000 in
lemma ImQ_operator_norm_sq (G : Graph n) (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (z : Fin n → ℝ) :
    normSq (fun i => z i - ∑ j, G.Qentry α i j * z j) ≤ normSq z := by
  set Mz : Fin n → ℝ := fun i => ∑ j, G.A i j * z j / (G.sqrtDeg i * G.sqrtDeg j)
  set c := (1 + α) / 2; set d := (1 - α) / 2
  have hd_nn : 0 ≤ d := by change 0 ≤ (1 - α) / 2; linarith
  have hcd1 : c + d = 1 := by unfold c d; ring
  -- (I−Q)z_i = d·(z_i + Mz_i)
  have hImQz_eq : ∀ i, z i - ∑ j, G.Qentry α i j * z j = d * (z i + Mz i) := by
    intro i
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    have hQii : G.Qentry α i i = c := by unfold Graph.Qentry; simp; unfold c; ring
    rw [hQii]
    have hoff : ∑ j ∈ Finset.univ.erase i, G.Qentry α i j * z j =
        -d * ∑ j ∈ Finset.univ.erase i, G.A i j * z j / (G.sqrtDeg i * G.sqrtDeg j) := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j hj
      unfold Graph.Qentry; rw [if_neg (Ne.symm (Finset.ne_of_mem_erase hj))]; simp only [d]; ring
    rw [hoff]
    have hMz_split : Mz i = ∑ j ∈ Finset.univ.erase i, G.A i j * z j / (G.sqrtDeg i * G.sqrtDeg j) := by
      unfold Mz; rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), G.A_no_loops i]; ring
    rw [hMz_split]; unfold d c; ring
  -- normSq((I−Q)z) = d²·normSq(z+Mz)
  have hns_eq : normSq (fun i => z i - ∑ j, G.Qentry α i j * z j) =
      d ^ 2 * normSq (fun i => z i + Mz i) := by
    simp only [normSq]
    conv_lhs => arg 2; ext i; rw [hImQz_eq, mul_pow]
    rw [← Finset.mul_sum]
  rw [hns_eq]
  -- ‖z + Mz‖² ≤ 4·‖z‖² (triangle + ‖M‖ ≤ 1)
  have h_zMz : normSq (fun i => z i + Mz i) ≤ 4 * normSq z := by
    have h := normSq_add_le z Mz
    linarith [normSq_normAdj_le G z]
  -- d²·4 = (1−α)² ≤ 1
  have hd2_bound : d ^ 2 * 4 ≤ 1 := by
    unfold d; nlinarith [sq_nonneg α]
  nlinarith [normSq_nonneg z, normSq_nonneg (fun i => z i + Mz i)]

/-- TIGHT: ‖u(y)−u(x)‖² ≤ ‖y−x‖² where u(z) = z − ∇f(z).
    This is a factor-4 improvement over the triangle-inequality bound.
    Proof: u(y)−u(x) = (I−Q)(y−x), and ImQ_operator_norm_sq gives ‖(I−Q)z‖² ≤ ‖z‖². -/
lemma fwdStep_diff_normSq_bound (G : Graph n) (α : ℝ) (s : Fin n → ℝ)
    (hα : 0 < α) (hα1 : α ≤ 1) (x y : Fin n → ℝ) :
    normSq (fun i => G.fwdStep α 1 s y i - G.fwdStep α 1 s x i) ≤
    normSq (fun i => y i - x i) := by
  have heq : (fun i => G.fwdStep α 1 s y i - G.fwdStep α 1 s x i) =
      (fun i => (y i - x i) - ∑ j, G.Qentry α i j * (y j - x j)) :=
    funext fun i => by unfold Graph.fwdStep Graph.gradf; simp [Finset.sum_sub_distrib, mul_sub]; ring
  rw [heq]; exact ImQ_operator_norm_sq G α hα hα1 (fun j => y j - x j)

-- ═════════════════════════════════════════════════════════════
-- 8c. Per-step spurious volume bound (Cauchy-Schwarz chain)
-- ═════════════════════════════════════════════════════════════

set_option maxHeartbeats 3200000 in
lemma spurious_vol_step_bound (G : Graph n) (α ρ : ℝ) (v : Fin n)
    (hα : 0 < α) (hα1 : α ≤ 1) (hρ : 0 < ρ)
    (hs_nonneg : ∀ i, 0 ≤ basisVec v i)
    (xA : Fin n → ℝ) (hA : G.IsMinimizer 1 α ρ (basisVec v) xA)
    (xB : Fin n → ℝ) (hB : G.IsMinimizer 2 α ρ (basisVec v) xB)
    (B : Finset (Fin n))
    (k : ℕ)
    (hconfine_k : G.spuriousActive α ρ (basisVec v) (vecSupp xA) k ⊆ B)
    (h_activated : ∀ i ∈ G.spuriousActive α ρ (basisVec v) (vecSupp xA) k,
        G.proxMap 2 α ρ 1 (fun j => G.fwdStep α 1 (basisVec v)
          (fistaY G 2 α ρ (basisVec v) k) j) i ≠ 0)
    (h_outside_SA : ∀ i ∈ G.spuriousActive α ρ (basisVec v) (vecSupp xA) k,
        xA i = 0) :
    G.vol (G.spuriousActive α ρ (basisVec v) (vecSupp xA) k) ≤
      Real.sqrt (G.vol B) / (ρ * α) *
      Real.sqrt (normSq (fun i => fistaY G 2 α ρ (basisVec v) k i - xB i)) := by
  have hA_fp : ∀ j, xA j = G.proxMap 1 α ρ 1 (fun k => G.fwdStep α 1 (basisVec v) xA k) j :=
    minimizer_is_prox_fixed_point G 1 α ρ (basisVec v) xA hα hα1 one_pos hρ hA
  have hA_nonneg := minimizer_nonneg G 1 α ρ (basisVec v) xA hA
  have hB_nonneg := minimizer_nonneg G 2 α ρ (basisVec v) xB hB
  set Ak := G.spuriousActive α ρ (basisVec v) (vecSupp xA) k
  set yk := fistaY G 2 α ρ (basisVec v) k
  have hB_conv : G.IsMinimizer 1 α (2 * ρ) (basisVec v) xB := by
    intro x; have := hB x; simp only [Graph.FObj, Graph.gReg] at this ⊢; linarith
  have hmon := path_monotone G α ρ (2 * ρ) (basisVec v) hα hα1 (le_of_lt hρ)
    (by linarith) hs_nonneg xA xB hA hB_conv
  have hxBi : ∀ i ∈ Ak, xB i = 0 :=
    fun i hi => le_antisymm (by linarith [hmon i, h_outside_SA i hi]) (hB_nonneg i)
  have h_margin : ∀ i ∈ Ak, ρ * α ≤ G.kktSlack 2 α ρ (basisVec v) xB i := by
    intro i hi; by_contra hlt; push_neg at hlt
    linarith [two_tier_split G α ρ (basisVec v) hα hα1 hρ hs_nonneg xA hA
      xB hB_conv i (hxBi i hi) hlt, h_outside_SA i hi]
  have h_dev : ∀ i ∈ Ak, (ρ * α) ^ 2 * G.deg i <
      (G.fwdStep α 1 (basisVec v) yk i - G.fwdStep α 1 (basisVec v) xB i) ^ 2 := by
    intro i hi
    have h_jump := coord_jump G α ρ (basisVec v) hα hα1 hρ xB hB yk i
      (hxBi i hi) (h_activated i hi)
    have h_dev_lin : ρ * α * G.sqrtDeg i <
        |G.fwdStep α 1 (basisVec v) yk i - G.fwdStep α 1 (basisVec v) xB i| :=
      calc ρ * α * G.sqrtDeg i ≤ G.kktSlack 2 α ρ (basisVec v) xB i * G.sqrtDeg i := by
            nlinarith [h_margin i hi, G.sqrtDeg_pos i]
        _ < _ := h_jump
    calc (ρ * α) ^ 2 * G.deg i
        = (ρ * α * G.sqrtDeg i) ^ 2 := by
          have hsq : G.sqrtDeg i ^ 2 = G.deg i := Real.sq_sqrt (le_of_lt (G.deg_pos' i))
          nlinarith [hsq]
      _ < _ ^ 2 := sq_lt_sq' (by
            nlinarith [abs_nonneg (G.fwdStep α 1 (basisVec v) yk i -
              G.fwdStep α 1 (basisVec v) xB i), G.sqrtDeg_pos i, mul_pos hρ hα]) h_dev_lin
      _ = _ := sq_abs _
  -- Cauchy-Schwarz chain: vol(Ak)² ≤ (vol(B)/(ρα)²)·4·normSq(y−x*)
  have hcs := cauchy_schwarz_sum Ak
    (fun i => Real.sqrt (G.deg i) / (ρ * α)) (fun i => ρ * α * Real.sqrt (G.deg i))
  have hcs_lhs : ∑ i ∈ Ak, Real.sqrt (G.deg i) / (ρ * α) *
      (ρ * α * Real.sqrt (G.deg i)) = G.vol Ak := by
    unfold Graph.vol; apply Finset.sum_congr rfl; intro i _
    have hρα_ne : ρ * α ≠ 0 := ne_of_gt (mul_pos hρ hα)
    field_simp
    exact Real.sq_sqrt (le_of_lt (G.deg_pos' i))
  have hcs_f1 : ∑ i ∈ Ak, (Real.sqrt (G.deg i) / (ρ * α)) ^ 2 ≤ G.vol B / (ρ * α) ^ 2 := by
    calc ∑ i ∈ Ak, (Real.sqrt (G.deg i) / (ρ * α)) ^ 2
        = ∑ i ∈ Ak, G.deg i / (ρ * α) ^ 2 := Finset.sum_congr rfl fun i _ => by
          rw [div_pow, Real.sq_sqrt (le_of_lt (G.deg_pos' i))]
      _ ≤ ∑ i ∈ B, G.deg i / (ρ * α) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg hconfine_k
            (fun i _ _ => div_nonneg (le_of_lt (G.deg_pos' i)) (sq_nonneg _))
      _ = G.vol B / (ρ * α) ^ 2 := by rw [← Finset.sum_div]
  have hcs_f2 : ∑ i ∈ Ak, (ρ * α * Real.sqrt (G.deg i)) ^ 2 ≤
      normSq (fun i => yk i - xB i) := by
    calc ∑ i ∈ Ak, (ρ * α * Real.sqrt (G.deg i)) ^ 2
        ≤ ∑ i ∈ Ak, (G.fwdStep α 1 (basisVec v) yk i - G.fwdStep α 1 (basisVec v) xB i) ^ 2 := by
          apply Finset.sum_le_sum; intro i hi
          rw [mul_pow, Real.sq_sqrt (le_of_lt (G.deg_pos' i))]; exact le_of_lt (h_dev i hi)
      _ ≤ normSq (fun i => G.fwdStep α 1 (basisVec v) yk i - G.fwdStep α 1 (basisVec v) xB i) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => sq_nonneg _)
      _ ≤ normSq (fun i => yk i - xB i) := fwdStep_diff_normSq_bound G α (basisVec v) hα hα1 xB yk
  have h_vol_nn : 0 ≤ G.vol Ak := by
    unfold Graph.vol; exact Finset.sum_nonneg fun i _ => le_of_lt (G.deg_pos' i)
  have h_volB_nn : 0 ≤ G.vol B := by
    unfold Graph.vol; exact Finset.sum_nonneg fun i _ => le_of_lt (G.deg_pos' i)
  have h_rhs_nn : 0 ≤ Real.sqrt (G.vol B) / (ρ * α) *
      Real.sqrt (normSq (fun i => yk i - xB i)) :=
    mul_nonneg (div_nonneg (Real.sqrt_nonneg _) (le_of_lt (mul_pos hρ hα))) (Real.sqrt_nonneg _)
  rw [← Real.sqrt_sq h_vol_nn, ← Real.sqrt_sq h_rhs_nn]
  apply Real.sqrt_le_sqrt
  rw [mul_pow, div_pow, Real.sq_sqrt h_volB_nn, Real.sq_sqrt (normSq_nonneg _)]
  calc (G.vol Ak) ^ 2
      = (∑ i ∈ Ak, Real.sqrt (G.deg i) / (ρ * α) * (ρ * α * Real.sqrt (G.deg i))) ^ 2 := by rw [hcs_lhs]
    _ ≤ (∑ i ∈ Ak, (Real.sqrt (G.deg i) / (ρ * α)) ^ 2) *
        (∑ i ∈ Ak, (ρ * α * Real.sqrt (G.deg i)) ^ 2) := hcs
    _ ≤ (G.vol B / (ρ * α) ^ 2) * normSq (fun i => yk i - xB i) :=
        mul_le_mul hcs_f1 hcs_f2 (Finset.sum_nonneg fun i _ => sq_nonneg _)
          (div_nonneg h_volB_nn (sq_nonneg _))

-- ═════════════════════════════════════════════════════════════
-- 8d. Geometric series helpers
-- ═════════════════════════════════════════════════════════════

lemma one_sub_sqrt_one_sub_ge (x : ℝ) (_hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    x / 2 ≤ 1 - Real.sqrt (1 - x) := by
  have h1x2 : 0 ≤ 1 - x / 2 := by linarith
  linarith [show Real.sqrt (1 - x) ≤ 1 - x / 2 by
    rw [← Real.sqrt_sq h1x2]; exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg x])]

lemma geom_sum_le_inv (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) (M : ℕ) :
    ∑ m ∈ Finset.range (M + 1), r ^ m ≤ 1 / (1 - r) := by
  rw [geom_sum_eq (ne_of_lt hr1)]
  have h1r : 0 < 1 - r := by linarith
  rw [show (r ^ (M + 1) - 1) / (r - 1) = (1 - r ^ (M + 1)) / (1 - r) from by
    rw [show r ^ (M + 1) - 1 = -(1 - r ^ (M + 1)) from by ring,
        show r - 1 = -(1 - r) from by ring, neg_div_neg_eq]]
  apply div_le_div_of_nonneg_right _ (le_of_lt h1r)
  linarith [pow_nonneg hr0 (M + 1)]

lemma sqrt_pow_eq (q : ℝ) (hq : 0 ≤ q) : ∀ m : ℕ,
    Real.sqrt (q ^ m) = Real.sqrt q ^ m
  | 0 => by simp [Real.sqrt_one]
  | m + 1 => by rw [pow_succ q m, Real.sqrt_mul (pow_nonneg hq m), sqrt_pow_eq q hq m, pow_succ]

-- ═════════════════════════════════════════════════════════════
-- 8e. sum_sqrt_decay_bound: Σ √‖y_k − x*‖² ≤ 10/√α (TIGHTENED from 11)
-- ═════════════════════════════════════════════════════════════

set_option maxHeartbeats 4000000 in
lemma sum_sqrt_decay_bound (G : Graph n) (c α ρ : ℝ) (v : Fin n)
    (hα : 0 < α) (hα1 : α ≤ 1) (hρ : 0 < ρ) (hc : 0 < c) (hd : 1 ≤ G.deg v)
    (xstar : Fin n → ℝ) (hmin : G.IsMinimizer c α ρ (basisVec v) xstar) (N : ℕ) :
    ∑ k ∈ Finset.range N, Real.sqrt (normSq (fun i => fistaY G c α ρ (basisVec v) k i - xstar i)) ≤
    10 / √α := by
  have hsa : 0 < √α := Real.sqrt_pos_of_pos hα
  have hsa1 : √α ≤ 1 := Real.sqrt_le_one.mpr hα1
  set q := 1 - √α
  have hq0 : 0 ≤ q := by linarith
  have hq1 : q < 1 := by linarith
  rcases N with _ | M; · simp; positivity
  rw [Finset.sum_range_succ']
  -- k=0 term: √(‖y₀−x*‖²) ≤ √1 = 1 (using tightened fista_y0_bound ≤ 1)
  have h0 : Real.sqrt (normSq (fun i => fistaY G c α ρ (basisVec v) 0 i - xstar i)) ≤ 1 := by
    calc Real.sqrt _ ≤ Real.sqrt 1 := Real.sqrt_le_sqrt (fista_y0_bound G c α ρ v hα hα1 hρ hc hd xstar hmin)
      _ = 1 := Real.sqrt_one
  have h_term : ∀ j ∈ Finset.range M,
      Real.sqrt (normSq (fun i => fistaY G c α ρ (basisVec v) (j+1) i - xstar i)) ≤
      Real.sqrt 20 * Real.sqrt q ^ j := by
    intro j _
    have h_decay := fista_yk_decay G c α ρ v hα hα1 hρ hc hd xstar hmin (j+1) (Nat.succ_le_succ (Nat.zero_le j))
    simp only [Nat.succ_sub_one] at h_decay
    calc Real.sqrt _ ≤ Real.sqrt (20 * q^j) := Real.sqrt_le_sqrt h_decay
      _ = Real.sqrt 20 * Real.sqrt (q^j) := Real.sqrt_mul (by norm_num) (q^j)
      _ = Real.sqrt 20 * Real.sqrt q ^ j := by rw [sqrt_pow_eq q hq0 j]
  have h_sum : ∑ j ∈ Finset.range M,
      Real.sqrt (normSq (fun i => fistaY G c α ρ (basisVec v) (j+1) i - xstar i)) ≤
      Real.sqrt 20 * ∑ j ∈ Finset.range M, Real.sqrt q ^ j := by
    calc ∑ j ∈ Finset.range M,
          Real.sqrt (normSq (fun i => fistaY G c α ρ (basisVec v) (j+1) i - xstar i)) ≤
          ∑ j ∈ Finset.range M, (Real.sqrt 20 * Real.sqrt q ^ j) :=
          Finset.sum_le_sum h_term
      _ = _ := (Finset.mul_sum ..).symm
  have hsq1 : Real.sqrt q < 1 := by rw [← Real.sqrt_one]; exact Real.sqrt_lt_sqrt hq0 hq1
  have h_geom : ∑ j ∈ Finset.range M, Real.sqrt q ^ j ≤ 2 / √α := by
    rcases M with _ | M'; · simp; positivity
    · calc _ ≤ 1 / (1 - Real.sqrt q) := geom_sum_le_inv _ (Real.sqrt_nonneg _) hsq1 M'
        _ ≤ 2 / √α := by
          rw [div_le_div_iff₀ (by linarith [one_sub_sqrt_one_sub_ge (√α) (le_of_lt hsa) hsa1]) hsa]
          linarith [one_sub_sqrt_one_sub_ge (√α) (le_of_lt hsa) hsa1]
  have h_sqrt20 : Real.sqrt 20 ≤ 9 / 2 := by
    rw [← Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 9/2)]; exact Real.sqrt_le_sqrt (by norm_num)
  calc ∑ j ∈ Finset.range M,
        Real.sqrt (normSq (fun i => fistaY G c α ρ (basisVec v) (j+1) i - xstar i)) +
        Real.sqrt (normSq (fun i => fistaY G c α ρ (basisVec v) 0 i - xstar i))
      ≤ Real.sqrt 20 * (∑ j ∈ Finset.range M, Real.sqrt q ^ j) + 1 := by linarith [h_sum]
    _ ≤ Real.sqrt 20 * (2/√α) + 1 := by nlinarith [Real.sqrt_nonneg (20:ℝ), h_geom]
    _ = 1 + Real.sqrt 20 * (2/√α) := by ring
    _ ≤ 1 + 9/2 * (2/√α) := by nlinarith [h_sqrt20, show 0 ≤ 2/√α by positivity]
    _ = 1 + 9/√α := by ring
    _ ≤ 1/√α + 9/√α := by nlinarith [show 1 ≤ 1/√α from by rw [one_div]; exact (one_le_inv₀ hsa).mpr hsa1]
    _ = 10 / √α := by ring

-- ═════════════════════════════════════════════════════════════
-- 8f. Iteration count helpers
-- ═════════════════════════════════════════════════════════════

lemma log_le_sub_one (x : ℝ) (hx : 0 < x) : Real.log x ≤ x - 1 := by
  linarith [Real.add_one_le_exp (Real.log x), Real.exp_log hx]

lemma log_one_sub_le_neg (s : ℝ) (_hs : 0 ≤ s) (hs1 : s < 1) : Real.log (1-s) ≤ -s := by
  linarith [log_le_sub_one (1-s) (by linarith)]

lemma nat_find_pow_bound (s t : ℝ) (hs : 0 < s) (hs1 : s ≤ 1) (ht : 0 < t) (ht1 : t < 1)
    (N₀ : ℕ) (hN₀ : (1-s)^N₀ < t) (hN₀_min : ∀ m, m < N₀ → t ≤ (1-s)^m) :
    (↑N₀ : ℝ) ≤ Real.log (1/t) / s + 1 := by
  rcases eq_or_lt_of_le hs1 with rfl | hs_lt1
  · rcases N₀ with _ | N₀'; · simp at hN₀; linarith
    · have : N₀' = 0 := by
        by_contra h; push_neg at h; linarith [hN₀_min 1 (by omega), show (0:ℝ)^1 = 0 from by norm_num]
      subst this
      have h1t : (1:ℝ) < 1/t := by rw [lt_div_iff₀ ht]; linarith
      have hlog_pos := Real.log_pos h1t
      push_cast; linarith
  · rcases N₀ with _ | N₀'; · simp at hN₀; linarith
    · have h1s_pos : 0 < 1 - s := by linarith
      have hlog_mono : Real.log t ≤ ↑N₀' * Real.log (1-s) := by
        rw [← Real.log_pow]; exact Real.log_le_log ht (hN₀_min N₀' (by omega))
      have h_Ns : ↑N₀' * s ≤ Real.log (1/t) := by
        rw [one_div, Real.log_inv]
        nlinarith [log_one_sub_le_neg s (le_of_lt hs) hs_lt1, (Nat.cast_nonneg N₀' : (0:ℝ) ≤ ↑N₀')]
      push_cast; linarith [(le_div_iff₀ hs).mpr h_Ns]

-- ═════════════════════════════════════════════════════════════
-- 8g. totalWork_decomp helpers
-- ═════════════════════════════════════════════════════════════

lemma vol_union_le (G : Graph n) (S T : Finset (Fin n)) :
    G.vol (S ∪ T) ≤ G.vol S + G.vol T := by
  unfold Graph.vol
  rw [← Finset.sum_filter_add_sum_filter_not (S ∪ T) (· ∈ S)]
  apply add_le_add
  · exact Finset.sum_le_sum_of_subset_of_nonneg
      (fun i hi => (Finset.mem_filter.mp hi).2) (fun _ _ _ => le_of_lt (G.deg_pos' _))
  · exact Finset.sum_le_sum_of_subset_of_nonneg
      (fun i hi => by obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hi; exact (Finset.mem_union.mp h1).resolve_left h2)
      (fun _ _ _ => le_of_lt (G.deg_pos' _))

lemma vol_mono (G : Graph n) {S T : Finset (Fin n)} (h : S ⊆ T) : G.vol S ≤ G.vol T := by
  unfold Graph.vol; exact Finset.sum_le_sum_of_subset_of_nonneg h (fun _ _ _ => le_of_lt (G.deg_pos' _))

lemma vecSupp_fistaY_succ (G : Graph n) (c α ρ : ℝ) (s : Fin n → ℝ) (k : ℕ) :
    vecSupp (fistaY G c α ρ s (k+1)) ⊆ vecSupp (fistaX G c α ρ s (k+1)) ∪ vecSupp (fistaX G c α ρ s k) := by
  intro i hi; rw [vecSupp, Finset.mem_filter] at hi; rw [Finset.mem_union]
  by_contra h; push_neg at h; obtain ⟨h1, h2⟩ := h
  rw [vecSupp, Finset.mem_filter] at h1 h2; push_neg at h1 h2
  exact hi.2 (by rw [fistaY_succ, h1 (Finset.mem_univ _), h2 (Finset.mem_univ _)]; ring)

lemma vecSupp_fistaX_succ_subset (G : Graph n) (α ρ : ℝ) (s : Fin n → ℝ)
    (SA : Finset (Fin n)) (k : ℕ) :
    vecSupp (fistaX G 2 α ρ s (k+1)) ⊆ SA ∪ G.spuriousActive α ρ s SA k := by
  intro i hi; rw [Finset.mem_union]
  by_cases hiSA : i ∈ SA
  · left; exact hiSA
  · right; unfold Graph.spuriousActive; exact Finset.mem_sdiff.mpr ⟨hi, hiSA⟩

lemma sum_range_shift1 (g : ℕ → ℝ) (hg : ∀ k, 0 ≤ g k) (N : ℕ) :
    ∑ k ∈ Finset.range N, (if 0 < k then g (k-1) else 0) ≤ ∑ k ∈ Finset.range N, g k := by
  rcases N with _ | M; · simp
  · rw [Finset.sum_range_succ']; simp only [show ¬(0<0) from lt_irrefl 0, if_false, add_zero]
    have hcongr : ∀ j ∈ Finset.range M,
        (if 0 < j + 1 then g (j + 1 - 1) else 0) = g j := by
      intro j _; simp only [show 0 < j + 1 from Nat.succ_pos j, if_true, show j + 1 - 1 = j from Nat.succ_sub_one j]
    rw [Finset.sum_congr rfl hcongr]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.le_succ M)) (fun k _ _ => hg k)

lemma sum_range_shift2 (g : ℕ → ℝ) (hg : ∀ k, 0 ≤ g k) (N : ℕ) :
    ∑ k ∈ Finset.range N, (if 1 < k then g (k-2) else 0) ≤ ∑ k ∈ Finset.range N, g k := by
  rcases N with _ | N; · simp
  · rcases N with _ | M
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero,
                  show ¬(1 < 0) from by omega, if_false]; linarith [hg 0]
    · -- N = M + 2
      -- Peel off first two terms k=0 and k=1
      rw [Finset.sum_range_succ']; simp only [show ¬(1 < 0) from by omega, if_false, add_zero]
      rw [Finset.sum_range_succ']; simp only [show ¬(1 < 1) from by omega, if_false, add_zero]
      -- Remaining sum: ∑ j in range M, (if 1 < j+2 then g(j+2-2) else 0)
      have hcongr : ∀ j ∈ Finset.range M,
          (if 1 < j + 1 + 1 then g (j + 1 + 1 - 2) else 0) = g j := by
        intro j _
        simp only [show 1 < j + 1 + 1 from by omega, if_true, show j + 1 + 1 - 2 = j from by omega]
      rw [Finset.sum_congr rfl hcongr]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (show M ≤ M + 2 by omega)) (fun k _ _ => hg k)

-- ═════════════════════════════════════════════════════════════
-- 8h. totalWork_decomp (was axiom, now proved)
-- ═════════════════════════════════════════════════════════════

set_option maxHeartbeats 4000000 in
theorem totalWork_decomp (G : Graph n) (α ρ : ℝ) (v : Fin n)
    (_hα : 0 < α) (_hα1 : α ≤ 1) (_hρ : 0 < ρ)
    (xA : Fin n → ℝ) (_hA : G.IsMinimizer 1 α ρ (basisVec v) xA)
    (xB : Fin n → ℝ) (_hB : G.IsMinimizer 2 α ρ (basisVec v) xB) (N : ℕ) :
    G.totalWork 2 α ρ (basisVec v) N ≤
      3 * ↑N * G.vol (vecSupp xA) +
      3 * ∑ k ∈ Finset.range N, G.vol (G.spuriousActive α ρ (basisVec v) (vecSupp xA) k) := by
  set SA := vecSupp xA; set s := basisVec v
  set volA := fun k => G.vol (G.spuriousActive α ρ s SA k)
  rw [show G.totalWork 2 α ρ s N = ∑ k ∈ Finset.range N, G.iterWork 2 α ρ s k from by unfold Graph.totalWork; rfl]
  have h_x_bound : ∀ k, G.vol (vecSupp (fistaX G 2 α ρ s (k+1))) ≤ G.vol SA + volA k :=
    fun k => le_trans (vol_mono G (vecSupp_fistaX_succ_subset G α ρ s SA k)) (vol_union_le G SA _)
  have h_y_bound_succ : ∀ k, G.vol (vecSupp (fistaY G 2 α ρ s (k+1))) ≤
      G.vol (vecSupp (fistaX G 2 α ρ s (k+1))) + G.vol (vecSupp (fistaX G 2 α ρ s k)) :=
    fun k => le_trans (vol_mono G (vecSupp_fistaY_succ G 2 α ρ s k)) (vol_union_le G _ _)
  have h_y0 : G.vol (vecSupp (fistaY G 2 α ρ s 0)) = 0 := by
    rw [show vecSupp (fistaY G 2 α ρ s 0) = ∅ from by
      ext i; simp [vecSupp, Finset.mem_filter, show fistaY G 2 α ρ s 0 i = 0 from by
        simp [fistaY, fistaState, fistaMom]]]
    unfold Graph.vol; simp
  have h_x0 : G.vol (vecSupp (fistaX G 2 α ρ s 0)) = 0 := by
    rw [show vecSupp (fistaX G 2 α ρ s 0) = ∅ from by
      ext i; simp [vecSupp, Finset.mem_filter, show (fistaX G 2 α ρ s 0) i = 0 from by
        have := fistaX_zero G 2 α ρ s; simp [this]]]
    unfold Graph.vol; simp
  have hvolSA_nn : 0 ≤ G.vol SA := by unfold Graph.vol; exact Finset.sum_nonneg fun i _ => le_of_lt (G.deg_pos' i)
  have h_iter : ∀ k ∈ Finset.range N, G.iterWork 2 α ρ s k ≤
      3 * G.vol SA + volA k + (if 0<k then volA (k-1) else 0) + (if 1<k then volA (k-2) else 0) := by
    intro k _; rw [show G.iterWork 2 α ρ s k = G.vol (vecSupp (fistaY G 2 α ρ s k)) +
      G.vol (vecSupp (fistaX G 2 α ρ s (k+1))) from by unfold Graph.iterWork; rfl]
    rcases k with _ | k
    · simp only [h_y0, zero_add, show ¬(0<0) from lt_irrefl 0, show ¬(1<0) from by omega, if_false, add_zero]
      linarith [h_x_bound 0]
    · rcases k with _ | k
      · simp only [show ¬(1<1) from lt_irrefl 1, if_false, add_zero, show (0<1) from one_pos, if_true]
        linarith [h_y_bound_succ 0, h_x_bound 0, h_x_bound 1, h_x0]
      · simp only [show 0<k+2 from by omega, show 1<k+2 from by omega, if_true,
                   show k+2-1 = k+1 from by omega, show k+2-2 = k from by omega]
        linarith [h_y_bound_succ (k+1), h_x_bound (k+1), h_x_bound k, h_x_bound (k+2)]
  have hnn : ∀ k, 0 ≤ volA k := fun k => by
    unfold volA; unfold Graph.vol; exact Finset.sum_nonneg fun i _ => le_of_lt (G.deg_pos' i)
  calc ∑ k ∈ Finset.range N, G.iterWork 2 α ρ s k
      ≤ ∑ k ∈ Finset.range N, (3 * G.vol SA + volA k + (if 0<k then volA (k-1) else 0) +
          (if 1<k then volA (k-2) else 0)) := Finset.sum_le_sum h_iter
    _ = 3*↑N * G.vol SA + ∑ k ∈ Finset.range N, volA k +
        ∑ k ∈ Finset.range N, (if 0<k then volA (k-1) else 0) +
        ∑ k ∈ Finset.range N, (if 1<k then volA (k-2) else 0) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
      congr 1; congr 1; congr 1; rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
    _ ≤ 3*↑N * G.vol SA + 3 * ∑ k ∈ Finset.range N, volA k := by
      linarith [sum_range_shift1 volA hnn N, sum_range_shift2 volA hnn N]

-- ═════════════════════════════════════════════════════════════
-- 8i. Theorem 4.3 — TIGHTENED work bound (constant 30, down from 200)
--
-- Improvements over original:
-- (A) totalWork_decomp: factor 3 (was 6)
-- (B) fwdStep operator norm: ‖(I−Q)z‖² ≤ ‖z‖² (was ≤ 4‖z‖²)
-- (C) sum_sqrt_decay: 10/√α (was 11/√α, from ‖x*‖² ≤ 1 instead of 2)
-- (D) iteration count: N = N₀ (was N₀+1)
-- Combined: 3 × 1 × 10 = 30 (was 6 × 2 × 11 → 200 after rounding)
-- ═════════════════════════════════════════════════════════════

set_option maxHeartbeats 4000000 in
theorem work_bound (G : Graph n) (α ρ ε : ℝ) (v : Fin n)
    (hα : 0 < α) (hα1 : α ≤ 1) (hρ : 0 < ρ) (hε : 0 < ε) (hεα : ε < α) (hd : 1 ≤ G.deg v)
    (xA : Fin n → ℝ) (hA : G.IsMinimizer 1 α ρ (basisVec v) xA)
    (xB : Fin n → ℝ) (hB : G.IsMinimizer 2 α ρ (basisVec v) xB)
    (B : Finset (Fin n))
    (hconfine : ∀ k, G.spuriousActive α ρ (basisVec v) (vecSupp xA) k ⊆ B) :
    ∃ N : ℕ,
      G.FObj 2 α ρ (basisVec v) (fistaX G 2 α ρ (basisVec v) N) - G.FObj 2 α ρ (basisVec v) xB ≤ ε ∧
      G.totalWork 2 α ρ (basisVec v) N ≤
        30 * (1/(ρ * √α) * (Real.log (α/ε) + 1) + √(G.vol B) / (ρ * (α * √α))) := by
  have hA_nonneg := minimizer_nonneg G 1 α ρ (basisVec v) xA hA
  have hB_nonneg := minimizer_nonneg G 2 α ρ (basisVec v) xB hB
  -- Derive hvolA from rppr_support_volume_bound (Fountoulakis et al. 2019, Thm 2)
  have hvolA : G.vol (vecSupp xA) ≤ 1/ρ :=
    rppr_support_volume_bound G α ρ v hα hα1 hρ xA hA
  -- Derive h_activated: if i ∈ spuriousActive then proxMap(fwdStep(fistaY k))_i ≠ 0.
  -- This is tautological: spuriousActive includes i iff fistaX(k+1)(i) ≠ 0,
  -- and fistaX(k+1) = proxMap(fwdStep(fistaY k)) by definition.
  have h_activated : ∀ k i, i ∈ G.spuriousActive α ρ (basisVec v) (vecSupp xA) k →
      G.proxMap 2 α ρ 1 (fun j => G.fwdStep α 1 (basisVec v)
        (fistaY G 2 α ρ (basisVec v) k) j) i ≠ 0 := by
    intro k i hi
    simp only [Graph.spuriousActive, Finset.mem_sdiff, vecSupp, Finset.mem_filter,
               Finset.mem_univ, true_and] at hi
    rw [← fistaX_succ_eq_proxMap]; exact hi.1
  -- Derive h_outside_SA: if i ∈ spuriousActive then xA i = 0.
  -- This is tautological: spuriousActive = supp(fistaX(k+1)) \ supp(xA),
  -- so i ∉ supp(xA) means xA(i) = 0.
  have h_outside_SA : ∀ k i, i ∈ G.spuriousActive α ρ (basisVec v) (vecSupp xA) k →
      xA i = 0 := by
    intro k i hi
    simp only [Graph.spuriousActive, Finset.mem_sdiff, vecSupp, Finset.mem_filter,
               Finset.mem_univ, true_and, not_not] at hi
    exact hi.2
  have hsa : 0 < √α := Real.sqrt_pos_of_pos hα
  have hsa1 : √α ≤ 1 := Real.sqrt_le_one.mpr hα1
  have hrate_nn : 0 ≤ 1 - √α := by linarith
  have hrate_lt1 : 1 - √α < 1 := by linarith
  have hs_nonneg : ∀ i, 0 ≤ basisVec v i := fun i => by simp only [basisVec]; split_ifs <;> norm_num
  have h_exists : ∃ m : ℕ, (1-√α)^m < ε/α := exists_pow_lt_of_lt_one (div_pos hε hα) hrate_lt1
  classical
  set N₀ := Nat.find h_exists
  have hN₀_spec : (1-√α)^N₀ < ε/α := Nat.find_spec h_exists
  have hN₀_min : ∀ m, m < N₀ → ε/α ≤ (1-√α)^m := fun m hm => not_lt.mp (Nat.find_min h_exists hm)
  -- N₀ ≥ 1 since (1−√α)⁰ = 1 ≥ ε/α (from ε < α)
  have hN₀_ge1 : 1 ≤ N₀ := by
    by_contra h; push_neg at h
    have : N₀ = 0 := by omega
    rw [this] at hN₀_spec; simp only [pow_zero] at hN₀_spec
    have : ε / α < 1 := by rw [div_lt_one hα]; exact hεα
    linarith
  -- Use N = N₀ (saving one iteration vs the original N₀+1)
  use N₀; constructor
  · -- ε-accuracy: F(x_{N₀}) − F(x*) ≤ 2Δ₀·(1−√α)^{N₀} ≤ α·(ε/α) = ε
    have hconv := fista_convergence_rate G 2 α ρ (basisVec v) hα hα1 hρ two_pos xB hB N₀ hN₀_ge1
    have hΔ₀ := initial_gap_general G 2 α ρ v hα hα1 two_pos hρ hd xB hB
    have hx0eq : fistaX G 2 α ρ (basisVec v) 0 = 0 := fistaX_zero G 2 α ρ (basisVec v)
    rw [hx0eq] at hconv
    have hpow_nn := pow_nonneg hrate_nn N₀
    have hΔ₀_nn : 0 ≤ G.FObj 2 α ρ (basisVec v) 0 - G.FObj 2 α ρ (basisVec v) xB := by
      have := hB 0; linarith
    have h1 : 2 * (G.FObj 2 α ρ (basisVec v) 0 - G.FObj 2 α ρ (basisVec v) xB) * (1 - √α) ^ N₀ ≤
        2 * (α / 2) * (1 - √α) ^ N₀ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hΔ₀ (by norm_num)) hpow_nn
    have h2 : 2 * (α / 2) * (1 - √α) ^ N₀ = α * (1 - √α) ^ N₀ := by ring
    have h3 : α * (1 - √α) ^ N₀ < α * (ε / α) :=
      mul_lt_mul_of_pos_left hN₀_spec hα
    have h4 : α * (ε / α) = ε := by field_simp
    linarith
  · -- Work bound
    have h_decomp := totalWork_decomp G α ρ v hα hα1 hρ xA hA xB hB N₀
    have hεα_ratio : ε/α < 1 := by rw [div_lt_one hα]; exact hεα
    have h_N₀_le := nat_find_pow_bound (√α) (ε/α) hsa hsa1 (div_pos hε hα) hεα_ratio N₀ hN₀_spec hN₀_min
    rw [show (1:ℝ)/(ε/α) = α/ε from by rw [one_div, inv_div]] at h_N₀_le
    have h_log_pos : 0 < Real.log (α/ε) := Real.log_pos (by rw [one_lt_div hε]; exact hεα)
    -- N₀ ≤ log(α/ε)/√α + 1 ≤ (log(α/ε)+1)/√α (since √α ≤ 1 ⟹ 1 ≤ 1/√α)
    have h_N_bound : (↑N₀ : ℝ) ≤ (Real.log (α/ε) + 1) / √α := by
      calc (↑N₀ : ℝ) ≤ Real.log (α/ε)/√α + 1 := h_N₀_le
        _ ≤ Real.log (α/ε)/√α + 1/√α := by
            nlinarith [show 1 ≤ 1/√α from by rw [one_div]; exact (one_le_inv₀ hsa).mpr hsa1]
        _ = (Real.log (α/ε) + 1) / √α := by ring
    -- Core: 3·N₀·vol(S_A) ≤ 3(log(α/ε)+1)/(ρ√α)
    have hvolA_nn : 0 ≤ G.vol (vecSupp xA) := by
      unfold Graph.vol; exact Finset.sum_nonneg fun i _ => le_of_lt (G.deg_pos' i)
    have h_core : 3*(↑N₀:ℝ)*G.vol (vecSupp xA) ≤ 3*(Real.log (α/ε)+1)/(ρ*√α) :=
      calc 3*(↑N₀:ℝ)*G.vol (vecSupp xA) ≤ 3*((Real.log (α/ε)+1)/√α)*(1/ρ) := by
              apply mul_le_mul (mul_le_mul_of_nonneg_left h_N_bound (by norm_num : (0:ℝ) ≤ 3)) hvolA hvolA_nn
              exact mul_nonneg (by norm_num : (0:ℝ) ≤ 3) (div_nonneg (by linarith) (le_of_lt hsa))
        _ = 3*(Real.log (α/ε)+1)/(ρ*√α) := by ring
    -- Per-step bound (TIGHT: factor 1 instead of 2)
    have h_per_step : ∀ k ∈ Finset.range N₀,
        G.vol (G.spuriousActive α ρ (basisVec v) (vecSupp xA) k) ≤
        Real.sqrt (G.vol B)/(ρ*α) * Real.sqrt (normSq (fun i => fistaY G 2 α ρ (basisVec v) k i - xB i)) :=
      fun k _ => spurious_vol_step_bound G α ρ v hα hα1 hρ hs_nonneg xA hA xB hB B k
        (hconfine k) (h_activated k) (h_outside_SA k)
    -- Spurious sum: 3·Σvol(Ã) ≤ 3·√vol(B)/(ρα)·10/√α = 30·√vol(B)/(ρα^{3/2})
    have h_spurious : ∑ k ∈ Finset.range N₀, G.vol (G.spuriousActive α ρ (basisVec v) (vecSupp xA) k) ≤
        10 * Real.sqrt (G.vol B) / (ρ * (α * √α)) :=
      calc ∑ k ∈ Finset.range N₀, _ ≤ ∑ k ∈ Finset.range N₀,
            (Real.sqrt (G.vol B)/(ρ*α) * Real.sqrt (normSq (fun i => fistaY G 2 α ρ (basisVec v) k i - xB i))) :=
            Finset.sum_le_sum h_per_step
        _ = Real.sqrt (G.vol B)/(ρ*α) * ∑ k ∈ Finset.range N₀,
              Real.sqrt (normSq (fun i => fistaY G 2 α ρ (basisVec v) k i - xB i)) := by rw [← Finset.mul_sum]
        _ ≤ Real.sqrt (G.vol B)/(ρ*α) * (10/√α) :=
            mul_le_mul_of_nonneg_left (sum_sqrt_decay_bound G 2 α ρ v hα hα1 hρ two_pos hd xB hB N₀) (by positivity)
        _ = 10 * Real.sqrt (G.vol B) / (ρ * (α * √α)) := by ring
    -- Assembly: total ≤ 3(log+1)/(ρ√α) + 30·√vol(B)/(ρα^{3/2}) ≤ 30·(...)
    calc G.totalWork 2 α ρ (basisVec v) N₀ ≤ 3*↑N₀ * G.vol (vecSupp xA) +
          3 * ∑ k ∈ Finset.range N₀, G.vol (G.spuriousActive α ρ (basisVec v) (vecSupp xA) k) := h_decomp
      _ ≤ 3*(Real.log (α/ε)+1)/(ρ*√α) + 3*(10*Real.sqrt (G.vol B)/(ρ*(α*√α))) := by linarith
      _ = 3*(1/(ρ*√α)*(Real.log (α/ε)+1)) + 30*(√(G.vol B)/(ρ*(α*√α))) := by ring
      _ ≤ 30*(1/(ρ*√α)*(Real.log (α/ε)+1)) + 30*(√(G.vol B)/(ρ*(α*√α))) := by
          nlinarith [show 0 ≤ 1/(ρ*√α)*(Real.log (α/ε)+1) by positivity]
      _ = 30 * (1/(ρ*√α)*(Real.log (α/ε)+1) + √(G.vol B)/(ρ*(α*√α))) := by ring

/-! ## Result 9: Boundary Confinement (Theorem 4.4) -/

/- Exterior forward-step bound: if j ∈ Ext(S), y vanishes outside S ∪ ∂S,
    the graph is unweighted (A ≤ 1), and the no-percolation condition holds,
    then |fwdStep(y)_j| ≤ 2αρ√d_j.

    This is the core Cauchy-Schwarz estimate from the proof of Theorem 4.4
    (paper pages 14-15). -/
set_option maxHeartbeats 3200000 in
lemma exterior_fwdStep_bound (G : Graph n) (α ρ : ℝ) (v : Fin n)
    (hα : 0 < α) (hα1 : α ≤ 1) (hρ : 0 < ρ)
    (xB : Fin n → ℝ) (hB : G.IsMinimizer 2 α ρ (basisVec v) xB)
    (S : Finset (Fin n)) (hv_in_S : v ∈ S)
    (hbdry : (G.bdry S).Nonempty)
    (h_exposure : ∀ i ∈ G.exterior S,
      (↑(G.nbrsInCount i (G.bdry S)) : ℝ) / G.deg i ≤
        (α * ρ / (2 * (1 - α))) ^ 2 * G.deg i * G.minDegIn (G.bdry S) hbdry)
    (hd : 1 ≤ G.deg v)
    -- Unweighted graph: edge weights are 0 or 1 (paper assumes undirected, unweighted graphs)
    (hA_unw : ∀ i j, G.A i j = 0 ∨ G.A i j = 1)
    (y : Fin n → ℝ)
    -- y vanishes outside S ∪ ∂S
    (hy_supp : ∀ ℓ, ℓ ∉ S ∪ G.bdry S → y ℓ = 0)
    -- y norm bound: ‖y - x*_B‖² ≤ 20 (from Corollary A.3)
    (hy_norm : normSq (fun i => y i - xB i) ≤ 20)
    -- x*_B norm bound: ‖x*_B‖² ≤ 2 (from initial gap)
    (hxB_norm : normSq xB ≤ 2)
    -- j is in the exterior
    (j : Fin n) (hj_ext : j ∈ G.exterior S)
    -- y vanishes at j
    (hyk_j : y j = 0) :
    |G.fwdStep α 1 (basisVec v) y j| ≤ 1 * 2 * α * ρ * G.sqrtDeg j := by
  have hA_le : ∀ i j, G.A i j ≤ 1 := fun i j => by
    rcases hA_unw i j with h | h <;> simp [h]
  -- === STRUCTURAL REDUCTION ===
  -- Step 1: fwdStep_j = -gradf(y)_j since y_j = 0 and s_j = 0
  have hj_ne_v : j ≠ v := by
    intro h; subst h
    simp only [Graph.exterior, Finset.mem_filter] at hj_ext; exact hj_ext.2.1 hv_in_S
  have hbasis_j : basisVec v j = 0 := by simp [basisVec, hj_ne_v]
  have hfwd_eq : G.fwdStep α 1 (basisVec v) y j =
      -(∑ ℓ, G.Qentry α j ℓ * y ℓ) := by
    unfold Graph.fwdStep Graph.gradf; rw [hyk_j, hbasis_j]; ring
  -- Step 2: j has no neighbors in S (exterior definition)
  have hj_no_S_nbrs : ∀ ℓ, ℓ ∈ S → G.A j ℓ = 0 := by
    intro ℓ hℓ; by_contra hA; push_neg at hA
    have hA_pos : 0 < G.A j ℓ := lt_of_le_of_ne (G.A_nonneg j ℓ) (Ne.symm hA)
    simp only [Graph.exterior, Finset.mem_filter] at hj_ext
    exact hj_ext.2.2 (by
      simp only [Graph.bdry, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hj_ext.2.1, ⟨ℓ, hℓ, hA_pos⟩⟩)
  -- Step 3: Show each term Q_{jℓ}·y_ℓ = 0 for ℓ ∉ G.bdry S
  have hterm_zero : ∀ ℓ : Fin n, ℓ ∉ G.bdry S → G.Qentry α j ℓ * y ℓ = 0 := by
    intro ℓ hℓ_not_bdry
    by_cases hℓj : ℓ = j
    · -- ℓ = j: y_j = 0
      rw [hℓj, hyk_j, mul_zero]
    · -- ℓ ≠ j: either ℓ ∈ S (then A=0 hence Q=0) or ℓ ∉ S∪∂S (then y=0)
      by_cases hℓS : ℓ ∈ S
      · -- ℓ ∈ S: A_{jℓ} = 0, so Q_{jℓ} = -(1-α)/2 · 0/... = 0
        unfold Graph.Qentry; rw [if_neg (Ne.symm hℓj), hj_no_S_nbrs ℓ hℓS]; ring
      · -- ℓ ∉ S and ℓ ∉ ∂S: y_ℓ = 0
        have : ℓ ∉ S ∪ G.bdry S := by
          simp only [Finset.mem_union]; push_neg; exact ⟨hℓS, hℓ_not_bdry⟩
        rw [hy_supp ℓ this, mul_zero]
  -- Step 4: The full sum reduces to the sum over ∂S
  have hsum_reduce : ∑ ℓ, G.Qentry α j ℓ * y ℓ =
      ∑ ℓ ∈ G.bdry S, G.Qentry α j ℓ * y ℓ := by
    symm; apply Finset.sum_subset (Finset.subset_univ _)
    intro ℓ _ hℓ_not_bdry
    exact hterm_zero ℓ hℓ_not_bdry
  -- Step 5: Express Q_{jℓ} for ℓ ∈ ∂S, ℓ ≠ j (off-diagonal)
  -- Q_{jℓ} = -(1-α)/2 · A_{jℓ}/(√dj · √dℓ)
  -- j ∉ ∂S (since j ∈ Ext(S)), so ℓ ≠ j for all ℓ ∈ ∂S
  have hj_not_bdry : j ∉ G.bdry S := by
    simp only [Graph.exterior, Finset.mem_filter] at hj_ext; exact hj_ext.2.2
  have hj_ne_bdry : ∀ ℓ ∈ G.bdry S, j ≠ ℓ := by
    intro ℓ hℓ h; rw [h] at hj_not_bdry; exact hj_not_bdry hℓ
  -- Step 6: Expand Q entries, factor, and bound.
  rw [hfwd_eq, abs_neg, hsum_reduce]
  -- Goal: |Σ_{ℓ∈∂S} Q_{jℓ}·y_ℓ| ≤ 2αρ·sqrtDeg j
  -- Step 6a: Replace Q_{jℓ} with off-diagonal formula for each ℓ ∈ ∂S
  have hQ_expand : ∀ ℓ ∈ G.bdry S, G.Qentry α j ℓ =
      -(1 - α) / 2 * G.A j ℓ / (G.sqrtDeg j * G.sqrtDeg ℓ) := by
    intro ℓ hℓ; unfold Graph.Qentry; exact if_neg (hj_ne_bdry ℓ hℓ)
  have hsum_expand : ∑ ℓ ∈ G.bdry S, G.Qentry α j ℓ * y ℓ =
      -(1 - α) / (2 * G.sqrtDeg j) *
        ∑ ℓ ∈ G.bdry S, G.A j ℓ * y ℓ / G.sqrtDeg ℓ := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro ℓ hℓ
    rw [hQ_expand ℓ hℓ]; rw [div_mul_eq_mul_div]
    have hsd := G.sqrtDeg_ne_zero ℓ; have hsdj := G.sqrtDeg_ne_zero j
    field_simp
  rw [hsum_expand]
  -- Step 6b: |c · Σ(...)| = |c| · |Σ(...)|
  rw [abs_mul]
  -- Step 6c: |c| = (1-α)/(2·sqrtDeg j) ≥ 0
  have hcoeff_nn : 0 ≤ (1 - α) / (2 * G.sqrtDeg j) :=
    div_nonneg (sub_nonneg.mpr hα1) (mul_nonneg (by norm_num) (le_of_lt (G.sqrtDeg_pos j)))
  have hcoeff_neg : -(1 - α) / (2 * G.sqrtDeg j) ≤ 0 := by
    rw [neg_div]; exact neg_nonpos.mpr hcoeff_nn
  rw [abs_of_nonpos hcoeff_neg]; simp only [neg_div, neg_neg]
  -- Goal: (1-α)/(2·sqrtDeg j) · |Σ A·y/√d| ≤ 2αρ·sqrtDeg j
  -- Step 6d: Triangle inequality: |Σ A·y/√d| ≤ Σ A·|y|/√d
  have h_tri : |∑ ℓ ∈ G.bdry S, G.A j ℓ * y ℓ / G.sqrtDeg ℓ| ≤
      ∑ ℓ ∈ G.bdry S, G.A j ℓ * |y ℓ| / G.sqrtDeg ℓ := by
    calc |∑ ℓ ∈ G.bdry S, G.A j ℓ * y ℓ / G.sqrtDeg ℓ|
        ≤ ∑ ℓ ∈ G.bdry S, |G.A j ℓ * y ℓ / G.sqrtDeg ℓ| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ ℓ ∈ G.bdry S, G.A j ℓ * |y ℓ| / G.sqrtDeg ℓ := by
          congr 1; ext ℓ
          rw [abs_div, abs_mul, abs_of_nonneg (G.A_nonneg j ℓ),
              abs_of_pos (G.sqrtDeg_pos ℓ)]
  -- Step 6e: Suffices to show (1-α)/(2√dj) · Σ A·|y|/√d ≤ 2αρ√dj
  calc (1 - α) / (2 * G.sqrtDeg j) *
          |∑ ℓ ∈ G.bdry S, G.A j ℓ * y ℓ / G.sqrtDeg ℓ|
      ≤ (1 - α) / (2 * G.sqrtDeg j) *
          (∑ ℓ ∈ G.bdry S, G.A j ℓ * |y ℓ| / G.sqrtDeg ℓ) := by
        apply mul_le_mul_of_nonneg_left h_tri hcoeff_nn
    _ ≤ 1 * 2 * α * ρ * G.sqrtDeg j := by
        -- === KEY INTERMEDIATE BOUNDS ===
        have hsd_j := G.sqrtDeg_pos j
        have hdeg_j := G.deg_pos' j
        have hsd_sq : G.sqrtDeg j ^ 2 = G.deg j := Real.sq_sqrt (le_of_lt hdeg_j)
        -- (A) normSq y ≤ 44 (from parallelogram inequality + hypotheses)
        have hy_sq : normSq y ≤ 44 := by
          have h := normSq_add_le (fun i => y i - xB i) xB
          have heq : (fun i => (y i - xB i) + xB i) = y := funext fun i => by ring
          rw [heq] at h; linarith
        -- (B) d_min > 0 (all degrees are positive)
        have hd_min_pos : 0 < G.minDegIn (G.bdry S) hbdry := by
          unfold Graph.minDegIn
          rw [Finset.lt_inf'_iff]; intro i _; exact G.deg_pos' i
        -- (C) Handle α = 1 case (coefficient vanishes)
        rcases eq_or_lt_of_le hα1 with rfl | hα_lt1
        · -- α = 1: (1-α)/(2√dj) = 0, so LHS = 0 ≤ 2·1·ρ·√dj
          have : (1 : ℝ) - 1 = 0 := sub_self 1
          simp only [this, zero_div, zero_mul]; positivity
        · -- (D) α < 1: Cauchy-Schwarz + exposure chain
          have h1α_pos : 0 < 1 - α := sub_pos.mpr hα_lt1
          -- (D.1) Squared inner sum bound (Cauchy-Schwarz + pointwise estimates)
          -- (Σ A·|y|/√d)² ≤ nbrsInCount · normSq(y) / d_min
          have h_sq_bound :
              (∑ ℓ ∈ G.bdry S, G.A j ℓ * |y ℓ| / G.sqrtDeg ℓ) ^ 2 ≤
              ↑(G.nbrsInCount j (G.bdry S)) / G.minDegIn (G.bdry S) hbdry *
              normSq y := by
            -- Apply CS: (Σ ab)² ≤ (Σ a²)(Σ b²) with a=√A, b=√A·|y|/√d
            have hcs := cauchy_schwarz_sum (G.bdry S)
              (fun ℓ => Real.sqrt (G.A j ℓ))
              (fun ℓ => Real.sqrt (G.A j ℓ) * |y ℓ| / G.sqrtDeg ℓ)
            -- LHS of CS = our LHS: √A · (√A·|y|/√d) = A·|y|/√d
            have hlhs : ∑ ℓ ∈ G.bdry S,
                Real.sqrt (G.A j ℓ) * (Real.sqrt (G.A j ℓ) * |y ℓ| / G.sqrtDeg ℓ) =
                ∑ ℓ ∈ G.bdry S, G.A j ℓ * |y ℓ| / G.sqrtDeg ℓ :=
              Finset.sum_congr rfl fun ℓ _ => by
                rw [← mul_div_assoc, ← mul_assoc, Real.mul_self_sqrt (G.A_nonneg j ℓ)]
            rw [hlhs] at hcs
            -- First factor: (√A)² = A
            have hf_eq : ∑ ℓ ∈ G.bdry S, Real.sqrt (G.A j ℓ) ^ 2 =
                ∑ ℓ ∈ G.bdry S, G.A j ℓ :=
              Finset.sum_congr rfl fun ℓ _ => Real.sq_sqrt (G.A_nonneg j ℓ)
            -- Second factor: (√A·|y|/√d)² = A·y²/d
            have hs_eq : ∑ ℓ ∈ G.bdry S,
                (Real.sqrt (G.A j ℓ) * |y ℓ| / G.sqrtDeg ℓ) ^ 2 =
                ∑ ℓ ∈ G.bdry S, G.A j ℓ * (y ℓ) ^ 2 / G.deg ℓ :=
              Finset.sum_congr rfl fun ℓ _ => by
                rw [div_pow, mul_pow, Real.sq_sqrt (G.A_nonneg j ℓ), sq_abs]
                unfold Graph.sqrtDeg; rw [Real.sq_sqrt (le_of_lt (G.deg_pos' ℓ))]
            rw [hf_eq, hs_eq] at hcs
            -- hcs: (Σ A·|y|/√d)² ≤ (Σ A) · (Σ A·y²/d)
            -- Bound 1: Σ_{∂S} A_{jℓ} ≤ ↑nbrsInCount
            have h_A_le_count :
                ∑ ℓ ∈ G.bdry S, G.A j ℓ ≤ ↑(G.nbrsInCount j (G.bdry S)) := by
              rw [← Finset.sum_filter_add_sum_filter_not (G.bdry S)
                (fun ℓ => (0 : ℝ) < G.A j ℓ)]
              have hzsum : ∑ ℓ ∈ (G.bdry S).filter (fun ℓ => ¬((0 : ℝ) < G.A j ℓ)),
                  G.A j ℓ = 0 :=
                Finset.sum_eq_zero fun ℓ hℓ => by
                  simp only [Finset.mem_filter] at hℓ
                  exact le_antisymm (not_lt.mp hℓ.2) (G.A_nonneg j ℓ)
              rw [hzsum, add_zero]
              unfold Graph.nbrsInCount
              calc ∑ ℓ ∈ (G.bdry S).filter (fun ℓ => (0 : ℝ) < G.A j ℓ), G.A j ℓ
                  ≤ ∑ ℓ ∈ (G.bdry S).filter (fun ℓ => (0 : ℝ) < G.A j ℓ), (1 : ℝ) :=
                    Finset.sum_le_sum fun ℓ _ => hA_le j ℓ
                _ = ↑((G.bdry S).filter (fun ℓ => 0 < G.A j ℓ)).card := by
                    simp [Finset.sum_const, nsmul_eq_mul]
            -- Bound 2: Σ_{∂S} A·y²/d ≤ normSq(y) / d_min
            have h_Ay2d_le :
                ∑ ℓ ∈ G.bdry S, G.A j ℓ * (y ℓ) ^ 2 / G.deg ℓ ≤
                normSq y / G.minDegIn (G.bdry S) hbdry := by
              calc ∑ ℓ ∈ G.bdry S, G.A j ℓ * (y ℓ) ^ 2 / G.deg ℓ
                  ≤ ∑ ℓ ∈ G.bdry S, (y ℓ) ^ 2 / G.minDegIn (G.bdry S) hbdry := by
                    apply Finset.sum_le_sum; intro ℓ hℓ
                    -- Pointwise: A·y²/d ≤ y²/d_min (A ≤ 1 and d_min ≤ d)
                    rw [div_le_div_iff₀ (G.deg_pos' ℓ) hd_min_pos]
                    have h_min_le : G.minDegIn (G.bdry S) hbdry ≤ G.deg ℓ := Finset.inf'_le _ hℓ
                    have h_am := mul_le_mul_of_nonneg_right (hA_le j ℓ) (le_of_lt hd_min_pos)
                    nlinarith [sq_nonneg (y ℓ)]
                _ = (∑ ℓ ∈ G.bdry S, (y ℓ) ^ 2) / G.minDegIn (G.bdry S) hbdry :=
                    by rw [Finset.sum_div]
                _ ≤ normSq y / G.minDegIn (G.bdry S) hbdry := by
                    apply div_le_div_of_nonneg_right _ (le_of_lt hd_min_pos)
                    -- Σ_{∂S} y² ≤ Σ_all y² = normSq y
                    exact Finset.sum_le_sum_of_subset_of_nonneg
                      (Finset.subset_univ _) (fun i _ _ => sq_nonneg _)
            -- Combine: (Σ)² ≤ (Σ A)(Σ A·y²/d) ≤ nbrsInCount · normSq/d_min
            calc (∑ ℓ ∈ G.bdry S, G.A j ℓ * |y ℓ| / G.sqrtDeg ℓ) ^ 2
                ≤ (∑ ℓ ∈ G.bdry S, G.A j ℓ) *
                  (∑ ℓ ∈ G.bdry S, G.A j ℓ * (y ℓ) ^ 2 / G.deg ℓ) := hcs
              _ ≤ ↑(G.nbrsInCount j (G.bdry S)) *
                  (normSq y / G.minDegIn (G.bdry S) hbdry) :=
                  mul_le_mul h_A_le_count h_Ay2d_le
                    (Finset.sum_nonneg fun ℓ _ => div_nonneg (mul_nonneg (G.A_nonneg j ℓ) (sq_nonneg _)) (le_of_lt (G.deg_pos' ℓ)))
                    (Nat.cast_nonneg _)
              _ = ↑(G.nbrsInCount j (G.bdry S)) / G.minDegIn (G.bdry S) hbdry *
                  normSq y := by ring
          -- (D.2) Exposure bound: nbrsInCount/d_min ≤ (αρ/(2(1-α)))² · dj²
          have h_exp_bound :
              ↑(G.nbrsInCount j (G.bdry S)) / G.minDegIn (G.bdry S) hbdry ≤
              (α * ρ / (2 * (1 - α))) ^ 2 * G.deg j ^ 2 := by
            rw [div_le_iff₀ hd_min_pos]
            have h_exp := h_exposure j hj_ext
            -- h_exp: nbrsInCount/dj ≤ (αρ/(2(1-α)))²·dj·d_min
            -- Multiply by dj: nbrsInCount ≤ (αρ/(2(1-α)))²·dj·d_min·dj
            --                              = (αρ/(2(1-α)))²·dj²·d_min
            have h1 : ↑(G.nbrsInCount j (G.bdry S)) ≤
                (α * ρ / (2 * (1 - α))) ^ 2 * G.deg j *
                G.minDegIn (G.bdry S) hbdry * G.deg j := by
              rwa [div_le_iff₀ hdeg_j] at h_exp
            nlinarith [sq_nonneg (G.deg j)]
          -- (D.3) Combined: (Σ)² ≤ (αρ/(2(1-α)))²·dj²·normSq(y)
          have h_combined_sq :
              (∑ ℓ ∈ G.bdry S, G.A j ℓ * |y ℓ| / G.sqrtDeg ℓ) ^ 2 ≤
              (α * ρ / (2 * (1 - α))) ^ 2 * G.deg j ^ 2 * normSq y := by
            calc (∑ ℓ ∈ G.bdry S, G.A j ℓ * |y ℓ| / G.sqrtDeg ℓ) ^ 2
                ≤ ↑(G.nbrsInCount j (G.bdry S)) / G.minDegIn (G.bdry S) hbdry *
                  normSq y := h_sq_bound
              _ ≤ (α * ρ / (2 * (1 - α))) ^ 2 * G.deg j ^ 2 * normSq y := by
                  nlinarith [h_exp_bound, normSq_nonneg y]
          -- (D.4) Take sqrt: Σ ≤ αρ/(2(1-α)) · dj · √(normSq y)
          have h_inner_nn : 0 ≤ ∑ ℓ ∈ G.bdry S, G.A j ℓ * |y ℓ| / G.sqrtDeg ℓ :=
            Finset.sum_nonneg fun ℓ _ => div_nonneg (mul_nonneg (G.A_nonneg j ℓ) (abs_nonneg _)) (le_of_lt (G.sqrtDeg_pos ℓ))
          have h_rhs_nn : 0 ≤ α * ρ / (2 * (1 - α)) * G.deg j * Real.sqrt (normSq y) := by
            positivity
          have h_inner_bound :
              ∑ ℓ ∈ G.bdry S, G.A j ℓ * |y ℓ| / G.sqrtDeg ℓ ≤
              α * ρ / (2 * (1 - α)) * G.deg j * Real.sqrt (normSq y) := by
            rw [← Real.sqrt_sq h_inner_nn, ← Real.sqrt_sq h_rhs_nn]
            exact Real.sqrt_le_sqrt (by
              rw [mul_pow, mul_pow, Real.sq_sqrt (normSq_nonneg y)]
              exact h_combined_sq)
          -- (D.5) Assembly: (1-α)/(2√dj) · inner ≤ 2αρ√dj
          have h_sqrt_bound : Real.sqrt (normSq y) ≤ 8 := by
            calc Real.sqrt (normSq y) ≤ Real.sqrt 64 :=
                  Real.sqrt_le_sqrt (by linarith)
              _ = 8 := by
                  rw [show (64 : ℝ) = 8 ^ 2 from by norm_num]
                  exact Real.sqrt_sq (by norm_num)
          have hdj_over_sdj : G.deg j / G.sqrtDeg j = G.sqrtDeg j := by
            rw [← hsd_sq]; field_simp
          calc (1 - α) / (2 * G.sqrtDeg j) *
                  (∑ ℓ ∈ G.bdry S, G.A j ℓ * |y ℓ| / G.sqrtDeg ℓ)
              ≤ (1 - α) / (2 * G.sqrtDeg j) *
                  (α * ρ / (2 * (1 - α)) * G.deg j * Real.sqrt (normSq y)) := by
                apply mul_le_mul_of_nonneg_left h_inner_bound hcoeff_nn
            _ = α * ρ / 4 * (G.deg j / G.sqrtDeg j) * Real.sqrt (normSq y) := by
                field_simp; ring
            _ = α * ρ / 4 * G.sqrtDeg j * Real.sqrt (normSq y) := by
                rw [hdj_over_sdj]
            _ ≤ α * ρ / 4 * G.sqrtDeg j * 8 := by
                apply mul_le_mul_of_nonneg_left h_sqrt_bound; positivity
            _ = 1 * 2 * α * ρ * G.sqrtDeg j := by ring

/-- Theorem 4.4 (Boundary confinement): Under the no-percolation condition,
    all FISTA iterates on problem (B) remain supported in S ∪ ∂S.

    PROOF STRATEGY (Paper Appendix A.3):
    By induction on k. Base case: x₀ = 0 (support empty).

    Inductive step: Assume supp(x_k) ⊆ S ∪ ∂S. For any exterior node j:
    1. x_{B,j}* = 0 (since S_B ⊆ S) and x_{k,j} = 0 (inductive hypothesis)
    2. y_{k,j} = x_{k,j} + β(x_{k,j} - x_{k-1,j}) = 0
    3. |∇_j f(y_k)| = |Σ_ℓ Q_{jℓ} y_{k,ℓ}| (only ∂S neighbors contribute)
    4. By no-percolation condition and Cauchy-Schwarz:
       |∇_j f(y_k)| ≤ (1-α)/2 · (nbrs_in_∂S / d_j)^{1/2} · ‖y_k‖_{∂S}
    5. Combined with the degree bound: |∇_j f(y_k)| < 2αρ√d_j = threshold
    6. So x_{k+1,j} = softThresh(threshold, w_{k,j}) = 0.

    BLOCKERS: Requires Q ≼ I (Lipschitz gradient), induction on FISTA state,
    and graph-theoretic percolation analysis. -/
theorem boundary_confinement (G : Graph n) (α ρ : ℝ) (v : Fin n)
    (hα : 0 < α) (hα1 : α < 1) (hρ : 0 < ρ)
    -- Problem (B) minimizer
    (xB : Fin n → ℝ) (hB : G.IsMinimizer 2 α ρ (basisVec v) xB)
    -- Candidate superset S ⊇ S_B containing the seed
    (S : Finset (Fin n))
    (_hSB : vecSupp xB ⊆ S) (hv_in_S : v ∈ S)
    -- Boundary is nonempty
    (hbdry : (G.bdry S).Nonempty)
    -- No-percolation condition: for all exterior nodes i,
    -- |N({i}) ∩ ∂S| / d_i ≤ (αρ/(2(1−α)))² · d_i · d_{min ∂S}
    (h_exposure : ∀ i ∈ G.exterior S,
      (↑(G.nbrsInCount i (G.bdry S)) : ℝ) / G.deg i ≤
        (α * ρ / (2 * (1 - α))) ^ 2 * G.deg i * G.minDegIn (G.bdry S) hbdry)
    -- Unit-weight lower bound on seed degree (holds for unweighted graphs)
    (hd : 1 ≤ G.deg v)
    -- Unweighted graph: edge weights are 0 or 1 (paper assumes undirected, unweighted graphs)
    (hA_unw : ∀ i j, G.A i j = 0 ∨ G.A i j = 1)
    (k : ℕ) :
    -- All iterates stay in S ∪ ∂S
    vecSupp (fistaX G 2 α ρ (basisVec v) k) ⊆ S ∪ G.bdry S := by
  -- Proof by strong induction on k (Paper Appendix A.3, pages 14-15).
  -- Strengthen: both components of fistaState have support in S ∪ ∂S.
  -- fistaState k = (x_{k-1}, x_k); fistaX k = (fistaState k).2.
  suffices h_inv : ∀ k,
      (∀ j, (fistaState G 2 α ρ (basisVec v) k).1 j ≠ 0 → j ∈ S ∪ G.bdry S) ∧
      (∀ j, (fistaState G 2 α ρ (basisVec v) k).2 j ≠ 0 → j ∈ S ∪ G.bdry S) by
    intro j hj; rw [vecSupp, Finset.mem_filter] at hj; exact (h_inv k).2 j hj.2
  intro k; induction k with
  | zero =>
    -- Base case: fistaState 0 = (0, 0). Both components have empty support.
    constructor <;> intro j hj <;> exfalso <;> simp [fistaState] at hj
  | succ k ih =>
    constructor
    · -- (fistaState (k+1)).1 = (fistaState k).2 by definition
      intro j hj; simp only [fistaState] at hj; exact ih.2 j hj
    · -- Inductive step: show (fistaState (k+1)).2 j ≠ 0 → j ∈ S ∪ ∂S.
      -- (fistaState (k+1)).2 = proxMap(fwdStep(y_k)).
      -- For j ∈ Ext(S), we show proxMap returns 0.
      intro j hj
      -- If j ∈ S ∪ ∂S, we are done. Assume otherwise for contradiction.
      by_contra h_ext
      -- Step (a): j is in the exterior Ext(S)
      have hj_ext : j ∈ G.exterior S := by
        simp only [Graph.exterior, Finset.mem_filter]
        exact ⟨Finset.mem_univ _,
               fun h => h_ext (Finset.mem_union_left _ h),
               fun h => h_ext (Finset.mem_union_right _ h)⟩
      -- Step (b): j has NO neighbors in S (by definition of exterior)
      have hj_no_S_nbrs : ∀ ℓ, ℓ ∈ S → G.A j ℓ = 0 := by
        intro ℓ hℓ; by_contra hA
        push_neg at hA
        have hA_pos : 0 < G.A j ℓ := lt_of_le_of_ne (G.A_nonneg j ℓ) (Ne.symm hA)
        have : j ∈ G.bdry S := by
          simp only [Graph.bdry, Finset.mem_filter]
          exact ⟨Finset.mem_univ _,
                 fun h => h_ext (Finset.mem_union_left _ h),
                 ⟨ℓ, hℓ, hA_pos⟩⟩
        exact h_ext (Finset.mem_union_right _ this)
      -- Step (c): j ≠ v (since v ∈ S and j ∉ S)
      have hj_ne_v : j ≠ v := by
        intro h; subst h; exact h_ext (Finset.mem_union_left _ hv_in_S)
      -- Step (d): fistaX k vanishes at j (from ih, contrapositive)
      have hxk_j : (fistaState G 2 α ρ (basisVec v) k).2 j = 0 := by
        by_contra h; exact h_ext (ih.2 j h)
      -- Step (e): Previous iterate vanishes at j (from ih)
      have hprev_j : (fistaState G 2 α ρ (basisVec v) k).1 j = 0 := by
        by_contra h; exact h_ext (ih.1 j h)
      -- Step (f): y_k vanishes at j (y_k = x_k + β(x_k - x_{k-1}) and both = 0)
      have hyk_j : fistaY G 2 α ρ (basisVec v) k j = 0 := by
        simp only [fistaY]; rw [hxk_j, hprev_j]; ring
      -- Step (g): (basisVec v)_j = 0 since j ≠ v
      have hbasis_j : basisVec v j = 0 := by
        simp only [basisVec]; exact if_neg hj_ne_v
      -- Step (h): The gradient at y_k, coordinate j, involves only ∂S neighbors.
      -- Since y_{k,j}=0, (basisVec v)_j=0, and A_{jℓ}=0 for ℓ∈S:
      --   gradf(y_k)_j = Σ_{ℓ∈∂S} Q_{jℓ} · y_{k,ℓ}
      -- And the forward step u(y_k)_j = -gradf(y_k)_j.
      --
      -- Step (i): |u(y_k)_j| ≤ (1-α)/(2√d_j) · Σ_{ℓ∈N(j)∩∂S} |y_{k,ℓ}|/√d_ℓ
      -- Step (j): By Cauchy-Schwarz:
      --   ≤ (1-α)/(2√d_j) · √(|N(j)∩∂S|/d_{min∂S}) · ‖y_k‖₂
      -- Step (k): By exposure condition (h_exposure):
      --   √(|N(j)∩∂S|/d_{min∂S}) ≤ αρ/(2(1-α)) · d_j
      -- Step (l): By Corollary A.3 + triangle inequality:
      --   ‖y_k‖₂ ≤ ‖y_k - x*_B‖₂ + ‖x*_B‖₂ ≤ √20 + 1
      -- Step (m): Combining: |u(y_k)_j| ≤ αρ√d_j/4 · (√20+1) < 2αρ√d_j
      -- Step (n): threshold = 1·2·α·ρ·√d_j = 2αρ√d_j, so proxMap returns 0.
      --
      -- The proxMap output is softThresh(2αρ√d_j, u(y_k)_j).
      -- Since |u(y_k)_j| ≤ 2αρ√d_j, softThresh returns 0.
      -- This contradicts hj (nonzero output).
      --
      -- The Cauchy-Schwarz chain (steps i-m) is a ~40-line algebraic argument.
      -- It requires: Finset.inner_mul_le_norm_mul, the exposure bound h_exposure,
      -- and the norm bounds fista_yk_uniform_bound/fista_y0_bound.
      -- The algebraic chain uses Cauchy-Schwarz + exposure + norm bounds.
      -- All proof steps are complete (induction, exterior membership, vanishing, CS chain).
      -- Step (h'): y_k vanishes at ALL exterior nodes (needed for sum simplification)
      have hyk_ext : ∀ ℓ, ℓ ∈ G.exterior S → fistaY G 2 α ρ (basisVec v) k ℓ = 0 := by
        intro ℓ hℓ_ext
        have hℓ_notS : ℓ ∉ S := by
          simp only [Graph.exterior, Finset.mem_filter] at hℓ_ext; exact hℓ_ext.2.1
        have hℓ_notBdryS : ℓ ∉ G.bdry S := by
          simp only [Graph.exterior, Finset.mem_filter] at hℓ_ext; exact hℓ_ext.2.2
        have hℓ_notSU : ℓ ∉ S ∪ G.bdry S := by
          simp only [Finset.mem_union]; push_neg; exact ⟨hℓ_notS, hℓ_notBdryS⟩
        have h2 : (fistaState G 2 α ρ (basisVec v) k).2 ℓ = 0 := by
          by_contra h; exact hℓ_notSU (ih.2 ℓ h)
        have h1 : (fistaState G 2 α ρ (basisVec v) k).1 ℓ = 0 := by
          by_contra h; exact hℓ_notSU (ih.1 ℓ h)
        simp only [fistaY]; rw [h2, h1]; ring
      -- Step (i): y_k vanishes outside S ∪ ∂S (combine with support info)
      have hy_supp : ∀ ℓ, ℓ ∉ S ∪ G.bdry S →
          fistaY G 2 α ρ (basisVec v) k ℓ = 0 := by
        intro ℓ hℓ
        apply hyk_ext
        simp only [Graph.exterior, Finset.mem_filter, Finset.mem_union] at hℓ ⊢
        push_neg at hℓ; exact ⟨Finset.mem_univ _, hℓ.1, hℓ.2⟩
      -- Step (j): Apply the exterior forward-step bound (helper lemma)
      set y := fistaY G 2 α ρ (basisVec v) k with hy_def
      -- Norm bounds needed by the helper
      have hy_norm := fista_yk_uniform_bound G 2 α ρ v hα (le_of_lt hα1) hρ (by norm_num : (0 : ℝ) < 2) hd xB hB k
      -- normSq xB ≤ 2: from fista_y0_bound (fistaY 0 = 0, so ‖0-xB‖² = ‖xB‖² ≤ 2)
      have hxB_norm : normSq xB ≤ 2 := by
        have h := fista_y0_bound_two G 2 α ρ v hα (le_of_lt hα1) hρ (by norm_num : (0 : ℝ) < 2) hd xB hB
        have heq : normSq (fun i => fistaY G 2 α ρ (basisVec v) 0 i - xB i) =
            normSq xB := by
          unfold normSq; congr 1; ext i; dsimp only
          have : fistaY G 2 α ρ (basisVec v) 0 i = 0 := by
            simp [fistaY, fistaState, fistaMom]
          rw [this, zero_sub, neg_sq]
        linarith
      -- The helper applies since y=fistaY k, which vanishes outside S ∪ ∂S
      -- and at j (exterior node), with the exposure condition satisfied.
      have hfwd_le_thresh := exterior_fwdStep_bound G α ρ v hα (le_of_lt hα1) hρ xB hB
        S hv_in_S hbdry h_exposure hd hA_unw y hy_supp
        (by rw [hy_def]; exact hy_norm) hxB_norm
        j hj_ext hyk_j
      -- Now: proxMap returns 0 since |fwdStep_j| ≤ threshold.
      -- (fistaState (k+1)).2 j = proxMap(...) j = softThresh(threshold, fwdStep_j)
      -- But softThresh(t, w) = 0 when |w| ≤ t. Contradiction with hj.
      apply hj
      simp only [fistaState]
      show G.proxMap 2 α ρ 1 (fun i => G.fwdStep α 1 (basisVec v)
        (fistaY G 2 α ρ (basisVec v) k) i) j = 0
      unfold Graph.proxMap softThresh
      split_ifs with h1 h2
      · -- fwdStep > threshold: contradicts |fwdStep| ≤ threshold
        exfalso
        have hle := le_abs_self (G.fwdStep α 1 (basisVec v)
          (fistaY G 2 α ρ (basisVec v) k) j)
        linarith [hfwd_le_thresh]
      · -- fwdStep < -threshold: contradicts |fwdStep| ≤ threshold
        exfalso
        have hle := neg_abs_le (G.fwdStep α 1 (basisVec v)
          (fistaY G 2 α ρ (basisVec v) k) j)
        linarith [hfwd_le_thresh]
      · -- |fwdStep| ≤ threshold: softThresh returns 0
        rfl

/-! ## Result 10: Degree Cutoff (Proposition A.8)

Large-degree nodes do not activate under over-regularization. If x_{A,i}* = 0
and d_i ≥ (R/(αρ))² (where R bounds ‖y_k − x*_B‖), then FISTA on
problem (B) never activates node i. -/

/- Proposition A.8 (Degree cutoff): Nodes with degree ≥ (R/(αρ))² that are
    (A)-inactive are never activated by FISTA on problem (B).

    PROOF STRATEGY (Paper Appendix B, Proposition B.1):
    Step 1: From path_monotone (ρ < 2ρ): x*_A ≥ x*_B ≥ 0 and x*_{A,i} = 0 ⟹ x*_{B,i} = 0.

    Step 2: M-matrix gradient comparison. Since Q_{jℓ} ≤ 0 for j ≠ ℓ and Δx = x*_A - x*_B ≥ 0:
      ∇_i f(x*_B) - ∇_i f(x*_A) = (Q·Δx)_i = Σ_{j≠i} Q_{ij}·Δx_j ≤ 0 (since Q_{ij} ≤ 0, Δx_j ≥ 0)
      Wait: (Q·Δx)_i = Q_{ii}·0 + Σ_{j≠i} Q_{ij}·Δx_j. Since Δx_i = 0 and Q_{ij} ≤ 0 for j≠i:
      ∇_i f(x*_B) - ∇_i f(x*_A) = -Σ_{j≠i} Q_{ij}·Δx_j ≥ 0.
      So |∇_i f(x*_B)| ≤ |∇_i f(x*_A)| ≤ αρ√d_i (by KKT for problem (A)).

    Step 3: Induction on k. Base: x₀ = 0. Inductive: if x_k,i = x_{k-1,i} = 0 then y_k,i = 0.
      |∇_i f(y_k)| ≤ |∇_i f(x*_B)| + ‖∇f(y_k) - ∇f(x*_B)‖₂
                   ≤ αρ√d_i + ‖y_k - x*_B‖₂  (1-smoothness: L=1)
                   ≤ αρ√d_i + R ≤ 2αρ√d_i     (since R ≤ αρ√d_i from d_i ≥ (R/(αρ))²)
      Threshold = 2αρ√d_i (c=2), so softThresh kills it: x_{k+1,i} = 0.

    Uses path_monotone and Q ≼ I (gradient Lipschitz, proved as gradf_coord_lipschitz). -/

/- Coordinate-wise gradient Lipschitz: |(Qz)_i|² ≤ ‖z‖² for unweighted graphs.
    Proof: Cauchy-Schwarz gives |(Qz)_i|² ≤ (Σ_j Q_{ij}²)·‖z‖².
    For unweighted graphs: Σ_j Q_{ij}² ≤ (1+α²)/2 ≤ 1. -/
set_option maxHeartbeats 1600000 in
lemma gradf_coord_lipschitz (G : Graph n) (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    -- Unweighted graph: edge weights are 0 or 1 (paper assumes undirected, unweighted graphs)
    (hA_unw : ∀ i j, G.A i j = 0 ∨ G.A i j = 1)
    -- Degree lower bound: d_j ≥ 1 (holds for unweighted graphs with integer degrees)
    (hd_ge : ∀ j, 1 ≤ G.deg j)
    (z : Fin n → ℝ) (i : Fin n) :
    (∑ j, G.Qentry α i j * z j) ^ 2 ≤ normSq z := by
  have hA_le : ∀ i j, G.A i j ≤ 1 := fun i j => by
    rcases hA_unw i j with h | h <;> simp [h]
  -- Step 1: Cauchy-Schwarz: (Σ Q_{ij}·z_j)² ≤ (Σ Q_{ij}²)·(Σ z_j²)
  have hcs := cauchy_schwarz_sum Finset.univ (fun j => G.Qentry α i j) z
  -- In Lean 4, ∑ i ∈ Finset.univ, f i = ∑ i, f i (definitionally or by simp)
  -- ∑ i ∈ Finset.univ, f i is definitionally ∑ i, f i
  -- Step 2: Σ Q_{ij}² ≤ 1
  suffices h_Q_sq_le : ∑ j : Fin n, G.Qentry α i j ^ 2 ≤ 1 by
    calc (∑ j, G.Qentry α i j * z j) ^ 2
        ≤ (∑ j, G.Qentry α i j ^ 2) * (∑ j, z j ^ 2) := hcs
      _ ≤ 1 * normSq z := by
          apply mul_le_mul_of_nonneg_right h_Q_sq_le (normSq_nonneg z)
      _ = normSq z := one_mul _
  -- Step 3: Bound Σ Q_{ij}² = Q_{ii}² + Σ_{j≠i} Q_{ij}²
  -- Separate the diagonal term
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  -- Q_{ii}² = ((1+α)/2)²
  have hQii : G.Qentry α i i = (1 + α) / 2 := by unfold Graph.Qentry; simp
  -- Σ_{j≠i} Q_{ij}² = ((1-α)/2)² · Σ_{j≠i} A_{ij}²/(d_i·d_j)
  -- For unweighted: A² = A, so ≤ ((1-α)/2)² · (1/d_i)·Σ_{j~i} 1/d_j ≤ ((1-α)/2)² · 1
  have hoff : ∑ j ∈ Finset.univ.erase i, G.Qentry α i j ^ 2 ≤ ((1 - α) / 2) ^ 2 := by
    calc ∑ j ∈ Finset.univ.erase i, G.Qentry α i j ^ 2
        = ∑ j ∈ Finset.univ.erase i,
            ((1 - α) / 2 * G.A i j / (G.sqrtDeg i * G.sqrtDeg j)) ^ 2 := by
          apply Finset.sum_congr rfl; intro j hj
          have hij : j ≠ i := Finset.ne_of_mem_erase hj
          unfold Graph.Qentry; rw [if_neg hij.symm]; ring
      _ = ∑ j ∈ Finset.univ.erase i,
            ((1 - α) / 2) ^ 2 * G.A i j ^ 2 / (G.deg i * G.deg j) := by
          apply Finset.sum_congr rfl; intro j _
          unfold Graph.sqrtDeg
          have hdi := le_of_lt (G.deg_pos' i)
          have hdj := le_of_lt (G.deg_pos' j)
          rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt hdi, Real.sq_sqrt hdj]
      _ ≤ ∑ j ∈ Finset.univ.erase i,
            ((1 - α) / 2) ^ 2 * G.A i j / (G.deg i * G.deg j) := by
          apply Finset.sum_le_sum; intro j _
          apply div_le_div_of_nonneg_right _ (mul_nonneg (le_of_lt (G.deg_pos i)) (le_of_lt (G.deg_pos j)))
          apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
          calc G.A i j ^ 2 = G.A i j * G.A i j := sq (G.A i j)
            _ ≤ G.A i j * 1 := by nlinarith [hA_le i j, G.A_nonneg i j]
            _ = G.A i j := mul_one _
      _ = ((1 - α) / 2) ^ 2 *
            ∑ j ∈ Finset.univ.erase i, G.A i j / (G.deg i * G.deg j) := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
      _ ≤ ((1 - α) / 2) ^ 2 * 1 := by
          apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
          -- Σ_{j≠i} A_{ij}/(d_i·d_j) ≤ 1
          -- = (1/d_i) · Σ_{j≠i} A_{ij}/d_j ≤ (1/d_i) · Σ_j A_{ij} = 1
          calc ∑ j ∈ Finset.univ.erase i, G.A i j / (G.deg i * G.deg j)
              = (1 / G.deg i) * ∑ j ∈ Finset.univ.erase i, G.A i j / G.deg j := by
                rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _
                field_simp
            _ ≤ (1 / G.deg i) * ∑ j ∈ Finset.univ.erase i, G.A i j := by
                apply mul_le_mul_of_nonneg_left _ (one_div_nonneg.mpr (le_of_lt (G.deg_pos i)))
                apply Finset.sum_le_sum; intro j _
                rw [div_le_iff₀ (G.deg_pos' j)]
                -- Goal: G.A i j ≤ G.A i j * G.deg j
                -- From hd_ge: 1 ≤ G.deg j, so A * 1 ≤ A * d_j
                exact le_mul_of_one_le_right (G.A_nonneg i j) (hd_ge j)
            _ ≤ (1 / G.deg i) * G.deg i := by
                apply mul_le_mul_of_nonneg_left _ (one_div_nonneg.mpr (le_of_lt (G.deg_pos i)))
                calc ∑ j ∈ Finset.univ.erase i, G.A i j
                    ≤ ∑ j, G.A i j := Finset.sum_le_sum_of_subset_of_nonneg
                        (Finset.erase_subset _ _) (fun j _ _ => G.A_nonneg i j)
                  _ = G.deg i := rfl
            _ = 1 := by rw [one_div, inv_mul_cancel₀ (ne_of_gt (G.deg_pos i))]
      _ = ((1 - α) / 2) ^ 2 := mul_one _
  -- Step 4: Combine: Q_{ii}² + Σ_{j≠i} Q_{ij}² ≤ ((1+α)/2)² + ((1-α)/2)² = (1+α²)/2 ≤ 1
  rw [hQii]
  calc ((1 + α) / 2) ^ 2 + ∑ j ∈ Finset.univ.erase i, G.Qentry α i j ^ 2
      ≤ ((1 + α) / 2) ^ 2 + ((1 - α) / 2) ^ 2 := by linarith
    _ = (1 + α ^ 2) / 2 := by ring
    _ ≤ 1 := by nlinarith [sq_nonneg α]

/-- Coordinate-wise gradient bound: for any x, y,
    |∇_i f(y) - ∇_i f(x)| ≤ ‖y - x‖.
    Uses gradf_coord_lipschitz (Q ≼ I coordinatewise). -/
lemma gradf_coord_bound (G : Graph n) (α : ℝ) (s : Fin n → ℝ)
    (hα : 0 < α) (hα1 : α ≤ 1) (hA_unw : ∀ i j, G.A i j = 0 ∨ G.A i j = 1)
    (hd_ge : ∀ j, 1 ≤ G.deg j)
    (x y : Fin n → ℝ) (i : Fin n) :
    |G.gradf α s y i - G.gradf α s x i| ≤ Real.sqrt (normSq (fun j => y j - x j)) := by
  -- ∇f(y)_i - ∇f(x)_i = (Q(y-x))_i = Σ_j Q_{ij}·(y_j - x_j)
  have hgradf_diff : G.gradf α s y i - G.gradf α s x i =
      ∑ j, G.Qentry α i j * (y j - x j) := by
    unfold Graph.gradf; simp [Finset.sum_sub_distrib, mul_sub]
  rw [hgradf_diff]
  -- |(Q·δ)_i| ≤ √(normSq δ) by gradf_coord_lipschitz
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (gradf_coord_lipschitz G α hα hα1 hA_unw hd_ge _ i)

set_option maxHeartbeats 800000 in
theorem degree_cutoff (G : Graph n) (α ρ R : ℝ) (v : Fin n)
    (hα : 0 < α) (hα1 : α ≤ 1) (hρ : 0 < ρ) (hR : 0 < R)
    -- Problem (A) minimizer
    (xA : Fin n → ℝ) (hA : G.IsMinimizer 1 α ρ (basisVec v) xA)
    -- Problem (B) minimizer
    (xB : Fin n → ℝ) (hB : G.IsMinimizer 2 α ρ (basisVec v) xB)
    -- R is an upper bound on ‖y_k − x*_B‖
    (hR_bound : ∀ k, normSq (fun j => fistaY G 2 α ρ (basisVec v) k j - xB j) ≤ R ^ 2)
    -- Unweighted graph: edge weights are 0 or 1 (paper assumes undirected, unweighted graphs)
    (hA_unw : ∀ i j, G.A i j = 0 ∨ G.A i j = 1)
    -- Degree lower bound (holds for unweighted graphs: degrees are positive integers)
    (hd_ge : ∀ j, 1 ≤ G.deg j)
    -- Coordinate i
    (i : Fin n) (hi_inactiveA : xA i = 0)
    -- Degree condition: d_i ≥ (R/(αρ))²
    (hdeg : (R / (α * ρ)) ^ 2 ≤ G.deg i) :
    -- Node i is never activated
    ∀ k, fistaX G 2 α ρ (basisVec v) k i = 0 ∧
         fistaY G 2 α ρ (basisVec v) k i = 0 := by
  have hA_nonneg := minimizer_nonneg G 1 α ρ (basisVec v) xA hA
  have hB_nonneg := minimizer_nonneg G 2 α ρ (basisVec v) xB hB
  -- === GRADIENT BOUND at x*_B (Proposition B.1 of Fountoulakis & Martínez-Rubio) ===
  -- Uses path_monotone (Lemma 4 of Ha, Fountoulakis & Mahoney, JMLR 2021).
  -- The proof follows Section C.3 of HFM2021: Q⁻¹_{A,A} ≥ 0 via Neumann series
  -- Q⁻¹ = 2/(1+α) · D⁻¹ᐟ² [Σ_{k≥0} ((1-α)/(1+α))^k · M^k] D⁻¹ᐟ²
  -- where M = (D⁻¹ᐟ²AD⁻¹ᐟ²)_{A,A} ≥ 0 entrywise.
  --
  -- Step 1: Convert IsMinimizer 2 α ρ to IsMinimizer 1 α (2*ρ)
  have hB_conv : G.IsMinimizer 1 α (2 * ρ) (basisVec v) xB := by
    intro x; have := hB x
    -- FObj 2 α ρ s x = FObj 1 α (2*ρ) s x since gReg 2 α ρ = gReg 1 α (2*ρ)
    simp only [Graph.FObj, Graph.gReg] at this ⊢; linarith
  -- Step 2: path_monotone gives xB ≤ xA (since ρ < 2*ρ)
  have hs_nn : ∀ j, 0 ≤ basisVec v j := fun j => by
    simp only [basisVec]; split_ifs <;> norm_num
  have hmon := path_monotone G α ρ (2 * ρ) (basisVec v) hα hα1 (le_of_lt hρ)
    (by linarith) hs_nn xA xB hA hB_conv
  -- Step 3: xB_i = 0 (since 0 ≤ xB_i ≤ xA_i = 0)
  have hxBi : xB i = 0 := le_antisymm (by linarith [hmon i]) (hB_nonneg i)
  -- Step 4: Gradient comparison (HFM2021, proof of Prop B.1)
  -- gradf(xB)_i - gradf(xA)_i = Σ_j Q_{ij}(xB_j - xA_j)
  -- = Q_{ii}·0 + Σ_{j≠i} Q_{ij}(xB_j - xA_j) ≥ 0
  -- (each term: Q_{ij} ≤ 0, xB_j - xA_j ≤ 0, product ≥ 0)
  have hgradf_compare : G.gradf α (basisVec v) xA i ≤ G.gradf α (basisVec v) xB i := by
    unfold Graph.gradf
    -- Both s terms cancel: same seed vector
    -- Need: Σ_j Q_{ij} xA_j ≤ Σ_j Q_{ij} xB_j
    -- i.e., Σ_j Q_{ij}(xA_j - xB_j) ≤ 0
    suffices h : ∑ j, G.Qentry α i j * xA j ≤ ∑ j, G.Qentry α i j * xB j by linarith
    -- Split into j = i and j ≠ i
    rw [← sub_nonneg]; simp only [← Finset.sum_sub_distrib, ← mul_sub]
    -- Goal: 0 ≤ Σ_j Q_{ij}(xB_j - xA_j)
    -- = Q_{ii}(xB_i - xA_i) + Σ_{j≠i} Q_{ij}(xB_j - xA_j)
    -- = Q_{ii}·0 + Σ_{j≠i} Q_{ij}(xB_j - xA_j)
    -- Each off-diag term: Q_{ij} ≤ 0 and xB_j - xA_j ≤ 0, so product ≥ 0
    apply Finset.sum_nonneg; intro j _
    by_cases hij : i = j
    · -- j = i: Q_{ii}(xB_i - xA_i) = Q_{ii}·0 = 0
      subst hij; rw [hxBi, hi_inactiveA, sub_self, mul_zero]
    · -- j ≠ i: Q_{ij} ≤ 0 and xB_j ≤ xA_j, so Q_{ij}(xB_j - xA_j) ≥ 0
      have hQ_nonpos : G.Qentry α i j ≤ 0 := by
        unfold Graph.Qentry; rw [if_neg hij]
        exact div_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonpos_of_nonneg (by linarith) (G.A_nonneg i j))
          (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      have hsub_nonpos : xB j - xA j ≤ 0 := sub_nonpos.mpr (hmon j)
      nlinarith [hQ_nonpos, hsub_nonpos]
  -- Step 5: Both gradients are ≤ 0 at inactive nonneg coordinates
  -- gradf(x*)_i = Σ_j Q_{ij} x*_j - α·invSqrtDeg·s_i
  -- = Σ_{j≠i} Q_{ij}·x*_j (since x*_i = 0 and we absorb the s term)
  -- Q_{ij} ≤ 0, x*_j ≥ 0 ⟹ each term ≤ 0. Also -α·invSqrtDeg·s_i ≤ 0.
  have hgA_nonpos : G.gradf α (basisVec v) xA i ≤ 0 := by
    unfold Graph.gradf
    have hQx_nonpos : ∑ j, G.Qentry α i j * xA j ≤ 0 := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
      have hdiag : G.Qentry α i i * xA i = 0 := by rw [hi_inactiveA, mul_zero]
      rw [hdiag, zero_add]
      apply Finset.sum_nonpos; intro j hj
      have hij : j ≠ i := Finset.ne_of_mem_erase hj
      exact mul_nonpos_of_nonpos_of_nonneg (by
        unfold Graph.Qentry; rw [if_neg hij.symm]
        exact div_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonpos_of_nonneg (by linarith) (G.A_nonneg i j))
          (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))) (hA_nonneg j)
    have hs_nonpos : -(α * G.invSqrtDeg i * basisVec v i) ≤ 0 := by
      simp only [neg_nonpos]; exact mul_nonneg (mul_nonneg (le_of_lt hα)
        (by unfold Graph.invSqrtDeg; positivity)) (hs_nn i)
    linarith
  -- Step 6: Gradient lower bound from minimality of xA
  -- For ε > 0: F_ρ(xA + ε·e_i) ≥ F_ρ(xA) implies gradf_i ≥ -αρ√d_i
  have hgA_lower : -(α * ρ * G.sqrtDeg i) ≤ G.gradf α (basisVec v) xA i := by
    -- Perturbation argument: if gradf_i < -αρ√d_i, then F(xA + ε·e_i) < F(xA)
    -- for small ε > 0, contradicting minimality.
    by_contra hlt; push_neg at hlt
    -- hlt : G.gradf α (basisVec v) xA i < -(α * ρ * G.sqrtDeg i)
    -- Test point: y = xA with y_i = ε for small ε > 0
    set g := G.gradf α (basisVec v) xA i + α * ρ * G.sqrtDeg i with hg_def
    have hg_neg : g < 0 := by unfold g; linarith
    have hQii : G.Qentry α i i = (1 + α) / 2 := by unfold Graph.Qentry; simp
    have hQii_pos : 0 < (1 + α) / 2 := by linarith
    -- Choose ε = -g / ((1+α)/2) > 0
    set ε := -g / ((1 + α) / 2) with hε_def
    have hε_pos : 0 < ε := by rw [hε_def]; exact div_pos (by linarith) hQii_pos
    -- Apply minimality to the test point y
    set y : Fin n → ℝ := fun j => if j = i then ε else xA j with hy_def
    have hmin_y := hA y
    -- Key: FObj(y) - FObj(xA) = ε·g + ε²/2·(1+α)/2
    -- At our ε: = -g²/((1+α)/2) + g²/(2·((1+α)/2)) = -g²/(2·((1+α)/2)) < 0
    -- This contradicts FObj(xA) ≤ FObj(y).
    --
    -- The expansion uses: y_j - xA_j = ε·δ_{ij} and xA_i = 0.
    -- fObj(y) = fObj(xA) + ε·gradf_i + ε²/2·Q_{ii}  [fObj_expansion]
    -- gReg(y) - gReg(xA) = αρ·√d_i·ε  [only i-th coordinate changes, from 0 to ε]
    -- So FObj(y) - FObj(xA) = ε·(gradf_i + αρ√d_i) + ε²/2·Q_{ii} = ε·g + ε²/2·Q_{ii}
    -- = (-g/Q_{ii})·g + (-g/Q_{ii})²/2·Q_{ii} = -g²/Q_{ii} + g²/(2Q_{ii}) = -g²/(2Q_{ii})
    -- Since g ≠ 0 and Q_{ii} > 0: this is < 0. Contradiction.
    --
    -- Formal proof of the expansion:
    -- Step A: fObj difference via fObj_expansion
    have hfexp := fObj_expansion G α (basisVec v) xA y
    -- y_j - xA_j simplification
    have hdiff : ∀ j, y j - xA j = if j = i then ε else 0 := fun j => by
      simp only [hy_def]; split_ifs with h
      · rw [h, hi_inactiveA]; ring
      · ring
    -- Gradient sum reduces to single term
    have hgsum : ∑ j, G.gradf α (basisVec v) xA j * (y j - xA j) =
        G.gradf α (basisVec v) xA i * ε := by
      rw [show ∑ j, G.gradf α (basisVec v) xA j * (y j - xA j) =
          ∑ j, G.gradf α (basisVec v) xA j * (if j = i then ε else 0) from
        Finset.sum_congr rfl fun j _ => by rw [hdiff]]
      simp [Finset.mem_univ]
    -- Quadratic sum reduces to ε²·Q_{ii}
    have hqinner : ∀ j, ∑ k, G.Qentry α j k * (y k - xA k) =
        G.Qentry α j i * ε := fun j => by
      rw [show ∑ k, G.Qentry α j k * (y k - xA k) =
          ∑ k, G.Qentry α j k * (if k = i then ε else 0) from
        Finset.sum_congr rfl fun k _ => by rw [hdiff]]
      simp [Finset.mem_univ, mul_comm]
    have hqsum : (1/2) * ∑ j, (y j - xA j) * (∑ k, G.Qentry α j k * (y k - xA k)) =
        ε ^ 2 / 2 * ((1 + α) / 2) := by
      simp_rw [hqinner]
      rw [show ∑ j, (y j - xA j) * (G.Qentry α j i * ε) =
          ∑ j, (if j = i then ε else 0) * (G.Qentry α j i * ε) from
        Finset.sum_congr rfl fun j _ => by rw [hdiff]]
      simp [Finset.sum_ite, Finset.mem_univ]; ring
    -- fObj difference
    have hfdiff : G.fObj α (basisVec v) y = G.fObj α (basisVec v) xA +
        G.gradf α (basisVec v) xA i * ε + ε ^ 2 / 2 * ((1 + α) / 2) := by
      linarith [hfexp, hgsum, hqsum]
    -- Step B: gReg difference
    have hgdiff : G.gReg 1 α ρ y - G.gReg 1 α ρ xA = α * ρ * G.sqrtDeg i * ε := by
      unfold Graph.gReg
      -- Factor: 1*α*ρ*(Σ sqrtDeg·|y|) - 1*α*ρ*(Σ sqrtDeg·|xA|)
      --       = α*ρ*(Σ sqrtDeg·|y| - Σ sqrtDeg·|xA|)
      --       = α*ρ*Σ(sqrtDeg·|y| - sqrtDeg·|xA|)
      have hsum_diff : ∑ j, G.sqrtDeg j * |y j| - ∑ j, G.sqrtDeg j * |xA j| =
          G.sqrtDeg i * ε := by
        rw [← Finset.sum_sub_distrib]
        rw [show ∑ j, (G.sqrtDeg j * |y j| - G.sqrtDeg j * |xA j|) =
            ∑ j, G.sqrtDeg j * (|y j| - |xA j|) from
          Finset.sum_congr rfl fun j _ => by ring]
        rw [show ∑ j, G.sqrtDeg j * (|y j| - |xA j|) =
            ∑ j, G.sqrtDeg j * (|if j = i then ε else xA j| - |xA j|) from rfl]
        conv_lhs =>
          arg 2; ext j
          rw [show |if j = i then ε else xA j| - |xA j| =
              if j = i then |ε| - |xA i| else 0 from by
            split_ifs with h
            · subst h; simp
            · simp]
        simp [Finset.mem_univ, hi_inactiveA,
              abs_of_pos hε_pos]
      have h1 : 1 * α * ρ * (∑ j, G.sqrtDeg j * |y j| - ∑ j, G.sqrtDeg j * |xA j|) =
          1 * α * ρ * (G.sqrtDeg i * ε) := by rw [hsum_diff]
      linarith
    -- Step C: FObj difference = ε·g + ε²/2·Q_{ii}
    have hFdiff : G.FObj 1 α ρ (basisVec v) y - G.FObj 1 α ρ (basisVec v) xA =
        g * ε + ε ^ 2 / 2 * ((1 + α) / 2) := by
      unfold Graph.FObj; linarith [hfdiff, hgdiff]
    -- Step D: At our ε, the difference = -g²/(2·(1+α)/2) < 0
    have hval : g * ε + ε ^ 2 / 2 * ((1 + α) / 2) = -(g ^ 2 / (2 * ((1 + α) / 2))) := by
      rw [hε_def]; field_simp; ring
    -- Contradiction: FObj(xA) ≤ FObj(y) but FObj(y) < FObj(xA)
    have hg_sq_pos : 0 < g ^ 2 := sq_pos_of_neg hg_neg
    have hdenom_pos : 0 < 2 * ((1 + α) / 2) := by linarith
    nlinarith [div_pos hg_sq_pos hdenom_pos, hmin_y, hFdiff, hval]
  -- Step 7: Combine to get |gradf(xB)_i| ≤ αρ√d_i
  have hgradf_xB_bound : |G.gradf α (basisVec v) xB i| ≤ α * ρ * G.sqrtDeg i := by
    -- From steps 4-6: -αρ√d_i ≤ gradf(xA)_i ≤ gradf(xB)_i ≤ 0
    -- So |gradf(xB)_i| = -gradf(xB)_i ≤ -gradf(xA)_i ≤ αρ√d_i
    rw [abs_le]; constructor
    · linarith [hgA_lower]  -- gradf(xB) ≥ gradf(xA) ≥ -αρ√d_i
    · -- gradf(xB) ≤ 0 ≤ αρ√d_i
      have hgB_nonpos : G.gradf α (basisVec v) xB i ≤ 0 := by
        unfold Graph.gradf
        have hQxB_nonpos : ∑ j, G.Qentry α i j * xB j ≤ 0 := by
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
          rw [show G.Qentry α i i * xB i = 0 from by rw [hxBi, mul_zero], zero_add]
          apply Finset.sum_nonpos; intro j hj
          have hij : j ≠ i := Finset.ne_of_mem_erase hj
          exact mul_nonpos_of_nonpos_of_nonneg (by
            unfold Graph.Qentry; rw [if_neg hij.symm]
            exact div_nonpos_of_nonpos_of_nonneg
              (mul_nonpos_of_nonpos_of_nonneg (by linarith) (G.A_nonneg i j))
              (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))) (hB_nonneg j)
        have hs_nonpos : -(α * G.invSqrtDeg i * basisVec v i) ≤ 0 := by
          simp only [neg_nonpos]; exact mul_nonneg (mul_nonneg (le_of_lt hα)
            (by unfold Graph.invSqrtDeg; positivity)) (hs_nn i)
        linarith
      calc G.gradf α (basisVec v) xB i ≤ 0 := hgB_nonpos
        _ ≤ α * ρ * G.sqrtDeg i := by positivity
  -- Key prerequisite: R ≤ αρ√d_i from the degree condition.
  have hR_le : R ≤ α * ρ * G.sqrtDeg i := by
    have hαρ_pos : 0 < α * ρ := mul_pos hα hρ
    have : R / (α * ρ) ≤ G.sqrtDeg i := by
      unfold Graph.sqrtDeg
      have h_div_nn : 0 ≤ R / (α * ρ) := div_nonneg (le_of_lt hR) (le_of_lt hαρ_pos)
      rw [← Real.sqrt_sq h_div_nn]
      exact Real.sqrt_le_sqrt hdeg
    calc R = α * ρ * (R / (α * ρ)) := by field_simp
      _ ≤ α * ρ * G.sqrtDeg i := by nlinarith [this]
  -- Main induction
  intro k; induction k with
  | zero =>
    -- Base case: fistaX 0 = 0 and fistaY 0 = 0
    exact ⟨by simp [fistaX, fistaState], by simp [fistaY, fistaState, fistaMom]⟩
  | succ k ihk =>
    obtain ⟨hxk, hyk⟩ := ihk
    -- Step 1: fistaX (k+1) i = 0.
    -- fistaX (k+1) = proxMap(fwdStep(fistaY k)).
    -- Since fistaY k i = 0 (from ihk):
    --   fwdStep(y_k)_i = 0 - 1·gradf(y_k)_i = -gradf(y_k)_i
    --
    -- Bound |gradf(y_k)_i|:
    -- |gradf(y_k)_i| = |gradf(y_k)_i - gradf(x*_B)_i + gradf(x*_B)_i|
    --                ≤ |gradf(y_k)_i - gradf(x*_B)_i| + |gradf(x*_B)_i|
    --
    -- For the first term: gradf(y_k) - gradf(x*_B) = Q(y_k - x*_B), so
    -- |gradf(y_k)_i - gradf(x*_B)_i| ≤ ‖Q(y_k - x*_B)‖ ≤ L·‖y_k - x*_B‖ ≤ R
    -- (using L-smoothness with L=1 and hR_bound).
    --
    -- For the second term: |gradf(x*_B)_i| ≤ αρ√d_i (from hgradf_xB_bound).
    --
    -- Combined: |gradf(y_k)_i| ≤ R + αρ√d_i ≤ 2αρ√d_i (using hR_le).
    -- Threshold = 1·2·α·ρ·√d_i = 2αρ√d_i.
    -- So softThresh(threshold, -gradf_i) = 0, giving fistaX (k+1) i = 0.
    --
    -- Step 2: fistaY (k+1) i = 0.
    -- y_{k+1,i} = x_{k+1,i} + β(x_{k+1,i} - x_{k,i}) = 0 + β(0 - 0) = 0.
    -- First prove fistaX (k+1) i = 0, then derive fistaY from it.
    suffices hxk1 : fistaX G 2 α ρ (basisVec v) (k + 1) i = 0 by
      exact ⟨hxk1, by rw [fistaY_succ]; rw [hxk1, hxk]; ring⟩
    -- fistaX (k+1) i = proxMap(fwdStep(fistaY k)) i
    -- = softThresh(2αρ√d_i, fwdStep(y_k)_i)
    -- Since y_{k,i} = 0: fwdStep(y_k)_i = -gradf(y_k)_i
    -- We bound |gradf(y_k)_i| ≤ 2αρ√d_i and conclude softThresh returns 0.
    set yk := fistaY G 2 α ρ (basisVec v) k
    -- Step A: Bound |gradf(y_k)_i - gradf(x*_B)_i| ≤ R using gradf_coord_bound
    have h_lip := gradf_coord_bound G α (basisVec v) hα hα1 hA_unw hd_ge xB yk i
    have h_norm_yk := hR_bound k
    have h_lip_R : |G.gradf α (basisVec v) yk i - G.gradf α (basisVec v) xB i| ≤ R := by
      calc |G.gradf α (basisVec v) yk i - G.gradf α (basisVec v) xB i|
          ≤ Real.sqrt (normSq (fun j => yk j - xB j)) := h_lip
        _ ≤ Real.sqrt (R ^ 2) := Real.sqrt_le_sqrt h_norm_yk
        _ = R := by rw [Real.sqrt_sq (le_of_lt hR)]
    -- Step B: Triangle inequality: |gradf(y_k)_i| ≤ |gradf(y_k) - gradf(xB)| + |gradf(xB)|
    have h_gradf_bound : |G.gradf α (basisVec v) yk i| ≤ 2 * α * ρ * G.sqrtDeg i := by
      calc |G.gradf α (basisVec v) yk i|
          = |(G.gradf α (basisVec v) yk i - G.gradf α (basisVec v) xB i) +
             G.gradf α (basisVec v) xB i| := by ring_nf
        _ ≤ |G.gradf α (basisVec v) yk i - G.gradf α (basisVec v) xB i| +
            |G.gradf α (basisVec v) xB i| := abs_add_le _ _
        _ ≤ R + α * ρ * G.sqrtDeg i := by linarith [h_lip_R, hgradf_xB_bound]
        _ ≤ α * ρ * G.sqrtDeg i + α * ρ * G.sqrtDeg i := by linarith [hR_le]
        _ = 2 * α * ρ * G.sqrtDeg i := by ring
    -- Step C: fwdStep(y_k)_i = -gradf(y_k)_i (since y_{k,i} = 0)
    have h_fwd_eq : G.fwdStep α 1 (basisVec v) yk i = -(G.gradf α (basisVec v) yk i) := by
      unfold Graph.fwdStep; rw [hyk]; ring
    -- Step D: |fwdStep(y_k)_i| ≤ threshold = 2αρ√d_i
    have h_fwd_bound : |G.fwdStep α 1 (basisVec v) yk i| ≤ 1 * 2 * α * ρ * G.sqrtDeg i := by
      rw [h_fwd_eq, abs_neg]; linarith [h_gradf_bound]
    -- Step E: proxMap returns 0 since |fwdStep| ≤ threshold
    show fistaX G 2 α ρ (basisVec v) (k + 1) i = 0
    -- fistaX (k+1) i unfolds to proxMap 2 α ρ 1 (fwdStep(yk)) i
    -- = softThresh(1*2*α*ρ*√d_i, fwdStep(yk)_i)
    -- Since |fwdStep| ≤ threshold, softThresh returns 0.
    simp only [fistaX, fistaState]
    show G.proxMap 2 α ρ 1 (fun j => G.fwdStep α 1 (basisVec v) yk j) i = 0
    unfold Graph.proxMap softThresh
    split_ifs with h1 h2
    · -- fwdStep > threshold: contradicts bound
      exfalso
      have hle := le_abs_self (G.fwdStep α 1 (basisVec v) yk i)
      linarith [h_fwd_bound]
    · -- fwdStep < -threshold: contradicts bound
      exfalso
      have hle := neg_abs_le (G.fwdStep α 1 (basisVec v) yk i)
      linarith [h_fwd_bound]
    · -- |fwdStep| ≤ threshold: softThresh returns 0
      rfl

end RPPR

end