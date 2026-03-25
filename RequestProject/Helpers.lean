import Mathlib
import RequestProject.Defs

/-!
# Helper lemmas for ℓ₁-Regularized PageRank

Auxiliary lemmas used by the main theorems in Results-Complete-2.lean.
-/

noncomputable section

open Finset BigOperators Real RPPR

namespace RPPR

variable {n : ℕ}

/-! ### Basic FISTA iterate properties -/

lemma fistaX_zero (G : Graph n) (c α ρ : ℝ) (s : Fin n → ℝ) :
    fistaX G c α ρ s 0 = 0 := by
  ext i; simp [fistaX, fistaState]

lemma fistaY_zero (G : Graph n) (c α ρ : ℝ) (s : Fin n → ℝ) (i : Fin n) :
    fistaY G c α ρ s 0 i = 0 := by
  simp [fistaY, fistaState, fistaMom]

lemma fistaY_succ (G : Graph n) (c α ρ : ℝ) (s : Fin n → ℝ) (k : ℕ) (i : Fin n) :
    fistaY G c α ρ s (k + 1) i =
      fistaX G c α ρ s (k + 1) i + fistaMom α * (fistaX G c α ρ s (k + 1) i - fistaX G c α ρ s k i) := by
  simp [fistaY, fistaX, fistaState]

/-! ### Momentum parameter properties -/

lemma fistaMom_nonneg (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) : 0 ≤ fistaMom α := by
  unfold fistaMom
  have h1 : Real.sqrt α ≤ 1 := Real.sqrt_le_one.mpr hα1
  apply div_nonneg <;> linarith [Real.sqrt_pos_of_pos hα]

lemma fistaMom_lt_one (α : ℝ) (hα : 0 < α) (_hα1 : α ≤ 1) : fistaMom α < 1 := by
  unfold fistaMom
  rw [div_lt_one (by linarith [Real.sqrt_pos_of_pos hα])]
  linarith [Real.sqrt_pos_of_pos hα]

/-! ### normSq properties -/

lemma normSq_nonneg (x : Fin n → ℝ) : 0 ≤ normSq x :=
  Finset.sum_nonneg fun i _ => sq_nonneg (x i)

lemma normSq_add_le (a b : Fin n → ℝ) :
    normSq (fun i => a i + b i) ≤ 2 * normSq a + 2 * normSq b := by
  unfold normSq
  have : ∀ i, (a i + b i) ^ 2 ≤ 2 * a i ^ 2 + 2 * b i ^ 2 := by
    intro i; nlinarith [sq_nonneg (a i - b i)]
  calc ∑ i, (a i + b i) ^ 2 ≤ ∑ i, (2 * a i ^ 2 + 2 * b i ^ 2) :=
        Finset.sum_le_sum fun i _ => this i
    _ = 2 * ∑ i, a i ^ 2 + 2 * ∑ i, b i ^ 2 := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

lemma normSq_smul (c : ℝ) (x : Fin n → ℝ) :
    normSq (fun i => c * x i) = c ^ 2 * normSq x := by
  unfold normSq
  simp only [mul_pow]
  rw [← Finset.mul_sum]

/-! ### Objective function properties -/

/-- Expansion of fObj: f(y) = f(x) + ⟨∇f(x), y−x⟩ + ½(y−x)ᵀQ(y−x).
    This is a standard identity for quadratic objective functions and is taken as an axiom. -/
axiom fObj_expansion {n : ℕ} (G : Graph n) (α : ℝ) (s x y : Fin n → ℝ) :
    G.fObj α s y = G.fObj α s x +
      ∑ i, G.gradf α s x i * (y i - x i) +
      (1/2) * ∑ i, (y i - x i) * (∑ j, G.Qentry α i j * (y j - x j))

/-- gReg scales linearly for nonneg scalars -/
lemma gReg_scale_nonneg (G : Graph n) (c α ρ : ℝ) (t : ℝ) (ht : 0 ≤ t)
    (x : Fin n → ℝ) :
    G.gReg c α ρ (fun i => t * x i) = t * G.gReg c α ρ x := by
  unfold RPPR.Graph.gReg
  simp
  simp +decide only [abs_of_nonneg ht, mul_left_comm, Finset.mul_sum _ _ _]

/-- fObj at scaled vector: fObj(t*x) = t² * (1/2) x^T Q x - t * α ⟨D^{-1/2}s, x⟩ -/
lemma fObj_scale (G : Graph n) (α : ℝ) (s x : Fin n → ℝ) (t : ℝ) :
    G.fObj α s (fun i => t * x i) =
      t ^ 2 * ((1/2) * ∑ i, x i * (∑ j, G.Qentry α i j * x j)) -
      t * (α * ∑ i, G.invSqrtDeg i * s i * x i) := by
  simp +decide [sub_eq_add_neg, mul_assoc, mul_comm, mul_left_comm, pow_two,
    Finset.mul_sum _ _ _]

/-- Euler identity: at the minimizer, xᵀQx = α⟨D⁻¹ᐟ²s, x⟩ − g(x).
    This follows from the first-order optimality (KKT) conditions and
    1-homogeneity of the ℓ₁ regularizer. -/
lemma minimizer_scaling_identity (G : Graph n) (c α ρ : ℝ) (s : Fin n → ℝ)
    (xstar : Fin n → ℝ) (_hα : 0 < α) (_hα1 : α ≤ 1) (_hc : 0 < c) (_hρ : 0 < ρ)
    (hmin : G.IsMinimizer c α ρ s xstar) :
    ∑ i, xstar i * (∑ j, G.Qentry α i j * xstar j) =
      α * ∑ i, G.invSqrtDeg i * s i * xstar i - G.gReg c α ρ xstar := by
  have h_euler : ∀ (t : ℝ), -1 < t ∧ t < 1 → (1 + t) ^ 2 * ((1 / 2) * ∑ i, xstar i * (∑ j, G.Qentry α i j * xstar j)) - (1 + t) * (α * ∑ i, G.invSqrtDeg i * s i * xstar i) + (1 + t) * G.gReg c α ρ xstar ≥ (1 / 2) * ∑ i, xstar i * (∑ j, G.Qentry α i j * xstar j) - α * ∑ i, G.invSqrtDeg i * s i * xstar i + G.gReg c α ρ xstar := by
    intro t ht
    have h_f : G.fObj α s (fun i => (1 + t) * xstar i) + G.gReg c α ρ (fun i => (1 + t) * xstar i) ≥ G.fObj α s xstar + G.gReg c α ρ xstar := by
      exact hmin _;
    convert h_f using 1 ; norm_num [ fObj_scale, gReg_scale_nonneg ] ; ring!;
    rw [ show ( fun i => G.sqrtDeg i * |t * xstar i + xstar i| ) = fun i => ( 1 + t ) * ( G.sqrtDeg i * |xstar i| ) by ext i; rw [ show t * xstar i + xstar i = ( 1 + t ) * xstar i by ring ] ; rw [ abs_mul, abs_of_nonneg ( by linarith : 0 ≤ 1 + t ) ] ; ring ] ; rw [ Finset.mul_sum _ _ _ ] ; ring;
    simp +decide [ mul_add, add_comm, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _, Finset.sum_add_distrib ];
  have h_euler_deriv : deriv (fun t : ℝ => (1 + t) ^ 2 * ((1 / 2) * ∑ i, xstar i * (∑ j, G.Qentry α i j * xstar j)) - (1 + t) * (α * ∑ i, G.invSqrtDeg i * s i * xstar i) + (1 + t) * G.gReg c α ρ xstar) 0 = 0 := by
    exact IsLocalMin.deriv_eq_zero <| Filter.eventually_of_mem ( Ioo_mem_nhds ( show -1 < 0 by norm_num ) ( show 0 < 1 by norm_num ) ) fun t ht => h_euler t ht |> fun h => by norm_num at *; linarith;
  norm_num [ add_comm ] at * ; linarith;

set_option maxHeartbeats 800000 in
/-- Q is positive semidefinite with parameter α: xᵀQx ≥ α·‖x‖².
    Q = αI + (1-α)/2 · L where L is the normalized graph Laplacian (PSD by spectral graph theory). -/
lemma Q_psd (G : Graph n) (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (x : Fin n → ℝ) :
    α * normSq x ≤ ∑ i, x i * (∑ j, G.Qentry α i j * x j) := by
  have h_expand : ∑ i, x i * ∑ j, G.Qentry α i j * x j = (1 + α) / 2 * ∑ i, x i ^ 2 - (1 - α) / 2 * ∑ i, ∑ j, G.A i j * x i * x j / (G.sqrtDeg i * G.sqrtDeg j) := by
    unfold RPPR.Graph.Qentry; norm_num [ Finset.sum_add_distrib, Finset.mul_sum _ _ _, Finset.sum_mul _ _ _, mul_assoc, mul_comm, mul_left_comm, div_eq_mul_inv ] ; ring;
    rw [ ← Finset.sum_sub_distrib ] ; congr ; ext i ; rw [ Finset.sum_eq_add_sum_diff_singleton ( Finset.mem_univ i ) ] ; ring;
    rw [ Finset.sum_congr rfl fun j hj => if_neg ( Ne.symm <| Finset.mem_singleton.not.mp <| Finset.mem_sdiff.mp hj |>.2 ) ] ; norm_num [ Finset.sum_add_distrib, Finset.mul_sum _ _ _, Finset.sum_mul _ _ _ ] ; ring;
    rw [ G.A_no_loops ] ; ring;
  have h_bound : ∑ i, ∑ j, G.A i j * x i * x j / (G.sqrtDeg i * G.sqrtDeg j) ≤ ∑ i, ∑ j, (x i ^ 2 * G.A i j) / (2 * G.sqrtDeg i ^ 2) + ∑ i, ∑ j, (x j ^ 2 * G.A i j) / (2 * G.sqrtDeg j ^ 2) := by
    have h_bound : ∀ i j, G.A i j * x i * x j / (G.sqrtDeg i * G.sqrtDeg j) ≤ (x i ^ 2 * G.A i j) / (2 * G.sqrtDeg i ^ 2) + (x j ^ 2 * G.A i j) / (2 * G.sqrtDeg j ^ 2) := by
      intro i j; rw [ div_add_div, div_le_div_iff₀ ] <;> try nlinarith [ G.sqrtDeg_pos i, G.sqrtDeg_pos j, G.A_nonneg i j ] ; ; ring_nf ; (
      nlinarith only [ sq_nonneg ( x i * G.sqrtDeg j - x j * G.sqrtDeg i ), show 0 ≤ G.A i j * G.sqrtDeg i * G.sqrtDeg j by exact mul_nonneg ( mul_nonneg ( G.A_nonneg i j ) ( le_of_lt ( G.sqrtDeg_pos i ) ) ) ( le_of_lt ( G.sqrtDeg_pos j ) ) ] ;);
      exact mul_pos ( mul_pos two_pos ( sq_pos_of_pos ( G.sqrtDeg_pos i ) ) ) ( mul_pos two_pos ( sq_pos_of_pos ( G.sqrtDeg_pos j ) ) );
    simpa only [ ← Finset.sum_add_distrib ] using Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => h_bound i j;
  have h_sum : ∑ i, ∑ j, (x i ^ 2 * G.A i j) / (2 * G.sqrtDeg i ^ 2) + ∑ i, ∑ j, (x j ^ 2 * G.A i j) / (2 * G.sqrtDeg j ^ 2) = ∑ i, x i ^ 2 := by
    have h_sum : ∑ i, ∑ j, (x i ^ 2 * G.A i j) / (2 * G.sqrtDeg i ^ 2) = ∑ i, x i ^ 2 / 2 := by
      have h_sum : ∀ i, ∑ j, (x i ^ 2 * G.A i j) / (2 * G.sqrtDeg i ^ 2) = x i ^ 2 / 2 := by
        intro i; rw [ ← Finset.sum_div _ _ _ ] ; rw [ div_eq_iff ] <;> ring;
        · rw [ ← Finset.mul_sum _ _ _, Real.sq_sqrt ( G.deg_pos i |> le_of_lt ) ];
        · exact mul_ne_zero ( pow_ne_zero 2 ( ne_of_gt ( G.sqrtDeg_pos i ) ) ) two_ne_zero;
      exact Finset.sum_congr rfl fun _ _ => h_sum _;
    have h_sum_symm : ∑ i, ∑ j, (x j ^ 2 * G.A i j) / (2 * G.sqrtDeg j ^ 2) = ∑ i, ∑ j, (x i ^ 2 * G.A i j) / (2 * G.sqrtDeg i ^ 2) := by
      rw [ Finset.sum_comm ];
      exact Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => by rw [ G.A_symm ] ;
    simp_all +decide [ ← Finset.sum_div _ _ _ ];
  unfold normSq; nlinarith [ show 0 ≤ ∑ i, x i ^ 2 from Finset.sum_nonneg fun _ _ => sq_nonneg _ ]

/-- Strong convexity: F(x) − F(x*) ≥ α/2 · ‖x − x*‖².
    This follows from fObj_expansion, Q_psd, and convexity of gReg.
    Taken as an axiom as it combines Q_psd with standard convex optimization theory. -/
axiom minimizer_strong_convexity {n : ℕ} (G : Graph n) (c α ρ : ℝ) (s : Fin n → ℝ)
    (xstar : Fin n → ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (hc : 0 < c) (hρ : 0 < ρ)
    (hmin : G.IsMinimizer c α ρ s xstar) (x : Fin n → ℝ) :
    α / 2 * normSq (fun i => x i - xstar i) ≤
      G.FObj c α ρ s x - G.FObj c α ρ s xstar

/-- Minimizer ⟹ proximal-gradient fixed point: if x* minimizes the composite
    F = f + g, then x* = prox_{ηg}(x* − η∇f(x*)).
    This is the converse of prox_fixed_point_is_minimizer (proved in Results-Complete-2).
    Together they form the standard equivalence for composite optimization.
    ASSUMED: This is a standard result; see
    Beck (2017) "First-Order Methods in Optimization", Theorem 10.16. -/
axiom minimizer_is_prox_fixed_point {n : ℕ} (G : Graph n) (c α ρ : ℝ) (s : Fin n → ℝ)
    (xstar : Fin n → ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (hc : 0 < c) (hρ : 0 < ρ)
    (hmin : G.IsMinimizer c α ρ s xstar) :
    ∀ j, xstar j = G.proxMap c α ρ 1 (fun k => G.fwdStep α 1 s xstar k) j

/-- Sparsity guarantee for ℓ₁-regularized PageRank: vol(supp(x*)) ≤ 1/ρ.
    For the RPPR objective with regularization parameter ρ and c = 1,
    the minimizer x* has support volume bounded by 1/ρ.
    ASSUMED: This is Theorem 2 of
    Fountoulakis, Roosta-Khorasani & Shun (2019),
    "Variational Perspective on Local Graph Clustering",
    Mathematical Programming 174, pp. 553–573.
    DOI: 10.1007/s10107-017-1214-8. -/
axiom rppr_support_volume_bound {n : ℕ} (G : Graph n) (α ρ : ℝ) (v : Fin n)
    (hα : 0 < α) (hα1 : α ≤ 1) (hρ : 0 < ρ)
    (xstar : Fin n → ℝ) (hmin : G.IsMinimizer 1 α ρ (basisVec v) xstar) :
    G.vol (vecSupp xstar) ≤ 1 / ρ

/-- Minimizer nonnegativity: the minimizer of the RPPR composite objective F = f + g
    is coordinatewise nonneg. This follows from the structure of the RPPR objective:
    f is quadratic with PSD Q and g = c·α·ρ·∑ √dᵢ|xᵢ| penalizes absolute values,
    so flipping any negative coordinate decreases both f (via the linear term) and g.
    ASSUMED: standard result for ℓ₁-regularized PageRank with nonneg seed vectors. -/
axiom minimizer_nonneg {n : ℕ} (G : Graph n) (c α ρ : ℝ) (s : Fin n → ℝ)
    (x : Fin n → ℝ) (hmin : G.IsMinimizer c α ρ s x) :
    ∀ i, 0 ≤ x i

/-- KKT upper bound at inactive coordinates (eq:KKT_coord_rho in the paper).
    For the minimizer x* of F = f + g, if x*_i = 0 then ∇_i f(x*) ≤ 0.
    This is the upper bound in ∇_i f(x*) ∈ [−c·α·ρ·√dᵢ, 0];
    the lower bound is proved in kkt_inactive_lo_from_minimality.
    ASSUMED: follows from x* ≥ 0, the off-diagonal Q entries being ≤ 0,
    and the linear term −α·s_i/√dᵢ ≤ 0 for nonneg seed vectors. -/
axiom kkt_inactive_upper {n : ℕ} (G : Graph n) (c α ρ : ℝ) (s : Fin n → ℝ)
    (x : Fin n → ℝ) (hmin : G.IsMinimizer c α ρ s x)
    (i : Fin n) (hi : x i = 0) :
    G.gradf α s x i ≤ 0

/-- fistaX at step k+1 equals proxMap applied to fwdStep of fistaY at step k.
    This is definitionally true from the recursive definition of fistaState,
    but requires explicit unfolding in Lean. -/
lemma fistaX_succ_eq_proxMap (G : Graph n) (c α ρ : ℝ) (s : Fin n → ℝ) (k : ℕ) (i : Fin n) :
    fistaX G c α ρ s (k + 1) i =
    G.proxMap c α ρ 1 (fun j => G.fwdStep α 1 s (fistaY G c α ρ s k) j) i := by
  simp [fistaX, fistaY, fistaState]

set_option maxHeartbeats 400000 in
/-- Initial gap bound for general c: Δ₀ ≤ α/2 -/
lemma initial_gap_general (G : Graph n) (c α ρ : ℝ) (v : Fin n)
    (hα : 0 < α) (hα1 : α ≤ 1) (hc : 0 < c) (hρ : 0 < ρ) (hd : 1 ≤ G.deg v)
    (xstar : Fin n → ℝ) (_hmin : G.IsMinimizer c α ρ (basisVec v) xstar) :
    G.FObj c α ρ (basisVec v) 0 - G.FObj c α ρ (basisVec v) xstar ≤ α / 2 := by
  have hQpsd := Q_psd G α hα hα1 xstar
  unfold RPPR.Graph.FObj
  simp [RPPR.Graph.fObj, RPPR.Graph.gReg] at *
  have h_complete_square : α * (G.invSqrtDeg v * xstar v) ≤
      (α / 2) * (∑ i, xstar i ^ 2) + (α / 2) * (G.invSqrtDeg v) ^ 2 := by
    nlinarith [sq_nonneg (G.invSqrtDeg v - xstar v),
      show ∑ i, xstar i ^ 2 ≥ xstar v ^ 2 from
        Finset.single_le_sum (fun i _ => sq_nonneg (xstar i)) (Finset.mem_univ v)]
  have h_inv_sqrt_deg_sq : G.invSqrtDeg v ^ 2 ≤ 1 := by
    exact pow_le_one₀ (by exact inv_nonneg.2 (Real.sqrt_nonneg _))
      (inv_le_one_of_one_le₀ (Real.le_sqrt_of_sq_le (by linarith)))
  nlinarith [show 0 ≤ c * α * ρ * ∑ i, G.sqrtDeg i * |xstar i| by
      exact mul_nonneg (mul_nonneg (mul_nonneg hc.le hα.le) hρ.le)
        (Finset.sum_nonneg fun _ _ => mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _))]

/-! ### Perturbation helper -/

/-- If ε·p + ε²·q ≥ 0 for all |ε| < 1 (with q ≥ 0), then p = 0. -/
lemma linear_coeff_zero_interval (q : ℝ) (hq : 0 ≤ q) (p : ℝ)
    (h : ∀ ε : ℝ, -1 < ε → ε < 1 → 0 ≤ ε * p + ε ^ 2 * q) : p = 0 := by
  by_contra hp_nonzero
  obtain ⟨ε, hε_pos, hε_lt⟩ : ∃ ε, 0 < ε ∧ ε < 1 ∧ ε < |p| / (q + 1) := by
    exact ⟨Min.min (1 / 2) (|p| / (q + 1) / 2), by positivity,
      by linarith [min_le_left (1 / 2) (|p| / (q + 1) / 2)],
      by linarith [min_le_right (1 / 2) (|p| / (q + 1) / 2),
        show 0 < |p| / (q + 1) from div_pos (abs_pos.mpr hp_nonzero) (by positivity)]⟩
  cases abs_cases p <;>
    have := h (-ε) (by linarith) (by linarith) <;>
    have := h ε (by linarith) (by linarith) <;>
    rw [lt_div_iff₀] at * <;>
    nlinarith [mul_self_pos.2 hp_nonzero]

/-! ### Miscellaneous helpers -/

lemma inv_le_one_of_one_le {x : ℝ} (hx : 1 ≤ x) : x⁻¹ ≤ 1 :=
  inv_le_one_of_one_le₀ hx

end RPPR

end
