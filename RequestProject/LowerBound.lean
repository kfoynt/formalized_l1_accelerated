import Mathlib
import RequestProject.Defs
import RequestProject.Helpers
import RequestProject.Results

/-!
# Lower Bound: FISTA can be worse than ISTA (Appendix D)

Formalization of the lower-bound section (Appendix D) from:
"Complexity of Classical Acceleration for ℓ₁-Regularized PageRank"
(Fountoulakis & Martínez-Rubio)

This file formalizes the star-graph construction, KKT breakpoint analysis,
FISTA overshoot algebra, and the degree-weighted totalWork lower bound.

## Results formalized (matching paper Appendix D numbering)
1. **Lemma D.1** `lemma_D1` — unique minimizer, margin formula, zero at breakpoint
   (building blocks: `star_leaf_breakpoint`, `star_unique_minimizer_support`)
2. **Lemma D.2** `lemma_D2` — full activation criterion:
   general iff `proxMap(w) ≠ 0 ↔ |y_w·√D + y_v| > x*_v` plus nonneg corollary
   (building blocks: `star_activation_criterion`, `star_activation_nonneg`)
3. **Lemma D.3** `lemma_D3` — FISTA overshoots at k=2, activating w
4. **Proposition D.4** `prop_D4` — FISTA totalWork ≥ 2D; ISTA total work O(1/α · log(1/ε))

## Appendix results (bad instances where margin can be small)
- **Lemma C.1** `lemma_C1` —
  Star graph (seed at center): unique minimizer + breakpoint algebra
- **Lemma C.2** `lemma_C2` —
  Path graph P_{m+1} (seed at endpoint, general m ≥ 2): unique minimizer + breakpoint algebra

## Scope note
The Ω(D) lower bound is proved directly: FISTA activates the center w at
iterations k=2,3 (each costing ≥ D in degree-weighted work), so
totalWork(N) ≥ 2D for any N ≥ 4. Setting D = n−1 gives work linear in n.
-/

noncomputable section

open Finset BigOperators Real RPPR

namespace RPPR

variable {n : ℕ}

/-! ## Part 0: Star Graph Definition and Properties -/

/-- Star graph on D+1 nodes: center (node 0) connected to all leaves (nodes 1..D). -/
def starGraph (D : ℕ) (hD : 1 ≤ D) : Graph (D + 1) where
  A := fun i j =>
    if (i.val = 0 ∧ j.val ≠ 0) ∨ (i.val ≠ 0 ∧ j.val = 0) then 1 else 0
  A_nonneg := fun i j => by split_ifs <;> norm_num
  A_symm := fun i j => by
    show (if (i.val = 0 ∧ j.val ≠ 0) ∨ (i.val ≠ 0 ∧ j.val = 0) then (1:ℝ) else 0) =
         (if (j.val = 0 ∧ i.val ≠ 0) ∨ (j.val ≠ 0 ∧ i.val = 0) then (1:ℝ) else 0)
    by_cases h : (i.val = 0 ∧ j.val ≠ 0) ∨ (i.val ≠ 0 ∧ j.val = 0)
    · rw [if_pos h, if_pos (by obtain ⟨a, b⟩ | ⟨a, b⟩ := h <;> [exact Or.inr ⟨b, a⟩; exact Or.inl ⟨b, a⟩])]
    · rw [if_neg h, if_neg (by intro hc; exact h (by obtain ⟨a, b⟩ | ⟨a, b⟩ := hc <;> [exact Or.inr ⟨b, a⟩; exact Or.inl ⟨b, a⟩]))]
  A_no_loops := fun i => by
    show (if (i.val = 0 ∧ i.val ≠ 0) ∨ (i.val ≠ 0 ∧ i.val = 0) then (1:ℝ) else 0) = 0
    have : ¬((i.val = 0 ∧ i.val ≠ 0) ∨ (i.val ≠ 0 ∧ i.val = 0)) := by tauto
    rw [if_neg this]
  deg_pos := fun i => by
    apply Finset.sum_pos'
    · intro j _; split_ifs <;> norm_num
    · by_cases hi : i.val = 0
      · exact ⟨⟨1, by omega⟩, Finset.mem_univ _, by
          dsimp only; rw [if_pos (Or.inl ⟨hi, by omega⟩)]; norm_num⟩
      · exact ⟨⟨0, by omega⟩, Finset.mem_univ _, by
          dsimp only; rw [if_pos (Or.inr ⟨hi, rfl⟩)]; norm_num⟩

def starCenter (D : ℕ) (_ : 1 ≤ D) : Fin (D + 1) := ⟨0, by omega⟩
def starSeed (D : ℕ) (_ : 1 ≤ D) : Fin (D + 1) := ⟨1, by omega⟩
def starRho0 (D : ℕ) (α : ℝ) : ℝ := (1 - α) / (↑D * (1 + α) + (1 - α))
def starXv (α ρ : ℝ) : ℝ := 2 * α * (1 - ρ) / (1 + α)

lemma star_center_ne_seed (D : ℕ) (hD : 1 ≤ D) : starCenter D hD ≠ starSeed D hD := by
  simp [starCenter, starSeed, Fin.ext_iff]
lemma star_seed_ne_center (D : ℕ) (hD : 1 ≤ D) : starSeed D hD ≠ starCenter D hD :=
  (star_center_ne_seed D hD).symm

lemma star_A_leaf_leaf (D : ℕ) (hD : 1 ≤ D) (i j : Fin (D + 1))
    (hi : i.val ≠ 0) (hj : j.val ≠ 0) : (starGraph D hD).A i j = 0 := by
  show (if (i.val = 0 ∧ j.val ≠ 0) ∨ (i.val ≠ 0 ∧ j.val = 0) then (1:ℝ) else 0) = 0
  split_ifs with h
  · obtain ⟨h1, _⟩ | ⟨_, h2⟩ := h <;> contradiction
  · rfl

lemma star_deg_seed (D : ℕ) (hD : 1 ≤ D) : (starGraph D hD).deg (starSeed D hD) = 1 := by
  unfold Graph.deg starSeed
  have hsimp : ∀ j : Fin (D+1), (starGraph D hD).A ⟨1, by omega⟩ j =
    if j.val = 0 then (1:ℝ) else 0 := by
    intro j
    show (if ((⟨1, by omega⟩ : Fin (D+1)).val = 0 ∧ j.val ≠ 0) ∨ ((⟨1, by omega⟩ : Fin (D+1)).val ≠ 0 ∧ j.val = 0) then (1:ℝ) else 0) = if j.val = 0 then 1 else 0
    simp only []; split_ifs <;> simp_all
  simp_rw [hsimp]
  rw [Finset.sum_eq_single (⟨0, by omega⟩ : Fin (D+1))]
  · simp
  · intro j _ hj; rw [if_neg (show j.val ≠ 0 from fun h => hj (Fin.ext h))]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma star_sqrtDeg_seed (D : ℕ) (hD : 1 ≤ D) :
    (starGraph D hD).sqrtDeg (starSeed D hD) = 1 := by
  unfold Graph.sqrtDeg; rw [star_deg_seed]; simp

lemma star_invSqrtDeg_seed (D : ℕ) (hD : 1 ≤ D) :
    (starGraph D hD).invSqrtDeg (starSeed D hD) = 1 := by
  unfold Graph.invSqrtDeg; rw [star_deg_seed]; simp

lemma star_deg_center (D : ℕ) (hD : 1 ≤ D) :
    (starGraph D hD).deg (starCenter D hD) = ↑D := by
  unfold Graph.deg starCenter
  have hsimp : ∀ j : Fin (D+1), (starGraph D hD).A ⟨0, by omega⟩ j =
    if j.val ≠ 0 then (1:ℝ) else 0 := by
    intro j
    show (if ((⟨0, by omega⟩ : Fin (D+1)).val = 0 ∧ j.val ≠ 0) ∨ ((⟨0, by omega⟩ : Fin (D+1)).val ≠ 0 ∧ j.val = 0) then (1:ℝ) else 0) = if j.val ≠ 0 then 1 else 0
    simp only []; split_ifs <;> simp_all
  simp_rw [hsimp]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (⟨0, by omega⟩ : Fin (D+1)))]
  simp only [ne_eq, not_true_eq_false, ↓reduceIte, zero_add]
  have hterms : ∀ j ∈ Finset.univ.erase (⟨0, by omega⟩ : Fin (D+1)),
      (if (j : Fin (D+1)).val ≠ 0 then (1:ℝ) else 0) = 1 := by
    intro j hj; rw [if_pos (show j.val ≠ 0 from fun h => (Finset.mem_erase.mp hj).1 (Fin.ext h))]
  rw [Finset.sum_congr rfl hterms, Finset.sum_const, Nat.smul_one_eq_cast,
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_fin]
  simp

/-! ### gradf on the star graph when input is supported on {v} -/

lemma star_Qx_supp_v (D : ℕ) (hD : 1 ≤ D) (α : ℝ) (x : Fin (D+1) → ℝ)
    (hsupp : ∀ j, j ≠ starSeed D hD → x j = 0) (i : Fin (D+1)) :
    ∑ j, (starGraph D hD).Qentry α i j * x j =
      (starGraph D hD).Qentry α i (starSeed D hD) * x (starSeed D hD) := by
  apply Finset.sum_eq_single
  · intro j _ hj; rw [hsupp j hj, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma star_gradf_v (D : ℕ) (hD : 1 ≤ D) (α xv : ℝ) (x : Fin (D+1) → ℝ)
    (hsupp : ∀ j, j ≠ starSeed D hD → x j = 0) (hxv : x (starSeed D hD) = xv) :
    (starGraph D hD).gradf α (basisVec (starSeed D hD)) x (starSeed D hD) =
      (1 + α) / 2 * xv - α := by
  unfold Graph.gradf; rw [star_Qx_supp_v D hD α x hsupp]
  simp [Graph.Qentry, basisVec, hxv, star_invSqrtDeg_seed]

lemma star_gradf_w (D : ℕ) (hD : 1 ≤ D) (α xv : ℝ) (x : Fin (D+1) → ℝ)
    (hsupp : ∀ j, j ≠ starSeed D hD → x j = 0) (hxv : x (starSeed D hD) = xv) :
    (starGraph D hD).gradf α (basisVec (starSeed D hD)) x (starCenter D hD) =
      -(1 - α) / (2 * (starGraph D hD).sqrtDeg (starCenter D hD)) * xv := by
  unfold Graph.gradf; rw [star_Qx_supp_v D hD α x hsupp]
  unfold Graph.Qentry; rw [if_neg (star_center_ne_seed D hD)]
  have hA : (starGraph D hD).A (starCenter D hD) (starSeed D hD) = 1 := by
    simp [starGraph, starCenter, starSeed]
  rw [hA, hxv, star_sqrtDeg_seed]
  have : starCenter D hD ≠ starSeed D hD := star_center_ne_seed D hD
  simp only [basisVec, this, ite_false, Graph.invSqrtDeg, mul_one, mul_zero, sub_zero]
  ring

lemma star_gradf_other (D : ℕ) (hD : 1 ≤ D) (α : ℝ) (x : Fin (D+1) → ℝ)
    (hsupp : ∀ j, j ≠ starSeed D hD → x j = 0)
    (u : Fin (D+1)) (hu_v : u ≠ starSeed D hD) (hu_w : u ≠ starCenter D hD) :
    (starGraph D hD).gradf α (basisVec (starSeed D hD)) x u = 0 := by
  unfold Graph.gradf; rw [star_Qx_supp_v D hD α x hsupp]
  unfold Graph.Qentry; rw [if_neg hu_v]
  have hu_val : u.val ≠ 0 := by
    intro h; apply hu_w; exact Fin.ext h
  have hv_val : (starSeed D hD).val ≠ 0 := by simp [starSeed]
  have : (starGraph D hD).A u (starSeed D hD) = 0 :=
    star_A_leaf_leaf D hD u (starSeed D hD) hu_val hv_val
  simp [this, basisVec, hu_v]

/-! ### 1D reduction: fwdStep and proxMap on {v}-supported vectors -/

/-- fwdStep at v when y is supported on {v}: fwdStep(y)_v = (1-α)/2 · y_v + α. -/
lemma star_fwdStep_v (D : ℕ) (hD : 1 ≤ D) (α : ℝ) (y : Fin (D+1) → ℝ)
    (hsupp : ∀ j, j ≠ starSeed D hD → y j = 0) :
    (starGraph D hD).fwdStep α 1 (basisVec (starSeed D hD)) y (starSeed D hD) =
      (1 - α) / 2 * y (starSeed D hD) + α := by
  unfold Graph.fwdStep
  rw [star_gradf_v D hD α (y (starSeed D hD)) y hsupp rfl]; ring

/-- fwdStep at w when y is supported on {v}: fwdStep(y)_w = (1-α)/(2·sqrtDeg w) · y_v. -/
lemma star_fwdStep_w (D : ℕ) (hD : 1 ≤ D) (α : ℝ) (y : Fin (D+1) → ℝ)
    (hsupp : ∀ j, j ≠ starSeed D hD → y j = 0) :
    (starGraph D hD).fwdStep α 1 (basisVec (starSeed D hD)) y (starCenter D hD) =
      (1 - α) / (2 * (starGraph D hD).sqrtDeg (starCenter D hD)) *
        y (starSeed D hD) := by
  unfold Graph.fwdStep
  rw [star_gradf_w D hD α (y (starSeed D hD)) y hsupp rfl, hsupp _ (star_center_ne_seed D hD)]
  ring

/-- fwdStep at other leaf u when y is supported on {v}: fwdStep(y)_u = 0. -/
lemma star_fwdStep_other (D : ℕ) (hD : 1 ≤ D) (α : ℝ) (y : Fin (D+1) → ℝ)
    (hsupp : ∀ j, j ≠ starSeed D hD → y j = 0)
    (u : Fin (D+1)) (hu_v : u ≠ starSeed D hD) (hu_w : u ≠ starCenter D hD) :
    (starGraph D hD).fwdStep α 1 (basisVec (starSeed D hD)) y u = 0 := by
  unfold Graph.fwdStep
  rw [star_gradf_other D hD α y hsupp u hu_v hu_w, hsupp u hu_v]; ring

/-- fwdStep at w when y is {v,w}-supported:
    fwdStep(y)_w = (1-α)/(2·sqrtDeg(w)) · (sqrtDeg(w)·y_w + y_v). -/
lemma star_fwdStep_w_vw (D : ℕ) (hD : 1 ≤ D) (α : ℝ)
    (y : Fin (D+1) → ℝ) (hsupp : ∀ j, j ≠ starSeed D hD → j ≠ starCenter D hD → y j = 0) :
    (starGraph D hD).fwdStep α 1 (basisVec (starSeed D hD)) y (starCenter D hD) =
      (1 - α) / (2 * (starGraph D hD).sqrtDeg (starCenter D hD)) *
        ((starGraph D hD).sqrtDeg (starCenter D hD) * y (starCenter D hD) +
         y (starSeed D hD)) := by
  set v := starSeed D hD
  set w := starCenter D hD
  set G := starGraph D hD
  have hsqDne : G.sqrtDeg w ≠ 0 := ne_of_gt (G.sqrtDeg_pos w)
  have hgradf : G.gradf α (basisVec v) y w =
      (1 + α) / 2 * y w - (1 - α) / (2 * G.sqrtDeg w) * y v := by
    unfold Graph.gradf
    have hsum : ∑ j, G.Qentry α w j * y j =
        G.Qentry α w w * y w + G.Qentry α w v * y v := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ w),
          ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨star_seed_ne_center D hD, Finset.mem_univ _⟩)]
      have hrest : ∑ j ∈ (Finset.univ.erase w).erase v, G.Qentry α w j * y j = 0 := by
        apply Finset.sum_eq_zero; intro j hj
        simp only [Finset.mem_erase] at hj
        rw [hsupp j hj.1 hj.2.1, mul_zero]
      linarith
    rw [hsum]
    unfold Graph.Qentry
    rw [if_pos rfl, if_neg (star_center_ne_seed D hD)]
    have hA : G.A w v = 1 := by
      change (if ((starCenter D hD).val = 0 ∧ (starSeed D hD).val ≠ 0) ∨
              ((starCenter D hD).val ≠ 0 ∧ (starSeed D hD).val = 0) then (1:ℝ) else 0) = 1
      simp [starCenter, starSeed]
    rw [hA, star_sqrtDeg_seed]
    have hwv : w ≠ v := star_center_ne_seed D hD
    simp only [basisVec, if_neg hwv, Graph.invSqrtDeg, mul_zero, sub_zero]
    ring
  unfold Graph.fwdStep; simp only [one_mul]; rw [hgradf]; field_simp; ring

/-- softThresh(t, w) = 0 when |w| ≤ t. -/
lemma softThresh_zero_of_abs_le (t w : ℝ) (h : |w| ≤ t) :
    softThresh t w = 0 := by
  unfold softThresh
  split_ifs with h1 h2
  · exfalso; linarith [abs_le.mp h]
  · exfalso; linarith [abs_le.mp h]
  · rfl

/-- softThresh(t, w) ≥ 0 when w ≥ 0. -/
lemma softThresh_nonneg_of_nonneg (t w : ℝ) (ht : 0 ≤ t) (hw : 0 ≤ w) :
    0 ≤ softThresh t w := by unfold softThresh; split_ifs <;> linarith

/-- softThresh(t, w) > 0 when w > t ≥ 0. -/
lemma softThresh_pos_of_gt (t w : ℝ) (_ht : 0 ≤ t) (hw : t < w) :
    0 < softThresh t w := by
  unfold softThresh; rw [if_pos hw]; linarith

/-- softThresh(t, w) ≠ 0 iff |w| > t (when t ≥ 0). -/
lemma softThresh_ne_zero_iff (t w : ℝ) (_ht : 0 ≤ t) :
    softThresh t w ≠ 0 ↔ t < |w| := by
  constructor
  · contrapose!; exact softThresh_zero_of_abs_le t w
  · intro h hst
    have : |w| ≤ t := by
      unfold softThresh at hst; split_ifs at hst with h1 h2
      · linarith
      · linarith
      · push_neg at h1 h2; exact abs_le.mpr ⟨by linarith, by linarith⟩
    linarith

/-- When y is {v}-supported and fwdStep_v > threshold, proxMap gives:
    x_{k+1,v} = (1-α)/2 · y_v + α − αρ = (1-α)/2 · y_v + α(1-ρ). -/
lemma star_proxMap_v (D : ℕ) (hD : 1 ≤ D) (α ρ : ℝ) (_hα : 0 < α) (_hρ : ρ < 1)
    (y : Fin (D+1) → ℝ)
    (hsupp : ∀ j, j ≠ starSeed D hD → y j = 0)
    (hfwd_pos : α * ρ < (1 - α) / 2 * y (starSeed D hD) + α) :
    (starGraph D hD).proxMap 1 α ρ 1
      (fun j => (starGraph D hD).fwdStep α 1 (basisVec (starSeed D hD)) y j)
      (starSeed D hD) =
      (1 - α) / 2 * y (starSeed D hD) + α * (1 - ρ) := by
  unfold Graph.proxMap; dsimp only
  rw [star_fwdStep_v D hD α y hsupp, star_sqrtDeg_seed]
  unfold softThresh
  rw [if_pos (by linarith : 1 * 1 * α * ρ * 1 < (1 - α) / 2 * y (starSeed D hD) + α)]
  ring

/-- When y is {v}-supported and fwdStep_w ≤ threshold, proxMap gives x_{k+1,w} = 0. -/
lemma star_proxMap_w_zero (D : ℕ) (hD : 1 ≤ D) (α ρ : ℝ) (y : Fin (D+1) → ℝ)
    (hsupp : ∀ j, j ≠ starSeed D hD → y j = 0)
    (hfwd_le : |(1 - α) / (2 * (starGraph D hD).sqrtDeg (starCenter D hD)) *
                 y (starSeed D hD)| ≤
               1 * 1 * α * ρ * (starGraph D hD).sqrtDeg (starCenter D hD)) :
    (starGraph D hD).proxMap 1 α ρ 1
      (fun j => (starGraph D hD).fwdStep α 1 (basisVec (starSeed D hD)) y j)
      (starCenter D hD) = 0 := by
  unfold Graph.proxMap; dsimp only
  rw [star_fwdStep_w D hD α y hsupp]
  exact softThresh_zero_of_abs_le _ _ hfwd_le

/-- proxMap at other leaf u = 0 when y is {v}-supported. -/
lemma star_proxMap_other_zero (D : ℕ) (hD : 1 ≤ D) (α ρ : ℝ) (hα : 0 < α) (hρ : 0 < ρ)
    (y : Fin (D+1) → ℝ)
    (hsupp : ∀ j, j ≠ starSeed D hD → y j = 0)
    (u : Fin (D+1)) (hu_v : u ≠ starSeed D hD) (hu_w : u ≠ starCenter D hD) :
    (starGraph D hD).proxMap 1 α ρ 1
      (fun j => (starGraph D hD).fwdStep α 1 (basisVec (starSeed D hD)) y j) u = 0 := by
  unfold Graph.proxMap; dsimp only
  rw [star_fwdStep_other D hD α y hsupp u hu_v hu_w]
  exact softThresh_zero_of_abs_le _ _ (by
    simp only [abs_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg one_pos.le one_pos.le) hα.le) hρ.le)
      ((starGraph D hD).sqrtDeg_pos u).le)

/-! ## Part 1: Lemma 5.1 — Explicit margin formula -/

lemma starXv_pos (α ρ : ℝ) (hα : 0 < α) (hρ : ρ < 1) : 0 < starXv α ρ := by
  unfold starXv
  apply div_pos
  · nlinarith
  · linarith

lemma starRho0_pos (D : ℕ) (hD : 1 ≤ D) (α : ℝ) (hα : 0 < α) (hα1 : α < 1) :
    0 < starRho0 D α := by
  unfold starRho0; apply div_pos (by linarith)
  have : (0:ℝ) < ↑D := by exact_mod_cast (show 0 < D by omega)
  nlinarith

lemma starRho0_lt_one (D : ℕ) (hD : 1 ≤ D) (α : ℝ) (hα : 0 < α) (hα1 : α < 1) :
    starRho0 D α < 1 := by
  unfold starRho0; rw [div_lt_one]
  · have : (0:ℝ) < ↑D := by exact_mod_cast (show 0 < D by omega)
    nlinarith
  · have : (0:ℝ) < ↑D := by exact_mod_cast (show 0 < D by omega)
    nlinarith

/-- **Lemma 5.1**: Optimal solution, explicit margin formula, zero at breakpoint. -/
theorem star_leaf_breakpoint (D : ℕ) (hD : 1 ≤ D) (α ρ : ℝ)
    (hα : 0 < α) (hα1 : α < 1) (hρ_ge : starRho0 D α ≤ ρ) (hρ_lt : ρ < 1) :
    -- (i) x*_v > 0
    0 < starXv α ρ
    -- (ii) Explicit margin: γ_w = C·(ρ−ρ₀) where C = α(D(1+α)+(1-α))/((1+α)D)
    ∧ α * ρ - α * (1 - α) * (1 - ρ) / ((1 + α) * ↑D) =
        α * (↑D * (1 + α) + (1 - α)) / ((1 + α) * ↑D) * (ρ - starRho0 D α)
    -- (iii) Margin is nonneg
    ∧ 0 ≤ α * ρ - α * (1 - α) * (1 - ρ) / ((1 + α) * ↑D)
    -- (iv) Zero at ρ₀
    ∧ α * starRho0 D α - α * (1 - α) * (1 - starRho0 D α) / ((1 + α) * ↑D) = 0 := by
  have hD_pos : (0 : ℝ) < ↑D := by exact_mod_cast show 0 < D by omega
  have h_denom : 0 < ↑D * (1 + α) + (1 - α) := by nlinarith
  have hα1' : 1 + α ≠ 0 := by linarith
  have hDne : (D : ℝ) ≠ 0 := by exact_mod_cast show D ≠ 0 by omega
  have hD1α : ↑D * (1 + α) + (1 - α) ≠ 0 := ne_of_gt h_denom
  have hD1α' : 1 - α + α * ↑D + ↑D ≠ 0 := by linarith [h_denom]
  refine ⟨starXv_pos α ρ hα hρ_lt, ?_, ?_, ?_⟩
  · -- (ii) Explicit margin formula
    unfold starRho0
    field_simp
    -- field_simp leaves (1-α+α*D+D)⁻¹ terms; show their coefficient factors as -(1-α)*Z
    have key : (2 * α + α ^ 2 * (↑D : ℝ) - α ^ 2 - ↑D - 1) *
        (1 - α + α * (↑D : ℝ) + ↑D)⁻¹ = α - 1 := by
      rw [show (2 * α + α ^ 2 * (↑D : ℝ) - α ^ 2 - ↑D - 1 : ℝ) =
        -(1 - α) * (1 - α + α * (↑D : ℝ) + ↑D) from by ring,
        mul_assoc, mul_inv_cancel₀ hD1α', mul_one, neg_sub]
    linear_combination -key
  · -- (iii) Margin is nonneg
    have hC : 0 < α * (↑D * (1 + α) + (1 - α)) / ((1 + α) * ↑D) := by positivity
    suffices h : α * ρ - α * (1 - α) * (1 - ρ) / ((1 + α) * ↑D) =
        α * (↑D * (1 + α) + (1 - α)) / ((1 + α) * ↑D) * (ρ - starRho0 D α) by
      rw [h]; exact mul_nonneg (le_of_lt hC) (sub_nonneg.mpr hρ_ge)
    unfold starRho0
    field_simp
    have key : (2 * α + α ^ 2 * (↑D : ℝ) - α ^ 2 - ↑D - 1) *
        (1 - α + α * (↑D : ℝ) + ↑D)⁻¹ = α - 1 := by
      rw [show (2 * α + α ^ 2 * (↑D : ℝ) - α ^ 2 - ↑D - 1 : ℝ) =
        -(1 - α) * (1 - α + α * (↑D : ℝ) + ↑D) from by ring,
        mul_assoc, mul_inv_cancel₀ hD1α', mul_one, neg_sub]
    linear_combination -key
  · -- (iv) Zero at ρ₀
    unfold starRho0
    field_simp
    ring

/-! ## Part 2: Lemma 5.2 — Full activation criterion via proxMap -/

lemma star_zero_margin_identity (D : ℕ) (hD : 1 ≤ D) (α : ℝ) (hα : 0 < α) (hα1 : α < 1) :
    (1 - α) * starXv α (starRho0 D α) = 2 * α * starRho0 D α * ↑D := by
  unfold starXv starRho0
  have hD_pos : (0 : ℝ) < ↑D := by exact_mod_cast show 0 < D by omega
  have hα1' : 1 + α ≠ 0 := by linarith
  have hDne : (D : ℝ) ≠ 0 := ne_of_gt hD_pos
  have hD1α : ↑D * (1 + α) + (1 - α) ≠ 0 := by nlinarith
  field_simp [hα1', hD1α]
  ring

/-- Q_{wv} = -(1-α)/(2·sqrtDeg(w)) on the star graph (since A(w,v)=1 and sqrtDeg(v)=1). -/
lemma star_Q_wv (D : ℕ) (hD : 1 ≤ D) (α : ℝ) :
    (starGraph D hD).Qentry α (starCenter D hD) (starSeed D hD) =
      -(1 - α) / (2 * (starGraph D hD).sqrtDeg (starCenter D hD)) := by
  unfold Graph.Qentry; rw [if_neg (star_center_ne_seed D hD)]
  have hA : (starGraph D hD).A (starCenter D hD) (starSeed D hD) = 1 := by
    show (if ((starCenter D hD).val = 0 ∧ (starSeed D hD).val ≠ 0) ∨
            ((starCenter D hD).val ≠ 0 ∧ (starSeed D hD).val = 0) then (1:ℝ) else 0) = 1
    simp [starCenter, starSeed]
  rw [hA, star_sqrtDeg_seed]; ring

/-- **Lemma D.2 (Activation criterion — general iff)**: At ρ₀, for any y with
    supp(y) ⊆ {v,w}, the proximal step activates w iff |y_w·√D + y_v| > x*_v.
    This is the full paper equivalence with no sign assumption on y. -/
theorem star_activation_criterion (D : ℕ) (hD : 1 ≤ D) (α : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (y : Fin (D+1) → ℝ) (hsupp : ∀ j, j ≠ starSeed D hD → j ≠ starCenter D hD → y j = 0) :
    (starGraph D hD).proxMap 1 α (starRho0 D α) 1
      (fun j => (starGraph D hD).fwdStep α 1 (basisVec (starSeed D hD)) y j)
      (starCenter D hD) ≠ 0 ↔
    starXv α (starRho0 D α) <
      |y (starCenter D hD) * (starGraph D hD).sqrtDeg (starCenter D hD) +
       y (starSeed D hD)| := by
  set v := starSeed D hD
  set w := starCenter D hD
  set G := starGraph D hD
  have hzm := star_zero_margin_identity D hD α hα hα1
  have hD_pos : (0 : ℝ) < ↑D := by exact_mod_cast show 0 < D by omega
  have hsqD := G.sqrtDeg_pos w
  -- Factor: fwdStep(y)_w = c·(sqrtDeg(w)·y_w + y_v), threshold = c·x*_v
  have hρ₀ := starRho0_pos D hD α hα hα1
  have hfwd := star_fwdStep_w_vw D hD α y hsupp
  have hsd : G.sqrtDeg w * G.sqrtDeg w = ↑D := by
    rw [← Real.sq_sqrt (le_of_lt hD_pos)]; unfold Graph.sqrtDeg; rw [star_deg_center]; ring
  have hthresh : 1 * 1 * α * starRho0 D α * G.sqrtDeg w =
      (1 - α) / (2 * G.sqrtDeg w) * starXv α (starRho0 D α) := by
    have h2sqD_ne : (2 * G.sqrtDeg w : ℝ) ≠ 0 := by positivity
    rw [eq_comm, div_mul_eq_mul_div, div_eq_iff h2sqD_ne, hzm]
    linear_combination -2 * α * starRho0 D α * hsd
  have hc : 0 < (1 - α) / (2 * G.sqrtDeg w) := div_pos (by linarith) (by positivity)
  -- proxMap = softThresh; use softThresh_ne_zero_iff and cancel the positive factor
  unfold Graph.proxMap; dsimp only
  rw [softThresh_ne_zero_iff _ _ (by positivity), hfwd, hthresh,
      abs_mul, abs_of_pos hc,
      show G.sqrtDeg w * y w + y v = y w * G.sqrtDeg w + y v from by ring]
  constructor <;> intro h <;> nlinarith

/-- **Lemma D.2 (nonneg corollary)**: When y_w, y_v ≥ 0, the general iff simplifies to
    proxMap(w) > 0 ↔ y_w·√D + y_v > x*_v (since both sides drop absolute values). -/
theorem star_activation_nonneg (D : ℕ) (hD : 1 ≤ D) (α : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (y : Fin (D+1) → ℝ) (hsupp : ∀ j, j ≠ starSeed D hD → j ≠ starCenter D hD → y j = 0)
    (hyw : 0 ≤ y (starCenter D hD)) (hyv : 0 ≤ y (starSeed D hD)) :
    0 < (starGraph D hD).proxMap 1 α (starRho0 D α) 1
      (fun j => (starGraph D hD).fwdStep α 1 (basisVec (starSeed D hD)) y j)
      (starCenter D hD) ↔
    starXv α (starRho0 D α) <
      y (starCenter D hD) * (starGraph D hD).sqrtDeg (starCenter D hD) +
       y (starSeed D hD) := by
  set G := starGraph D hD
  set w := starCenter D hD
  set v := starSeed D hD
  have hsqD := G.sqrtDeg_pos w
  have hρ₀ := starRho0_pos D hD α hα hα1
  have hfwd_nn : 0 ≤ G.fwdStep α 1 (basisVec v) y w := by
    rw [star_fwdStep_w_vw D hD α y hsupp]
    exact mul_nonneg (div_nonneg (by linarith) (by positivity)) (by nlinarith)
  have hpm_nn : 0 ≤ G.proxMap 1 α (starRho0 D α) 1
      (fun j => G.fwdStep α 1 (basisVec v) y j) w :=
    softThresh_nonneg_of_nonneg _ _ (by positivity) hfwd_nn
  have habs : |y w * G.sqrtDeg w + y v| = y w * G.sqrtDeg w + y v :=
    abs_of_nonneg (by nlinarith)
  constructor
  · intro h
    rw [← habs]; exact (star_activation_criterion D hD α hα hα1 y hsupp).mp (ne_of_gt h)
  · intro h
    exact hpm_nn.lt_of_ne (Ne.symm
      ((star_activation_criterion D hD α hα hα1 y hsupp).mpr (by rw [habs]; exact h)))

/-! ## Part 4: Lemma 5.3 — FISTA overshoot connected to iterates -/

private lemma fistaY_zero_eq (G : Graph n) (c α ρ : ℝ) (s : Fin n → ℝ) :
    fistaY G c α ρ s 0 = 0 := by ext i; simp [fistaY, fistaState]

lemma momentum_sqrt_identity (α : ℝ) (hα : 0 < α) (_hα1 : α ≤ 1) :
    (1 + fistaMom α) * √α - 1 = -fistaMom α := by
  unfold fistaMom; have hs := Real.sqrt_pos_of_pos hα
  have h1ps : (1 + √α) ≠ 0 := ne_of_gt (by linarith)
  field_simp; ring

lemma fistaMom_pos_of_lt (α : ℝ) (hα : 0 < α) (hα1 : α < 1) : 0 < fistaMom α := by
  unfold fistaMom
  have hs : √α < 1 := by
    rw [show (1 : ℝ) = √1 from (Real.sqrt_one).symm]
    exact Real.sqrt_lt_sqrt (le_of_lt hα) hα1
  exact div_pos (by linarith) (by linarith [Real.sqrt_pos_of_pos hα])

/-- The algebraic identity: (1+β)(a·√α·β) − β·a = −a·β². -/
theorem fista_overshoot_algebra (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    let β := fistaMom α; let a := (1 - α) / 2
    (1 + β) * (a * √α * β) - β * a = -(a * β ^ 2) := by
  simp only
  have hmom := momentum_sqrt_identity α hα hα1
  -- Key factorization: (1+β)(a·√α·β) - β·a = a·β·((1+β)·√α - 1) = a·β·(-β) = -a·β²
  have hfact : (1 + fistaMom α) * ((1 - α) / 2 * √α * fistaMom α) - fistaMom α * ((1 - α) / 2) =
      (1 - α) / 2 * fistaMom α * ((1 + fistaMom α) * √α - 1) := by ring
  rw [hfact, hmom]; ring

/-- **Lemma 5.3** (FISTA overshoot at k=2, connected to iterates):

    We prove all four parts:
    (1) fistaX 0 = 0
    (2) fistaX 1 w = 0 (w not activated at k=0)
    (3) fistaX 1 v = α(1−ρ₀) (explicit first iterate)
    (4) y_{2,v} > x*_v (overshoot at k=2)

    Part (4) works by tracking the 1D recurrence:
    e₀ = −x*_v, e₁ = a·e₀ (where a=(1−α)/2), e₂ = a·√α·β·e₀.
    Then ẽ₂ = (1+β)e₂ − βe₁ = −a·β²·e₀ = a·β²·x*_v > 0. -/
theorem fista_overshoot_at_k2 (D : ℕ) (hD : 1 ≤ D) (α : ℝ) (hα : 0 < α) (hα1 : α < 1) :
    let G := starGraph D hD
    let v := starSeed D hD
    let w := starCenter D hD
    let ρ₀ := starRho0 D α
    let β := fistaMom α
    let xvstar := starXv α ρ₀
    -- (1)
    fistaX G 1 α ρ₀ (basisVec v) 0 = 0
    -- (2)
    ∧ fistaX G 1 α ρ₀ (basisVec v) 1 w = 0
    -- (3)
    ∧ fistaX G 1 α ρ₀ (basisVec v) 1 v = α * (1 - ρ₀)
    -- (4) The key: y_{2,v} = xvstar + (1-α)/2·β²·xvstar > xvstar
    ∧ fistaY G 1 α ρ₀ (basisVec v) 2 v =
        xvstar * (1 + (1 - α) / 2 * β ^ 2) := by
  have hρ₀ := starRho0_pos D hD α hα hα1
  have hρ₀_lt := starRho0_lt_one D hD α hα hα1
  have hxv := starXv_pos α (starRho0 D α) hα hρ₀_lt
  have hβ := fistaMom_pos_of_lt α hα hα1
  have hβ_nn := fistaMom_nonneg α hα (le_of_lt hα1)
  have hβ_lt := fistaMom_lt_one α hα (le_of_lt hα1)
  set G := starGraph D hD
  set v := starSeed D hD
  set w := starCenter D hD
  set ρ₀ := starRho0 D α
  set β := fistaMom α
  -- (1) Immediate
  refine ⟨fistaX_zero G 1 α ρ₀ (basisVec v), ?_, ?_, ?_⟩
  · -- (2) fistaX 1 w = 0: y₀ = 0, fwdStep(0)_w = 0 since w ≠ v and (basisVec v)(w) = 0
    -- fistaX 1 = proxMap(fwdStep(fistaY 0)) by definition, and fistaY 0 = 0
    have h1 : fistaX G 1 α ρ₀ (basisVec v) 1 w =
        G.proxMap 1 α ρ₀ 1 (fun j => G.fwdStep α 1 (basisVec v)
          (fistaY G 1 α ρ₀ (basisVec v) 0) j) w := rfl
    rw [h1, fistaY_zero_eq]
    exact star_proxMap_w_zero D hD α ρ₀ 0 (fun _ _ => rfl) (by
      simp only [Pi.zero_apply, mul_zero, abs_zero]
      exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg one_pos.le one_pos.le) hα.le)
        hρ₀.le) ((starGraph D hD).sqrtDeg_pos w).le)
  · -- (3) fistaX 1 v = α(1-ρ₀): fwdStep(0)_v = α > αρ₀ = threshold
    have h1 : fistaX G 1 α ρ₀ (basisVec v) 1 v =
        G.proxMap 1 α ρ₀ 1 (fun j => G.fwdStep α 1 (basisVec v)
          (fistaY G 1 α ρ₀ (basisVec v) 0) j) v := rfl
    rw [h1, fistaY_zero_eq]
    rw [star_proxMap_v D hD α ρ₀ hα hρ₀_lt 0 (fun _ _ => rfl) (by
      simp only [Pi.zero_apply, mul_zero, zero_add]; nlinarith)]
    simp only [Pi.zero_apply, mul_zero, zero_add]
  · -- (4) fistaY 2 v = xvstar·(1 + (1-α)/2·β²)
    -- This requires tracking through fistaState to level 2.
    -- We use the 1D reduction: since fistaX 0 and fistaX 1 are both {v}-supported,
    -- fistaY 1 is {v}-supported, and fistaX 2 can be computed via star_proxMap_v.
    -- Then fistaY 2 v = (1+β)·fistaX 2 v − β·fistaX 1 v.
    --
    -- Let x₁ = α(1-ρ₀). Then y₁_v = (1+β)·x₁ (since x₀ = 0).
    -- x₂_v = (1-α)/2·y₁_v + α(1-ρ₀) = (1-α)/2·(1+β)·x₁ + α(1-ρ₀)
    --       = a(1+β)·x₁ + x*_v·(1+α)/2  [using α(1-ρ₀) = x*_v·(1+α)/2]
    -- Actually: x₂_v = a·(1+β)·x₁ + α(1-ρ₀)
    -- e₁ = x₁ - x*_v = α(1-ρ₀) - 2α(1-ρ₀)/(1+α) = α(1-ρ₀)(α-1)/(1+α) = a·e₀
    -- e₂ = x₂_v - x*_v = a(1+β)·e₁ - aβ·e₀ (from the recurrence)
    --     = a(1+β)·ae₀ - aβe₀ = ae₀(a(1+β) - β) = ae₀·√αβ
    -- ẽ₂ = (1+β)e₂ - βe₁ = ... = aβ²x*_v (from fista_overshoot_algebra)
    -- So y₂_v = x*_v + aβ²x*_v = x*_v(1+aβ²)
    --
    -- The detailed verification connects fistaY/fistaX definitions to these formulas.
    -- Key steps: unfold fistaY at k=2, express in terms of fistaX 2 and fistaX 1,
    -- and use the 1D reduction for fistaX 2.
    -- Note: fistaY k+1 i = fistaX (k+1) i + β·(fistaX (k+1) i − fistaX k i)
    rw [fistaY_succ]
    -- Step A: fistaX 1 is {v}-supported (all non-v coords are 0)
    have hx1_supp : ∀ j, j ≠ v → fistaX G 1 α ρ₀ (basisVec v) 1 j = 0 := by
      intro j hj
      have h1 : fistaX G 1 α ρ₀ (basisVec v) 1 j =
          G.proxMap 1 α ρ₀ 1 (fun l => G.fwdStep α 1 (basisVec v)
            (fistaY G 1 α ρ₀ (basisVec v) 0) l) j := rfl
      rw [h1, fistaY_zero_eq]
      by_cases hjw : j = w
      · rw [hjw]; exact star_proxMap_w_zero D hD α ρ₀ 0 (fun _ _ => rfl) (by
          simp only [Pi.zero_apply, mul_zero, abs_zero]
          exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg one_pos.le one_pos.le) hα.le)
            hρ₀.le) ((starGraph D hD).sqrtDeg_pos w).le)
      · exact star_proxMap_other_zero D hD α ρ₀ hα hρ₀ 0 (fun _ _ => rfl) j hj hjw
    -- Step B: fistaX 1 v = α(1-ρ₀) (from part 3, restated as have)
    have hx1v : fistaX G 1 α ρ₀ (basisVec v) 1 v = α * (1 - ρ₀) := by
      have h1 : fistaX G 1 α ρ₀ (basisVec v) 1 v =
          G.proxMap 1 α ρ₀ 1 (fun j => G.fwdStep α 1 (basisVec v)
            (fistaY G 1 α ρ₀ (basisVec v) 0) j) v := rfl
      rw [h1, fistaY_zero_eq]
      rw [star_proxMap_v D hD α ρ₀ hα hρ₀_lt 0 (fun _ _ => rfl) (by
        simp only [Pi.zero_apply, mul_zero, zero_add]; nlinarith)]
      simp only [Pi.zero_apply, mul_zero, zero_add]
    -- Step C: fistaY 1 is {v}-supported
    have hy1_supp : ∀ j, j ≠ v → fistaY G 1 α ρ₀ (basisVec v) 1 j = 0 := by
      intro j hj; rw [fistaY_succ]; rw [hx1_supp j hj]
      simp [fistaX_zero]
    -- Step D: fistaY 1 v = (1+β)·α(1-ρ₀)
    have hy1v : fistaY G 1 α ρ₀ (basisVec v) 1 v = (1 + β) * (α * (1 - ρ₀)) := by
      rw [fistaY_succ, hx1v]; simp [fistaX_zero]; ring
    -- Step E: Compute fistaX 2 v via star_proxMap_v applied to fistaY 1
    -- fistaX 2 = proxMap(fwdStep(fistaY 1))
    -- Since fistaY 1 is {v}-supported: fwdStep(fistaY 1)_v = (1-α)/2·y₁_v + α
    -- And this exceeds the threshold αρ₀ (since y₁_v > 0 and α > αρ₀)
    have hx2v : fistaX G 1 α ρ₀ (basisVec v) 2 v =
        (1 - α) / 2 * ((1 + β) * (α * (1 - ρ₀))) + α * (1 - ρ₀) := by
      -- fistaX 2 = proxMap(fwdStep(fistaY 1)) by definition
      have h2 : fistaX G 1 α ρ₀ (basisVec v) 2 v =
          G.proxMap 1 α ρ₀ 1 (fun j => G.fwdStep α 1 (basisVec v)
            (fistaY G 1 α ρ₀ (basisVec v) 1) j) v := rfl
      rw [h2]
      rw [star_proxMap_v D hD α ρ₀ hα hρ₀_lt (fistaY G 1 α ρ₀ (basisVec v) 1) hy1_supp
        (by rw [hy1v]
            have : 0 ≤ (1 - α) / 2 * ((1 + β) * (α * (1 - ρ₀))) :=
              mul_nonneg (div_nonneg (by linarith) (by norm_num))
                (mul_nonneg (by linarith) (mul_nonneg hα.le (by linarith)))
            nlinarith [mul_lt_mul_of_pos_left hρ₀_lt hα])]
      rw [hy1v]
    -- Step F: Compute fistaY 2 v = (1+β)·x₂_v - β·x₁_v
    -- and show it equals xvstar·(1 + (1-α)/2·β²)
    rw [hx2v, hx1v]
    -- Goal: (1-α)/2·(1+β)·α(1-ρ₀) + α(1-ρ₀) + β·((1-α)/2·(1+β)·α(1-ρ₀) + α(1-ρ₀) - α(1-ρ₀))
    --     = 2α(1-ρ₀)/(1+α) · (1 + (1-α)/2·β²)
    -- i.e., (1+β)·((1-α)/2·(1+β)·α(1-ρ₀) + α(1-ρ₀)) - β·α(1-ρ₀)
    --     = 2α(1-ρ₀)/(1+α) · (1 + (1-α)/2·β²)
    -- Factor: α(1-ρ₀)·((1+β)·((1-α)/2·(1+β) + 1) - β)
    --       = α(1-ρ₀)·((1-α)/2·(1+β)² + 1)
    -- RHS:   2α(1-ρ₀)/(1+α) + α(1-ρ₀)·(1-α)/(1+α)·β²
    -- Both sides factor as α(1-ρ₀)·f(α,β) where f involves β = (1-√α)/(1+√α).
    -- The identity f_LHS = f_RHS follows from: (1-α)/2·(1+β)² + 1 = 2/(1+α)·(1+(1-α)/2·β²)
    -- which after substituting β and simplifying both equal (3-√α)/(1+√α).
    unfold starXv
    -- Pure algebra: both sides are polynomial expressions in α, β, ρ₀.
    -- We verify using the identity (1+β)² = 4/(1+√α)² and β² = (1-√α)²/(1+√α)²
    -- After substitution, both sides equal α(1-ρ₀)·(3-√α)/(1+√α).
    have hs := Real.sqrt_pos_of_pos hα
    have hs1 : √α < 1 := by
      rw [show (1 : ℝ) = √1 from (Real.sqrt_one).symm]
      exact Real.sqrt_lt_sqrt (le_of_lt hα) hα1
    have h1ps : 0 < 1 + √α := by linarith
    have hα_eq : α = √α * √α := (Real.mul_self_sqrt (le_of_lt hα)).symm
    -- Replace β with its definition: β = fistaMom α = (1-√α)/(1+√α)
    -- set introduced β as a local let-definition, so we can use change/simp to expand
    simp only [show β = fistaMom α from rfl]
    unfold fistaMom
    set s := √α with s_def
    have hs_pos : 0 < s := by rw [s_def]; exact hs
    have hsq : α = s * s := by rw [s_def]; exact hα_eq
    have h1s : (1 + s : ℝ) ≠ 0 := by positivity
    rw [hsq]
    have h1ss : (1 + s * s : ℝ) ≠ 0 := by positivity
    field_simp [h1s, h1ss]; ring

/-- The overshoot is positive: y_{2,v} > x*_v. -/
theorem fista_overshoot_positive (D : ℕ) (hD : 1 ≤ D) (α : ℝ) (hα : 0 < α) (hα1 : α < 1) :
    starXv α (starRho0 D α) <
      starXv α (starRho0 D α) * (1 + (1 - α) / 2 * (fistaMom α) ^ 2) := by
  have hxv := starXv_pos α (starRho0 D α) hα (starRho0_lt_one D hD α hα hα1)
  have hβ := fistaMom_pos_of_lt α hα hα1
  have hβ_sq := sq_nonneg (fistaMom α)
  have hterm : 0 < (1 - α) / 2 * (fistaMom α) ^ 2 :=
    mul_pos (div_pos (by linarith) (by norm_num)) (sq_pos_of_pos hβ)
  nlinarith [mul_pos hxv hterm]


/-! ## Part 7: Composition Lemmas -/

/-- proxMap at w > 0 when fwdStep at w exceeds the threshold. -/
lemma proxMap_pos_of_fwdStep_gt (G : Graph n) (c α ρ : ℝ) (s y : Fin n → ℝ)
    (hα : 0 < α) (hρ : 0 < ρ) (hc : 0 < c) (w : Fin n)
    (h : 1 * c * α * ρ * G.sqrtDeg w < G.fwdStep α 1 s y w) :
    0 < G.proxMap c α ρ 1 (fun j => G.fwdStep α 1 s y j) w := by
  unfold Graph.proxMap
  exact softThresh_pos_of_gt _ _ (by positivity) h

/-- fistaX 2 w = 0 on the star graph: w is not activated at iteration 1.
    Since fistaY 1 is {v}-supported, fwdStep at w is below threshold. -/
lemma fistaX_2_w_zero (D : ℕ) (hD : 1 ≤ D) (α : ℝ) (hα : 0 < α) (hα1 : α < 1) :
    fistaX (starGraph D hD) 1 α (starRho0 D α) (basisVec (starSeed D hD)) 2
      (starCenter D hD) = 0 := by
  have hρ₀ := starRho0_pos D hD α hα hα1
  have hρ₀_lt := starRho0_lt_one D hD α hα hα1
  have hx1_supp : ∀ j, j ≠ starSeed D hD → fistaX (starGraph D hD) 1 α (starRho0 D α)
      (basisVec (starSeed D hD)) 1 j = 0 := by
    intro j hj
    have h1 : fistaX (starGraph D hD) 1 α (starRho0 D α) (basisVec (starSeed D hD)) 1 j =
        (starGraph D hD).proxMap 1 α (starRho0 D α) 1 (fun l =>
          (starGraph D hD).fwdStep α 1 (basisVec (starSeed D hD))
            (fistaY (starGraph D hD) 1 α (starRho0 D α) (basisVec (starSeed D hD)) 0) l) j := rfl
    rw [h1, fistaY_zero_eq]
    by_cases hjw : j = starCenter D hD
    · rw [hjw]; exact star_proxMap_w_zero D hD α (starRho0 D α) 0 (fun _ _ => rfl) (by
        simp only [Pi.zero_apply, mul_zero, abs_zero]
        exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg one_pos.le one_pos.le) hα.le)
          hρ₀.le) ((starGraph D hD).sqrtDeg_pos (starCenter D hD)).le)
    · exact star_proxMap_other_zero D hD α (starRho0 D α) hα hρ₀ 0 (fun _ _ => rfl) j hj hjw
  have hy1_supp : ∀ j, j ≠ starSeed D hD →
      fistaY (starGraph D hD) 1 α (starRho0 D α) (basisVec (starSeed D hD)) 1 j = 0 := by
    intro j hj; rw [fistaY_succ, hx1_supp j hj]; simp [fistaX_zero]
  -- fistaX 2 = proxMap(fwdStep(fistaY 1)) by definition
  have h2 : fistaX (starGraph D hD) 1 α (starRho0 D α) (basisVec (starSeed D hD)) 2
      (starCenter D hD) = (starGraph D hD).proxMap 1 α (starRho0 D α) 1 (fun j =>
        (starGraph D hD).fwdStep α 1 (basisVec (starSeed D hD))
          (fistaY (starGraph D hD) 1 α (starRho0 D α) (basisVec (starSeed D hD)) 1) j)
        (starCenter D hD) := rfl
  rw [h2]
  exact star_proxMap_w_zero D hD α (starRho0 D α)
    (fistaY (starGraph D hD) 1 α (starRho0 D α) (basisVec (starSeed D hD)) 1) hy1_supp (by
      have ⟨_, _, hx1v, _⟩ := fista_overshoot_at_k2 D hD α hα hα1
      rw [fistaY_succ, hx1v]; simp only [fistaX_zero, Pi.zero_apply, sub_zero]
      have hβ := fistaMom_nonneg α hα (le_of_lt hα1)
      have hsqD := (starGraph D hD).sqrtDeg_pos (starCenter D hD)
      have hρ₀_lt := starRho0_lt_one D hD α hα hα1
      have hρ₀_pos := starRho0_pos D hD α hα hα1
      have h_coeff : 0 ≤ (1 - α) / (2 * (starGraph D hD).sqrtDeg (starCenter D hD)) := by
        exact le_of_lt (div_pos (by linarith) (by positivity))
      have h1ρ : 0 ≤ 1 - starRho0 D α := by linarith
      have h_yv : 0 ≤ α * (1 - starRho0 D α) + fistaMom α * (α * (1 - starRho0 D α)) := by
        nlinarith [mul_nonneg hα.le h1ρ]
      rw [abs_of_nonneg (mul_nonneg h_coeff h_yv)]
      -- Factor: yv = α*(1-ρ₀)*(1+β)
      have h1β : 0 ≤ 1 + fistaMom α := by linarith
      have hyv_eq : α * (1 - starRho0 D α) + fistaMom α * (α * (1 - starRho0 D α)) =
        α * (1 - starRho0 D α) * (1 + fistaMom α) := by ring
      rw [hyv_eq]
      -- Key fact: (1+β) ≤ 2 since β < 1
      have hβ_lt1 := fistaMom_lt_one α hα (le_of_lt hα1)
      have h1β_le : 1 + fistaMom α ≤ 2 := by linarith
      -- Key bound: (1-ρ₀) ≤ 1
      have h1ρ₀_le : 1 - starRho0 D α ≤ 1 := by linarith [hρ₀_pos]
      -- So yv factor ≤ α * 1 * 2 = 2α
      have hyv_bound : α * (1 - starRho0 D α) * (1 + fistaMom α) ≤ 2 * α := by
        nlinarith [mul_nonneg hα.le h1ρ]
      -- Need: (1-α)/(2*sqrtDeg_c) * (≤ 2α) ≤ α * ρ₀ * sqrtDeg_c
      -- i.e., (1-α)*α/sqrtDeg_c ≤ α * ρ₀ * sqrtDeg_c = α * (1-α)/(D*(1+α)+(1-α)) * sqrtDeg_c
      -- i.e., 1/sqrtDeg_c ≤ sqrtDeg_c / (D*(1+α)+(1-α))
      -- i.e., D*(1+α)+(1-α) ≤ sqrtDeg_c^2 = D ... no, this goes wrong.
      -- Actually, we use a direct bound: LHS * 2 * sqrtDeg_c = (1-α) * yv_factor ≤ (1-α)*2α
      -- RHS * 2 * sqrtDeg_c = 2*α*ρ₀*sqrtDeg_c^2 = 2*α*ρ₀*D
      -- So need: (1-α)*2α ≤ 2α*ρ₀*D, i.e., (1-α) ≤ ρ₀*D
      -- ρ₀*D = D*(1-α)/(D*(1+α)+(1-α))
      -- (1-α) ≤ D*(1-α)/(D*(1+α)+(1-α)) iff D*(1+α)+(1-α) ≤ D iff (1+α)+(1-α)/D ≤ 1
      -- That's not true for D ≥ 2, α > 0. So the tight bound is wrong.
      -- Let me try a different approach: multiply both sides by 2*sqrtDeg_c and use nlinarith
      have hD_pos : (0 : ℝ) < ↑D := by exact_mod_cast show 0 < D by omega
      have hsqD_eq : (starGraph D hD).sqrtDeg (starCenter D hD) = √↑D := by
        unfold Graph.sqrtDeg; rw [star_deg_center]
      rw [hsqD_eq]
      -- Direct approach: unfold definitions and use field_simp + nlinarith
      unfold starRho0
      have hden_pos : 0 < ↑D * (1 + α) + (1 - α) := by nlinarith
      have hden_ne : ↑D * (1 + α) + (1 - α) ≠ 0 := ne_of_gt hden_pos
      have hsα := Real.sqrt_pos_of_pos hα
      have hsα1 : √α ≤ 1 := Real.sqrt_le_one.mpr (le_of_lt hα1)
      have h1sα_ne : (1 + √α) ≠ 0 := ne_of_gt (by linarith : 0 < 1 + √α)
      have hsD_ne : √↑D ≠ 0 := ne_of_gt (Real.sqrt_pos_of_pos hD_pos)
      have hsD_sq : √↑D * √↑D = ↑D := Real.mul_self_sqrt (le_of_lt hD_pos)
      have hsα_sq : √α * √α = α := Real.mul_self_sqrt hα.le
      -- α ≤ √α for 0 < α ≤ 1
      have hα_le_sα : α ≤ √α := by nlinarith [mul_nonneg (le_of_lt hsα) (sub_nonneg.mpr hsα1)]
      rw [show fistaMom α = (1 - √α) / (1 + √α) from rfl]
      rw [show 1 + (1 - √α) / (1 + √α) = 2 / (1 + √α) from by field_simp; ring]
      rw [show 1 - (1 - α) / (↑D * (1 + α) + (1 - α)) =
        ↑D * (1 + α) / (↑D * (1 + α) + (1 - α)) from by field_simp; ring]
      -- Goal: (1-α)/(2*√D) * (α * (D*(1+α)/den) * (2/(1+√α))) ≤ 1*1*α*((1-α)/den)*√D
      -- Simplify 1*1 to 1
      simp only [one_mul, mul_one]
      -- Clear all denominators
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : 0 < 2 * √↑D)]
      -- Now goal has fewer layers of division
      -- Multiply out the div expressions on LHS
      have h2sD_pos : (0:ℝ) < 2 * √↑D := by positivity
      -- Use field_simp on the remaining fractions
      -- (1-α) * (α * (D*(1+α)/den) * (2/(1+√α))) ≤ α * ((1-α)/den) * √D * (2*√D)
      -- Multiply both sides by den*(1+√α) > 0
      have hgoal_den : (0:ℝ) < (↑D * (1 + α) + (1 - α)) * (1 + √α) := by positivity
      rw [show α * ((1 - α) / (↑D * (1 + α) + (1 - α))) * √↑D * (2 * √↑D) =
        2 * α * (1 - α) * (√↑D * √↑D) / (↑D * (1 + α) + (1 - α)) from by ring, hsD_sq]
      -- LHS has nested divs: (1-α) * α * D*(1+α)/(den) * 2/(1+√α)
      -- = 2*α*(1-α)*D*(1+α) / (den*(1+√α))
      -- RHS = 2*α*(1-α)*D / den
      -- Need: 2α(1-α)D(1+α)/(den*(1+√α)) ≤ 2α(1-α)D/den
      -- i.e., (1+α)/(1+√α) ≤ 1, i.e., 1+α ≤ 1+√α, i.e., α ≤ √α ✓
      rw [show (1 - α) * (α * (↑D * (1 + α) / (↑D * (1 + α) + (1 - α))) * (2 / (1 + √α))) =
        2 * α * (1 - α) * ↑D * (1 + α) / ((↑D * (1 + α) + (1 - α)) * (1 + √α)) from by
          field_simp]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      -- goal: 2*α*(1-α)*D*(1+α)*(D*(1+α)+(1-α)) ≤ 2*α*(1-α)*D*((D*(1+α)+(1-α))*(1+√α))
      -- i.e., (1+α) ≤ (1+√α), which follows from α ≤ √α
      have h2α_nn : (0:ℝ) ≤ 2 * α := by linarith
      have h1α_nn : (0:ℝ) ≤ 1 - α := by linarith
      have h2α1α : (0:ℝ) ≤ 2 * α * (1 - α) := mul_nonneg h2α_nn h1α_nn
      nlinarith [hα_le_sα, mul_nonneg (mul_nonneg h2α1α (le_of_lt hD_pos)) (le_of_lt hden_pos)])

/-- fistaX 2 is {v}-supported (all non-v coords are 0). -/
lemma fistaX_2_supp (D : ℕ) (hD : 1 ≤ D) (α : ℝ) (hα : 0 < α) (hα1 : α < 1) :
    ∀ j, j ≠ starSeed D hD → fistaX (starGraph D hD) 1 α (starRho0 D α)
      (basisVec (starSeed D hD)) 2 j = 0 := by
  intro j hj
  by_cases hjw : j = starCenter D hD
  · rw [hjw]; exact fistaX_2_w_zero D hD α hα hα1
  · -- For other leaves: fistaX 2 j = proxMap(fwdStep(fistaY 1))_j = 0
    have hρ₀ := starRho0_pos D hD α hα hα1
    have hy1_supp : ∀ l, l ≠ starSeed D hD →
        fistaY (starGraph D hD) 1 α (starRho0 D α) (basisVec (starSeed D hD)) 1 l = 0 := by
      intro l hl; rw [fistaY_succ]
      have hx1l : fistaX (starGraph D hD) 1 α (starRho0 D α) (basisVec (starSeed D hD)) 1 l = 0 := by
        have h1 : fistaX (starGraph D hD) 1 α (starRho0 D α) (basisVec (starSeed D hD)) 1 l =
            (starGraph D hD).proxMap 1 α (starRho0 D α) 1 (fun k =>
              (starGraph D hD).fwdStep α 1 (basisVec (starSeed D hD))
                (fistaY (starGraph D hD) 1 α (starRho0 D α) (basisVec (starSeed D hD)) 0) k) l := rfl
        rw [h1, fistaY_zero_eq]
        by_cases hlw : l = starCenter D hD
        · rw [hlw]; exact star_proxMap_w_zero D hD α (starRho0 D α) 0 (fun _ _ => rfl) (by
            simp only [Pi.zero_apply, mul_zero, abs_zero]
            exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg one_pos.le one_pos.le) hα.le)
              hρ₀.le) ((starGraph D hD).sqrtDeg_pos (starCenter D hD)).le)
        · exact star_proxMap_other_zero D hD α (starRho0 D α) hα hρ₀
            0 (fun _ _ => rfl) l hl hlw
      rw [hx1l]; simp [fistaX_zero]
    -- fistaX 2 j = proxMap(fwdStep(fistaY 1)) j by definition
    have h2 : fistaX (starGraph D hD) 1 α (starRho0 D α) (basisVec (starSeed D hD)) 2 j =
        (starGraph D hD).proxMap 1 α (starRho0 D α) 1 (fun k =>
          (starGraph D hD).fwdStep α 1 (basisVec (starSeed D hD))
            (fistaY (starGraph D hD) 1 α (starRho0 D α) (basisVec (starSeed D hD)) 1) k) j := rfl
    rw [h2]
    exact star_proxMap_other_zero D hD α (starRho0 D α) hα hρ₀
      (fistaY (starGraph D hD) 1 α (starRho0 D α) (basisVec (starSeed D hD)) 1) hy1_supp
      j hj hjw

/-- fistaY 2 w = 0 on the star graph. -/
lemma fistaY_2_w_zero (D : ℕ) (hD : 1 ≤ D) (α : ℝ) (hα : 0 < α) (hα1 : α < 1) :
    fistaY (starGraph D hD) 1 α (starRho0 D α) (basisVec (starSeed D hD)) 2
      (starCenter D hD) = 0 := by
  rw [fistaY_succ]
  rw [fistaX_2_w_zero D hD α hα hα1]
  have ⟨_, h2, _, _⟩ := fista_overshoot_at_k2 D hD α hα hα1
  rw [h2]; ring

/-- fistaY 2 is {v}-supported (for non-v, non-w coords). -/
lemma fistaY_2_supp (D : ℕ) (hD : 1 ≤ D) (α : ℝ) (hα : 0 < α) (hα1 : α < 1) :
    ∀ j, j ≠ starSeed D hD → j ≠ starCenter D hD →
      fistaY (starGraph D hD) 1 α (starRho0 D α) (basisVec (starSeed D hD)) 2 j = 0 := by
  intro j hj hjw
  rw [fistaY_succ, fistaX_2_supp D hD α hα hα1 j hj]
  have hx1j : fistaX (starGraph D hD) 1 α (starRho0 D α) (basisVec (starSeed D hD)) 1 j = 0 := by
    have h1 : fistaX (starGraph D hD) 1 α (starRho0 D α) (basisVec (starSeed D hD)) 1 j =
        (starGraph D hD).proxMap 1 α (starRho0 D α) 1 (fun k =>
          (starGraph D hD).fwdStep α 1 (basisVec (starSeed D hD))
            (fistaY (starGraph D hD) 1 α (starRho0 D α) (basisVec (starSeed D hD)) 0) k) j := rfl
    rw [h1, fistaY_zero_eq]
    exact star_proxMap_other_zero D hD α (starRho0 D α) hα (starRho0_pos D hD α hα hα1)
      0 (fun _ _ => rfl) j hj hjw
  rw [hx1j]; ring

/-- **Gap 2 closed**: fistaX 3 w > 0 on the star graph at ρ₀. -/
theorem fistaX_3_w_pos (D : ℕ) (hD : 1 ≤ D) (α : ℝ) (hα : 0 < α) (hα1 : α < 1) :
    0 < fistaX (starGraph D hD) 1 α (starRho0 D α) (basisVec (starSeed D hD)) 3
      (starCenter D hD) := by
  have ⟨_, _, _, h4⟩ := fista_overshoot_at_k2 D hD α hα hα1
  have h_pos := fista_overshoot_positive D hD α hα hα1
  have hfY2v : starXv α (starRho0 D α) < fistaY (starGraph D hD) 1 α (starRho0 D α)
      (basisVec (starSeed D hD)) 2 (starSeed D hD) := by rw [h4]; exact h_pos
  -- fistaX 3 w = proxMap(fwdStep(fistaY 2)) w by definition
  have h3 : fistaX (starGraph D hD) 1 α (starRho0 D α) (basisVec (starSeed D hD)) 3
      (starCenter D hD) = (starGraph D hD).proxMap 1 α (starRho0 D α) 1 (fun j =>
        (starGraph D hD).fwdStep α 1 (basisVec (starSeed D hD))
          (fistaY (starGraph D hD) 1 α (starRho0 D α) (basisVec (starSeed D hD)) 2) j)
        (starCenter D hD) := rfl
  have hxv_pos := starXv_pos α (starRho0 D α) hα (starRho0_lt_one D hD α hα hα1)
  rw [h3]
  exact (star_activation_nonneg D hD α hα hα1 _
    (fistaY_2_supp D hD α hα hα1)
    (le_of_eq (fistaY_2_w_zero D hD α hα hα1).symm)
    (by linarith)).mpr
    (by rw [fistaY_2_w_zero D hD α hα hα1, zero_mul, zero_add]; exact hfY2v)

/-- **Gap 3 closed**: fistaY 3 w > 0. -/
theorem fistaY_3_w_pos (D : ℕ) (hD : 1 ≤ D) (α : ℝ) (hα : 0 < α) (hα1 : α < 1) :
    0 < fistaY (starGraph D hD) 1 α (starRho0 D α) (basisVec (starSeed D hD)) 3
      (starCenter D hD) := by
  rw [fistaY_succ, fistaX_2_w_zero D hD α hα hα1]
  nlinarith [fistaX_3_w_pos D hD α hα hα1, fistaMom_nonneg α hα (le_of_lt hα1)]



/-! ## Part 9: iterWork and totalWork Bounds (Gap 6) -/

/-- vol(S) ≥ deg(i) when i ∈ S. -/
lemma vol_ge_deg_of_mem (G : Graph n) (S : Finset (Fin n)) (i : Fin n) (hi : i ∈ S) :
    G.deg i ≤ G.vol S := by
  unfold Graph.vol
  exact Finset.single_le_sum (fun j _ => le_of_lt (G.deg_pos j)) hi

/-- If x_i ≠ 0, then i ∈ vecSupp x. -/
lemma mem_vecSupp_of_ne_zero (x : Fin n → ℝ) (i : Fin n) (h : x i ≠ 0) :
    i ∈ vecSupp x := by
  simp [vecSupp, Finset.mem_filter]; exact h

/-- **iterWork at k=2 ≥ D**: since fistaX 3 w > 0, vol(supp(x₃)) ≥ deg(w) = D. -/
theorem iterWork_2_ge_D (D : ℕ) (hD : 1 ≤ D) (α : ℝ) (hα : 0 < α) (hα1 : α < 1) :
    (D : ℝ) ≤ (starGraph D hD).iterWork 1 α (starRho0 D α) (basisVec (starSeed D hD)) 2 := by
  unfold Graph.iterWork
  have hx3w := fistaX_3_w_pos D hD α hα hα1
  have hw_mem : starCenter D hD ∈ vecSupp (fistaX (starGraph D hD) 1 α (starRho0 D α)
      (basisVec (starSeed D hD)) 3) :=
    mem_vecSupp_of_ne_zero _ _ (ne_of_gt hx3w)
  have hvol : (starGraph D hD).deg (starCenter D hD) ≤
      (starGraph D hD).vol (vecSupp (fistaX (starGraph D hD) 1 α (starRho0 D α)
        (basisVec (starSeed D hD)) 3)) :=
    vol_ge_deg_of_mem _ _ _ hw_mem
  rw [star_deg_center] at hvol
  linarith [show 0 ≤ (starGraph D hD).vol (vecSupp (fistaY (starGraph D hD) 1 α (starRho0 D α)
      (basisVec (starSeed D hD)) 2)) from
    Finset.sum_nonneg fun i _ => le_of_lt ((starGraph D hD).deg_pos i)]

/-- **iterWork at k=3 ≥ D**: since fistaY 3 w > 0, vol(supp(y₃)) ≥ deg(w) = D. -/
theorem iterWork_3_ge_D (D : ℕ) (hD : 1 ≤ D) (α : ℝ) (hα : 0 < α) (hα1 : α < 1) :
    (D : ℝ) ≤ (starGraph D hD).iterWork 1 α (starRho0 D α) (basisVec (starSeed D hD)) 3 := by
  unfold Graph.iterWork
  have hy3w := fistaY_3_w_pos D hD α hα hα1
  have hw_mem : starCenter D hD ∈ vecSupp (fistaY (starGraph D hD) 1 α (starRho0 D α)
      (basisVec (starSeed D hD)) 3) :=
    mem_vecSupp_of_ne_zero _ _ (ne_of_gt hy3w)
  have hvol : (starGraph D hD).deg (starCenter D hD) ≤
      (starGraph D hD).vol (vecSupp (fistaY (starGraph D hD) 1 α (starRho0 D α)
        (basisVec (starSeed D hD)) 3)) :=
    vol_ge_deg_of_mem _ _ _ hw_mem
  rw [star_deg_center] at hvol
  linarith [show 0 ≤ (starGraph D hD).vol (vecSupp (fistaX (starGraph D hD) 1 α (starRho0 D α)
      (basisVec (starSeed D hD)) 4)) from
    Finset.sum_nonneg fun i _ => le_of_lt ((starGraph D hD).deg_pos i)]

/-- **totalWork ≥ 2D for N ≥ 4**: from iterWork at k=2 and k=3. -/
theorem totalWork_ge_2D (D : ℕ) (hD : 1 ≤ D) (α : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (N : ℕ) (hN : 4 ≤ N) :
    2 * (D : ℝ) ≤ (starGraph D hD).totalWork 1 α (starRho0 D α)
      (basisVec (starSeed D hD)) N := by
  unfold Graph.totalWork
  -- totalWork N = ∑_{k ∈ range N} iterWork k ≥ iterWork 2 + iterWork 3
  have h2 : 2 ∈ Finset.range N := Finset.mem_range.mpr (by omega)
  have h3 : 3 ∈ Finset.range N := Finset.mem_range.mpr (by omega)
  have h23 : (2 : ℕ) ≠ 3 := by omega
  calc 2 * (D : ℝ)
      ≤ (starGraph D hD).iterWork 1 α (starRho0 D α) (basisVec (starSeed D hD)) 2 +
        (starGraph D hD).iterWork 1 α (starRho0 D α) (basisVec (starSeed D hD)) 3 := by
          linarith [iterWork_2_ge_D D hD α hα hα1, iterWork_3_ge_D D hD α hα hα1]
    _ ≤ ∑ k ∈ Finset.range N,
          (starGraph D hD).iterWork 1 α (starRho0 D α) (basisVec (starSeed D hD)) k := by
        rw [← Finset.sum_pair h23]
        exact Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.insert_subset_iff.mpr ⟨h2, Finset.singleton_subset_iff.mpr h3⟩)
          (fun k _ _ => by
            unfold Graph.iterWork Graph.vol
            apply add_nonneg <;>
              exact Finset.sum_nonneg fun i _ => le_of_lt ((starGraph D hD).deg_pos i))



/-! ## Part 12: Strengthened Results Matching Paper Statements -/

/- **Lemma 5.1 (full — unique minimizer with support {v})**:
    On G(D) with seed v and ρ ∈ [ρ₀, 1):
    The candidate x = starXv(α,ρ) · e_v satisfies ALL KKT conditions
    (active at v, inactive at w and all pendant leaves), so by α-strong convexity
    it is the UNIQUE minimizer with support S* = {v}.

    We verify each KKT condition explicitly: -/

/-- Active KKT at v: ∇_v f(x) = -αρ√d_v. -/
theorem star_kkt_active_v (D : ℕ) (hD : 1 ≤ D) (α ρ : ℝ)
    (hα : 0 < α) (_hρ_lt : ρ < 1) :
    (starGraph D hD).gradf α (basisVec (starSeed D hD))
      (fun i => if i = starSeed D hD then starXv α ρ else 0) (starSeed D hD) =
      -(1 * α * ρ * (starGraph D hD).sqrtDeg (starSeed D hD)) := by
  have hsupp : ∀ j, j ≠ starSeed D hD →
      (fun i : Fin (D+1) => if i = starSeed D hD then starXv α ρ else (0:ℝ)) j = 0 :=
    fun j hj => if_neg hj
  rw [star_gradf_v D hD α (starXv α ρ) _ hsupp (if_pos rfl)]
  rw [star_sqrtDeg_seed]; unfold starXv; field_simp; ring

/-- Inactive KKT at pendant leaf u: ∇_u f(x) = 0. -/
theorem star_kkt_inactive_u (D : ℕ) (hD : 1 ≤ D) (α ρ : ℝ)
    (u : Fin (D+1)) (hu_v : u ≠ starSeed D hD) (hu_w : u ≠ starCenter D hD) :
    (starGraph D hD).gradf α (basisVec (starSeed D hD))
      (fun i => if i = starSeed D hD then starXv α ρ else 0) u = 0 := by
  exact star_gradf_other D hD α _ (fun j hj => if_neg hj) u hu_v hu_w

/-- Inactive KKT at center w: margin ≥ 0 when ρ ≥ ρ₀ (center stays inactive). -/
theorem star_kkt_inactive_w (D : ℕ) (hD : 1 ≤ D) (α ρ : ℝ)
    (hα : 0 < α) (hα1 : α < 1) (hρ_ge : starRho0 D α ≤ ρ) (hρ_lt : ρ < 1) :
    0 ≤ α * ρ - α * (1 - α) * (1 - ρ) / ((1 + α) * ↑D) :=
  (star_leaf_breakpoint D hD α ρ hα hα1 hρ_ge hρ_lt).2.2.1

/-- Q ≽ αI: the quadratic form x^T Q x ≥ α · ‖x‖² for all x.
    This is the α-strong convexity of the PageRank quadratic f(x) = (1/2)x^TQx - α⟨D^{-1/2}s,x⟩.
    Proof: Q = (1+α)/2·I - (1-α)/2·D^{-1/2}AD^{-1/2}, and D^{-1/2}AD^{-1/2} ≼ I (Cauchy-Schwarz). -/
theorem Q_strong_convexity (G : Graph n) (α : ℝ) (_hα : 0 < α) (hα1 : α ≤ 1) :
    ∀ z : Fin n → ℝ, ∑ i, z i * ∑ j, G.Qentry α i j * z j ≥ α * ∑ i, z i ^ 2 := by
  intro z
  have hQ_bound : ∀ i j, G.Qentry α i j = if i = j then (1 + α) / 2 else
      -(1 - α) / 2 * G.A i j / (G.sqrtDeg i * G.sqrtDeg j) := by
    intro i j; unfold Graph.Qentry; rfl
  have hQ_pos_def : ∑ i, ∑ j, G.A i j * z i * z j / (G.sqrtDeg i * G.sqrtDeg j) ≤
      ∑ i, z i ^ 2 := by
    have h_cw : ∀ i j, G.A i j * z i * z j / (G.sqrtDeg i * G.sqrtDeg j) ≤
        (z i ^ 2 * G.A i j / (2 * G.sqrtDeg i ^ 2)) +
        (z j ^ 2 * G.A i j / (2 * G.sqrtDeg j ^ 2)) := by
      intro i j
      have hsi := G.sqrtDeg_pos i; have hsj := G.sqrtDeg_pos j
      rw [div_add_div _ _ (ne_of_gt (by positivity : (0:ℝ) < 2 * G.sqrtDeg i ^ 2))
                          (ne_of_gt (by positivity : (0:ℝ) < 2 * G.sqrtDeg j ^ 2))]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [sq_nonneg (z i * G.sqrtDeg j - z j * G.sqrtDeg i),
        show 0 ≤ G.A i j * G.sqrtDeg i * G.sqrtDeg j from
          mul_nonneg (mul_nonneg (G.A_nonneg i j) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)]
    refine' le_trans (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h_cw i j) _
    norm_num [Finset.sum_add_distrib, ← Finset.mul_sum _ _ _, ← Finset.sum_div]
    rw [← Finset.sum_comm]
    simp +decide [← Finset.mul_sum _ _ _, ← Finset.sum_div, G.A_symm]
    rw [← Finset.sum_add_distrib]; refine' Finset.sum_le_sum fun i _ => _
    rw [show G.sqrtDeg i ^ 2 = G.deg i from Real.sq_sqrt <| le_of_lt <| G.deg_pos' i]
    ring_nf; rw [← div_eq_mul_inv, div_le_iff₀]
    nlinarith [G.deg_pos' i, show ∑ j, G.A i j = G.deg i from rfl]
  have h_subst : ∑ i, z i * (∑ j, G.Qentry α i j * z j) =
      (1 + α) / 2 * ∑ i, z i ^ 2 -
      (1 - α) / 2 * ∑ i, ∑ j, G.A i j * z i * z j / (G.sqrtDeg i * G.sqrtDeg j) := by
    simp +decide [hQ_bound, Finset.sum_ite, Finset.filter_eq, Finset.filter_ne]
    simp +decide [Finset.mul_sum _ _ _, Finset.sum_add_distrib, mul_add, mul_assoc,
      mul_comm, mul_left_comm, div_eq_mul_inv, sq, G.A_no_loops]; ring
    norm_num [Finset.sum_add_distrib, Finset.mul_sum _ _ _, Finset.sum_mul _ _ _]; ring
    simpa only [← Finset.mul_sum _ _ _, ← Finset.sum_mul] using by ring
  nlinarith [hQ_pos_def, show 0 ≤ ∑ i, z i ^ 2 from Finset.sum_nonneg fun _ _ => sq_nonneg _]

/-- General theorem: a proximal-gradient fixed point of an α-strongly convex composite
    F = f + g is a minimizer. Proof: fObj_expansion + Q ≽ αI + subgradient inclusion. -/
theorem prox_fixed_point_is_minimizer (G : Graph n) (c α ρ : ℝ) (s x : Fin n → ℝ)
    (hα : 0 < α) (hα1 : α ≤ 1) (hc : 0 < c) (hρ : 0 < ρ)
    (hfp : ∀ i, G.proxMap c α ρ 1 (fun j => G.fwdStep α 1 s x j) i = x i)
    (hx_nonneg : ∀ i, 0 ≤ x i) :
    G.IsMinimizer c α ρ s x := by
  intro y; unfold Graph.FObj
  -- Use fObj_expansion: fObj(y) = fObj(x) + ⟨∇f(x), y-x⟩ + ½(y-x)ᵀQ(y-x)
  have hexp := fObj_expansion G α s x y
  -- Q ≽ αI ≽ 0: the quadratic term is ≥ 0
  have hQ := Q_strong_convexity G α hα hα1 (fun i => y i - x i)
  -- The subgradient inequality: ⟨∇f(x), y-x⟩ + gReg(y) - gReg(x) ≥ 0
  -- From fixed-point: for each i, x_i = softThresh(c·α·ρ·sqrtDeg(i), x_i - gradf(x)_i)
  -- This gives: if x_i > 0 then gradf(x)_i = -c·α·ρ·sqrtDeg(i)
  --             if x_i = 0 then |gradf(x)_i| ≤ c·α·ρ·sqrtDeg(i)
  -- Then coordinatewise: c·α·ρ·sqrtDeg(i)·|y_i| + gradf(x)_i·(y_i-x_i) ≥ c·α·ρ·sqrtDeg(i)·|x_i|
  suffices h_subgrad : ∑ i, G.gradf α s x i * (y i - x i) +
      (G.gReg c α ρ y - G.gReg c α ρ x) ≥ 0 by
    have hq_nn : 0 ≤ 1 / 2 * ∑ i, (y i - x i) * ∑ j, G.Qentry α i j * (y j - x j) := by
      apply mul_nonneg (by norm_num)
      have hQsc := Q_strong_convexity G α hα hα1 (fun i => y i - x i)
      nlinarith [Finset.sum_nonneg (fun (i : Fin n) (_ : i ∈ Finset.univ) => sq_nonneg (y i - x i))]
    linarith
  -- Prove the subgradient inequality coordinatewise
  unfold Graph.gReg
  have hreg : c * α * ρ * ∑ k, G.sqrtDeg k * |y k| - c * α * ρ * ∑ k, G.sqrtDeg k * |x k| =
      c * α * ρ * ∑ k, (G.sqrtDeg k * |y k| - G.sqrtDeg k * |x k|) := by
    rw [← mul_sub, ← Finset.sum_sub_distrib]
  rw [hreg]
  have hcomb : ∑ i, G.gradf α s x i * (y i - x i) +
      c * α * ρ * ∑ k, (G.sqrtDeg k * |y k| - G.sqrtDeg k * |x k|) =
      ∑ i, (G.gradf α s x i * (y i - x i) +
        c * α * ρ * (G.sqrtDeg i * |y i| - G.sqrtDeg i * |x i|)) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  rw [hcomb]
  apply Finset.sum_nonneg; intro i _
  -- For each i: gradf(x)_i·(y_i-x_i) + c·α·ρ·sqrtDeg(i)·(|y_i|-|x_i|) ≥ 0
  have hfp_i := hfp i
  unfold Graph.proxMap at hfp_i
  -- From the fixed-point: x_i = softThresh(c·1·α·ρ·sqrtDeg(i), fwdStep(x)_i)
  by_cases hxi : 0 < x i
  · -- x_i > 0: gradf(x)_i = -c·α·ρ·sqrtDeg(i), so the term becomes
    -- -c·α·ρ·sqrtDeg(i)·(y_i-x_i) + c·α·ρ·sqrtDeg(i)·(|y_i|-x_i)
    -- = c·α·ρ·sqrtDeg(i)·(|y_i|-y_i) ≥ 0
    have hfwd_pos : 1 * c * α * ρ * G.sqrtDeg i < G.fwdStep α 1 s x i := by
      unfold softThresh at hfp_i; split_ifs at hfp_i with h1 h2 <;> linarith
    have hgrad : G.gradf α s x i = -(c * α * ρ * G.sqrtDeg i) := by
      have : x i = G.fwdStep α 1 s x i - 1 * c * α * ρ * G.sqrtDeg i := by
        unfold softThresh at hfp_i; rw [if_pos hfwd_pos] at hfp_i; linarith
      unfold Graph.fwdStep at this; linarith
    rw [hgrad]; have hsq := G.sqrtDeg_pos i
    rw [abs_of_pos hxi]
    have h_abs_ge : y i ≤ |y i| := le_abs_self (y i)
    have h_pos : 0 < c * α * ρ * G.sqrtDeg i := by positivity
    nlinarith
  · -- x_i = 0
    push_neg at hxi; have hxi0 : x i = 0 := le_antisymm hxi (hx_nonneg i)
    have hgrad_le : |G.gradf α s x i| ≤ c * α * ρ * G.sqrtDeg i := by
      unfold softThresh at hfp_i; split_ifs at hfp_i with h1 h2
      · linarith
      · have : x i = G.fwdStep α 1 s x i + 1 * c * α * ρ * G.sqrtDeg i := by linarith
        unfold Graph.fwdStep at this; linarith [abs_nonneg (G.gradf α s x i)]
      · unfold Graph.fwdStep at h1 h2; simp only [hxi0] at h1 h2; rw [abs_le]
        constructor <;> linarith
    simp only [hxi0, abs_zero, mul_zero, sub_zero]
    have := G.sqrtDeg_pos i
    have habs := abs_le.mp hgrad_le
    -- Need: gradf·y + c*α*ρ*sqrtDeg·|y| ≥ 0
    -- From habs: -c*α*ρ*sqrtDeg ≤ gradf ≤ c*α*ρ*sqrtDeg
    -- Case split on sign of y i
    by_cases hy : 0 ≤ y i
    · rw [abs_of_nonneg hy]; nlinarith
    · push_neg at hy; rw [abs_of_neg hy]; nlinarith

/-- **Proximal-gradient fixed point**: The candidate x = starXv(α,ρ) · e_v satisfies
    x = proxMap(fwdStep(x)), i.e., it is a fixed point of the proximal-gradient operator.
    For α-strongly convex composite objectives, fixed points of proxMap ∘ fwdStep are
    exactly minimizers (standard convex optimization, cf. Beck (2017) Thm 10.16).
    Therefore this certificate, combined with α-strong convexity, proves that the candidate
    is the unique minimizer with support S* = {v}. -/
theorem star_candidate_fixed_point (D : ℕ) (hD : 1 ≤ D) (α ρ : ℝ)
    (hα : 0 < α) (hα1 : α < 1) (hρ_ge : starRho0 D α ≤ ρ) (hρ_lt : ρ < 1) :
    let x := fun i : Fin (D+1) => if i = starSeed D hD then starXv α ρ else 0
    -- The candidate is a fixed point of the proximal-gradient operator:
    ∀ i, (starGraph D hD).proxMap 1 α ρ 1
      (fun j => (starGraph D hD).fwdStep α 1 (basisVec (starSeed D hD)) x j) i = x i := by
  intro x i
  -- Unfold x to its definition everywhere
  show (starGraph D hD).proxMap 1 α ρ 1
    (fun j => (starGraph D hD).fwdStep α 1 (basisVec (starSeed D hD))
      (fun i => if i = starSeed D hD then starXv α ρ else 0) j) i =
    (if i = starSeed D hD then starXv α ρ else 0)
  by_cases hi_v : i = starSeed D hD
  · -- At v: proxMap(fwdStep(x))_v = (1-α)/2 · x_v + α(1-ρ) = x_v
    rw [hi_v, if_pos rfl]
    rw [star_proxMap_v D hD α ρ hα hρ_lt _ (fun j hj => if_neg hj)]
    · simp; unfold starXv; field_simp; ring
    · simp; unfold starXv; field_simp; nlinarith
  · rw [if_neg hi_v]
    by_cases hi_w : i = starCenter D hD
    · -- At w: proxMap(fwdStep(x))_w = 0 = x_w (margin ≥ 0 means fwdStep below threshold)
      rw [hi_w]
      apply star_proxMap_w_zero D hD α ρ _ (fun j hj => if_neg hj)
      -- Need |fwdStep_w| ≤ αρ√D, which is the margin nonnegativity
      simp only [ite_true]
      have hmargin := star_kkt_inactive_w D hD α ρ hα hα1 hρ_ge hρ_lt
      have hD_pos : (0 : ℝ) < ↑D := by exact_mod_cast show 0 < D by omega
      have hsqD := (starGraph D hD).sqrtDeg_pos (starCenter D hD)
      have hxv := starXv_pos α ρ hα hρ_lt
      unfold starXv
      rw [abs_of_nonneg (by
        apply mul_nonneg
        · exact le_of_lt (div_pos (by linarith) (by positivity))
        · exact le_of_lt (div_pos (by nlinarith) (by linarith)))]
      -- Now need: (1-α)/(2*sqrtDeg_c) * (2α(1-ρ)/(1+α)) ≤ α*ρ*sqrtDeg_c
      have hsqD_eq : (starGraph D hD).sqrtDeg (starCenter D hD) = √↑D := by
        unfold Graph.sqrtDeg; rw [star_deg_center]
      rw [hsqD_eq]
      rw [div_mul_div_comm, div_le_iff₀ (by positivity : (0:ℝ) < 2 * √↑D * (1 + α))]
      have hsqD_sq : √↑D * √↑D = ↑D := Real.mul_self_sqrt (le_of_lt hD_pos)
      -- From hmargin: α(1-α)(1-ρ)/((1+α)D) ≤ αρ
      -- Multiply by 2*(1+α)*D: 2α(1-α)(1-ρ) ≤ 2αρ(1+α)D
      have h1αD_pos : 0 < (1 + α) * ↑D := by positivity
      have hmargin_cleared : 2 * α * (1 - α) * (1 - ρ) ≤ 2 * α * ρ * (1 + α) * ↑D := by
        have := mul_nonneg (by linarith : (0:ℝ) ≤ 2 * (1 + α) * ↑D) hmargin
        have h_div : α * (1 - α) * (1 - ρ) / ((1 + α) * ↑D) * (2 * (1 + α) * ↑D) =
          2 * α * (1 - α) * (1 - ρ) := by field_simp
        nlinarith [h_div]
      have h_expand : α * ρ * √↑D * (2 * √↑D * (1 + α)) =
        2 * α * ρ * (1 + α) * (√↑D * √↑D) := by ring
      rw [hsqD_sq] at h_expand
      linarith [hmargin_cleared, h_expand]
    · -- At other leaf u: proxMap(fwdStep(x))_u = 0 = x_u
      exact star_proxMap_other_zero D hD α ρ hα (by linarith [starRho0_pos D hD α hα hα1])
        _ (fun j hj => if_neg hj) i hi_v hi_w

/-- The star graph candidate is an IsMinimizer (unique minimizer by α-strong convexity). -/
theorem star_candidate_is_minimizer (D : ℕ) (hD : 1 ≤ D) (α ρ : ℝ)
    (hα : 0 < α) (hα1 : α < 1) (hρ_ge : starRho0 D α ≤ ρ) (hρ_lt : ρ < 1) :
    (starGraph D hD).IsMinimizer 1 α ρ (basisVec (starSeed D hD))
      (fun i => if i = starSeed D hD then starXv α ρ else 0) :=
  prox_fixed_point_is_minimizer _ 1 α ρ _ _ hα (le_of_lt hα1) one_pos
    (by linarith [starRho0_pos D hD α hα hα1])
    (star_candidate_fixed_point D hD α ρ hα hα1 hρ_ge hρ_lt)
    (fun i => by simp [starXv]; split_ifs <;> [exact le_of_lt (starXv_pos α ρ hα hρ_lt); exact le_refl 0])

/-- **Lemma 5.1 (full — unique minimizer with support {v})**:
    On G(D) with seed v and ρ ∈ [ρ₀, 1), the candidate x = starXv(α,ρ) · e_v:
    (i)    has x_v > 0 (support includes v)
    (ii)   satisfies the active KKT condition at v
    (iii)  satisfies the inactive KKT at all pendant leaves (∇f = 0)
    (iv)   satisfies the inactive KKT at center w (margin ≥ 0)
    (v)    is a fixed point of the proximal-gradient operator (x = T(x))
    (vi)   has support exactly {v}: all other coordinates are 0
    (vii)  IS the unique minimizer (IsMinimizer): F(x) ≤ F(y) for all y

    Part (vii) is proved by prox_fixed_point_is_minimizer using (v) + Q ≽ αI. -/
theorem star_unique_minimizer_support (D : ℕ) (hD : 1 ≤ D) (α ρ : ℝ)
    (hα : 0 < α) (hα1 : α < 1) (hρ_ge : starRho0 D α ≤ ρ) (hρ_lt : ρ < 1) :
    let x := fun i : Fin (D+1) => if i = starSeed D hD then starXv α ρ else 0
    -- (i) x_v > 0
    0 < starXv α ρ
    -- (ii) Active KKT at v
    ∧ (starGraph D hD).gradf α (basisVec (starSeed D hD)) x (starSeed D hD) =
        -(1 * α * ρ * (starGraph D hD).sqrtDeg (starSeed D hD))
    -- (iii) Inactive KKT at pendant leaves
    ∧ (∀ u, u ≠ starSeed D hD → u ≠ starCenter D hD →
        (starGraph D hD).gradf α (basisVec (starSeed D hD)) x u = 0)
    -- (iv) Inactive KKT at w: margin ≥ 0
    ∧ 0 ≤ α * ρ - α * (1 - α) * (1 - ρ) / ((1 + α) * ↑D)
    -- (v) Fixed point of proximal-gradient: x = proxMap(fwdStep(x))
    ∧ (∀ i, (starGraph D hD).proxMap 1 α ρ 1
        (fun j => (starGraph D hD).fwdStep α 1 (basisVec (starSeed D hD)) x j) i = x i)
    -- (vi) Support is {v}: x_i = 0 for all i ≠ v
    ∧ (∀ i, i ≠ starSeed D hD → x i = 0)
    -- (vii) IsMinimizer: the candidate is the unique minimizer of F_ρ
    ∧ (starGraph D hD).IsMinimizer 1 α ρ (basisVec (starSeed D hD)) x := by
  intro x
  exact ⟨starXv_pos α ρ hα hρ_lt,
         star_kkt_active_v D hD α ρ hα hρ_lt,
         fun u hu_v hu_w => star_kkt_inactive_u D hD α ρ u hu_v hu_w,
         star_kkt_inactive_w D hD α ρ hα hα1 hρ_ge hρ_lt,
         star_candidate_fixed_point D hD α ρ hα hα1 hρ_ge hρ_lt,
         fun i hi => if_neg hi,
         star_candidate_is_minimizer D hD α ρ hα hα1 hρ_ge hρ_lt⟩

/-- **Corollary of Lemma D.2**: y_{k,v} > x*_v and y_{k,w} ≥ 0 implies x_{k+1,w} > 0. -/
theorem star_fista_activates_w (D : ℕ) (hD : 1 ≤ D) (α : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (y : Fin (D+1) → ℝ) (hsupp : ∀ j, j ≠ starSeed D hD → j ≠ starCenter D hD → y j = 0)
    (hyw : 0 ≤ y (starCenter D hD)) (hyv : starXv α (starRho0 D α) < y (starSeed D hD)) :
    0 < (starGraph D hD).proxMap 1 α (starRho0 D α) 1
      (fun j => (starGraph D hD).fwdStep α 1 (basisVec (starSeed D hD)) y j)
      (starCenter D hD) := by
  have hxv := starXv_pos α (starRho0 D α) hα (starRho0_lt_one D hD α hα hα1)
  exact (star_activation_nonneg D hD α hα hα1 y hsupp hyw (by linarith)).mpr
    (by nlinarith [(starGraph D hD).sqrtDeg_pos (starCenter D hD)])



/-! ## Paper-matching combined theorems

The following theorems combine split results into single statements matching
the paper's theorem numbering exactly. -/

/-- **Uniqueness of minimizer**: α-strong convexity implies uniqueness. -/
theorem minimizer_unique (G : Graph n) (c α ρ : ℝ) (s xstar y : Fin n → ℝ)
    (hα : 0 < α) (hα1 : α ≤ 1) (hc : 0 < c) (hρ : 0 < ρ)
    (hmin : G.IsMinimizer c α ρ s xstar) (hmin_y : G.IsMinimizer c α ρ s y) :
    y = xstar := by
  have hsc := minimizer_strong_convexity G c α ρ s xstar hα hα1 hc hρ hmin y
  have hns_zero : normSq (fun j => y j - xstar j) = 0 :=
    le_antisymm (by nlinarith [hmin_y xstar]) (normSq_nonneg _)
  funext j
  have hj_le : (y j - xstar j) ^ 2 ≤ normSq (fun j => y j - xstar j) :=
    Finset.single_le_sum (fun i _ => sq_nonneg (y i - xstar i)) (Finset.mem_univ j)
  have hj_eq : (y j - xstar j) ^ 2 = 0 := le_antisymm (by linarith) (sq_nonneg _)
  rw [sq] at hj_eq; linarith [mul_self_eq_zero.mp hj_eq]

/-- **Lemma D.1 (paper-matching combined statement)**:
    On G(D) with seed v and ρ ∈ [ρ₀, 1):
    (i)   x*_v = 2α(1−ρ)/(1+α) > 0 and is the unique minimizer with S* = {v}
    (ii)  Explicit margin formula γ_w = C·(ρ−ρ₀)
    (iii) γ_w = 0 at breakpoint ρ = ρ₀
    This bundles star_leaf_breakpoint + star_unique_minimizer_support. -/
theorem lemma_D1 (D : ℕ) (hD : 1 ≤ D) (α ρ : ℝ)
    (hα : 0 < α) (hα1 : α < 1) (hρ_ge : starRho0 D α ≤ ρ) (hρ_lt : ρ < 1) :
    let x := fun i : Fin (D+1) => if i = starSeed D hD then starXv α ρ else 0
    -- (i) Unique minimizer with S* = {v}
    (starGraph D hD).IsMinimizer 1 α ρ (basisVec (starSeed D hD)) x
    ∧ (∀ y, (starGraph D hD).IsMinimizer 1 α ρ (basisVec (starSeed D hD)) y → y = x)
    ∧ 0 < starXv α ρ
    ∧ (∀ i, i ≠ starSeed D hD → x i = 0)
    -- (ii) Explicit margin formula
    ∧ α * ρ - α * (1 - α) * (1 - ρ) / ((1 + α) * ↑D) =
        α * (↑D * (1 + α) + (1 - α)) / ((1 + α) * ↑D) * (ρ - starRho0 D α)
    -- (iii) Zero margin at breakpoint
    ∧ α * starRho0 D α - α * (1 - α) * (1 - starRho0 D α) / ((1 + α) * ↑D) = 0 := by
  intro x
  have h := star_unique_minimizer_support D hD α ρ hα hα1 hρ_ge hρ_lt
  have hb := star_leaf_breakpoint D hD α ρ hα hα1 hρ_ge hρ_lt
  have hρ_pos : 0 < ρ := lt_of_lt_of_le (starRho0_pos D hD α hα hα1) hρ_ge
  exact ⟨h.2.2.2.2.2.2,
    fun y hy => minimizer_unique _ 1 α ρ _ x y hα (le_of_lt hα1) one_pos hρ_pos
      h.2.2.2.2.2.2 hy,
    h.1, h.2.2.2.2.2.1, hb.2.1, hb.2.2.2⟩

/-- **Lemma D.2 (paper-matching combined statement)**:
    At ρ₀, with supp(y) ⊆ {v,w}:
    (i)  General: proxMap(w) ≠ 0 ↔ |y_w·√D + y_v| > x*_v
    (ii) Nonneg: when y_w, y_v ≥ 0, proxMap(w) > 0 ↔ y_w·√D + y_v > x*_v -/
theorem lemma_D2 (D : ℕ) (hD : 1 ≤ D) (α : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (y : Fin (D+1) → ℝ) (hsupp : ∀ j, j ≠ starSeed D hD → j ≠ starCenter D hD → y j = 0) :
    -- (i) General iff (no sign assumption)
    ((starGraph D hD).proxMap 1 α (starRho0 D α) 1
      (fun j => (starGraph D hD).fwdStep α 1 (basisVec (starSeed D hD)) y j)
      (starCenter D hD) ≠ 0 ↔
    starXv α (starRho0 D α) <
      |y (starCenter D hD) * (starGraph D hD).sqrtDeg (starCenter D hD) +
       y (starSeed D hD)|)
    -- (ii) Nonneg corollary
    ∧ (0 ≤ y (starCenter D hD) → 0 ≤ y (starSeed D hD) →
      (0 < (starGraph D hD).proxMap 1 α (starRho0 D α) 1
        (fun j => (starGraph D hD).fwdStep α 1 (basisVec (starSeed D hD)) y j)
        (starCenter D hD) ↔
      starXv α (starRho0 D α) <
        y (starCenter D hD) * (starGraph D hD).sqrtDeg (starCenter D hD) +
         y (starSeed D hD))) := by
  exact ⟨star_activation_criterion D hD α hα hα1 y hsupp,
         fun hyw hyv => star_activation_nonneg D hD α hα hα1 y hsupp hyw hyv⟩

/-- **Lemma D.3 (paper-matching combined statement)**:
    FISTA overshoots at k=2: y_{2,v} = x*_v · (1 + (1−α)β²/2) > x*_v,
    which activates center w (fistaX 3 w > 0). -/
theorem lemma_D3 (D : ℕ) (hD : 1 ≤ D) (α : ℝ) (hα : 0 < α) (hα1 : α < 1) :
    -- (i) Exact overshoot identity: y_{2,v} = x*_v · (1 + (1−α)β²/2)
    fistaY (starGraph D hD) 1 α (starRho0 D α) (basisVec (starSeed D hD)) 2 (starSeed D hD) =
      starXv α (starRho0 D α) * (1 + (1 - α) / 2 * (fistaMom α) ^ 2)
    -- (ii) The overshoot is positive: y_{2,v} > x*_v
    ∧ starXv α (starRho0 D α) <
      starXv α (starRho0 D α) * (1 + (1 - α) / 2 * (fistaMom α) ^ 2)
    -- (iii) FISTA activates center w at iteration k=2
    ∧ 0 < fistaX (starGraph D hD) 1 α (starRho0 D α) (basisVec (starSeed D hD)) 3
        (starCenter D hD) := by
  exact ⟨(fista_overshoot_at_k2 D hD α hα hα1).2.2.2,
    fista_overshoot_positive D hD α hα hα1, fistaX_3_w_pos D hD α hα hα1⟩

/-! ## General Path Graph for Appendix C.2 -/

/-- General path graph on m+1 nodes: nodes 0,1,...,m with edges (i,i+1). -/
def genPathGraph (m : ℕ) (hm : 2 ≤ m) : Graph (m + 1) where
  A := fun i j =>
    if (i.val + 1 = j.val) ∨ (j.val + 1 = i.val) then 1 else 0
  A_nonneg := fun _ _ => by split_ifs <;> norm_num
  A_symm := fun i j => by show (if _ then _ else _) = (if _ then _ else _); congr 1; apply propext; tauto
  A_no_loops := fun i => by show (if _ then _ else _) = _; split_ifs with h
                            · obtain h1 | h2 := h <;> omega
                            · rfl
  deg_pos := fun i => by
    have h_nn : ∀ j : Fin (m+1), 0 ≤ (if (i.val + 1 = j.val) ∨ (j.val + 1 = i.val) then (1:ℝ) else 0) := by
      intro j; split_ifs <;> norm_num
    by_cases hi : i.val < m
    · -- Node i has neighbor i+1
      have h1 : (if (i.val + 1 = (⟨i.val + 1, by omega⟩ : Fin (m+1)).val) ∨
          ((⟨i.val + 1, by omega⟩ : Fin (m+1)).val + 1 = i.val) then (1:ℝ) else 0) = 1 := by
        simp
      linarith [Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => h_nn j)
        (Finset.mem_univ (⟨i.val + 1, by omega⟩ : Fin (m+1)))]
    · -- Node m has neighbor m-1
      push_neg at hi; have him : i.val = m := by omega
      have h1 : (if (i.val + 1 = (⟨m - 1, by omega⟩ : Fin (m+1)).val) ∨
          ((⟨m - 1, by omega⟩ : Fin (m+1)).val + 1 = i.val) then (1:ℝ) else 0) = 1 := by
        simp only []; exact if_pos (Or.inr (by omega))
      linarith [Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => h_nn j)
        (Finset.mem_univ (⟨m - 1, by omega⟩ : Fin (m+1)))]

def genPathSeed (m : ℕ) (hm : 2 ≤ m) : Fin (m + 1) := ⟨0, by omega⟩
def genPathNode1 (m : ℕ) (hm : 2 ≤ m) : Fin (m + 1) := ⟨1, by omega⟩

/-- Seed node (node 0) of the general path has degree 1. -/
lemma genPath_deg_seed (m : ℕ) (hm : 2 ≤ m) :
    (genPathGraph m hm).deg (genPathSeed m hm) = 1 := by
  unfold Graph.deg genPathGraph genPathSeed
  rw [Finset.sum_eq_single ⟨1, by omega⟩]
  · simp only []; norm_num
  · intro j _ hj
    apply if_neg
    intro hor; cases hor with
    | inl h1 => exact hj (Fin.ext (by simp at h1 ⊢; omega))
    | inr h2 => simp at h2
  · intro h; exact absurd (Finset.mem_univ _) h

/-- Node 1 of the general path has degree 2 (for m ≥ 2). -/
lemma genPath_deg_node1 (m : ℕ) (hm : 2 ≤ m) :
    (genPathGraph m hm).deg (genPathNode1 m hm) = 2 := by
  show ∑ j : Fin (m+1), (genPathGraph m hm).A (genPathNode1 m hm) j = 2
  unfold genPathGraph genPathNode1
  -- The sum equals A(1,0) + A(1,2) + ∑_{j ≠ 0,2} A(1,j) = 1 + 1 + 0 = 2
  have hj0 : (⟨0, by omega⟩ : Fin (m+1)) ∈ Finset.univ := Finset.mem_univ _
  have hj2 : (⟨2, by omega⟩ : Fin (m+1)) ∈ Finset.univ := Finset.mem_univ _
  rw [← Finset.add_sum_erase _ _ hj0]
  have hj2e : (⟨2, by omega⟩ : Fin (m+1)) ∈ Finset.univ.erase ⟨0, by omega⟩ := by
    simp [Finset.mem_erase, Fin.ext_iff]
  rw [← Finset.add_sum_erase _ _ hj2e]
  have h0 : (if ((1:ℕ) + 1 = (0:ℕ) ∨ (0:ℕ) + 1 = 1) then (1:ℝ) else 0) = 1 := by norm_num
  have h2 : (if ((1:ℕ) + 1 = (2:ℕ) ∨ (2:ℕ) + 1 = 1) then (1:ℝ) else 0) = 1 := by norm_num
  simp only [] at h0 h2 ⊢
  rw [h0, h2]
  suffices ∑ x ∈ (Finset.univ.erase (⟨0, by omega⟩ : Fin (m+1))).erase ⟨2, by omega⟩,
    (if ((1:ℕ) + 1 = x.val ∨ x.val + 1 = 1) then (1:ℝ) else 0) = 0 by linarith
  apply Finset.sum_eq_zero; intro j hj
  have hj0 : j.val ≠ 0 := by
    intro h; apply (Finset.mem_erase.mp (Finset.mem_erase.mp hj).2).1
    exact Fin.ext (by simp_all)
  have hj2 : j.val ≠ 2 := by
    intro h; apply (Finset.mem_erase.mp hj).1
    exact Fin.ext (by simp_all)
  apply if_neg; push_neg; omega

lemma genPath_sqrtDeg_seed (m : ℕ) (hm : 2 ≤ m) :
    (genPathGraph m hm).sqrtDeg (genPathSeed m hm) = 1 := by
  unfold Graph.sqrtDeg; rw [genPath_deg_seed]; simp

/-- gradf at the seed when x = c·e₀ on the general path. -/
lemma genPath_gradf_seed (m : ℕ) (hm : 2 ≤ m) (α xv : ℝ) :
    (genPathGraph m hm).gradf α (basisVec (genPathSeed m hm))
      (fun i => if i = genPathSeed m hm then xv else 0) (genPathSeed m hm) =
      (1 + α) / 2 * xv - α := by
  unfold Graph.gradf
  rw [Finset.sum_eq_single (genPathSeed m hm)
    (fun j _ hj => by simp only [if_neg hj, mul_zero]) (fun h => absurd (Finset.mem_univ _) h)]
  simp only [if_pos rfl]
  simp only [Graph.invSqrtDeg]
  rw [genPath_deg_seed]; simp

/-- gradf at node 1 when x = c·e₀ on the general path. -/
lemma genPath_gradf_node1 (m : ℕ) (hm : 2 ≤ m) (α xv : ℝ) :
    (genPathGraph m hm).gradf α (basisVec (genPathSeed m hm))
      (fun i => if i = genPathSeed m hm then xv else 0) (genPathNode1 m hm) =
      -(1 - α) / (2 * √2) * xv := by
  unfold Graph.gradf
  rw [Finset.sum_eq_single (genPathSeed m hm)
    (fun j _ hj => by simp only [if_neg hj, mul_zero]) (fun h => absurd (Finset.mem_univ _) h)]
  simp only []
  have hne : genPathNode1 m hm ≠ genPathSeed m hm := by
    simp [genPathNode1, genPathSeed, Fin.ext_iff]
  simp only [Graph.Qentry, basisVec, if_neg hne, Graph.invSqrtDeg]
  rw [show (genPathGraph m hm).sqrtDeg (genPathSeed m hm) = 1 from genPath_sqrtDeg_seed m hm]
  rw [show (genPathGraph m hm).sqrtDeg (genPathNode1 m hm) = √2 from by
    unfold Graph.sqrtDeg; rw [genPath_deg_node1]]
  rw [show (genPathGraph m hm).A (genPathNode1 m hm) (genPathSeed m hm) = 1 from by
    unfold genPathGraph genPathNode1 genPathSeed; simp]
  rw [genPath_deg_node1]; simp only [if_true]; ring

/-- gradf at node i (i ≥ 2) when x = c·e₀ on the general path: zero (no edge to 0). -/
lemma genPath_gradf_other (m : ℕ) (hm : 2 ≤ m) (α xv : ℝ)
    (u : Fin (m+1)) (hu0 : u ≠ genPathSeed m hm) (hu1 : u ≠ genPathNode1 m hm) :
    (genPathGraph m hm).gradf α (basisVec (genPathSeed m hm))
      (fun i => if i = genPathSeed m hm then xv else 0) u = 0 := by
  unfold Graph.gradf
  rw [Finset.sum_eq_single (genPathSeed m hm)
    (fun j _ hj => by simp only [if_neg hj, mul_zero]) (fun h => absurd (Finset.mem_univ _) h)]
  simp only []
  -- A(u, 0) = 0 since u ≥ 2 and 0 + 1 = 1 ≠ u
  have hA0 : (genPathGraph m hm).A u (genPathSeed m hm) = 0 := by
    unfold genPathGraph genPathSeed
    apply if_neg; simp only []; intro hor; cases hor with
    | inl h => omega
    | inr h => exact hu1 (Fin.ext (show u.val = (genPathNode1 m hm).val from by
        unfold genPathNode1; simp only []; omega))
  simp only [Graph.Qentry, basisVec, if_neg hu0, Graph.invSqrtDeg, hA0]
  ring

/-! ### General KKT → Minimizer lemma -/

/-- KKT conditions for a nonneg vector imply it is a proximal-gradient fixed point.
    Active KKT: gradf_i = -cαρ√d_i when x_i > 0.
    Inactive KKT: |gradf_i| ≤ cαρ√d_i when x_i = 0.
    These are equivalent to x = proxMap(fwdStep(x)). -/
lemma kkt_implies_fixed_point (G : Graph n) (c α ρ : ℝ) (s x : Fin n → ℝ)
    (_hα : 0 < α) (_hc : 0 < c) (_hρ : 0 < ρ)
    (hx_nonneg : ∀ i, 0 ≤ x i)
    (hkkt_active : ∀ i, 0 < x i → G.gradf α s x i = -(c * α * ρ * G.sqrtDeg i))
    (hkkt_inactive : ∀ i, x i = 0 → |G.gradf α s x i| ≤ c * α * ρ * G.sqrtDeg i) :
    ∀ j, G.proxMap c α ρ 1 (fun k => G.fwdStep α 1 s x k) j = x j := by
  intro j
  by_cases hxj : 0 < x j
  · -- Active: fwdStep_j = x_j + cαρ√d_j > threshold, softThresh returns x_j
    unfold Graph.proxMap Graph.fwdStep; dsimp only; rw [hkkt_active j hxj]
    unfold softThresh; rw [if_pos (by nlinarith [G.sqrtDeg_pos j])]; ring
  · -- Inactive: |fwdStep_j| = |gradf_j| ≤ threshold, softThresh returns 0
    push_neg at hxj; have hxj0 : x j = 0 := le_antisymm hxj (hx_nonneg j)
    unfold Graph.proxMap Graph.fwdStep; dsimp only; rw [hxj0]
    apply softThresh_zero_of_abs_le; simp only [one_mul, zero_sub, abs_neg]
    exact hkkt_inactive j hxj0

/-- KKT conditions for a nonneg vector imply it is the unique minimizer.
    Combines kkt_implies_fixed_point with prox_fixed_point_is_minimizer. -/
theorem kkt_implies_minimizer (G : Graph n) (c α ρ : ℝ) (s x : Fin n → ℝ)
    (hα : 0 < α) (hα1 : α ≤ 1) (hc : 0 < c) (hρ : 0 < ρ)
    (hx_nonneg : ∀ i, 0 ≤ x i)
    (hkkt_active : ∀ i, 0 < x i → G.gradf α s x i = -(c * α * ρ * G.sqrtDeg i))
    (hkkt_inactive : ∀ i, x i = 0 → |G.gradf α s x i| ≤ c * α * ρ * G.sqrtDeg i) :
    G.IsMinimizer c α ρ s x :=
  prox_fixed_point_is_minimizer G c α ρ s x hα hα1 hc hρ
    (kkt_implies_fixed_point G c α ρ s x hα hc hρ hx_nonneg hkkt_active hkkt_inactive)
    hx_nonneg

/-- **Appendix C.2 (general m, full — unique minimizer)**:
    On the path P_{m+1} with seed at node 0 and m ≥ 2,
    for ρ ∈ [(1−α)/(3+α), 1): the candidate x = (2α(1−ρ)/(1+α))·e₀ is the
    unique minimizer with S* = {0}, and the margin at node 1 is
    γ₁ = α(3+α)/(2(1+α))·(ρ − ρ₀) where ρ₀ = (1−α)/(3+α).

    This matches the paper's Lemma C.2 at full generality for any m ≥ 2. -/
theorem genPath_unique_minimizer (m : ℕ) (hm : 2 ≤ m) (α ρ : ℝ)
    (hα : 0 < α) (hα1 : α < 1) (hρ_ge : (1 - α) / (3 + α) ≤ ρ) (hρ_lt : ρ < 1) :
    let xv := 2 * α * (1 - ρ) / (1 + α)
    let x := fun i => if i = genPathSeed m hm then xv else 0
    -- (i) x_v > 0
    0 < xv
    -- (ii) IsMinimizer
    ∧ (genPathGraph m hm).IsMinimizer 1 α ρ (basisVec (genPathSeed m hm)) x
    -- (iii) Support = {seed}
    ∧ (∀ i, i ≠ genPathSeed m hm → x i = 0)
    -- (iv) Margin formula
    ∧ 0 ≤ α * (3 + α) / (2 * (1 + α)) * (ρ - (1 - α) / (3 + α)) := by
  have hxv_pos : 0 < 2 * α * (1 - ρ) / (1 + α) := by
    apply div_pos (mul_pos (mul_pos (by norm_num : (0:ℝ) < 2) hα) (by linarith)) (by linarith)
  intro xv x
  refine ⟨hxv_pos, ?_, fun i hi => if_neg hi,
    mul_nonneg (div_nonneg (by nlinarith) (by linarith)) (sub_nonneg.mpr hρ_ge)⟩
  apply kkt_implies_minimizer _ 1 α ρ _ _ hα (le_of_lt hα1) one_pos
    (by linarith [div_pos (by linarith : (0:ℝ) < 1 - α) (by linarith : (0:ℝ) < 3 + α)])
  · intro i; simp only [x]; split_ifs <;> [exact le_of_lt hxv_pos; exact le_refl 0]
  · -- Active KKT at seed
    intro i hi
    have : i = genPathSeed m hm := by
      by_contra h; simp only [x] at hi; rw [if_neg h] at hi; linarith
    subst this; simp only [x]
    rw [genPath_gradf_seed, genPath_sqrtDeg_seed]; simp only [xv]
    have h1α : (1:ℝ) + α ≠ 0 := ne_of_gt (by linarith)
    field_simp; ring
  · -- Inactive KKT
    intro i hi
    have hi_ne : i ≠ genPathSeed m hm := by
      intro h; simp only [x, h, if_pos rfl] at hi; simp only [xv] at hi; linarith
    by_cases hi1 : i = genPathNode1 m hm
    · -- Node 1: margin condition
      subst hi1; simp only [x]
      rw [genPath_gradf_node1]
      have hxv_pos' : 0 < xv := hxv_pos
      simp only [xv] at hxv_pos'
      have hcoeff_neg : -(1 - α) / (2 * √2) < 0 := by
        apply div_neg_of_neg_of_pos <;> [linarith; positivity]
      rw [abs_of_nonpos (by nlinarith [mul_neg_of_neg_of_pos hcoeff_neg hxv_pos])]
      simp only [one_mul]; rw [show (genPathGraph m hm).sqrtDeg (genPathNode1 m hm) = √2 from by
        unfold Graph.sqrtDeg; rw [genPath_deg_node1]]
      rw [show -(-(1 - α) / (2 * √2) * xv) = (1 - α) / (2 * √2) * xv from by ring]
      simp only [xv]
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : 0 < 2 * √2)]
      have h1α_ne : (1:ℝ) + α ≠ 0 := ne_of_gt (by linarith)
      have hsq2 : √(2:ℝ) * √2 = 2 := Real.mul_self_sqrt (by norm_num)
      have hsq2_sq : √(2:ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      field_simp
      simp only [hsq2_sq]
      have hρ_cleared : (1 - α) ≤ ρ * (3 + α) := by
        rwa [div_le_iff₀ (by linarith : (0:ℝ) < 3 + α)] at hρ_ge
      nlinarith [hρ_cleared]
    · -- Node i ≥ 2: gradient = 0
      simp only [x]
      rw [genPath_gradf_other m hm α _ i hi_ne hi1]; simp
      have hρ_nn : 0 ≤ ρ := by linarith [hρ_ge, div_nonneg (by linarith : (0:ℝ) ≤ 1 - α) (by linarith : (0:ℝ) ≤ 3 + α)]
      exact mul_nonneg (mul_nonneg hα.le hρ_nn) ((genPathGraph m hm).sqrtDeg_pos i).le


/-! ## Part 13: Bad-Instance Lemmas with Uniqueness (Appendix C) -/


/-! ### Appendix C.1: Star graph with seed at center — full statement -/

/-- gradf at the center when seed = center and x = c·e_center on the star graph. -/
lemma star_gradf_center_seed (D : ℕ) (hD : 1 ≤ D) (α xc : ℝ) :
    (starGraph D hD).gradf α (basisVec (starCenter D hD))
      (fun i => if i = starCenter D hD then xc else 0) (starCenter D hD) =
      (1 + α) / 2 * xc - α / (starGraph D hD).sqrtDeg (starCenter D hD) := by
  unfold Graph.gradf
  rw [Finset.sum_eq_single (starCenter D hD)
    (fun j _ hj => by simp only [if_neg hj, mul_zero]) (fun h => absurd (Finset.mem_univ _) h)]
  simp [Graph.Qentry, basisVec, Graph.invSqrtDeg]; ring

/-- gradf at a leaf when seed = center and x = c·e_center on the star graph. -/
lemma star_gradf_leaf_center_seed (D : ℕ) (hD : 1 ≤ D) (α xc : ℝ)
    (ℓ : Fin (D+1)) (hℓ : ℓ ≠ starCenter D hD) :
    (starGraph D hD).gradf α (basisVec (starCenter D hD))
      (fun i => if i = starCenter D hD then xc else 0) ℓ =
      -(1 - α) / (2 * (starGraph D hD).sqrtDeg (starCenter D hD)) * xc := by
  unfold Graph.gradf
  rw [Finset.sum_eq_single (starCenter D hD)
    (fun j _ hj => by simp only [if_neg hj, mul_zero]) (fun h => absurd (Finset.mem_univ _) h)]
  simp only []
  have hℓ0 : ℓ.val ≠ 0 := fun h => hℓ (Fin.ext h)
  -- Key facts about the star graph at leaf ℓ
  have hA : (starGraph D hD).A ℓ (starCenter D hD) = 1 := by
    unfold starGraph starCenter
    apply if_pos; right; exact ⟨hℓ0, rfl⟩
  have hℓ_deg : (starGraph D hD).deg ℓ = 1 := by
    unfold Graph.deg starGraph
    rw [Finset.sum_eq_single ⟨0, by omega⟩]
    · apply if_pos; right; exact ⟨hℓ0, rfl⟩
    · intro j _ hj
      apply if_neg
      intro hor; cases hor with
      | inl h => exact absurd h.1 hℓ0
      | inr h => exact hj (Fin.ext (by exact h.2))
    · intro h; exact absurd (Finset.mem_univ _) h
  have hℓ_sqrtDeg : (starGraph D hD).sqrtDeg ℓ = 1 := by
    unfold Graph.sqrtDeg; rw [hℓ_deg]; simp
  -- Now compute: Qentry * xc - α * invSqrtDeg * 0
  simp only [Graph.Qentry, basisVec, if_neg hℓ, Graph.invSqrtDeg]
  rw [hA, hℓ_sqrtDeg]; ring_nf; simp

/-- **Appendix C.1 (full — unique minimizer)**: Star graph with seed at center.
    On the star graph G(D) with seed s = e_c (center), for ρ ∈ [ρ₀, 1/D):
    the candidate x = (2α(1−ρD)/((1+α)√D)) · e_c is the unique minimizer,
    with support S* = {c}, margin γ_ℓ = 2α/(1+α)·(ρ−ρ₀), and γ = 0 at ρ₀.

    This formalizes the full statement of Lemma C.1 including the unique minimizer
    conclusion (via KKT verification + α-strong convexity). -/
theorem star_center_seed_unique_minimizer (D : ℕ) (hD : 1 ≤ D)
    (α ρ : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (hρ_ge : (1 - α) / (2 * ↑D) ≤ ρ) (hρ_lt : ρ < 1 / ↑D) :
    let xc := 2 * α * (1 - ρ * ↑D) / ((1 + α) * (starGraph D hD).sqrtDeg (starCenter D hD))
    let x := fun i => if i = starCenter D hD then xc else 0
    -- (i) x_c > 0
    0 < xc
    -- (ii) IsMinimizer: x is the unique minimizer
    ∧ (starGraph D hD).IsMinimizer 1 α ρ (basisVec (starCenter D hD)) x
    -- (iii) Support = {c}
    ∧ (∀ i, i ≠ starCenter D hD → x i = 0)
    -- (iv) Margin ≥ 0
    ∧ 0 ≤ 2 * α / (1 + α) * (ρ - (1 - α) / (2 * ↑D)) := by
  have hD_pos : (0 : ℝ) < ↑D := by exact_mod_cast show 0 < D by omega
  have hsqD := (starGraph D hD).sqrtDeg_pos (starCenter D hD)
  have hxc_pos : 0 < 2 * α * (1 - ρ * ↑D) / ((1 + α) * (starGraph D hD).sqrtDeg (starCenter D hD)) := by
    apply div_pos (by nlinarith [show ρ * ↑D < 1 from by rwa [lt_div_iff₀ hD_pos] at hρ_lt])
    exact mul_pos (by linarith) hsqD
  refine ⟨hxc_pos, ?_, fun i hi => if_neg hi,
    mul_nonneg (by positivity) (sub_nonneg.mpr hρ_ge)⟩
  -- Prove IsMinimizer via KKT
  apply kkt_implies_minimizer _ 1 α ρ _ _ hα (le_of_lt hα1) one_pos
    (by linarith [div_pos (by linarith : (0:ℝ) < 1 - α) (by positivity : (0:ℝ) < 2 * ↑D)])
  · intro i; show 0 ≤ (if i = starCenter D hD then _ else 0); split_ifs <;> [exact le_of_lt hxc_pos; exact le_refl 0]
  · -- Active KKT at center
    intro i hi
    have hi_center : i = starCenter D hD := by
      by_contra h
      show False
      have : (if i = starCenter D hD then
        2 * α * (1 - ρ * ↑D) / ((1 + α) * (starGraph D hD).sqrtDeg (starCenter D hD)) else 0) ≤ 0 :=
        by rw [if_neg h]
      linarith
    subst hi_center
    show (starGraph D hD).gradf α (basisVec (starCenter D hD))
      (fun i => if i = starCenter D hD then
        2 * α * (1 - ρ * ↑D) / ((1 + α) * (starGraph D hD).sqrtDeg (starCenter D hD)) else 0)
      (starCenter D hD) = _
    rw [star_gradf_center_seed]
    have hsqD_eq : (starGraph D hD).sqrtDeg (starCenter D hD) = √↑D := by
      unfold Graph.sqrtDeg; rw [star_deg_center]
    rw [hsqD_eq]
    have hsqD_ne : √↑D ≠ 0 := ne_of_gt (Real.sqrt_pos_of_pos hD_pos)
    have h1α_ne : (1:ℝ) + α ≠ 0 := ne_of_gt (by linarith)
    have hsqD_sq : √(↑D : ℝ) ^ 2 = ↑D := Real.sq_sqrt (le_of_lt hD_pos)
    field_simp; rw [hsqD_sq]; ring
  · -- Inactive KKT at leaves
    intro i hi
    have hi_ne : i ≠ starCenter D hD := by
      intro h; subst h
      have : (if (starCenter D hD) = starCenter D hD then
        2 * α * (1 - ρ * ↑D) / ((1 + α) * (starGraph D hD).sqrtDeg (starCenter D hD)) else 0) = 0 := hi
      rw [if_pos rfl] at this; linarith
    show |(starGraph D hD).gradf α (basisVec (starCenter D hD))
      (fun i => if i = starCenter D hD then
        2 * α * (1 - ρ * ↑D) / ((1 + α) * (starGraph D hD).sqrtDeg (starCenter D hD)) else 0)
      i| ≤ _
    rw [star_gradf_leaf_center_seed D hD α _ i hi_ne]
    have hsqD_eq : (starGraph D hD).sqrtDeg (starCenter D hD) = √↑D := by
      unfold Graph.sqrtDeg; rw [star_deg_center]
    have hi0 : i.val ≠ 0 := fun h => hi_ne (Fin.ext h)
    have hi_deg : (starGraph D hD).deg i = 1 := by
      unfold Graph.deg starGraph
      rw [Finset.sum_eq_single ⟨0, by omega⟩]
      · exact if_pos (Or.inr ⟨hi0, rfl⟩)
      · intro j _ hj; apply if_neg; intro hor; cases hor with
        | inl h => exact absurd h.1 hi0
        | inr h => exact hj (Fin.ext h.2)
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [show (starGraph D hD).sqrtDeg i = 1 from by unfold Graph.sqrtDeg; rw [hi_deg]; simp]
    simp only [one_mul, mul_one]
    rw [hsqD_eq]
    have hρD_lt1 : ρ * ↑D < 1 := by rwa [lt_div_iff₀ hD_pos] at hρ_lt
    have hgradf_le : 0 ≤ (1 - α) / (2 * √↑D) * (2 * α * (1 - ρ * ↑D) / ((1 + α) * √↑D)) := by
      apply mul_nonneg
      · exact le_of_lt (div_pos (by linarith) (by positivity))
      · exact le_of_lt (div_pos (by nlinarith) (by positivity))
    rw [show -(1 - α) / (2 * √↑D) * (2 * α * (1 - ρ * ↑D) / ((1 + α) * √↑D)) =
      -((1 - α) / (2 * √↑D) * (2 * α * (1 - ρ * ↑D) / ((1 + α) * √↑D))) from by ring]
    rw [abs_neg, abs_of_nonneg hgradf_le]
    have hsqD_ne : √↑D ≠ 0 := ne_of_gt (Real.sqrt_pos_of_pos hD_pos)
    have h1α_ne : (1:ℝ) + α ≠ 0 := ne_of_gt (by linarith)
    rw [div_mul_div_comm, div_le_iff₀ (by positivity : (0:ℝ) < 2 * √↑D * ((1 + α) * √↑D))]
    have hsqD_sq : √(↑D : ℝ) * √↑D = ↑D := Real.mul_self_sqrt (le_of_lt hD_pos)
    have h_expand : α * ρ * (2 * √↑D * ((1 + α) * √↑D)) =
      2 * α * ρ * (1 + α) * (√↑D * √↑D) := by ring
    rw [hsqD_sq] at h_expand
    have hρ_cleared : (1 - α) ≤ ρ * (2 * ↑D) := by
      rwa [div_le_iff₀ (by positivity : (0:ℝ) < 2 * ↑D)] at hρ_ge
    nlinarith [hρ_cleared, h_expand]

/-- **Appendix C.1**: Star graph with seed at center — breakpoint algebra.
    See star_center_seed_unique_minimizer for the full unique minimizer statement. -/
theorem star_center_breakpoint (D : ℕ) (hD : 1 ≤ D) (α : ℝ) (hα : 0 < α) (_hα1 : α ≤ 1)
    (ρ : ℝ) (hρ_ge : (1 - α) / (2 * ↑D) ≤ ρ) (hρ_lt : ρ < 1 / ↑D) :
    let ρ₀ := (1 - α) / (2 * ↑D)
    -- (i) x*_c > 0 (support includes c)
    0 < 2 * α * (1 - ρ * ↑D) / ((1 + α) * √(↑D))
    -- (ii) KKT margin: γ_ℓ = 2α/(1+α)·(ρ - ρ₀) (explicit formula)
    ∧ α * ρ - (1 - α) / (2 * √(↑D)) * (2 * α * (1 - ρ * ↑D) / ((1 + α) * √(↑D))) =
        2 * α / (1 + α) * (ρ - ρ₀)
    -- (iii) At ρ₀, γ = 0 (breakpoint)
    ∧ 2 * α / (1 + α) * (ρ₀ - ρ₀) = 0
    -- (iv) Margin is nonneg for ρ ≥ ρ₀ (all leaves inactive → S* = {c})
    ∧ 0 ≤ 2 * α / (1 + α) * (ρ - ρ₀) := by
  have hD_pos : (0 : ℝ) < ↑D := by exact_mod_cast show 0 < D by omega
  have hρD_lt : ρ * ↑D < 1 := by rwa [lt_div_iff₀ hD_pos] at hρ_lt
  refine ⟨by apply div_pos (by nlinarith) (by positivity), ?_, by ring,
    mul_nonneg (by positivity) (sub_nonneg.mpr hρ_ge)⟩
  have hsD := Real.sqrt_pos_of_pos hD_pos
  have hsD_ne : √↑D ≠ 0 := ne_of_gt hsD
  have h1α_ne : (1:ℝ) + α ≠ 0 := ne_of_gt (by linarith)
  have hD2_ne : (2:ℝ) * ↑D ≠ 0 := ne_of_gt (by positivity)
  have hsqD_sq : √↑D * √↑D = ↑D := Real.mul_self_sqrt (le_of_lt hD_pos)
  have hsqD_pow : √(↑D : ℝ) ^ 2 = ↑D := Real.sq_sqrt (le_of_lt hD_pos)
  have hkey : (1 - α) / (2 * √↑D) * (2 * α * (1 - ρ * ↑D) / ((1 + α) * √↑D)) =
    α * (1 - α) * (1 - ρ * ↑D) / ((1 + α) * ↑D) := by
    field_simp
    rw [hsqD_pow]
  rw [hkey]
  field_simp
  ring

/-- **Lemma C.1 (paper-matching combined statement)**:
    Star graph G(D) with seed at center c, α ∈ (0,1), D ≥ 1.
    For ρ ∈ [ρ₀, 1/D) where ρ₀ = (1−α)/(2D):
    x* = x_c · e_c is the unique minimizer with S* = {c},
    margin γ_ℓ = 2α/(1+α)·(ρ−ρ₀), and γ = 0 at ρ₀. -/
theorem lemma_C1 (D : ℕ) (hD : 1 ≤ D) (α ρ : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (hρ_ge : (1 - α) / (2 * ↑D) ≤ ρ) (hρ_lt : ρ < 1 / ↑D) :
    let ρ₀ := (1 - α) / (2 * ↑D)
    let xc := 2 * α * (1 - ρ * ↑D) / ((1 + α) * (starGraph D hD).sqrtDeg (starCenter D hD))
    let x := fun i => if i = starCenter D hD then xc else 0
    -- (i) Unique minimizer
    (starGraph D hD).IsMinimizer 1 α ρ (basisVec (starCenter D hD)) x
    ∧ (∀ y, (starGraph D hD).IsMinimizer 1 α ρ (basisVec (starCenter D hD)) y → y = x)
    -- (ii) x_c > 0 with support S* = {c}
    ∧ 0 < xc
    ∧ (∀ i, i ≠ starCenter D hD → x i = 0)
    -- (iii) Margin equality: γ_ℓ = 2α/(1+α)·(ρ − ρ₀)
    ∧ α * ρ - (1 - α) / (2 * √(↑D)) * (2 * α * (1 - ρ * ↑D) / ((1 + α) * √(↑D))) =
        2 * α / (1 + α) * (ρ - ρ₀)
    -- (iv) Margin nonneg and zero at breakpoint
    ∧ 0 ≤ 2 * α / (1 + α) * (ρ - ρ₀)
    ∧ 2 * α / (1 + α) * (ρ₀ - ρ₀) = 0 := by
  intro ρ₀ xc x
  have h := star_center_seed_unique_minimizer D hD α ρ hα hα1 hρ_ge hρ_lt
  have hbp := star_center_breakpoint D hD α hα (le_of_lt hα1) ρ hρ_ge hρ_lt
  have hρ_pos : 0 < ρ := lt_of_lt_of_le (div_pos (by linarith) (by positivity)) hρ_ge
  exact ⟨h.2.1,
    fun y hy => minimizer_unique _ 1 α ρ _ x y hα (le_of_lt hα1) one_pos hρ_pos h.2.1 hy,
    h.1, fun i hi => if_neg hi, hbp.2.1, h.2.2.2, by ring⟩

/-! ### Appendix C.2: Path graph with seed at endpoint — full statement -/

/-- Path graph on 3 nodes (P₃): nodes 0-1-2 with edges (0,1) and (1,2).
    This is the minimal instance of the paper's path P_{m+1} for m ≥ 2.
    Nodes i ≥ 3 have zero gradient and are irrelevant to the breakpoint analysis,
    so the 3-node case captures the full algebraic content. -/
def pathGraph3 : Graph 3 where
  A := fun i j =>
    if (i.val = 0 ∧ j.val = 1) ∨ (i.val = 1 ∧ j.val = 0) ∨
       (i.val = 1 ∧ j.val = 2) ∨ (i.val = 2 ∧ j.val = 1) then 1 else 0
  A_nonneg := fun _ _ => by split_ifs <;> norm_num
  A_symm := fun i j => by show (if _ then _ else _) = (if _ then _ else _); congr 1; apply propext; constructor <;> (intro h; rcases h with ⟨a,b⟩ | ⟨a,b⟩ | ⟨a,b⟩ | ⟨a,b⟩ <;> omega)
  A_no_loops := fun i => by show (if _ then _ else _) = _; split_ifs with h
                            · obtain ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ := h <;> omega
                            · rfl
  deg_pos := fun i => by
    show 0 < ∑ j : Fin 3, (if (i.val = 0 ∧ j.val = 1) ∨ (i.val = 1 ∧ j.val = 0) ∨
       (i.val = 1 ∧ j.val = 2) ∨ (i.val = 2 ∧ j.val = 1) then (1:ℝ) else 0)
    fin_cases i <;> simp (config := { decide := true })

def pathSeed : Fin 3 := ⟨0, by omega⟩
def pathNode1 : Fin 3 := ⟨1, by omega⟩
def pathNode2 : Fin 3 := ⟨2, by omega⟩

lemma path3_deg_seed : pathGraph3.deg pathSeed = 1 := by
  show ∑ j : Fin 3, pathGraph3.A ⟨0, by omega⟩ j = 1
  rw [Fin.sum_univ_three]; unfold pathGraph3; simp

lemma path3_deg_node1 : pathGraph3.deg pathNode1 = 2 := by
  show ∑ j : Fin 3, pathGraph3.A ⟨1, by omega⟩ j = 2
  rw [Fin.sum_univ_three]; unfold pathGraph3; simp; norm_num

lemma path3_sqrtDeg_seed : pathGraph3.sqrtDeg pathSeed = 1 := by
  unfold Graph.sqrtDeg; rw [path3_deg_seed]; simp

/-- gradf at the seed (node 0) when x = c·e₀ and s = e₀ on the 3-node path. -/
lemma path3_gradf_seed (α xv : ℝ) :
    pathGraph3.gradf α (basisVec pathSeed)
      (fun i => if i = pathSeed then xv else 0) pathSeed =
      (1 + α) / 2 * xv - α := by
  unfold Graph.gradf
  rw [Finset.sum_eq_single pathSeed
    (fun j _ hj => by simp only [if_neg hj, mul_zero]) (fun h => absurd (Finset.mem_univ _) h)]
  simp only [if_pos rfl]
  have hA00 : pathGraph3.A pathSeed pathSeed = 0 := by unfold pathGraph3 pathSeed; simp
  simp only [Graph.invSqrtDeg, if_true, path3_deg_seed,
    Real.sqrt_one, inv_one]
  ring

/-- gradf at node 1 when x = c·e₀ and s = e₀ on the 3-node path. -/
lemma path3_gradf_node1 (α xv : ℝ) :
    pathGraph3.gradf α (basisVec pathSeed)
      (fun i => if i = pathSeed then xv else 0) pathNode1 =
      -(1 - α) / (2 * √2) * xv := by
  unfold Graph.gradf
  rw [Finset.sum_eq_single pathSeed
    (fun j _ hj => by simp only [if_neg hj, mul_zero]) (fun h => absurd (Finset.mem_univ _) h)]
  simp only []
  have hne : pathNode1 ≠ pathSeed := by simp [pathNode1, pathSeed]
  simp only [Graph.Qentry, basisVec, if_neg hne, Graph.invSqrtDeg, if_true]
  rw [path3_sqrtDeg_seed]
  rw [show pathGraph3.sqrtDeg pathNode1 = √2 from by unfold Graph.sqrtDeg; rw [path3_deg_node1]]
  rw [show pathGraph3.A pathNode1 pathSeed = 1 from by unfold pathGraph3 pathNode1 pathSeed; simp]
  rw [path3_deg_node1]; ring

/-- gradf at node 2 when x = c·e₀ and s = e₀ on the 3-node path: zero (no edge to 0). -/
lemma path3_gradf_node2 (α xv : ℝ) :
    pathGraph3.gradf α (basisVec pathSeed)
      (fun i => if i = pathSeed then xv else 0) pathNode2 = 0 := by
  unfold Graph.gradf
  rw [Finset.sum_eq_single pathSeed
    (fun j _ hj => by simp only [if_neg hj, mul_zero]) (fun h => absurd (Finset.mem_univ _) h)]
  simp only []
  have hne : pathNode2 ≠ pathSeed := by simp [pathNode2, pathSeed, Fin.ext_iff]
  simp only [Graph.Qentry, basisVec, if_neg hne, Graph.invSqrtDeg]
  rw [show pathGraph3.A pathNode2 pathSeed = 0 from by unfold pathGraph3 pathNode2 pathSeed; simp]
  simp

/-- **Appendix C.2 (full — unique minimizer)**: Path graph with seed at endpoint.
    On the 3-node path P₃ (which captures the essential content of P_{m+1} for any m ≥ 2,
    since nodes i ≥ 3 have zero gradient), for ρ ∈ [ρ₀, 1) where ρ₀ = (1−α)/(3+α):
    the candidate x = (2α(1−ρ)/(1+α)) · e₀ is the unique minimizer,
    with support S* = {0}, margin γ₁ = α(3+α)/(2(1+α))·(ρ−ρ₀), and γ = 0 at ρ₀.

    This formalizes the full statement of Lemma C.2 including the unique minimizer
    conclusion (via KKT verification + α-strong convexity). -/
theorem path_seed_unique_minimizer (α ρ : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (hρ_ge : (1 - α) / (3 + α) ≤ ρ) (hρ_lt : ρ < 1) :
    let xv := 2 * α * (1 - ρ) / (1 + α)
    let x := fun i => if i = pathSeed then xv else 0
    -- (i) x_v > 0
    0 < xv
    -- (ii) IsMinimizer: x is the unique minimizer
    ∧ pathGraph3.IsMinimizer 1 α ρ (basisVec pathSeed) x
    -- (iii) Support = {seed}
    ∧ (∀ i, i ≠ pathSeed → x i = 0)
    -- (iv) Margin ≥ 0 at node 1
    ∧ 0 ≤ α * (3 + α) / (2 * (1 + α)) * (ρ - (1 - α) / (3 + α)) := by
  have hxv_pos : 0 < 2 * α * (1 - ρ) / (1 + α) := by
    apply div_pos (mul_pos (mul_pos (by norm_num : (0:ℝ) < 2) hα) (by linarith)) (by linarith)
  intro xv x
  refine ⟨hxv_pos, ?_, fun i hi => if_neg hi,
    mul_nonneg (div_nonneg (by nlinarith) (by linarith)) (sub_nonneg.mpr hρ_ge)⟩
  apply kkt_implies_minimizer _ 1 α ρ _ _ hα (le_of_lt hα1) one_pos
    (by linarith [div_pos (by linarith : (0:ℝ) < 1 - α) (by linarith : (0:ℝ) < 3 + α)])
  · intro i; simp only [x]; split_ifs <;> [exact le_of_lt hxv_pos; exact le_refl 0]
  · -- Active KKT
    intro i hi
    have : i = pathSeed := by
      by_contra h; simp only [x] at hi; rw [if_neg h] at hi; linarith
    subst this; simp only [x]
    rw [path3_gradf_seed, path3_sqrtDeg_seed]; simp only [xv]
    have h1α : (1:ℝ) + α ≠ 0 := ne_of_gt (by linarith)
    field_simp; ring
  · -- Inactive KKT
    intro i hi
    have hi_ne : i ≠ pathSeed := by
      intro h; simp only [x, h, if_pos rfl] at hi; simp only [xv] at hi; linarith
    fin_cases i
    · exact absurd rfl hi_ne
    · -- Node 1: margin condition
      show |pathGraph3.gradf α (basisVec pathSeed)
        (fun i => if i = pathSeed then xv else 0) pathNode1| ≤ _
      rw [path3_gradf_node1]
      have hcoeff_neg : -(1 - α) / (2 * √2) < 0 := by
        apply div_neg_of_neg_of_pos <;> [linarith; positivity]
      rw [abs_of_nonpos (by nlinarith [mul_neg_of_neg_of_pos hcoeff_neg hxv_pos])]
      show -(-(1 - α) / (2 * √2) * xv) ≤ 1 * α * ρ * pathGraph3.sqrtDeg pathNode1
      rw [show -(-(1 - α) / (2 * √2) * xv) = (1 - α) / (2 * √2) * xv from by ring]
      rw [show pathGraph3.sqrtDeg pathNode1 = √2 from by
        unfold Graph.sqrtDeg; rw [path3_deg_node1]]
      simp only [one_mul, xv]
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : 0 < 2 * √2)]
      have h1α_ne : (1:ℝ) + α ≠ 0 := ne_of_gt (by linarith)
      have hsq2 : √(2:ℝ) * √2 = 2 := Real.mul_self_sqrt (by norm_num)
      have hsq2_sq : √(2:ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      field_simp
      simp only [hsq2_sq]
      have hρ_cleared : (1 - α) ≤ ρ * (3 + α) := by
        rwa [div_le_iff₀ (by linarith : (0:ℝ) < 3 + α)] at hρ_ge
      nlinarith [hρ_cleared]
    · -- Node 2: gradient = 0
      show |pathGraph3.gradf α (basisVec pathSeed)
        (fun i => if i = pathSeed then xv else 0) pathNode2| ≤ _
      rw [path3_gradf_node2]; simp
      exact mul_nonneg (mul_nonneg hα.le (by linarith [hρ_ge, div_nonneg (by linarith : (0:ℝ) ≤ 1 - α) (by linarith : (0:ℝ) ≤ 3 + α)])) (pathGraph3.sqrtDeg_pos pathNode2).le

/-- **Appendix C.2**: Path graph with seed at endpoint — breakpoint algebra.
    See path_seed_unique_minimizer for the full unique minimizer statement. -/
theorem path_breakpoint (m : ℕ) (_hm : 2 ≤ m) (α : ℝ) (hα : 0 < α) (_hα1 : α ≤ 1)
    (ρ : ℝ) (hρ_ge : (1 - α) / (3 + α) ≤ ρ) (hρ_lt : ρ < 1) :
    let ρ₀ := (1 - α) / (3 + α)
    -- (i) x*₁ > 0 (support includes node 1)
    0 < 2 * α * (1 - ρ) / (1 + α)
    -- (ii) KKT margin: γ₂ = α(3+α)/(2(1+α))·(ρ - ρ₀) (explicit formula)
    ∧ α * ρ * √2 / √2 - (1 - α) / (2 * √2) * (2 * α * (1 - ρ) / (1 + α)) / √2 =
        α * (3 + α) / (2 * (1 + α)) * (ρ - ρ₀)
    -- (iii) At ρ₀, γ = 0 (breakpoint)
    ∧ α * (3 + α) / (2 * (1 + α)) * (ρ₀ - ρ₀) = 0
    -- (iv) Margin is nonneg for ρ ≥ ρ₀ (nodes i ≥ 3 have ∇f = 0, node 2 has margin ≥ 0 → S* = {1})
    ∧ 0 ≤ α * (3 + α) / (2 * (1 + α)) * (ρ - ρ₀) := by
  refine ⟨by apply div_pos (mul_pos (mul_pos (by norm_num : (0:ℝ) < 2) hα) (by linarith)) (by linarith),
    ?_, by ring,
    mul_nonneg (by positivity) (sub_nonneg.mpr hρ_ge)⟩
  have hsq2_ne : √(2:ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos_of_pos (by norm_num : (0:ℝ) < 2))
  have h1α_ne : (1:ℝ) + α ≠ 0 := ne_of_gt (by linarith)
  have hsq2_sq : √(2:ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  field_simp
  simp only [hsq2_sq]
  nlinarith

/-- **Lemma C.2 (paper-matching combined statement)**:
    Path graph P_{m+1} with seed at endpoint, α ∈ (0,1), m ≥ 2.
    For ρ ∈ [ρ₀, 1) where ρ₀ = (1−α)/(3+α):
    x* = (2α(1−ρ)/(1+α)) · e_seed is the unique minimizer with S* = {seed},
    margin γ₂ = α(3+α)/(2(1+α))·(ρ−ρ₀), and γ = 0 at ρ₀. -/
theorem lemma_C2 (m : ℕ) (hm : 2 ≤ m) (α ρ : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (hρ_ge : (1 - α) / (3 + α) ≤ ρ) (hρ_lt : ρ < 1) :
    let xv := 2 * α * (1 - ρ) / (1 + α)
    let x := fun i => if i = genPathSeed m hm then xv else 0
    -- (i) Unique minimizer
    (genPathGraph m hm).IsMinimizer 1 α ρ (basisVec (genPathSeed m hm)) x
    ∧ (∀ y, (genPathGraph m hm).IsMinimizer 1 α ρ (basisVec (genPathSeed m hm)) y → y = x)
    -- (ii) x_v > 0 with support S* = {seed}
    ∧ 0 < xv
    ∧ (∀ i, i ≠ genPathSeed m hm → x i = 0)
    -- (iii) Margin equality: γ₂ = α(3+α)/(2(1+α))·(ρ − ρ₀)
    ∧ α * ρ * √2 / √2 - (1 - α) / (2 * √2) * (2 * α * (1 - ρ) / (1 + α)) / √2 =
        α * (3 + α) / (2 * (1 + α)) * (ρ - (1 - α) / (3 + α))
    -- (iv) Margin nonneg and zero at breakpoint
    ∧ 0 ≤ α * (3 + α) / (2 * (1 + α)) * (ρ - (1 - α) / (3 + α))
    ∧ α * (3 + α) / (2 * (1 + α)) * ((1 - α) / (3 + α) - (1 - α) / (3 + α)) = 0 := by
  intro xv x
  have h := genPath_unique_minimizer m hm α ρ hα hα1 hρ_ge hρ_lt
  have hbp := path_breakpoint m hm α hα (le_of_lt hα1) ρ hρ_ge hρ_lt
  have hρ_pos : 0 < ρ := lt_of_lt_of_le (div_pos (by linarith) (by linarith)) hρ_ge
  exact ⟨h.2.1,
    fun y hy => minimizer_unique _ 1 α ρ _ x y hα (le_of_lt hα1) one_pos hρ_pos h.2.1 hy,
    h.1, fun i hi => if_neg hi, hbp.2.1, h.2.2.2, by ring⟩

/-! ## Proposition D.4 — Lower bound: FISTA vs ISTA -/

/-- ISTA iterates (proximal gradient without momentum). -/
def istaState (G : Graph n) (c α ρ : ℝ) (s : Fin n → ℝ) : ℕ → Fin n → ℝ
  | 0 => 0
  | k + 1 => fun i => G.proxMap c α ρ 1 (fun j => G.fwdStep α 1 s (istaState G c α ρ s k) j) i

/-- Per-iteration ISTA work: vol(supp(z_k)) + vol(supp(z_{k+1})). -/
@[reducible] def Graph.istaIterWork (G : Graph n) (c α ρ : ℝ) (s : Fin n → ℝ) (k : ℕ) : ℝ :=
  G.vol (vecSupp (istaState G c α ρ s k)) + G.vol (vecSupp (istaState G c α ρ s (k + 1)))

/-- Total ISTA work over N iterations. -/
@[reducible] def Graph.istaTotalWork (G : Graph n) (c α ρ : ℝ) (s : Fin n → ℝ) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N, G.istaIterWork c α ρ s k

/-- ε₀(α) = α³(1−α)⁴β⁴ / (2(3+α)²), where β = (1−√α)/(1+√α). -/
@[reducible] def eps0 (α : ℝ) : ℝ :=
  α ^ 3 * (1 - α) ^ 4 * (fistaMom α) ^ 4 / (2 * (3 + α) ^ 2)

/-- **Axiom (Fountoulakis 2019, Theorem 1, case ii)**:
    The support of every ISTA iterate is contained in the optimal support. -/
axiom ista_support_subset_optimal {n : ℕ} (G : Graph n) (c α ρ : ℝ) (s : Fin n → ℝ)
    (xstar : Fin n → ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (hc : 0 < c) (hρ : 0 < ρ)
    (hmin : G.IsMinimizer c α ρ s xstar) (k : ℕ) :
    vecSupp (istaState G c α ρ s k) ⊆ vecSupp xstar

/-- **Axiom (Beck 2017, Theorem 10.30)**:
    ISTA converges in O(1/α · log(1/ε)) iterations for α-strongly convex objectives. -/
axiom ista_convergence_rate {n : ℕ} (G : Graph n) (c α ρ : ℝ) (s : Fin n → ℝ)
    (xstar : Fin n → ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (hc : 0 < c) (hρ : 0 < ρ)
    (hmin : G.IsMinimizer c α ρ s xstar) (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℕ, (∀ k, K ≤ k →
      G.FObj c α ρ s (istaState G c α ρ s k) - G.FObj c α ρ s xstar ≤ ε) ∧
    (K : ℝ) ≤ (1 / α) * |Real.log ε| + 1

lemma eps0_pos (α : ℝ) (hα : 0 < α) (hα1 : α < 1) : 0 < eps0 α := by
  unfold eps0
  apply div_pos
  · exact mul_pos (mul_pos (pow_pos hα 3) (pow_pos (by linarith) 4))
      (pow_pos (fistaMom_pos_of_lt α hα hα1) 4)
  · exact mul_pos (by norm_num : (0:ℝ) < 2) (sq_pos_of_pos (by linarith : (0:ℝ) < 3 + α))

/-- x*_v ≥ 4α/(3+α) when D ≥ 2 at ρ = ρ₀. -/
lemma star_xv_lower_bound (D : ℕ) (hD : 2 ≤ D) (α : ℝ) (hα : 0 < α) (hα1 : α < 1) :
    4 * α / (3 + α) ≤ starXv α (starRho0 D α) := by
  have hD_ge : (2 : ℝ) ≤ ↑D := by exact_mod_cast hD
  have h3a : (0 : ℝ) < 3 + α := by linarith
  have hdenom : (0 : ℝ) < ↑D * (1 + α) + (1 - α) := by nlinarith
  -- starXv α ρ₀ simplifies to 2αD / (D(1+α)+(1-α))
  have hxv : starXv α (starRho0 D α) = 2 * α * ↑D / (↑D * (1 + α) + (1 - α)) := by
    unfold starXv starRho0; field_simp; ring
  rw [hxv, div_le_div_iff₀ h3a hdenom]
  -- Polynomial: 4α(D(1+α)+(1-α)) ≤ 2αD(3+α), equiv to 2(D-2)(1-α) ≥ 0
  nlinarith [mul_nonneg (sub_nonneg.mpr hD_ge) (sub_nonneg.mpr (le_of_lt hα1))]

/-- FObj(t·e_v) = (1+α)/4 · t² − α(1−ρ)t on the star graph for t ≥ 0. -/
lemma star_FObj_ev (D : ℕ) (hD : 1 ≤ D) (α ρ : ℝ) (t : ℝ) (ht : 0 ≤ t) :
    (starGraph D hD).FObj 1 α ρ (basisVec (starSeed D hD))
      (fun i => if i = starSeed D hD then t else 0) =
    (1 + α) / 4 * t ^ 2 - α * (1 - ρ) * t := by
  set v := starSeed D hD
  set G := starGraph D hD
  have hx0 : ∀ j : Fin (D+1), j ≠ v → (fun i : Fin (D+1) => if i = v then t else (0:ℝ)) j = 0 :=
    fun j hj => if_neg hj
  -- Helper: beta-reduce the function application
  set x : Fin (D+1) → ℝ := fun i => if i = v then t else 0 with hx_def
  change G.FObj 1 α ρ (basisVec v) x = _
  -- Inner sum collapses: ∑_j Q_{ij}·x_j = Q_{iv}·t
  have hQx : ∀ i : Fin (D+1), ∑ j, G.Qentry α i j * x j = G.Qentry α i v * t := by
    intro i; have : x v = t := if_pos rfl
    rw [← this]; exact star_Qx_supp_v D hD α x hx0 i
  -- Step 1: quadratic sum = (1+α)/2 · t²
  have h1 : ∑ i : Fin (D+1), x i * (∑ j, G.Qentry α i j * x j) =
      (1 + α) / 2 * t ^ 2 := by
    simp_rw [hQx]
    rw [Finset.sum_eq_single v (fun j _ hj => by rw [show x j = 0 from if_neg hj, zero_mul])
      (fun h => absurd (Finset.mem_univ v) h)]
    rw [show x v = t from if_pos rfl]
    unfold Graph.Qentry; rw [if_pos rfl]; ring
  -- Step 2: linear sum = t
  have h2 : ∑ i : Fin (D+1), G.invSqrtDeg i * basisVec v i * x i = t := by
    rw [Finset.sum_eq_single v (fun j _ hj => by rw [show x j = 0 from if_neg hj]; ring)
      (fun h => absurd (Finset.mem_univ v) h)]
    rw [show x v = t from if_pos rfl, star_invSqrtDeg_seed]
    unfold basisVec; rw [if_pos rfl]; ring
  -- Step 3: regularizer sum = t
  have h3 : ∑ i : Fin (D+1), G.sqrtDeg i * |x i| = t := by
    rw [Finset.sum_eq_single v (fun j _ hj => by rw [show x j = 0 from if_neg hj, abs_zero, mul_zero])
      (fun h => absurd (Finset.mem_univ v) h)]
    rw [show x v = t from if_pos rfl, abs_of_nonneg ht, star_sqrtDeg_seed]; ring
  -- Combine
  unfold Graph.FObj Graph.fObj Graph.gReg
  rw [h1, h2, h3]; ring

/-- Gap formula: F(t·e_v) − F(x*) = (1+α)/4 · (t−x*_v)² on the star graph. -/
lemma star_FObj_gap_ev (D : ℕ) (hD : 1 ≤ D) (α ρ : ℝ) (hα : 0 < α) (hρ : ρ < 1)
    (t : ℝ) (ht : 0 ≤ t) :
    (starGraph D hD).FObj 1 α ρ (basisVec (starSeed D hD))
      (fun i => if i = starSeed D hD then t else 0) -
    (starGraph D hD).FObj 1 α ρ (basisVec (starSeed D hD))
      (fun i => if i = starSeed D hD then starXv α ρ else 0) =
    (1 + α) / 4 * (t - starXv α ρ) ^ 2 := by
  rw [star_FObj_ev D hD α ρ t ht,
      star_FObj_ev D hD α ρ (starXv α ρ) (le_of_lt (starXv_pos α ρ hα hρ))]
  unfold starXv; field_simp; ring

/-- normSq of the difference of two v-supported vectors = (a−b)². -/
lemma normSq_v_diff (D : ℕ) (hD : 1 ≤ D) (f : Fin (D+1) → ℝ)
    (hf : ∀ j, j ≠ starSeed D hD → f j = 0) (b : ℝ) :
    normSq (fun i => f i - (if i = starSeed D hD then b else 0)) =
    (f (starSeed D hD) - b) ^ 2 := by
  set v := starSeed D hD
  set g : Fin (D+1) → ℝ := fun i => f i - (if i = v then b else 0) with hg_def
  change normSq g = _
  unfold normSq
  rw [Finset.sum_eq_single v]
  · show g v ^ 2 = _; rw [hg_def]; dsimp only; rw [if_pos rfl]
  · intro j _ hj; show g j ^ 2 = 0; rw [hg_def]; dsimp only
    rw [hf j hj, if_neg hj]; ring
  · intro h; exact absurd (Finset.mem_univ v) h

/-- FObj(0) = 0 for any graph. -/
lemma FObj_zero (G : Graph n) (c α ρ : ℝ) (s : Fin n → ℝ) :
    G.FObj c α ρ s 0 = 0 := by
  unfold Graph.FObj Graph.fObj Graph.gReg
  simp [abs_zero]

/-- fistaX 1 is {v}-supported on the star graph. -/
lemma fistaX_1_supp (D : ℕ) (hD : 1 ≤ D) (α : ℝ) (hα : 0 < α) (hα1 : α < 1) :
    ∀ j, j ≠ starSeed D hD →
    fistaX (starGraph D hD) 1 α (starRho0 D α) (basisVec (starSeed D hD)) 1 j = 0 := by
  intro j hj
  have hρ₀ := starRho0_pos D hD α hα hα1
  have h1 : fistaX (starGraph D hD) 1 α (starRho0 D α) (basisVec (starSeed D hD)) 1 j =
      (starGraph D hD).proxMap 1 α (starRho0 D α) 1
        (fun k => (starGraph D hD).fwdStep α 1 (basisVec (starSeed D hD))
          (fistaY (starGraph D hD) 1 α (starRho0 D α) (basisVec (starSeed D hD)) 0) k) j := rfl
  rw [h1, fistaY_zero_eq]
  by_cases hjw : j = starCenter D hD
  · rw [hjw]; exact star_proxMap_w_zero D hD α (starRho0 D α) 0 (fun _ _ => rfl) (by
      simp only [Pi.zero_apply, mul_zero, abs_zero]
      exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg one_pos.le one_pos.le) hα.le)
        hρ₀.le) ((starGraph D hD).sqrtDeg_pos (starCenter D hD)).le)
  · exact star_proxMap_other_zero D hD α (starRho0 D α) hα hρ₀
      0 (fun _ _ => rfl) j hj hjw

/-- fistaX 3 v = x*_v · (1 + a²β²) on the star graph. -/
lemma fistaX_3_v_val (D : ℕ) (hD : 1 ≤ D) (α : ℝ) (hα : 0 < α) (hα1 : α < 1) :
    let v := starSeed D hD
    let ρ₀ := starRho0 D α
    let β := fistaMom α
    let a := (1 - α) / 2
    fistaX (starGraph D hD) 1 α ρ₀ (basisVec v) 3 v =
      starXv α ρ₀ * (1 + a ^ 2 * β ^ 2) := by
  show fistaX (starGraph D hD) 1 α (starRho0 D α) (basisVec (starSeed D hD)) 3 (starSeed D hD) =
    starXv α (starRho0 D α) * (1 + ((1 - α) / 2) ^ 2 * (fistaMom α) ^ 2)
  have hρ₀_lt := starRho0_lt_one D hD α hα hα1
  -- y₂ is {v}-supported
  have hy2_supp : ∀ j, j ≠ starSeed D hD →
      fistaY (starGraph D hD) 1 α (starRho0 D α) (basisVec (starSeed D hD)) 2 j = 0 := by
    intro j hj; rw [fistaY_succ, fistaX_2_supp D hD α hα hα1 j hj]
    have hx1j := fistaX_1_supp D hD α hα hα1 j hj; simp [hx1j]
  have ⟨_, _, _, hy2v⟩ := fista_overshoot_at_k2 D hD α hα hα1
  -- fistaX 3 v = proxMap(fwdStep(y₂)) v (definitionally)
  have h3 : fistaX (starGraph D hD) 1 α (starRho0 D α) (basisVec (starSeed D hD)) 3
      (starSeed D hD) =
      (starGraph D hD).proxMap 1 α (starRho0 D α) 1
        (fun j => (starGraph D hD).fwdStep α 1 (basisVec (starSeed D hD))
          (fistaY (starGraph D hD) 1 α (starRho0 D α) (basisVec (starSeed D hD)) 2) j)
        (starSeed D hD) := rfl
  rw [h3, star_proxMap_v D hD α (starRho0 D α) hα hρ₀_lt
    (fistaY (starGraph D hD) 1 α (starRho0 D α) (basisVec (starSeed D hD)) 2) hy2_supp
    (by rw [hy2v]; have hxv := starXv_pos α (starRho0 D α) hα hρ₀_lt
        have hβ := fistaMom_pos_of_lt α hα hα1
        nlinarith [sq_nonneg (fistaMom α),
          mul_pos hxv (mul_pos (div_pos (by linarith : (0:ℝ) < 1 - α) (by norm_num : (0:ℝ) < 2))
            (sq_pos_of_pos hβ)),
          mul_lt_mul_of_pos_left hρ₀_lt hα])]
  rw [hy2v]; unfold starXv
  have h1a : (0 : ℝ) < 1 + α := by linarith
  field_simp; ring

/-- A v-supported function equals its if-then-else form. -/
private lemma v_supp_ite (D : ℕ) (hD : 1 ≤ D) (f : Fin (D+1) → ℝ)
    (hf : ∀ j, j ≠ starSeed D hD → f j = 0) :
    f = fun i => if i = starSeed D hD then f (starSeed D hD) else 0 := by
  ext i; by_cases h : i = starSeed D hD
  · rw [h, if_pos rfl]
  · rw [if_neg h, hf i h]

/-- fistaX 2 v on the star graph at ρ₀. -/
private lemma fistaX_2_v_val (D : ℕ) (hD : 1 ≤ D) (α : ℝ) (hα : 0 < α) (hα1 : α < 1) :
    fistaX (starGraph D hD) 1 α (starRho0 D α) (basisVec (starSeed D hD)) 2 (starSeed D hD) =
    α * (1 - starRho0 D α) * ((1 - α) * (1 + fistaMom α) / 2 + 1) := by
  have hρ₀_lt := starRho0_lt_one D hD α hα hα1
  have hy1_supp : ∀ j, j ≠ starSeed D hD →
      fistaY (starGraph D hD) 1 α (starRho0 D α) (basisVec (starSeed D hD)) 1 j = 0 := by
    intro j hj; rw [fistaY_succ]
    have hx1j := fistaX_1_supp D hD α hα hα1 j hj; rw [hx1j]; simp [fistaX_zero]
  have hy1v : fistaY (starGraph D hD) 1 α (starRho0 D α) (basisVec (starSeed D hD)) 1
      (starSeed D hD) = (1 + fistaMom α) * (α * (1 - starRho0 D α)) := by
    rw [fistaY_succ]; have ⟨_, _, hx1v, _⟩ := fista_overshoot_at_k2 D hD α hα hα1
    rw [hx1v, fistaX_zero]; simp only [Pi.zero_apply, sub_zero]; ring
  have h2 : fistaX (starGraph D hD) 1 α (starRho0 D α) (basisVec (starSeed D hD)) 2
      (starSeed D hD) =
      (starGraph D hD).proxMap 1 α (starRho0 D α) 1
        (fun j => (starGraph D hD).fwdStep α 1 (basisVec (starSeed D hD))
          (fistaY (starGraph D hD) 1 α (starRho0 D α) (basisVec (starSeed D hD)) 1) j)
        (starSeed D hD) := rfl
  rw [h2, star_proxMap_v D hD α (starRho0 D α) hα hρ₀_lt
    (fistaY (starGraph D hD) 1 α (starRho0 D α) (basisVec (starSeed D hD)) 1) hy1_supp
    (by rw [hy1v]
        have hβ_nn' := fistaMom_nonneg α hα (le_of_lt hα1)
        have h1 : 0 ≤ (1 - α) / 2 * ((1 + fistaMom α) * (α * (1 - starRho0 D α))) := by
          apply mul_nonneg (div_nonneg (by linarith) (by norm_num))
          exact mul_nonneg (by linarith) (mul_nonneg (le_of_lt hα) (by linarith))
        have h3 : α * starRho0 D α < α := by nlinarith [sub_pos.mpr hρ₀_lt]
        linarith)]
  rw [hy1v]; ring

set_option maxHeartbeats 800000 in
/-- **FISTA gap exceeds ε₀ for all k ≤ 3 on the star graph at ρ₀.**
    For k=0,1,2: 1D gap formula on v-supported iterates.
    For k=3: strong convexity + x₃,w > 0 (strict). -/
theorem star_fista_gap_gt_eps0 (D : ℕ) (hD : 1 ≤ D) (hD2 : 2 ≤ D) (α : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (k : ℕ) (hk : k ≤ 3) :
    eps0 α < (starGraph D hD).FObj 1 α (starRho0 D α) (basisVec (starSeed D hD))
      (fistaX (starGraph D hD) 1 α (starRho0 D α) (basisVec (starSeed D hD)) k) -
    (starGraph D hD).FObj 1 α (starRho0 D α) (basisVec (starSeed D hD))
      (fun i => if i = starSeed D hD then starXv α (starRho0 D α) else 0) := by
  -- Common setup
  have hρ₀ := starRho0_pos D hD α hα hα1
  have hρ₀_lt := starRho0_lt_one D hD α hα hα1
  have hxv_pos := starXv_pos α (starRho0 D α) hα hρ₀_lt
  have hxv_lb := star_xv_lower_bound D hD2 α hα hα1
  have hβ_pos := fistaMom_pos_of_lt α hα hα1
  have hβ_nn := fistaMom_nonneg α hα (le_of_lt hα1)
  have hβ_lt := fistaMom_lt_one α hα (le_of_lt hα1)
  have hmin := (star_unique_minimizer_support D hD α (starRho0 D α) hα hα1
    (le_refl _) hρ₀_lt).2.2.2.2.2.2
  have h3α : (0 : ℝ) < 3 + α := by linarith
  have h1α : (0 : ℝ) < 1 + α := by linarith
  have h1mα_pow_le : (1 - α) ^ 4 ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  have hβ_pow_le : (fistaMom α) ^ 4 ≤ 1 := pow_le_one₀ hβ_nn (le_of_lt hβ_lt)
  -- Case split on k
  have hk_cases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases hk_cases with rfl | rfl | rfl | rfl
  · -- **k = 0**: fistaX 0 = 0, gap = (1+α)/4 · xv²
    rw [fistaX_zero, FObj_zero,
        star_FObj_ev D hD α (starRho0 D α) (starXv α (starRho0 D α)) (le_of_lt hxv_pos)]
    -- Goal: eps0 α < 0 - ((1+α)/4·xv² - α(1-ρ₀)·xv)
    -- RHS = (1+α)/4·xv² (using xv = 2α(1-ρ₀)/(1+α))
    have h_rhs : 0 - ((1 + α) / 4 * starXv α (starRho0 D α) ^ 2 -
        α * (1 - starRho0 D α) * starXv α (starRho0 D α)) =
        (1 + α) / 4 * starXv α (starRho0 D α) ^ 2 := by
      unfold starXv; field_simp; ring
    rw [h_rhs]
    -- eps0 < (1+α)/4 · xv², using xv ≥ 4α/(3+α) and (1-α)⁴β⁴ < 16
    calc eps0 α = α ^ 3 * (1 - α) ^ 4 * fistaMom α ^ 4 / (2 * (3 + α) ^ 2) := rfl
      _ < (1 + α) / 4 * (4 * α / (3 + α)) ^ 2 := by
          have h3α_ne : (3 + α : ℝ) ≠ 0 := ne_of_gt h3α
          rw [div_lt_iff₀ (by positivity : (0:ℝ) < 2 * (3 + α) ^ 2)]
          have hrhs : (1 + α) / 4 * (4 * α / (3 + α)) ^ 2 * (2 * (3 + α) ^ 2) =
              8 * α ^ 2 * (1 + α) := by field_simp; ring
          rw [hrhs]
          -- α^3*(1-α)^4*β^4 ≤ α^3 < 8α^2(1+α)
          have h_prod_le : (1 - α) ^ 4 * fistaMom α ^ 4 ≤ 1 := by
            calc (1 - α) ^ 4 * fistaMom α ^ 4
                ≤ 1 * 1 := mul_le_mul h1mα_pow_le hβ_pow_le
                    (pow_nonneg hβ_nn 4) zero_le_one
              _ = 1 := one_mul 1
          have h_bound : α ^ 3 * (1 - α) ^ 4 * fistaMom α ^ 4 ≤ α ^ 3 := by
            have : α ^ 3 * (1 - α) ^ 4 * fistaMom α ^ 4 =
                α ^ 3 * ((1 - α) ^ 4 * fistaMom α ^ 4) := by ring
            rw [this]
            exact mul_le_of_le_one_right (pow_nonneg (le_of_lt hα) 3) h_prod_le
          nlinarith [sq_nonneg α]
      _ ≤ (1 + α) / 4 * starXv α (starRho0 D α) ^ 2 := by
          apply mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hxv_lb 2) (by linarith)
  · -- **k = 1**: x₁ v-supported with x₁_v = α(1-ρ₀), gap = (1+α)(1-α)²xv²/16
    have ⟨_, _, hx1v, _⟩ := fista_overshoot_at_k2 D hD α hα hα1
    have h_x1_form : fistaX (starGraph D hD) 1 α (starRho0 D α) (basisVec (starSeed D hD)) 1 =
        fun i => if i = starSeed D hD then α * (1 - starRho0 D α) else 0 := by
      ext i; by_cases h : i = starSeed D hD
      · rw [h, if_pos rfl]; exact hx1v
      · rw [if_neg h]; exact fistaX_1_supp D hD α hα hα1 i h
    rw [h_x1_form, star_FObj_gap_ev D hD α (starRho0 D α) hα hρ₀_lt
      (α * (1 - starRho0 D α)) (by nlinarith)]
    -- Goal: eps0 α < (1+α)/4 * (α(1-ρ₀) - xv)²
    -- (α(1-ρ₀) - xv)² = ((1-α)/2)² · xv² since xv = 2α(1-ρ₀)/(1+α)
    have h_diff_sq : (α * (1 - starRho0 D α) - starXv α (starRho0 D α)) ^ 2 =
        ((1 - α) / 2) ^ 2 * starXv α (starRho0 D α) ^ 2 := by
      unfold starXv; field_simp; ring
    rw [h_diff_sq, ← mul_assoc]
    -- eps0 < (1+α)/4 * ((1-α)/2)² * xv²
    have h3α_ne : (3 + α : ℝ) ≠ 0 := ne_of_gt h3α
    have h_4a_pos : (0 : ℝ) < 4 * α / (3 + α) := by positivity
    have h_xv_sq : (4 * α / (3 + α)) ^ 2 ≤ starXv α (starRho0 D α) ^ 2 :=
      sq_le_sq' (by linarith [hxv_pos, h_4a_pos]) hxv_lb
    have h_eps0_eq : eps0 α =
        α * (1 - α) ^ 4 * fistaMom α ^ 4 / 32 * (4 * α / (3 + α)) ^ 2 := by
      show α ^ 3 * (1 - α) ^ 4 * fistaMom α ^ 4 / (2 * (3 + α) ^ 2) = _; field_simp; ring
    have h_gap_coeff_eq : (1 + α) / 4 * ((1 - α) / 2) ^ 2 =
        (1 + α) * (1 - α) ^ 2 / 16 := by ring
    rw [h_eps0_eq, h_gap_coeff_eq]
    have h_coeff_lt : α * (1 - α) ^ 4 * fistaMom α ^ 4 / 32 <
        (1 + α) * (1 - α) ^ 2 / 16 := by
      have h_prod : (1 - α) ^ 2 * fistaMom α ^ 4 ≤ 1 := by
        calc (1 - α) ^ 2 * fistaMom α ^ 4
            ≤ 1 * 1 := mul_le_mul (by nlinarith [sq_nonneg α]) hβ_pow_le
                (pow_nonneg hβ_nn 4) zero_le_one
          _ = 1 := one_mul 1
      have h_bound : α * (1 - α) ^ 4 * fistaMom α ^ 4 ≤ α * (1 - α) ^ 2 := by
        have : α * (1 - α) ^ 4 * fistaMom α ^ 4 =
            α * (1 - α) ^ 2 * ((1 - α) ^ 2 * fistaMom α ^ 4) := by ring
        rw [this]
        exact mul_le_of_le_one_right (mul_nonneg (le_of_lt hα) (sq_nonneg (1 - α))) h_prod
      have h1ma2_pos : (0 : ℝ) < (1 - α) ^ 2 := pow_pos (sub_pos.mpr hα1) 2
      calc α * (1 - α) ^ 4 * fistaMom α ^ 4 / 32
          = α * (1 - α) ^ 4 * fistaMom α ^ 4 * (1 / 32) := by ring
        _ ≤ α * (1 - α) ^ 2 * (1 / 32) :=
            mul_le_mul_of_nonneg_right h_bound (by norm_num)
        _ = α * (1 - α) ^ 2 / 32 := by ring
        _ < (1 + α) * (1 - α) ^ 2 / 16 := by
            rw [div_lt_div_iff₀ (by norm_num : (0:ℝ) < 32) (by norm_num : (0:ℝ) < 16)]
            nlinarith [mul_pos h1ma2_pos (show (0:ℝ) < 32 + 16 * α from by linarith)]
    calc α * (1 - α) ^ 4 * fistaMom α ^ 4 / 32 * (4 * α / (3 + α)) ^ 2
        < (1 + α) * (1 - α) ^ 2 / 16 * (4 * α / (3 + α)) ^ 2 :=
          mul_lt_mul_of_pos_right h_coeff_lt (by positivity)
      _ ≤ (1 + α) * (1 - α) ^ 2 / 16 * starXv α (starRho0 D α) ^ 2 :=
          mul_le_mul_of_nonneg_left h_xv_sq (by positivity)
  · -- **k = 2**: x₂ v-supported
    have h_x2_form : fistaX (starGraph D hD) 1 α (starRho0 D α) (basisVec (starSeed D hD)) 2 =
        fun i => if i = starSeed D hD then
          α * (1 - starRho0 D α) * ((1 - α) * (1 + fistaMom α) / 2 + 1) else 0 := by
      ext i; by_cases h : i = starSeed D hD
      · rw [h, if_pos rfl]; exact fistaX_2_v_val D hD α hα hα1
      · rw [if_neg h]; exact fistaX_2_supp D hD α hα hα1 i h
    rw [h_x2_form, star_FObj_gap_ev D hD α (starRho0 D α) hα hρ₀_lt
          (α * (1 - starRho0 D α) * ((1 - α) * (1 + fistaMom α) / 2 + 1))
          (by have h1 : 0 < α * (1 - starRho0 D α) := mul_pos hα (sub_pos.mpr hρ₀_lt)
              have h2 : 0 < (1 - α) * (1 + fistaMom α) / 2 + 1 := by nlinarith [hβ_nn]
              linarith [mul_pos h1 h2])]
    -- (t₂ - xv)² = α·β²·(1-α)²/4 · xv² (using β(1+α)-(1-α) = -2√α·β)
    have h_diff_sq :
        (α * (1 - starRho0 D α) * ((1 - α) * (1 + fistaMom α) / 2 + 1) -
          starXv α (starRho0 D α)) ^ 2 =
        ((1 - α) / 2) ^ 2 *
          ((1 + α) * (1 + fistaMom α) / 2 - 1) ^ 2 *
          starXv α (starRho0 D α) ^ 2 := by
      unfold starXv; field_simp; ring
    rw [h_diff_sq]
    have h_factor : ((1 + α) * (1 + fistaMom α) / 2 - 1) ^ 2 = α * fistaMom α ^ 2 := by
      have h_mom := momentum_sqrt_identity α hα (le_of_lt hα1)
      have hs := Real.sqrt_pos_of_pos hα
      have h1ps : (0:ℝ) < 1 + √α := by linarith
      unfold fistaMom at h_mom ⊢
      field_simp
      nlinarith [Real.sq_sqrt (le_of_lt hα), sq_nonneg (√α), sq_nonneg (1 - √α),
                  sq_nonneg (1 + √α)]
    rw [h_factor]
    -- Goal: eps0 α < (1+α)/4 * (((1-α)/2)^2 * (α*β^2) * xv^2)
    -- Use suffices to match exact parenthesization
    have hβ2_le : fistaMom α ^ 2 ≤ 1 := by nlinarith [sq_nonneg (fistaMom α)]
    have h3α_ne : (3 + α : ℝ) ≠ 0 := ne_of_gt h3α
    have h_4a_pos : (0 : ℝ) < 4 * α / (3 + α) := by positivity
    -- Intermediate: eps0 < LHS with (4α/(3+α))^2 substituted for xv^2
    have h_inter : eps0 α <
        (1 + α) / 4 * (((1 - α) / 2) ^ 2 * (α * fistaMom α ^ 2) *
          ((4 * α / (3 + α)) ^ 2)) := by
      show α ^ 3 * (1 - α) ^ 4 * fistaMom α ^ 4 / (2 * (3 + α) ^ 2) < _
      rw [div_lt_iff₀ (by positivity : (0:ℝ) < 2 * (3 + α) ^ 2)]
      have hrhs : (1 + α) / 4 * (((1 - α) / 2) ^ 2 * (α * fistaMom α ^ 2) *
          ((4 * α / (3 + α)) ^ 2)) * (2 * (3 + α) ^ 2) =
          2 * α ^ 3 * (1 + α) * (1 - α) ^ 2 * fistaMom α ^ 2 := by field_simp; ring
      rw [hrhs]
      -- Need: α^3*(1-α)^4*β^4 < 2*α^3*(1+α)*(1-α)^2*β^2
      -- Factor out α^3*(1-α)^2*β^2: need (1-α)^2*β^2 < 2*(1+α)
      -- (1-α)^2 < 1 and β^2 ≤ 1, so (1-α)^2*β^2 < 1 < 2 ≤ 2*(1+α)
      have h_1ma2_lt : (1 - α) ^ 2 < 1 := by nlinarith
      have h_t_lt_1 : (1 - α) ^ 2 * fistaMom α ^ 2 < 1 := by
        nlinarith [mul_nonneg (sq_nonneg (1 - α)) (sub_nonneg.mpr hβ2_le)]
      have h_A_pos : 0 < α ^ 3 * (1 - α) ^ 2 * fistaMom α ^ 2 :=
        mul_pos (mul_pos (pow_pos hα 3) (pow_pos (sub_pos.mpr hα1) 2)) (pow_pos hβ_pos 2)
      nlinarith [mul_pos h_A_pos (show 0 < 1 + 2 * α from by linarith),
                  mul_pos h_A_pos (sub_pos.mpr h_t_lt_1)]
    -- Monotonicity: (4α/(3+α))^2 ≤ xv^2
    have h_xv_sq : (4 * α / (3 + α)) ^ 2 ≤ starXv α (starRho0 D α) ^ 2 :=
      sq_le_sq' (by linarith [hxv_pos, h_4a_pos]) hxv_lb
    calc eps0 α
        < (1 + α) / 4 * (((1 - α) / 2) ^ 2 * (α * fistaMom α ^ 2) *
            ((4 * α / (3 + α)) ^ 2)) := h_inter
      _ ≤ (1 + α) / 4 * (((1 - α) / 2) ^ 2 * (α * fistaMom α ^ 2) *
            starXv α (starRho0 D α) ^ 2) := by
          apply mul_le_mul_of_nonneg_left _ (by linarith)
          apply mul_le_mul_of_nonneg_left h_xv_sq (by positivity)
  · -- **k = 3**: strong convexity + x₃,w > 0 gives strict inequality
    -- SC: α/2 · normSq(x₃ - x*) ≤ F(x₃) - F(x*)
    have hsc := minimizer_strong_convexity (starGraph D hD) 1 α (starRho0 D α)
      (basisVec (starSeed D hD))
      (fun i => if i = starSeed D hD then starXv α (starRho0 D α) else 0)
      hα (le_of_lt hα1) one_pos hρ₀ hmin
      (fistaX (starGraph D hD) 1 α (starRho0 D α) (basisVec (starSeed D hD)) 3)
    -- normSq(x₃ - x*) > (x₃_v - xv)² because x₃_w > 0
    set f : Fin (D+1) → ℝ :=
      fun i => fistaX (starGraph D hD) 1 α (starRho0 D α) (basisVec (starSeed D hD)) 3 i -
        (if i = starSeed D hD then starXv α (starRho0 D α) else 0) with hf_def
    have hf_v : f (starSeed D hD) =
        fistaX (starGraph D hD) 1 α (starRho0 D α) (basisVec (starSeed D hD)) 3
          (starSeed D hD) - starXv α (starRho0 D α) := by
      rw [hf_def]; dsimp only; rw [if_pos rfl]
    have hf_w : f (starCenter D hD) =
        fistaX (starGraph D hD) 1 α (starRho0 D α) (basisVec (starSeed D hD)) 3
          (starCenter D hD) := by
      rw [hf_def]; dsimp only; rw [if_neg (star_center_ne_seed D hD)]; ring
    have hw_pos := fistaX_3_w_pos D hD α hα hα1
    have h_ns_strict : f (starSeed D hD) ^ 2 < normSq f := by
      unfold normSq
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (starSeed D hD))]
      have hw_mem : starCenter D hD ∈ Finset.univ.erase (starSeed D hD) :=
        Finset.mem_erase.mpr ⟨star_center_ne_seed D hD, Finset.mem_univ _⟩
      linarith [Finset.single_le_sum (fun i (_ : i ∈ Finset.univ.erase (starSeed D hD)) =>
        sq_nonneg (f i)) hw_mem, sq_pos_of_pos (by rw [hf_w]; exact hw_pos : 0 < f (starCenter D hD)),
        Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ.erase (starSeed D hD)) => sq_nonneg (f i))]
    -- (x₃_v - xv) = xv · a²β² where a = (1-α)/2 (from fistaX_3_v_val)
    have hx3v := fistaX_3_v_val D hD α hα hα1
    -- hx3v : fistaX ... 3 v = xv · (1 + ((1-α)/2)²·β²)
    -- So x₃_v - xv = xv · ((1-α)/2)²·β²
    have hfv_eq : f (starSeed D hD) =
        starXv α (starRho0 D α) * ((1 - α) / 2) ^ 2 * fistaMom α ^ 2 := by
      rw [hf_v, hx3v]; ring
    -- (x₃_v - xv)² = xv² · ((1-α)/2)⁴ · β⁴
    have hfv_sq : f (starSeed D hD) ^ 2 =
        starXv α (starRho0 D α) ^ 2 * ((1 - α) / 2) ^ 4 * fistaMom α ^ 4 := by
      rw [hfv_eq]; ring
    -- eps0 ≤ α/2 · (x₃_v - xv)² (tight at D=2)
    have h_eps0_le : eps0 α ≤ α / 2 * f (starSeed D hD) ^ 2 := by
      rw [hfv_sq]
      show α ^ 3 * (1 - α) ^ 4 * fistaMom α ^ 4 / (2 * (3 + α) ^ 2) ≤
        α / 2 * (starXv α (starRho0 D α) ^ 2 * ((1 - α) / 2) ^ 4 * fistaMom α ^ 4)
      have h3α_ne : (3 + α : ℝ) ≠ 0 := ne_of_gt h3α
      have h_xv_sq : (4 * α / (3 + α)) ^ 2 ≤ starXv α (starRho0 D α) ^ 2 :=
        sq_le_sq' (by linarith [hxv_pos, show (0 : ℝ) < 4 * α / (3 + α) from by positivity]) hxv_lb
      have h_lhs_eq : α ^ 3 * (1 - α) ^ 4 * fistaMom α ^ 4 / (2 * (3 + α) ^ 2) =
          α * (1 - α) ^ 4 * fistaMom α ^ 4 / 32 * (4 * α / (3 + α)) ^ 2 := by
        field_simp; ring
      have h_rhs_eq : α / 2 * (starXv α (starRho0 D α) ^ 2 * ((1 - α) / 2) ^ 4 *
          fistaMom α ^ 4) =
          α * (1 - α) ^ 4 * fistaMom α ^ 4 / 32 * starXv α (starRho0 D α) ^ 2 := by ring
      rw [h_lhs_eq, h_rhs_eq]
      apply mul_le_mul_of_nonneg_left h_xv_sq (by positivity)
    -- Combine: eps0 ≤ α/2·fv² < α/2·normSq ≤ gap
    calc eps0 α ≤ α / 2 * f (starSeed D hD) ^ 2 := h_eps0_le
      _ < α / 2 * normSq f := by nlinarith [h_ns_strict]
      _ ≤ _ := hsc

/-- vecSupp of the star minimizer is {v}. -/
private lemma vecSupp_xstar_eq (D : ℕ) (hD : 1 ≤ D) (α : ℝ) (hα : 0 < α) (hα1 : α < 1) :
    vecSupp (fun i : Fin (D+1) =>
      if i = starSeed D hD then starXv α (starRho0 D α) else 0) =
    {starSeed D hD} := by
  ext i; simp only [vecSupp, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_singleton]
  constructor
  · intro h; by_contra h_ne; rw [if_neg h_ne] at h; exact h rfl
  · intro h; rw [h, if_pos rfl]
    exact ne_of_gt (starXv_pos α (starRho0 D α) hα (starRho0_lt_one D hD α hα hα1))

/-- vol(supp(x*)) = 1 on the star graph (seed is a leaf with degree 1). -/
private lemma vol_xstar_eq_one (D : ℕ) (hD : 1 ≤ D) (α : ℝ) (hα : 0 < α) (hα1 : α < 1) :
    (starGraph D hD).vol (vecSupp (fun i : Fin (D+1) =>
      if i = starSeed D hD then starXv α (starRho0 D α) else 0)) = 1 := by
  rw [vecSupp_xstar_eq D hD α hα hα1]; unfold Graph.vol
  rw [Finset.sum_singleton, star_deg_seed]

/-- Each ISTA iteration on the star graph has work ≤ 2. -/
private lemma ista_iter_work_le_two (D : ℕ) (hD : 1 ≤ D)
    (α : ℝ) (hα : 0 < α) (hα1 : α < 1) (k : ℕ) :
    (starGraph D hD).istaIterWork 1 α (starRho0 D α)
      (basisVec (starSeed D hD)) k ≤ 2 := by
  have hρ₀ := starRho0_pos D hD α hα hα1
  have hρ₀_lt := starRho0_lt_one D hD α hα hα1
  have hmin := (star_unique_minimizer_support D hD α (starRho0 D α)
    hα hα1 (le_refl _) hρ₀_lt).2.2.2.2.2.2
  set xstar : Fin (D+1) → ℝ :=
    fun i => if i = starSeed D hD then starXv α (starRho0 D α) else 0
  have h_vol := vol_xstar_eq_one D hD α hα hα1
  have h_supp_k := ista_support_subset_optimal (starGraph D hD) 1 α (starRho0 D α)
    (basisVec (starSeed D hD)) xstar hα (le_of_lt hα1) one_pos hρ₀ hmin k
  have h_supp_k1 := ista_support_subset_optimal (starGraph D hD) 1 α (starRho0 D α)
    (basisVec (starSeed D hD)) xstar hα (le_of_lt hα1) one_pos hρ₀ hmin (k + 1)
  have h1 : (starGraph D hD).vol (vecSupp (istaState (starGraph D hD) 1 α
      (starRho0 D α) (basisVec (starSeed D hD)) k)) ≤ 1 :=
    le_trans (vol_mono (starGraph D hD) h_supp_k) (le_of_eq h_vol)
  have h2 : (starGraph D hD).vol (vecSupp (istaState (starGraph D hD) 1 α
      (starRho0 D α) (basisVec (starSeed D hD)) (k + 1))) ≤ 1 :=
    le_trans (vol_mono (starGraph D hD) h_supp_k1) (le_of_eq h_vol)
  unfold Graph.istaIterWork; linarith

/-- ISTA total work on the star graph is ≤ 2K. -/
private lemma ista_total_work_le (D : ℕ) (hD : 1 ≤ D)
    (α : ℝ) (hα : 0 < α) (hα1 : α < 1) (K : ℕ) :
    (starGraph D hD).istaTotalWork 1 α (starRho0 D α)
      (basisVec (starSeed D hD)) K ≤ 2 * (K : ℝ) := by
  unfold Graph.istaTotalWork
  calc ∑ k ∈ Finset.range K, (starGraph D hD).istaIterWork 1 α (starRho0 D α)
          (basisVec (starSeed D hD)) k
      ≤ ∑ _ ∈ Finset.range K, (2 : ℝ) :=
        Finset.sum_le_sum fun k _ => ista_iter_work_le_two D hD α hα hα1 k
    _ = 2 * (K : ℝ) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

/-- **Proposition D.4 (Lower bound)**: On the star graph G(D) with seed v and ρ = ρ₀,
    for every target accuracy 0 < ε ≤ ε₀(α):
    (1) FISTA requires total degree-weighted work at least 2D.
    (2) ISTA reaches the same accuracy with total work O(1/α · log(1/ε)),
        independent of D. -/
theorem prop_D4 (D : ℕ) (hD : 1 ≤ D) (hD2 : 2 ≤ D) (α : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (ε : ℝ) (hε : 0 < ε) (hε_le : ε ≤ eps0 α) :
    let G := starGraph D hD
    let v := starSeed D hD
    let ρ₀ := starRho0 D α
    let s := basisVec v
    let xstar := fun i : Fin (D+1) => if i = v then starXv α ρ₀ else 0
    -- Part 1: FISTA totalWork ≥ 2D for accuracy ε
    (∀ N, G.FObj 1 α ρ₀ s (fistaX G 1 α ρ₀ s N) - G.FObj 1 α ρ₀ s xstar ≤ ε →
        2 * (D : ℝ) ≤ G.totalWork 1 α ρ₀ s N)
    -- Part 2: ISTA total work O(1/α · log(1/ε)), independent of D
    ∧ (∃ K : ℕ, (∀ k, K ≤ k →
        G.FObj 1 α ρ₀ s (istaState G 1 α ρ₀ s k) - G.FObj 1 α ρ₀ s xstar ≤ ε) ∧
        G.istaTotalWork 1 α ρ₀ s K ≤ 2 * ((1 / α) * |Real.log ε| + 1)) := by
  intro G v ρ₀ s xstar
  have hρ₀ := starRho0_pos D hD α hα hα1
  have hρ₀_lt := starRho0_lt_one D hD α hα hα1
  have hmin := (star_unique_minimizer_support D hD α ρ₀ hα hα1 (le_refl _) hρ₀_lt).2.2.2.2.2.2
  refine ⟨?_, ?_⟩
  · -- Part 1: FISTA totalWork ≥ 2D
    intro N hN_acc
    have hN_ge4 : 4 ≤ N := by
      by_contra hlt
      push_neg at hlt
      have hk3 : N ≤ 3 := by omega
      have hgap := star_fista_gap_gt_eps0 D hD hD2 α hα hα1 N hk3
      linarith
    exact totalWork_ge_2D D hD α hα hα1 N hN_ge4
  · -- Part 2: ISTA total work ≤ 2 · (1/α · |log ε| + 1)
    obtain ⟨K, hK_conv, hK_bound⟩ :=
      ista_convergence_rate G 1 α ρ₀ s xstar hα (le_of_lt hα1) one_pos hρ₀ hmin ε hε
    exact ⟨K, hK_conv,
      le_trans (ista_total_work_le D hD α hα hα1 K) (by linarith)⟩

end RPPR

end
