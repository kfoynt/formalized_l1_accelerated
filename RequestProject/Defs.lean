import Mathlib

/-!
# Definitions for ℓ₁-Regularized PageRank Formalization
-/

noncomputable section

open Finset BigOperators Real

namespace RPPR

/-- A graph on n vertices. -/
structure Graph (n : ℕ) where
  A : Fin n → Fin n → ℝ
  A_nonneg : ∀ i j, 0 ≤ A i j
  A_symm : ∀ i j, A i j = A j i
  A_no_loops : ∀ i, A i i = 0
  deg_pos : ∀ i, 0 < ∑ j : Fin n, A i j

variable {n : ℕ}

@[reducible] def Graph.deg (G : Graph n) (i : Fin n) : ℝ := ∑ j, G.A i j
@[reducible] def Graph.sqrtDeg (G : Graph n) (i : Fin n) : ℝ := Real.sqrt (G.deg i)
@[reducible] def Graph.invSqrtDeg (G : Graph n) (i : Fin n) : ℝ := (Real.sqrt (G.deg i))⁻¹

def Graph.deg_pos' (G : Graph n) (i : Fin n) : 0 < G.deg i := G.deg_pos i

lemma Graph.sqrtDeg_pos (G : Graph n) (i : Fin n) : 0 < G.sqrtDeg i :=
  Real.sqrt_pos_of_pos (G.deg_pos i)

lemma Graph.sqrtDeg_ne_zero (G : Graph n) (i : Fin n) : G.sqrtDeg i ≠ 0 :=
  ne_of_gt (G.sqrtDeg_pos i)

@[reducible] def Graph.Qentry (G : Graph n) (α : ℝ) (i j : Fin n) : ℝ :=
  if i = j then (1 + α) / 2
  else -(1 - α) / 2 * G.A i j / (G.sqrtDeg i * G.sqrtDeg j)

@[reducible] def Graph.gradf (G : Graph n) (α : ℝ) (s x : Fin n → ℝ) (i : Fin n) : ℝ :=
  ∑ j, G.Qentry α i j * x j - α * G.invSqrtDeg i * s i

@[reducible] def Graph.fObj (G : Graph n) (α : ℝ) (s x : Fin n → ℝ) : ℝ :=
  (1/2) * ∑ i, x i * (∑ j, G.Qentry α i j * x j) -
  α * ∑ i, G.invSqrtDeg i * s i * x i

@[reducible] def Graph.gReg (G : Graph n) (c α ρ : ℝ) (x : Fin n → ℝ) : ℝ :=
  c * α * ρ * ∑ i, G.sqrtDeg i * |x i|

@[reducible] def Graph.FObj (G : Graph n) (c α ρ : ℝ) (s x : Fin n → ℝ) : ℝ :=
  G.fObj α s x + G.gReg c α ρ x

def Graph.IsMinimizer (G : Graph n) (c α ρ : ℝ) (s xstar : Fin n → ℝ) : Prop :=
  ∀ x : Fin n → ℝ, G.FObj c α ρ s xstar ≤ G.FObj c α ρ s x

@[reducible] def Graph.fwdStep (G : Graph n) (α η : ℝ) (s x : Fin n → ℝ) (i : Fin n) : ℝ :=
  x i - η * G.gradf α s x i

@[reducible] def softThresh (t w : ℝ) : ℝ :=
  if t < w then w - t
  else if w < -t then w + t
  else 0

@[reducible] def Graph.proxMap (G : Graph n) (c α ρ η : ℝ) (w : Fin n → ℝ) (i : Fin n) : ℝ :=
  softThresh (η * c * α * ρ * G.sqrtDeg i) (w i)

@[reducible] def Graph.kktSlack (G : Graph n) (c α ρ : ℝ) (s x : Fin n → ℝ) (i : Fin n) : ℝ :=
  c * ρ * α - |G.gradf α s x i| / G.sqrtDeg i

@[reducible] def fistaMom (α : ℝ) : ℝ := (1 - Real.sqrt α) / (1 + Real.sqrt α)

def fistaState (G : Graph n) (c α ρ : ℝ) (s : Fin n → ℝ) : ℕ → (Fin n → ℝ) × (Fin n → ℝ)
  | 0 => (0, 0)
  | k + 1 =>
    let (xprev, xcur) := fistaState G c α ρ s k
    let β := fistaMom α
    let y := fun i => xcur i + β * (xcur i - xprev i)
    let xnext := fun i => G.proxMap c α ρ 1 (fun j => G.fwdStep α 1 s y j) i
    (xcur, xnext)

@[reducible] def fistaX (G : Graph n) (c α ρ : ℝ) (s : Fin n → ℝ) (k : ℕ) : Fin n → ℝ :=
  (fistaState G c α ρ s k).2

@[reducible] def fistaY (G : Graph n) (c α ρ : ℝ) (s : Fin n → ℝ) (k : ℕ) : Fin n → ℝ :=
  let (xprev, xcur) := fistaState G c α ρ s k
  fun i => xcur i + fistaMom α * (xcur i - xprev i)

@[reducible] def basisVec {n : ℕ} (v : Fin n) (i : Fin n) : ℝ := if i = v then 1 else 0

@[reducible] def normSq {n : ℕ} (x : Fin n → ℝ) : ℝ := ∑ i, x i ^ 2

@[reducible] def vecSupp {n : ℕ} (x : Fin n → ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => x i ≠ 0)

@[reducible] def Graph.vol (G : Graph n) (S : Finset (Fin n)) : ℝ :=
  ∑ i ∈ S, G.deg i

def Graph.bdry (G : Graph n) (S : Finset (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter (fun j => j ∉ S ∧ ∃ i ∈ S, 0 < G.A j i)

def Graph.exterior (G : Graph n) (S : Finset (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter (fun j => j ∉ S ∧ j ∉ G.bdry S)

def Graph.nbrsInCount (G : Graph n) (i : Fin n) (T : Finset (Fin n)) : ℕ :=
  (T.filter (fun j => 0 < G.A i j)).card

def Graph.minDegIn (G : Graph n) (T : Finset (Fin n)) (hT : T.Nonempty) : ℝ :=
  T.inf' hT G.deg

def Graph.spuriousActive (G : Graph n) (α ρ : ℝ) (s : Fin n → ℝ)
    (SA : Finset (Fin n)) (k : ℕ) : Finset (Fin n) :=
  vecSupp (fistaX G 2 α ρ s (k + 1)) \ SA

@[reducible] def Graph.iterWork (G : Graph n) (c α ρ : ℝ) (s : Fin n → ℝ) (k : ℕ) : ℝ :=
  G.vol (vecSupp (fistaY G c α ρ s k)) + G.vol (vecSupp (fistaX G c α ρ s (k + 1)))

@[reducible] def Graph.totalWork (G : Graph n) (c α ρ : ℝ) (s : Fin n → ℝ) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N, G.iterWork c α ρ s k

end RPPR

end
