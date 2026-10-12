/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.ProjectiveLine.CrossRatio
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Linear coordinate changes on the projective line

An invertible two-by-two coordinate matrix gives an actual equivalence of
projective points. Its action preserves the projective cross ratio.
-/

namespace AnabelianGeometry.ProjectiveLine

universe u

variable {K : Type u} [Field K]

/-- The linear map associated to a two-by-two coordinate matrix. -/
def coordinateLinearMap (α β γ δ : K) : (K × K) →ₗ[K] (K × K) where
  toFun := transform α β γ δ
  map_add' a b := by
    apply Prod.ext
    · change α * (a.1 + b.1) + β * (a.2 + b.2) =
        (α * a.1 + β * a.2) + (α * b.1 + β * b.2)
      ring
    · change γ * (a.1 + b.1) + δ * (a.2 + b.2) =
        (γ * a.1 + δ * a.2) + (γ * b.1 + δ * b.2)
      ring
  map_smul' t a := by
    apply Prod.ext
    · change α * (t * a.1) + β * (t * a.2) = t * (α * a.1 + β * a.2)
      ring
    · change γ * (t * a.1) + δ * (t * a.2) = t * (γ * a.1 + δ * a.2)
      ring

/-- A nonzero determinant makes the coordinate map injective. -/
theorem coordinateLinearMap_injective (α β γ δ : K) (hdet : α * δ - β * γ ≠ 0) :
    Function.Injective (coordinateLinearMap α β γ δ) := by
  intro a b h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  change α * a.1 + β * a.2 = α * b.1 + β * b.2 at h1
  change γ * a.1 + δ * a.2 = γ * b.1 + δ * b.2 at h2
  have hx : (α * δ - β * γ) * (a.1 - b.1) = 0 := by
    linear_combination δ * h1 - β * h2
  have hy : (α * δ - β * γ) * (a.2 - b.2) = 0 := by
    linear_combination α * h2 - γ * h1
  exact Prod.ext
    (sub_eq_zero.mp ((mul_eq_zero.mp hx).resolve_left hdet))
    (sub_eq_zero.mp ((mul_eq_zero.mp hy).resolve_left hdet))

/-- The corresponding linear equivalence when the determinant is nonzero. -/
noncomputable def coordinateLinearEquiv (α β γ δ : K)
    (hdet : α * δ - β * γ ≠ 0) : (K × K) ≃ₗ[K] (K × K) :=
  LinearEquiv.ofBijective (coordinateLinearMap α β γ δ)
    ⟨coordinateLinearMap_injective α β γ δ hdet,
      LinearMap.surjective_of_injective (coordinateLinearMap_injective α β γ δ hdet)⟩

/-- A linear equivalence induces an equivalence on the projective line. -/
def projectiveLinearEquiv (f : (K × K) ≃ₗ[K] (K × K)) :
    Projectivization K (K × K) ≃ Projectivization K (K × K) where
  toFun := Projectivization.map f.toLinearMap f.injective
  invFun := Projectivization.map f.symm.toLinearMap f.symm.injective
  left_inv p := by
    induction p using Projectivization.ind with
    | h v hv =>
      simp only [Projectivization.map_mk]
      change Projectivization.mk K (f.symm (f v)) _ = Projectivization.mk K v hv
      simp only [LinearEquiv.symm_apply_apply]
  right_inv p := by
    induction p using Projectivization.ind with
    | h v hv =>
      simp only [Projectivization.map_mk]
      change Projectivization.mk K (f (f.symm v)) _ = Projectivization.mk K v hv
      simp only [LinearEquiv.apply_symm_apply]

/-- Evaluation of the induced equivalence on a homogeneous representative. -/
theorem projectiveLinearEquiv_mk (f : (K × K) ≃ₗ[K] (K × K))
    (v : K × K) (hv : v ≠ 0) :
    projectiveLinearEquiv f (Projectivization.mk K v hv) =
      Projectivization.mk K (f v) (map_zero f ▸ f.injective.ne hv) := rfl

/-- The projective coordinate equivalence attached to an invertible matrix. -/
noncomputable def projectiveCoordinateChange (α β γ δ : K)
    (hdet : α * δ - β * γ ≠ 0) :
    Projectivization K (K × K) ≃ Projectivization K (K × K) :=
  projectiveLinearEquiv (coordinateLinearEquiv α β γ δ hdet)

/-- Cross ratios of actual projective points are preserved by coordinate changes. -/
theorem crossRatio_projectiveCoordinateChange (α β γ δ : K)
    (hdet : α * δ - β * γ ≠ 0) (a b c d : Projectivization K (K × K)) :
    crossRatio (projectiveCoordinateChange α β γ δ hdet a)
      (projectiveCoordinateChange α β γ δ hdet b)
      (projectiveCoordinateChange α β γ δ hdet c)
      (projectiveCoordinateChange α β γ δ hdet d) = crossRatio a b c d := by
  rw [← a.mk_rep, ← b.mk_rep, ← c.mk_rep, ← d.mk_rep]
  simp only [projectiveCoordinateChange, projectiveLinearEquiv_mk, crossRatio_mk]
  exact homogeneousCrossRatio_transform α β γ δ hdet a.rep b.rep c.rep d.rep

end AnabelianGeometry.ProjectiveLine
