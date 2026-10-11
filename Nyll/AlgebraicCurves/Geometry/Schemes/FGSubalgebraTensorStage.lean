/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_FGSubalgebraTensorStage.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.Order.DirectedInverseSystem
import Nyll.SchemeTheory.Descent.FGSubalgebra

/-!
Tensor products at finitely generated subalgebra stages and their directed-limit maps.
-/

universe u

open TensorProduct

namespace AlgebraicGeometry.FGSubalgebra

variable (k : Type u) [CommRing k] (A : Type u) [CommRing A] [Algebra k A]
  (Γ : Type u) [CommRing Γ] [Algebra k Γ]

/-- The tensor product with the given finitely generated subalgebra. -/
abbrev tensorStage (D : FGSubalgebra k A) : Type u := Γ ⊗[k] ↥D.1

/-- The transition algebra map induced by inclusion of finitely generated subalgebras. -/
noncomputable abbrev tensorStageMap (D D' : FGSubalgebra k A) (h : D ≤ D') :
    tensorStage k A Γ D →ₐ[Γ] tensorStage k A Γ D' :=
  Algebra.TensorProduct.map (AlgHom.id Γ Γ) (Subalgebra.inclusion (show D.1 ≤ D'.1 from h))

/-- The algebra map from a tensor stage to the tensor product with the ambient algebra. -/
noncomputable abbrev tensorStageToColimit (D : FGSubalgebra k A) : tensorStage k A Γ D →ₐ[Γ] Γ
    ⊗[k] A :=
  Algebra.TensorProduct.map (AlgHom.id Γ Γ) D.1.val

instance tensorStage_directedSystem : DirectedSystem (tensorStage k A Γ) (fun i j h =>
    tensorStageMap k A Γ i j h) where
  map_self := fun i x => by
    induction x using TensorProduct.inductionOn with
    | tmul γ d => rw [Algebra.TensorProduct.map_tmul]; rfl
    | add x y hx hy => rw [map_add, hx, hy]
  map_map := fun i j l hij hjl x => by
    induction x using TensorProduct.inductionOn with
    | tmul γ d => rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul]; rfl
    | add x y hx hy => simp only [map_add, hx, hy]

theorem tensorStageToColimit_comp (i j : FGSubalgebra k A) (h : i ≤ j) :
    (tensorStageToColimit k A Γ j).comp (tensorStageMap k A Γ i j h) = tensorStageToColimit k A
      Γ i := by
  refine AlgHom.ext fun x => ?_
  induction x using TensorProduct.inductionOn with
  | tmul γ d => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem tensorStageToColimit_comm (D : FGSubalgebra k A) (u : ↥D.1 ⊗[k] Γ) :
    tensorStageToColimit k A Γ D (TensorProduct.comm k _ _ u) = TensorProduct.comm k _ _
      (D.1.val.toLinearMap.rTensor Γ u) := by
  induction u using TensorProduct.inductionOn with
  | tmul d γ => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem tensorStageMap_comm (D D' : FGSubalgebra k A) (h : D ≤ D') (u : ↥D.1 ⊗[k] Γ) :
    tensorStageMap k A Γ D D' h (TensorProduct.comm k _ _ u) =
      TensorProduct.comm k _ _ ((Subalgebra.inclusion (show D.1 ≤ D'.1 from
        h)).toLinearMap.rTensor Γ u) := by
  induction u using TensorProduct.inductionOn with
  | tmul d γ => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem tensorStageToColimit_surj (b : Γ ⊗[k] A) : ∃ (D : FGSubalgebra k A) (x : tensorStage k A
    Γ D), tensorStageToColimit k A Γ D x = b := by
  obtain ⟨D, hD, u, hu⟩ := TensorProduct.Algebra.exists_of_fg (TensorProduct.comm k _ _ b)
  refine ⟨⟨D, hD⟩, TensorProduct.comm k _ _ u, ?_⟩
  rw [tensorStageToColimit_comm, hu, ← TensorProduct.comm_symm, LinearEquiv.symm_apply_apply]

theorem tensorStageToColimit_zero (D : FGSubalgebra k A) (x : tensorStage k A Γ D) (hx :
    tensorStageToColimit k A Γ D x = 0) :
    ∃ (D' : FGSubalgebra k A) (h : D ≤ D'), tensorStageMap k A Γ D D' h x = 0 := by
  have hx' : D.1.val.toLinearMap.rTensor Γ ((TensorProduct.comm k _ _).symm x) =
      D.1.val.toLinearMap.rTensor Γ 0 := by
    rw [map_zero]
    have := tensorStageToColimit_comm k A Γ D ((TensorProduct.comm k _ _).symm x)
    rw [LinearEquiv.apply_symm_apply, hx] at this
    exact (LinearEquiv.map_eq_zero_iff _).mp this.symm
  obtain ⟨D', hDD', hD', h⟩ := TensorProduct.Algebra.eq_of_fg_of_subtype_eq D.2 hx'
  refine ⟨⟨D', hD'⟩, hDD', ?_⟩
  rw [map_zero] at h
  have := tensorStageMap_comm k A Γ D ⟨D', hD'⟩ hDD' ((TensorProduct.comm k _ _).symm x)
  rw [LinearEquiv.apply_symm_apply] at this
  rw [this, h, map_zero]

end AlgebraicGeometry.FGSubalgebra
