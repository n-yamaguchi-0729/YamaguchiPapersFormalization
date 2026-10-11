/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Category.Ring.FinitePresentation
import Mathlib.Algebra.Category.Ring.Under.Basic
import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Maps
import Nyll.EtaleFundamentalGroups.GenericTensor.FilteredColimit.CategoricalDescent
import Nyll.EtaleFundamentalGroups.GenericTensor.FilteredColimit.NativeTensorCorrespondence
import Nyll.EtaleFundamentalGroups.GenericTensor.FilteredColimit.NativeTensorDescent
import Nyll.EtaleFundamentalGroups.GenericTensor.FilteredColimit.FiniteFieldTensorDiagram

/-!
# Map descent to an actual finite constant extension

Native tensor algebras are compared directly with their categorical pushouts.
The original algebra actions are retained throughout, and the literal field
inclusion squares follow from the native pushout comparison's naturality.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace EtaleFundamentalGroups

open CategoryTheory.CategoricalTensorDescent

/-- Native Hom descent preserves the literal coefficient square. -/
theorem exists_finiteIntermediateField_tensorProduct_algHom
    (k L R B D : Type u) [Field k] [Field L]
    [CommRing R] [CommRing B] [CommRing D]
    [Algebra k L] [Algebra k R] [Algebra.IsAlgebraic k L]
    [Algebra R B] [Algebra R D]
    [Algebra.FinitePresentation R B]
    (e : ((R ⊗[k] L) ⊗[R] B) →ₐ[R ⊗[k] L] ((R ⊗[k] L) ⊗[R] D)) :
    ∃ F : IntermediateField k L, FiniteDimensional k F ∧
      ∃ eF : ((R ⊗[k] F.toSubalgebra) ⊗[R] B) →ₐ[R ⊗[k] F.toSubalgebra]
        ((R ⊗[k] F.toSubalgebra) ⊗[R] D),
        (Algebra.TensorProduct.map
            (Algebra.TensorProduct.map (R := k) (S := R) (AlgHom.id R R) F.val)
            (AlgHom.id R D)).comp (eF.restrictScalars R) =
          (e.restrictScalars R).comp
            (Algebra.TensorProduct.map
              (Algebra.TensorProduct.map (R := k) (S := R) (AlgHom.id R R) F.val)
              (AlgHom.id R B)) := by
  let F := finiteIntermediateFieldTensorDiagram k L R
  let c := finiteIntermediateFieldTensorCocone k L R
  let B₀ : Under (CommRingCat.of R) := CommRingCat.mkUnder (CommRingCat.of R) B
  let D₀ : Under (CommRingCat.of R) := CommRingCat.mkUnder (CommRingCat.of R) D
  have hB : IsFinitelyPresentable.{u} B₀ :=
    CommRingCat.isFinitelyPresentable_under (CommRingCat.of R) B₀
      (CategoricalTensor.native_finitePresentation (CommAlgCat.of R B))
  let eP : model c.pt B₀ ⟶ model c.pt D₀ :=
    NativeTensorDescent.homEquiv R (R ⊗[k] L) B D e
  obtain ⟨i, fP, hfP⟩ :=
    CategoryTheory.CategoricalTensorDescent.exists_hom_stage B₀ D₀ F c
      (finiteIntermediateFieldTensorCoconeIsColimit k L R) eP
  let eF : ((R ⊗[k] i.val.toSubalgebra) ⊗[R] B) →ₐ[R ⊗[k] i.val.toSubalgebra]
      ((R ⊗[k] i.val.toSubalgebra) ⊗[R] D) :=
    (NativeTensorDescent.homEquiv R (R ⊗[k] i.val.toSubalgebra) B D).symm fP
  have heF : NativeTensorDescent.homEquiv R (R ⊗[k] i.val.toSubalgebra) B D eF = fP :=
    (NativeTensorDescent.homEquiv R (R ⊗[k] i.val.toSubalgebra) B D).apply_symm_apply fP
  have hs := extend_leg (c.ι.app i) fP
  rw [hfP, ← heF] at hs
  let q : (R ⊗[k] i.val.toSubalgebra) →ₐ[R] (R ⊗[k] L) :=
    Algebra.TensorProduct.map (R := k) (S := R) (AlgHom.id R R) i.val.val
  refine ⟨i.val, i.property, eF, ?_⟩
  exact NativeTensorDescent.hom_square R (R ⊗[k] L) B D q eF e hs

/-- Native isomorphism descent preserves both literal coefficient squares. -/
theorem exists_finiteIntermediateField_tensorProduct_algEquiv
    (k L R B D : Type u) [Field k] [Field L]
    [CommRing R] [CommRing B] [CommRing D]
    [Algebra k L] [Algebra k R] [Algebra.IsAlgebraic k L]
    [Algebra R B] [Algebra R D]
    [Algebra.FinitePresentation R B] [Algebra.FinitePresentation R D]
    (e : ((R ⊗[k] L) ⊗[R] B) ≃ₐ[R ⊗[k] L] ((R ⊗[k] L) ⊗[R] D)) :
    ∃ F : IntermediateField k L, FiniteDimensional k F ∧
      ∃ eF : ((R ⊗[k] F.toSubalgebra) ⊗[R] B) ≃ₐ[R ⊗[k] F.toSubalgebra]
        ((R ⊗[k] F.toSubalgebra) ⊗[R] D),
        (Algebra.TensorProduct.map
            (Algebra.TensorProduct.map (R := k) (S := R) (AlgHom.id R R) F.val)
            (AlgHom.id R D)).comp (eF.toAlgHom.restrictScalars R) =
          (e.toAlgHom.restrictScalars R).comp
            (Algebra.TensorProduct.map
              (Algebra.TensorProduct.map (R := k) (S := R) (AlgHom.id R R) F.val)
              (AlgHom.id R B)) ∧
        (Algebra.TensorProduct.map
            (Algebra.TensorProduct.map (R := k) (S := R) (AlgHom.id R R) F.val)
            (AlgHom.id R B)).comp (eF.symm.toAlgHom.restrictScalars R) =
          (e.symm.toAlgHom.restrictScalars R).comp
            (Algebra.TensorProduct.map
              (Algebra.TensorProduct.map (R := k) (S := R) (AlgHom.id R R) F.val)
              (AlgHom.id R D)) := by
  let F := finiteIntermediateFieldTensorDiagram k L R
  let c := finiteIntermediateFieldTensorCocone k L R
  let B₀ : Under (CommRingCat.of R) := CommRingCat.mkUnder (CommRingCat.of R) B
  let D₀ : Under (CommRingCat.of R) := CommRingCat.mkUnder (CommRingCat.of R) D
  have hB : IsFinitelyPresentable.{u} B₀ :=
    CommRingCat.isFinitelyPresentable_under (CommRingCat.of R) B₀
      (CategoricalTensor.native_finitePresentation (CommAlgCat.of R B))
  have hD : IsFinitelyPresentable.{u} D₀ :=
    CommRingCat.isFinitelyPresentable_under (CommRingCat.of R) D₀
      (CategoricalTensor.native_finitePresentation (CommAlgCat.of R D))
  let eP : model c.pt B₀ ≅ model c.pt D₀ :=
    NativeTensorDescent.isoEquiv R (R ⊗[k] L) B D e
  obtain ⟨i, ei, hforward, _⟩ :=
    CategoryTheory.CategoricalTensorDescent.exists_iso_stage B₀ D₀ F c
      (finiteIntermediateFieldTensorCoconeIsColimit k L R) eP
  let eF : ((R ⊗[k] i.val.toSubalgebra) ⊗[R] B) ≃ₐ[R ⊗[k] i.val.toSubalgebra]
      ((R ⊗[k] i.val.toSubalgebra) ⊗[R] D) :=
    (NativeTensorDescent.isoEquiv R (R ⊗[k] i.val.toSubalgebra) B D).symm ei
  have heF : NativeTensorDescent.isoEquiv R (R ⊗[k] i.val.toSubalgebra) B D eF = ei :=
    (NativeTensorDescent.isoEquiv R (R ⊗[k] i.val.toSubalgebra) B D).apply_symm_apply ei
  let q : (R ⊗[k] i.val.toSubalgebra) →ₐ[R] (R ⊗[k] L) :=
    Algebra.TensorProduct.map (R := k) (S := R) (AlgHom.id R R) i.val.val
  have hs := extend_leg (c.ι.app i) ei.hom
  rw [hforward, ← heF] at hs
  change leg (c.ι.app i) B₀ ≫
      (NativeTensorDescent.isoEquiv R (R ⊗[k] L) B D e).hom.right =
    (NativeTensorDescent.isoEquiv R (R ⊗[k] i.val.toSubalgebra) B D eF).hom.right ≫
      leg (c.ι.app i) D₀ at hs
  rw [NativeTensorDescent.isoEquiv_hom, NativeTensorDescent.isoEquiv_hom] at hs
  have hNative := NativeTensorDescent.hom_square
    (S := R ⊗[k] i.val.toSubalgebra) R (R ⊗[k] L) B D q
    eF.toAlgHom e.toAlgHom hs
  refine ⟨i.val, i.property, eF, hNative, ?_⟩
  apply AlgHom.ext
  intro x
  apply e.injective
  have hx := AlgHom.congr_fun hNative (eF.symm x)
  simpa only [AlgHom.comp_apply, AlgHom.restrictScalars_apply,
    AlgEquiv.toAlgHom_apply, AlgEquiv.apply_symm_apply] using hx.symm

end EtaleFundamentalGroups

end
