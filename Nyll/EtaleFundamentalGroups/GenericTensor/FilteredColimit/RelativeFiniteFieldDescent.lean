/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Category.Ring.FinitePresentation
import Mathlib.Algebra.Category.Ring.Under.Basic
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.CategoryTheory.Presentable.Finite
import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Maps
import Nyll.EtaleFundamentalGroups.GenericTensor.FilteredColimit.AlgEquivDescent
import Nyll.EtaleFundamentalGroups.GenericTensor.FilteredColimit.CoconeLeg
import Nyll.EtaleFundamentalGroups.GenericTensor.FilteredColimit.FiniteFieldTensorDiagram
import Nyll.EtaleFundamentalGroups.GenericTensor.FilteredColimit.RelativeFiniteFieldTensorDiagram

/-!
# Relative finite-field descent of tensor-product maps

For algebra models over `R ⊗[k] F₀`, morphisms and isomorphisms after extension
of coefficients to an algebraic field extension `L/k` descend to an actual
finite intermediate field containing `F₀`. The coefficient legs are the
literal tensor maps induced by the field inclusions.

Maps defined at two finite stages which agree after extension to `L` agree at
one actual finite intermediate field containing both stages. The equality
endpoint reuses existing finite-presentation compactness.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace EtaleFundamentalGroups

variable (k L R : Type u) [Field k] [Field L] [CommRing R]
variable [Algebra k L] [Algebra k R]

local instance relativeFiniteTensorPointAlgebra (F₀ : IntermediateField k L) :
    Algebra (R ⊗[k] F₀.toSubalgebra) (R ⊗[k] L) :=
  (Algebra.TensorProduct.map (R := k) (S := R) (AlgHom.id R R)
    F₀.toSubalgebra.val).toRingHom.toAlgebra

@[reducible]
private def stageAction (F₀ E : IntermediateField k L) (hle : F₀ ≤ E) :
    Algebra (R ⊗[k] F₀.toSubalgebra) (R ⊗[k] E.toSubalgebra) :=
  (Algebra.TensorProduct.map (R := k) (S := R) (AlgHom.id R R)
    (Subalgebra.inclusion
      (show F₀.toSubalgebra ≤ E.toSubalgebra from hle))).toRingHom.toAlgebra

private def stageTensorLeg (F₀ : FiniteIntermediateFieldIndex k L)
    (E : IntermediateField k L) (hfinite : FiniteDimensional k E)
    (hle : F₀.val ≤ E)
    (B : Type u) [CommRing B] [Algebra (R ⊗[k] F₀.val.toSubalgebra) B] :
    let : Algebra (R ⊗[k] F₀.val.toSubalgebra) (R ⊗[k] E.toSubalgebra) :=
      stageAction k L R F₀.val E hle
    ((R ⊗[k] E.toSubalgebra) ⊗[R ⊗[k] F₀.val.toSubalgebra] B) →ₐ[R ⊗[k] F₀.val.toSubalgebra]
      ((R ⊗[k] L) ⊗[R ⊗[k] F₀.val.toSubalgebra] B) := by
  intro stageAlgebra
  let c := relativeFiniteIntermediateFieldTensorCocone k L R F₀
  let i : Under F₀ := Under.mk (homOfLE (show F₀ ≤ ⟨E, hfinite⟩ from hle))
  with_unfolding_all exact filteredTensorToColimitAlgHom c i (A := B)

private theorem stageTensorLeg_tmul (F₀ : FiniteIntermediateFieldIndex k L)
    (E : IntermediateField k L) (hfinite : FiniteDimensional k E)
    (hle : F₀.val ≤ E)
    (B : Type u) [CommRing B] [Algebra (R ⊗[k] F₀.val.toSubalgebra) B]
    (x : R ⊗[k] E.toSubalgebra) (b : B) :
    let : Algebra (R ⊗[k] F₀.val.toSubalgebra) (R ⊗[k] E.toSubalgebra) :=
      stageAction k L R F₀.val E hle
    stageTensorLeg k L R F₀ E hfinite hle B (x ⊗ₜ[R ⊗[k] F₀.val.toSubalgebra] b) =
      Algebra.TensorProduct.map (R := k) (S := R) (AlgHom.id R R) E.toSubalgebra.val x
        ⊗ₜ[R ⊗[k] F₀.val.toSubalgebra] b := by
  rfl

/-- Relative Hom descent with the actual finite containing field and literal
coefficient legs; only the source model is finitely presented. -/
theorem exists_finiteIntermediateField_tensorProduct_algHom_of_finiteModel
    [Algebra.IsAlgebraic k L]
    (F₀ : FiniteIntermediateFieldIndex k L)
    (B D : Type u) [CommRing B] [CommRing D]
    [Algebra (R ⊗[k] F₀.val.toSubalgebra) B] [Algebra (R ⊗[k] F₀.val.toSubalgebra) D]
    [Algebra.FinitePresentation (R ⊗[k] F₀.val.toSubalgebra) B]
    (f : ((R ⊗[k] L) ⊗[R ⊗[k] F₀.val.toSubalgebra] B) →ₐ[R ⊗[k] L]
      ((R ⊗[k] L) ⊗[R ⊗[k] F₀.val.toSubalgebra] D)) :
    ∃ E : IntermediateField k L, ∃ hfinite : FiniteDimensional k E,
      ∃ hle : F₀.val ≤ E,
        let : Algebra (R ⊗[k] F₀.val.toSubalgebra) (R ⊗[k] E.toSubalgebra) :=
          stageAction k L R F₀.val E hle
        ∃ fE : ((R ⊗[k] E.toSubalgebra) ⊗[R ⊗[k] F₀.val.toSubalgebra] B) →ₐ[R ⊗[k] E.toSubalgebra]
          ((R ⊗[k] E.toSubalgebra) ⊗[R ⊗[k] F₀.val.toSubalgebra] D),
        (stageTensorLeg k L R F₀ E hfinite hle D).comp
            (fE.restrictScalars (R ⊗[k] F₀.val.toSubalgebra)) =
          (f.restrictScalars (R ⊗[k] F₀.val.toSubalgebra)).comp
            (stageTensorLeg k L R F₀ E hfinite hle B) := by
  let F := relativeFiniteIntermediateFieldTensorDiagram k L R F₀
  let c := relativeFiniteIntermediateFieldTensorCocone k L R F₀
  have hc : IsColimit c := relativeFiniteIntermediateFieldTensorCoconeIsColimit k L R F₀
  obtain ⟨E, es, hforward⟩ :=
    exists_tensorProduct_algHom_stage_of_filteredColimit
      (R := R ⊗[k] F₀.val.toSubalgebra) (B := B) (D := D)
      F c hc (by with_unfolding_all exact f)
  refine ⟨E.right.val, E.right.property, E.hom.le, ?_⟩
  intro stageAlgebra
  refine ⟨(by with_unfolding_all exact es), ?_⟩
  with_unfolding_all
    exact hforward

/-- Relative isomorphism descent retains both literal inclusion squares at
one actual finite containing field. -/
theorem exists_finiteIntermediateField_tensorProduct_algEquiv_of_finiteModel
    [Algebra.IsAlgebraic k L]
    (F₀ : FiniteIntermediateFieldIndex k L)
    (B D : Type u) [CommRing B] [CommRing D]
    [Algebra (R ⊗[k] F₀.val.toSubalgebra) B] [Algebra (R ⊗[k] F₀.val.toSubalgebra) D]
    [Algebra.FinitePresentation (R ⊗[k] F₀.val.toSubalgebra) B]
    [Algebra.FinitePresentation (R ⊗[k] F₀.val.toSubalgebra) D]
    (e : ((R ⊗[k] L) ⊗[R ⊗[k] F₀.val.toSubalgebra] B) ≃ₐ[R ⊗[k] L]
      ((R ⊗[k] L) ⊗[R ⊗[k] F₀.val.toSubalgebra] D)) :
    ∃ E : IntermediateField k L, ∃ hfinite : FiniteDimensional k E,
      ∃ hle : F₀.val ≤ E,
        let : Algebra (R ⊗[k] F₀.val.toSubalgebra) (R ⊗[k] E.toSubalgebra) :=
          stageAction k L R F₀.val E hle
        ∃ eE : ((R ⊗[k] E.toSubalgebra) ⊗[R ⊗[k] F₀.val.toSubalgebra] B) ≃ₐ[R ⊗[k] E.toSubalgebra]
          ((R ⊗[k] E.toSubalgebra) ⊗[R ⊗[k] F₀.val.toSubalgebra] D),
        (stageTensorLeg k L R F₀ E hfinite hle D).comp
            (eE.toAlgHom.restrictScalars (R ⊗[k] F₀.val.toSubalgebra)) =
          (e.toAlgHom.restrictScalars (R ⊗[k] F₀.val.toSubalgebra)).comp
            (stageTensorLeg k L R F₀ E hfinite hle B) ∧
        (stageTensorLeg k L R F₀ E hfinite hle B).comp
            (eE.symm.toAlgHom.restrictScalars (R ⊗[k] F₀.val.toSubalgebra)) =
          (e.symm.toAlgHom.restrictScalars (R ⊗[k] F₀.val.toSubalgebra)).comp
            (stageTensorLeg k L R F₀ E hfinite hle D) := by
  let F := relativeFiniteIntermediateFieldTensorDiagram k L R F₀
  let c := relativeFiniteIntermediateFieldTensorCocone k L R F₀
  have hc : IsColimit c := relativeFiniteIntermediateFieldTensorCoconeIsColimit k L R F₀
  obtain ⟨E, es, hforward, hinverse⟩ :=
    exists_tensorProduct_algEquiv_stage_of_filteredColimit
      (R := R ⊗[k] F₀.val.toSubalgebra) (B := B) (D := D)
      F c hc (by with_unfolding_all exact e)
  refine ⟨E.right.val, E.right.property, E.hom.le, ?_⟩
  intro stageAlgebra
  refine ⟨(by with_unfolding_all exact es), ?_, ?_⟩
  · with_unfolding_all exact hforward
  · with_unfolding_all exact hinverse

private def stageTensorTransition
    (F₀ : FiniteIntermediateFieldIndex k L)
    (E H : IntermediateField k L)
    (hE : FiniteDimensional k E) (hH : FiniteDimensional k H)
    (hF₀E : F₀.val ≤ E) (hF₀H : F₀.val ≤ H) (hEH : E ≤ H)
    (B : Type u) [CommRing B] [Algebra (R ⊗[k] F₀.val.toSubalgebra) B] :
    let : Algebra (R ⊗[k] F₀.val.toSubalgebra) (R ⊗[k] E.toSubalgebra) :=
      stageAction k L R F₀.val E hF₀E
    let : Algebra (R ⊗[k] F₀.val.toSubalgebra) (R ⊗[k] H.toSubalgebra) :=
      stageAction k L R F₀.val H hF₀H
    ((R ⊗[k] E.toSubalgebra) ⊗[R ⊗[k] F₀.val.toSubalgebra] B) →ₐ[R ⊗[k] F₀.val.toSubalgebra]
      ((R ⊗[k] H.toSubalgebra) ⊗[R ⊗[k] F₀.val.toSubalgebra] B) := by
  intro stageEAlgebra stageHAlgebra
  let F := relativeFiniteIntermediateFieldTensorDiagram k L R F₀
  let iE : Under F₀ := Under.mk (homOfLE (show F₀ ≤ ⟨E, hE⟩ from hF₀E))
  let iH : Under F₀ := Under.mk (homOfLE (show F₀ ≤ ⟨H, hH⟩ from hF₀H))
  let u : iE ⟶ iH := Under.homMk (homOfLE (show (⟨E,hE⟩ : FiniteIntermediateFieldIndex k L) ≤
    ⟨H,hH⟩ from hEH))
  let c := F.mapCocone (Over.forgetCocone iH)
  with_unfolding_all exact filteredTensorToColimitAlgHom c (Over.mk u) (A := B)

private theorem stageTensorTransition_tmul
    (F₀ : FiniteIntermediateFieldIndex k L)
    (E H : IntermediateField k L)
    (hE : FiniteDimensional k E) (hH : FiniteDimensional k H)
    (hF₀E : F₀.val ≤ E) (hF₀H : F₀.val ≤ H) (hEH : E ≤ H)
    (B : Type u) [CommRing B] [Algebra (R ⊗[k] F₀.val.toSubalgebra) B]
    (x : R ⊗[k] E.toSubalgebra) (b : B) :
    let : Algebra (R ⊗[k] F₀.val.toSubalgebra) (R ⊗[k] E.toSubalgebra) :=
      stageAction k L R F₀.val E hF₀E
    let : Algebra (R ⊗[k] F₀.val.toSubalgebra) (R ⊗[k] H.toSubalgebra) :=
      stageAction k L R F₀.val H hF₀H
    stageTensorTransition k L R F₀ E H hE hH hF₀E hF₀H hEH B
        (x ⊗ₜ[R ⊗[k] F₀.val.toSubalgebra] b) =
      Algebra.TensorProduct.map (R := k) (S := R) (AlgHom.id R R)
          (Subalgebra.inclusion (show E.toSubalgebra ≤ H.toSubalgebra from hEH)) x
          ⊗ₜ[R ⊗[k] F₀.val.toSubalgebra] b := by
  rfl

attribute [local instance] EtaleFundamentalGroups.underCommRingCatAlgebra

private theorem exists_tensorProduct_algHom_eq_stage
    {A B D : Type u} [CommRing A] [CommRing B] [CommRing D]
    [Algebra A B] [Algebra A D] [Algebra.FinitePresentation A B]
    {J : Type u} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ Under (CommRingCat.of A)) (c : Cocone F) (hc : IsColimit c)
    {i j : J}
    (f : B →ₐ[A] (F.obj i ⊗[A] D)) (g : B →ₐ[A] (F.obj j ⊗[A] D))
    (h : (filteredTensorToColimitAlgHom c i (A := D)).comp f =
      (filteredTensorToColimitAlgHom c j (A := D)).comp g) :
    ∃ (l : J) (u : i ⟶ l) (v : j ⟶ l),
      (Algebra.TensorProduct.map (CommRingCat.toAlgHom (F.map u)) (AlgHom.id A D)).comp f =
        (Algebra.TensorProduct.map (CommRingCat.toAlgHom (F.map v)) (AlgHom.id A D)).comp g := by
  let A₀ : CommRingCat.{u} := CommRingCat.of A
  let D₀ : CommRingCat.{u} := CommRingCat.of D
  let tD : Under A₀ ⥤ Under D₀ := CommRingCat.tensorProd A₀ D₀
  let q : Under D₀ ⥤ Under A₀ := Under.map (CommRingCat.ofHom (algebraMap A D))
  let tq : Under A₀ ⥤ Under A₀ := tD ⋙ q
  let : PreservesColimit F tD :=
    preservesColimit_of_natIso F (CommRingCat.tensorProdIsoPushout A₀ D₀).symm
  let : IsConnected J := IsFiltered.isConnected J
  let : PreservesColimit F (tq ⋙ Under.forget A₀) := by
    change PreservesColimit F (tD ⋙ Under.forget D₀)
    infer_instance
  let : PreservesColimit F tq :=
    preservesColimit_of_reflects_of_preserves tq (Under.forget A₀)
  let cD : Cocone (F ⋙ tq) := tq.mapCocone c
  have hcD : IsColimit cD := isColimitOfPreserves tq hc
  let X : Under A₀ := CommRingCat.mkUnder A₀ B
  have hX : X.hom.hom.FinitePresentation := by
    change (algebraMap A B).FinitePresentation
    exact RingHom.finitePresentation_algebraMap.mpr inferInstance
  let : IsFinitelyPresentable.{u} X := CommRingCat.isFinitelyPresentable_under A₀ X hX
  let fi : B →ₐ[A] (D ⊗[A] F.obj i) :=
    (Algebra.TensorProduct.comm A (F.obj i) D).toAlgHom.comp f
  let gj : B →ₐ[A] (D ⊗[A] F.obj j) :=
    (Algebra.TensorProduct.comm A (F.obj j) D).toAlgHom.comp g
  have hcol : fi.toUnder ≫ cD.ι.app i = gj.toUnder ≫ cD.ι.app j := by
    apply CommRingCat.mkUnder_ext
    intro b
    change filteredBaseChangeCoconeLegAlgHom c i (A := D)
        ((Algebra.TensorProduct.comm A (F.obj i) D) (f b)) =
      filteredBaseChangeCoconeLegAlgHom c j (A := D)
        ((Algebra.TensorProduct.comm A (F.obj j) D) (g b))
    rw [filteredBaseChangeCoconeLegAlgHom_comm, filteredBaseChangeCoconeLegAlgHom_comm]
    exact congrArg (Algebra.TensorProduct.comm A c.pt D) (AlgHom.congr_fun h b)
  obtain ⟨l, u, v, hl⟩ :=
    IsFinitelyPresentable.exists_eq_of_isColimit
      (X := X) (i := i) (j := j) hcD
      (AlgHom.toUnder (R := A₀) fi) (AlgHom.toUnder (R := A₀) gj) hcol
  refine ⟨l, u, v, ?_⟩
  apply AlgHom.ext
  intro b
  apply (Algebra.TensorProduct.comm A (F.obj l) D).injective
  change (Algebra.TensorProduct.comm A (F.obj l) D)
      (Algebra.TensorProduct.map (CommRingCat.toAlgHom (F.map u)) (AlgHom.id A D) (f b)) =
    (Algebra.TensorProduct.comm A (F.obj l) D)
      (Algebra.TensorProduct.map (CommRingCat.toAlgHom (F.map v)) (AlgHom.id A D) (g b))
  rw [Algebra.TensorProduct.comm_comp_map_apply, Algebra.TensorProduct.comm_comp_map_apply]
  exact congrArg (fun z ↦ z.right b) hl

/-- Two maps from one finitely presented model which agree over L agree after
extension to one actual finite intermediate field containing both input fields. -/
theorem exists_finiteIntermediateField_tensorProduct_algHom_eq_of_finiteModel
    [Algebra.IsAlgebraic k L]
    (F₀ : FiniteIntermediateFieldIndex k L)
    (E G : IntermediateField k L)
    (hE : FiniteDimensional k E) (hG : FiniteDimensional k G)
    (h₀E : F₀.val ≤ E) (h₀G : F₀.val ≤ G)
    (B D : Type u) [CommRing B] [CommRing D]
    [Algebra (R ⊗[k] F₀.val.toSubalgebra) B]
    [Algebra (R ⊗[k] F₀.val.toSubalgebra) D]
    [Algebra.FinitePresentation (R ⊗[k] F₀.val.toSubalgebra) B] :
    let : Algebra (R ⊗[k] F₀.val.toSubalgebra) (R ⊗[k] E.toSubalgebra) :=
      stageAction k L R F₀.val E h₀E
    let : Algebra (R ⊗[k] F₀.val.toSubalgebra) (R ⊗[k] G.toSubalgebra) :=
      stageAction k L R F₀.val G h₀G
    ∀ (f : B →ₐ[R ⊗[k] F₀.val.toSubalgebra]
        ((R ⊗[k] E.toSubalgebra) ⊗[R ⊗[k] F₀.val.toSubalgebra] D))
      (g : B →ₐ[R ⊗[k] F₀.val.toSubalgebra]
        ((R ⊗[k] G.toSubalgebra) ⊗[R ⊗[k] F₀.val.toSubalgebra] D)),
      (stageTensorLeg k L R F₀ E hE h₀E D).comp f =
          (stageTensorLeg k L R F₀ G hG h₀G D).comp g →
      ∃ H : IntermediateField k L, ∃ hH : FiniteDimensional k H,
        ∃ h₀H : F₀.val ≤ H, ∃ hEH : E ≤ H, ∃ hGH : G ≤ H,
        let : Algebra (R ⊗[k] F₀.val.toSubalgebra) (R ⊗[k] H.toSubalgebra) :=
          stageAction k L R F₀.val H h₀H
        (stageTensorTransition k L R F₀ E H hE hH h₀E h₀H hEH D).comp f =
          (stageTensorTransition k L R F₀ G H hG hH h₀G h₀H hGH D).comp g := by
  intro stageEAlgebra stageGAlgebra f g h
  let F := relativeFiniteIntermediateFieldTensorDiagram k L R F₀
  let c := relativeFiniteIntermediateFieldTensorCocone k L R F₀
  have hc : IsColimit c := relativeFiniteIntermediateFieldTensorCoconeIsColimit k L R F₀
  let iE : Under F₀ := Under.mk (homOfLE (show F₀ ≤ ⟨E, hE⟩ from h₀E))
  let iG : Under F₀ := Under.mk (homOfLE (show F₀ ≤ ⟨G, hG⟩ from h₀G))
  obtain ⟨H, uEH, uGH, heq⟩ :=
    exists_tensorProduct_algHom_eq_stage
      (A := R ⊗[k] F₀.val.toSubalgebra) (B := B) (D := D) F c hc
      (i := iE) (j := iG)
      (by with_unfolding_all exact f)
      (by with_unfolding_all exact g)
      (by with_unfolding_all exact h)
  refine ⟨H.right.val, H.right.property, H.hom.le, uEH.right.le, uGH.right.le, ?_⟩
  intro stageHAlgebra
  with_unfolding_all exact heq
end EtaleFundamentalGroups
end
