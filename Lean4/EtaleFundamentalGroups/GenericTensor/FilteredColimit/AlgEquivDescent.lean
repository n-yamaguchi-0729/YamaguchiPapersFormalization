/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Category.Ring.FinitePresentation
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Category.Ring.Under.Basic
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.CategoryTheory.Presentable.Basic
import Mathlib.RingTheory.FiniteStability
import Mathlib.RingTheory.FinitePresentation
import Mathlib.Data.Fintype.EquivFin
import Mathlib.RingTheory.TensorProduct.Maps
import EtaleFundamentalGroups.GenericTensor.FilteredColimit.CoconeLeg


/-!
# Descending tensor-product equivalences from filtered colimits

A finite presentation over a base ring is compact with respect to filtered
colimits.  Applying this twice, to the forward and inverse maps of an
equivalence after base change, and then moving the two inverse equations to a
common later stage, descends the whole equivalence to one finite stage.

This is the finite-data descent needed after a strict-Henselian splitting.  It
does not assume or construct a strict henselization: the input is an arbitrary
filtered colimit of pointed base algebras.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace EtaleFundamentalGroups

universe u

local instance underCommRingCatAlgebraDescent
    {R : Type u} [CommRing R] (A : Under (CommRingCat.of R)) : Algebra R A :=
  RingHom.toAlgebra A.hom.hom

/-- Descend one tensor-product morphism to a finite stage of the coefficient
colimit. Only the source algebra needs a finite presentation. The descended
map is an actual algebra homomorphism between the two stage tensor products,
and its scalar extension recovers the given morphism along the literal cocone maps. -/
theorem exists_tensorProduct_algHom_stage_of_filteredColimit
    {R B D : Type u} [CommRing R] [CommRing B] [CommRing D]
    [Algebra R B] [Algebra R D]
    [Algebra.FinitePresentation R B]
    {J : Type u} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ Under (CommRingCat.of R))
    (c : Cocone F) (hc : IsColimit c)
    (f : (c.pt ⊗[R] B) →ₐ[c.pt] (c.pt ⊗[R] D)) :
    ∃ (i : J) (fᵢ : (F.obj i ⊗[R] B) →ₐ[F.obj i] (F.obj i ⊗[R] D)),
      (filteredTensorToColimitAlgHom c i (A := D)).comp (fᵢ.restrictScalars R) =
        (f.restrictScalars R).comp
          (filteredTensorToColimitAlgHom c i (A := B)) := by
  classical
  let R₀ : CommRingCat.{u} := CommRingCat.of R
  let D₀ : CommRingCat.{u} := CommRingCat.of D
  let tD : Under R₀ ⥤ Under D₀ := CommRingCat.tensorProd R₀ D₀
  let cD : Cocone (F ⋙ tD) := tD.mapCocone c
  let : PreservesColimit F tD :=
    preservesColimit_of_natIso F
      (CommRingCat.tensorProdIsoPushout R₀ D₀).symm
  have hcD : IsColimit cD := isColimitOfPreserves tD hc
  let fInf : B →ₐ[R] (D ⊗[R] c.pt) :=
    (Algebra.TensorProduct.comm R c.pt D).toAlgHom.comp
      ((f.restrictScalars R).comp Algebra.TensorProduct.includeRight)
  let fInfD : (D ⊗[R] B) →ₐ[D] (D ⊗[R] c.pt) :=
    AlgHom.liftEquiv R D B (D ⊗[R] c.pt) fInf
  let DB : Under D₀ := CommRingCat.mkUnder D₀ (D ⊗[R] B)
  have hDBfp : DB.hom.hom.FinitePresentation := by
    change (algebraMap D (D ⊗[R] B)).FinitePresentation
    exact RingHom.finitePresentation_algebraMap.mpr inferInstance
  let : IsFinitelyPresentable.{u} DB :=
    CommRingCat.isFinitelyPresentable_under D₀ DB hDBfp
  obtain ⟨i, fᵢD, hfᵢD⟩ :=
    IsFinitelyPresentable.exists_hom_of_isColimit hcD fInfD.toUnder
  let fiDCanonical : (D ⊗[R] B) →ₐ[D] (D ⊗[R] F.obj i) :=
    { __ := (CommRingCat.toAlgHom fᵢD).toRingHom
      commutes' := by
        intro d
        exact (CommRingCat.toAlgHom fᵢD).commutes d }
  have hfCanonical :
      (filteredBaseChangeCoconeLegAlgHom c i (A := D)).comp
          fiDCanonical = fInfD := by
    apply AlgHom.ext
    intro z
    have hfi : fiDCanonical.toUnder = fᵢD := rfl
    have hleg :
        (filteredBaseChangeCoconeLegAlgHom c i (A := D)).toUnder =
          cD.ι.app i := rfl
    have hcomp := hfᵢD
    rw [← hfi, ← hleg] at hcomp
    exact congrArg (fun q ↦ q.right z) hcomp
  let fiPrime : B →ₐ[R] (D ⊗[R] F.obj i) :=
    (AlgHom.liftEquiv R D B (D ⊗[R] F.obj i)).symm fiDCanonical
  let fᵢ : B →ₐ[R] (F.obj i ⊗[R] D) :=
    (Algebra.TensorProduct.comm R D (F.obj i)).toAlgHom.comp fiPrime
  have hfᵢ (b : B) :
      filteredTensorToColimitAlgHom c i (A := D) (fᵢ b) = f (1 ⊗ₜ[R] b) := by
    apply (Algebra.TensorProduct.comm R c.pt D).injective
    calc
      (Algebra.TensorProduct.comm R c.pt D)
          (filteredTensorToColimitAlgHom c i (A := D) (fᵢ b)) =
          filteredBaseChangeCoconeLegAlgHom c i (A := D)
            ((Algebra.TensorProduct.comm R (F.obj i) D) (fᵢ b)) :=
        (filteredBaseChangeCoconeLegAlgHom_comm c i (fᵢ b)).symm
      _ = filteredBaseChangeCoconeLegAlgHom c i (A := D)
            (fiDCanonical (1 ⊗ₜ[R] b)) := by
        change filteredBaseChangeCoconeLegAlgHom c i (A := D)
            ((Algebra.TensorProduct.comm R (F.obj i) D)
              ((Algebra.TensorProduct.comm R D (F.obj i)) (fiPrime b))) =
          filteredBaseChangeCoconeLegAlgHom c i (A := D)
            (fiDCanonical (1 ⊗ₜ[R] b))
        rw [← Algebra.TensorProduct.comm_symm, AlgEquiv.symm_apply_apply]
        rfl
      _ = fInfD (1 ⊗ₜ[R] b) :=
        congrArg (fun h ↦ h (1 ⊗ₜ[R] b)) hfCanonical
      _ = (Algebra.TensorProduct.comm R c.pt D) (f (1 ⊗ₜ[R] b)) := by
        simp only [fInfD, AlgHom.liftEquiv_tmul, one_smul, fInf,
          AlgHom.comp_apply, AlgHom.restrictScalars_apply,
          AlgEquiv.toAlgHom_apply, Algebra.TensorProduct.includeRight_apply]
  let φᵢ : (F.obj i ⊗[R] B) →ₐ[F.obj i] (F.obj i ⊗[R] D) :=
    AlgHom.liftEquiv R (F.obj i) B (F.obj i ⊗[R] D) fᵢ
  refine ⟨i, φᵢ, ?_⟩
  apply Algebra.TensorProduct.ext
  · ext x
    change filteredTensorToColimitAlgHom c i
        (φᵢ (algebraMap (F.obj i) (F.obj i ⊗[R] B) x)) =
      f (filteredTensorToColimitAlgHom c i
        (algebraMap (F.obj i) (F.obj i ⊗[R] B) x))
    rw [φᵢ.commutes]
    change CommRingCat.toAlgHom (c.ι.app i) x ⊗ₜ[R] (1 : D) =
      f (CommRingCat.toAlgHom (c.ι.app i) x ⊗ₜ[R] (1 : B))
    exact (f.commutes (CommRingCat.toAlgHom (c.ι.app i) x)).symm
  · ext b
    simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply, φᵢ,
      AlgHom.liftEquiv_tmul, one_smul, Algebra.TensorProduct.includeRight_apply,
      filteredTensorToColimitAlgHom_tmul, map_one]
    exact hfᵢ b

/-- Descend both maps of an equivalence to a common finite stage. -/
private theorem exists_stage_algHom_pair_of_filteredColimit
    {R B D : Type u} [CommRing R] [CommRing B] [CommRing D]
    [Algebra R B] [Algebra R D]
    [Algebra.FinitePresentation R B]
    [Algebra.FinitePresentation R D]
    {J : Type u} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ Under (CommRingCat.of R))
    (c : Cocone F) (hc : IsColimit c)
    (e : (c.pt ⊗[R] B) ≃ₐ[c.pt] (c.pt ⊗[R] D)) :
    ∃ (k : J)
      (fₖ : B →ₐ[R] (F.obj k ⊗[R] D))
      (gₖ : D →ₐ[R] (F.obj k ⊗[R] B)),
      (filteredTensorToColimitAlgHom c k (A := D)).comp
          ((AlgHom.liftEquiv R (F.obj k) B (F.obj k ⊗[R] D) fₖ).restrictScalars R) =
        (e.toAlgHom.restrictScalars R).comp
          (filteredTensorToColimitAlgHom c k (A := B)) ∧
      (filteredTensorToColimitAlgHom c k (A := B)).comp
          ((AlgHom.liftEquiv R (F.obj k) D (F.obj k ⊗[R] B) gₖ).restrictScalars R) =
        (e.symm.toAlgHom.restrictScalars R).comp
          (filteredTensorToColimitAlgHom c k (A := D)) := by
  classical
  obtain ⟨i, φᵢ, hfᵢ⟩ :=
    exists_tensorProduct_algHom_stage_of_filteredColimit F c hc e.toAlgHom
  obtain ⟨j, ψⱼ, hgⱼ⟩ :=
    exists_tensorProduct_algHom_stage_of_filteredColimit F c hc e.symm.toAlgHom
  let fᵢ : B →ₐ[R] (F.obj i ⊗[R] D) :=
    (φᵢ.restrictScalars R).comp Algebra.TensorProduct.includeRight
  let gⱼ : D →ₐ[R] (F.obj j ⊗[R] B) :=
    (ψⱼ.restrictScalars R).comp Algebra.TensorProduct.includeRight
  let k := IsFiltered.max i j
  let hik : i ⟶ k := IsFiltered.leftToMax i j
  let hjk : j ⟶ k := IsFiltered.rightToMax i j
  let fik : F.obj i →ₐ[R] F.obj k := CommRingCat.toAlgHom (F.map hik)
  let fjk : F.obj j →ₐ[R] F.obj k := CommRingCat.toAlgHom (F.map hjk)
  let fₖ : B →ₐ[R] (F.obj k ⊗[R] D) :=
    (Algebra.TensorProduct.map fik (AlgHom.id R D)).comp fᵢ
  let gₖ : D →ₐ[R] (F.obj k ⊗[R] B) :=
    (Algebra.TensorProduct.map fjk (AlgHom.id R B)).comp gⱼ
  have hleg {a b : J} (h : a ⟶ b) (A : Type u) [CommRing A] [Algebra R A] :
      (filteredTensorToColimitAlgHom c b (A := A)).comp
          (Algebra.TensorProduct.map (CommRingCat.toAlgHom (F.map h)) (AlgHom.id R A)) =
        filteredTensorToColimitAlgHom c a (A := A) := by
    change (Algebra.TensorProduct.map (CommRingCat.toAlgHom (c.ι.app b))
        (AlgHom.id R A)).comp
        (Algebra.TensorProduct.map (CommRingCat.toAlgHom (F.map h)) (AlgHom.id R A)) =
      Algebra.TensorProduct.map (CommRingCat.toAlgHom (c.ι.app a)) (AlgHom.id R A)
    rw [← Algebra.TensorProduct.map_comp, AlgHom.id_comp,
      ← CommRingCat.toAlgHom_comp, c.w h]
  refine ⟨k, fₖ, gₖ, ?_, ?_⟩
  · apply Algebra.TensorProduct.ext
    · ext x
      change filteredTensorToColimitAlgHom c k
          ((AlgHom.liftEquiv R (F.obj k) B (F.obj k ⊗[R] D) fₖ)
            (algebraMap (F.obj k) (F.obj k ⊗[R] B) x)) =
        e (filteredTensorToColimitAlgHom c k
          (algebraMap (F.obj k) (F.obj k ⊗[R] B) x))
      rw [AlgHom.commutes]
      change CommRingCat.toAlgHom (c.ι.app k) x ⊗ₜ[R] (1 : D) =
        e (CommRingCat.toAlgHom (c.ι.app k) x ⊗ₜ[R] (1 : B))
      exact (e.commutes (CommRingCat.toAlgHom (c.ι.app k) x)).symm
    · ext b
      have hf : filteredTensorToColimitAlgHom c i (A := D) (fᵢ b) =
          e (1 ⊗ₜ[R] b) := by
        simpa only [fᵢ, AlgHom.comp_apply, AlgHom.restrictScalars_apply,
          Algebra.TensorProduct.includeRight_apply, filteredTensorToColimitAlgHom_tmul,
          map_one, AlgEquiv.toAlgHom_apply] using
          congrArg (fun h ↦ h (1 ⊗ₜ[R] b)) hfᵢ
      have hnat := congrArg (fun h ↦ h (fᵢ b)) (hleg hik D)
      simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply,
        AlgHom.liftEquiv_tmul, one_smul, Algebra.TensorProduct.includeRight_apply,
        filteredTensorToColimitAlgHom_tmul, map_one, AlgEquiv.toAlgHom_apply, fₖ]
      rw [show filteredTensorToColimitAlgHom c k (A := D)
        ((Algebra.TensorProduct.map fik (AlgHom.id R D)) (fᵢ b)) =
          filteredTensorToColimitAlgHom c i (A := D) (fᵢ b) from hnat]
      exact hf
  · apply Algebra.TensorProduct.ext
    · ext x
      change filteredTensorToColimitAlgHom c k
          ((AlgHom.liftEquiv R (F.obj k) D (F.obj k ⊗[R] B) gₖ)
            (algebraMap (F.obj k) (F.obj k ⊗[R] D) x)) =
        e.symm (filteredTensorToColimitAlgHom c k
          (algebraMap (F.obj k) (F.obj k ⊗[R] D) x))
      rw [AlgHom.commutes]
      change CommRingCat.toAlgHom (c.ι.app k) x ⊗ₜ[R] (1 : B) =
        e.symm (CommRingCat.toAlgHom (c.ι.app k) x ⊗ₜ[R] (1 : D))
      exact (e.symm.commutes (CommRingCat.toAlgHom (c.ι.app k) x)).symm
    · ext d
      have hg : filteredTensorToColimitAlgHom c j (A := B) (gⱼ d) =
          e.symm (1 ⊗ₜ[R] d) := by
        simpa only [gⱼ, AlgHom.comp_apply, AlgHom.restrictScalars_apply,
          Algebra.TensorProduct.includeRight_apply, filteredTensorToColimitAlgHom_tmul,
          map_one, AlgEquiv.toAlgHom_apply] using
          congrArg (fun h ↦ h (1 ⊗ₜ[R] d)) hgⱼ
      have hnat := congrArg (fun h ↦ h (gⱼ d)) (hleg hjk B)
      simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply,
        AlgHom.liftEquiv_tmul, one_smul, Algebra.TensorProduct.includeRight_apply,
        filteredTensorToColimitAlgHom_tmul, map_one, AlgEquiv.toAlgHom_apply, gₖ]
      rw [show filteredTensorToColimitAlgHom c k (A := B)
        ((Algebra.TensorProduct.map fjk (AlgHom.id R B)) (gⱼ d)) =
          filteredTensorToColimitAlgHom c j (A := B) (gⱼ d) from hnat]
      exact hg

/-- The two descended maps compose to the identity after applying the colimit cocone. -/
private theorem stage_comp_identity_at_colimit
    {R B D : Type u} [CommRing R] [CommRing B] [CommRing D]
    [Algebra R B] [Algebra R D]
    {J : Type u} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ Under (CommRingCat.of R))
    (c : Cocone F) (k : J)
    (e : (c.pt ⊗[R] B) ≃ₐ[c.pt] (c.pt ⊗[R] D))
    (φₖ : (F.obj k ⊗[R] B) →ₐ[F.obj k] (F.obj k ⊗[R] D))
    (ψₖ : (F.obj k ⊗[R] D) →ₐ[F.obj k] (F.obj k ⊗[R] B))
    (hφₖ :
      (filteredTensorToColimitAlgHom c k (A := D)).comp
          (φₖ.restrictScalars R) =
        (e.toAlgHom.restrictScalars R).comp
          (filteredTensorToColimitAlgHom c k (A := B)))
    (hψₖ :
      (filteredTensorToColimitAlgHom c k (A := B)).comp
          (ψₖ.restrictScalars R) =
        (e.symm.toAlgHom.restrictScalars R).comp
          (filteredTensorToColimitAlgHom c k (A := D))) :
    let compB : B →ₐ[R] (B ⊗[R] F.obj k) :=
      (Algebra.TensorProduct.comm R (F.obj k) B).toAlgHom.comp
        (((ψₖ.comp φₖ).restrictScalars R).comp
          Algebra.TensorProduct.includeRight)
    let idB : B →ₐ[R] (B ⊗[R] F.obj k) :=
      Algebra.TensorProduct.includeLeft
    let compBB : (B ⊗[R] B) →ₐ[B] (B ⊗[R] F.obj k) :=
      AlgHom.liftEquiv R B B (B ⊗[R] F.obj k) compB
    let idBB : (B ⊗[R] B) →ₐ[B] (B ⊗[R] F.obj k) :=
      AlgHom.liftEquiv R B B (B ⊗[R] F.obj k) idB
    (filteredBaseChangeCoconeLegAlgHom c k (A := B)).comp compBB =
      (filteredBaseChangeCoconeLegAlgHom c k (A := B)).comp idBB := by
  let compB : B →ₐ[R] (B ⊗[R] F.obj k) :=
    (Algebra.TensorProduct.comm R (F.obj k) B).toAlgHom.comp
      (((ψₖ.comp φₖ).restrictScalars R).comp
        Algebra.TensorProduct.includeRight)
  let idB : B →ₐ[R] (B ⊗[R] F.obj k) :=
    Algebra.TensorProduct.includeLeft
  let compBB : (B ⊗[R] B) →ₐ[B] (B ⊗[R] F.obj k) :=
    AlgHom.liftEquiv R B B (B ⊗[R] F.obj k) compB
  let idBB : (B ⊗[R] B) →ₐ[B] (B ⊗[R] F.obj k) :=
    AlgHom.liftEquiv R B B (B ⊗[R] F.obj k) idB
  change (filteredBaseChangeCoconeLegAlgHom c k (A := B)).comp compBB =
    (filteredBaseChangeCoconeLegAlgHom c k (A := B)).comp idBB
  apply Algebra.TensorProduct.ext_ring
  ext b
  simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply,
    compBB, idBB, AlgHom.liftEquiv_tmul, one_smul,
    compB, idB, Algebra.TensorProduct.includeRight_apply]
  change filteredBaseChangeCoconeLegAlgHom c k
      ((Algebra.TensorProduct.comm R (F.obj k) B)
        (ψₖ (φₖ (1 ⊗ₜ[R] b)))) =
    filteredBaseChangeCoconeLegAlgHom c k (b ⊗ₜ[R] 1)
  nth_rewrite 2 [← Algebra.TensorProduct.comm_tmul]
  rw [filteredBaseChangeCoconeLegAlgHom_comm,
    filteredBaseChangeCoconeLegAlgHom_comm]
  have hψ := congrArg (fun h ↦ h (φₖ (1 ⊗ₜ[R] b))) hψₖ
  have hφ := congrArg (fun h ↦ h (1 ⊗ₜ[R] b)) hφₖ
  have hinner :
      filteredTensorToColimitAlgHom c k (ψₖ (φₖ (1 ⊗ₜ[R] b))) =
        filteredTensorToColimitAlgHom c k (1 ⊗ₜ[R] b) := by
    calc
      filteredTensorToColimitAlgHom c k (ψₖ (φₖ (1 ⊗ₜ[R] b))) =
        ((filteredTensorToColimitAlgHom c k).comp
          (ψₖ.restrictScalars R)) (φₖ (1 ⊗ₜ[R] b)) := rfl
      _ = ((e.symm.toAlgHom.restrictScalars R).comp
          (filteredTensorToColimitAlgHom c k))
            (φₖ (1 ⊗ₜ[R] b)) := hψ
      _ = e.symm (((filteredTensorToColimitAlgHom c k).comp
          (φₖ.restrictScalars R)) (1 ⊗ₜ[R] b)) := rfl
      _ = e.symm (((e.toAlgHom.restrictScalars R).comp
          (filteredTensorToColimitAlgHom c k)) (1 ⊗ₜ[R] b)) := by
            rw [hφ]
      _ = filteredTensorToColimitAlgHom c k (1 ⊗ₜ[R] b) :=
        e.symm_apply_apply _
  exact congrArg (fun z ↦ Algebra.TensorProduct.comm R c.pt B z) hinner

/-- Equality of two maps from a finitely presented algebra into a base-change
stage is detected after one common transition of the coefficient diagram. -/
private theorem exists_baseChange_algHom_eq_stage
    {R B A : Type u} [CommRing R] [CommRing B] [CommRing A]
    [Algebra R B] [Algebra B A] [Algebra.FinitePresentation B A]
    {J : Type u} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ Under (CommRingCat.of R))
    (c : Cocone F) (hc : IsColimit c) (k : J)
    (f g : A →ₐ[B] (B ⊗[R] F.obj k))
    (hfg : (filteredBaseChangeCoconeLegAlgHom c k (A := B)).comp f =
      (filteredBaseChangeCoconeLegAlgHom c k (A := B)).comp g) :
    ∃ (l : J) (hkl : k ⟶ l),
      f.toUnder ≫ (F ⋙ CommRingCat.tensorProd (CommRingCat.of R)
          (CommRingCat.of B)).map hkl =
        g.toUnder ≫ (F ⋙ CommRingCat.tensorProd (CommRingCat.of R)
          (CommRingCat.of B)).map hkl := by
  let R₀ : CommRingCat.{u} := CommRingCat.of R
  let B₀ : CommRingCat.{u} := CommRingCat.of B
  let tB : Under R₀ ⥤ Under B₀ := CommRingCat.tensorProd R₀ B₀
  let FB : J ⥤ Under B₀ := F ⋙ tB
  let cB : Cocone FB := tB.mapCocone c
  let : PreservesColimit F tB :=
    preservesColimit_of_natIso F
      (CommRingCat.tensorProdIsoPushout R₀ B₀).symm
  have hcB : IsColimit cB := isColimitOfPreserves tB hc
  let A₀ : Under B₀ := CommRingCat.mkUnder B₀ A
  have hAfp : A₀.hom.hom.FinitePresentation := by
    change (algebraMap B A).FinitePresentation
    exact RingHom.finitePresentation_algebraMap.mpr inferInstance
  let : IsFinitelyPresentable.{u} A₀ :=
    CommRingCat.isFinitelyPresentable_under B₀ A₀ hAfp
  have hfgUnder : f.toUnder ≫ cB.ι.app k = g.toUnder ≫ cB.ι.app k := by
    apply CommRingCat.mkUnder_ext
    intro a
    exact congrArg (fun q ↦ q a) hfg
  exact exists_eq_of_preservesColimit_coyoneda_self (X := A₀) hcB
    f.toUnder g.toUnder hfgUnder

/-- A finitely presented algebra detects one composite identity at a finite stage. -/
private theorem exists_stage_comp_identity
    {R B D : Type u} [CommRing R] [CommRing B] [CommRing D]
    [Algebra R B] [Algebra R D]
    [Algebra.FinitePresentation R B]
    {J : Type u} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ Under (CommRingCat.of R))
    (c : Cocone F) (hc : IsColimit c) (k : J)
    (e : (c.pt ⊗[R] B) ≃ₐ[c.pt] (c.pt ⊗[R] D))
    (φₖ : (F.obj k ⊗[R] B) →ₐ[F.obj k] (F.obj k ⊗[R] D))
    (ψₖ : (F.obj k ⊗[R] D) →ₐ[F.obj k] (F.obj k ⊗[R] B))
    (hφₖ :
      (filteredTensorToColimitAlgHom c k (A := D)).comp
          (φₖ.restrictScalars R) =
        (e.toAlgHom.restrictScalars R).comp
          (filteredTensorToColimitAlgHom c k (A := B)))
    (hψₖ :
      (filteredTensorToColimitAlgHom c k (A := B)).comp
          (ψₖ.restrictScalars R) =
        (e.symm.toAlgHom.restrictScalars R).comp
          (filteredTensorToColimitAlgHom c k (A := D))) :
    let R₀ : CommRingCat.{u} := CommRingCat.of R
    let B₀ : CommRingCat.{u} := CommRingCat.of B
    let tB : Under R₀ ⥤ Under B₀ := CommRingCat.tensorProd R₀ B₀
    let FB : J ⥤ Under B₀ := F ⋙ tB
    let compB : B →ₐ[R] (B ⊗[R] F.obj k) :=
      (Algebra.TensorProduct.comm R (F.obj k) B).toAlgHom.comp
        (((ψₖ.comp φₖ).restrictScalars R).comp
          Algebra.TensorProduct.includeRight)
    let idB : B →ₐ[R] (B ⊗[R] F.obj k) :=
      Algebra.TensorProduct.includeLeft
    let compBB : (B ⊗[R] B) →ₐ[B] (B ⊗[R] F.obj k) :=
      AlgHom.liftEquiv R B B (B ⊗[R] F.obj k) compB
    let idBB : (B ⊗[R] B) →ₐ[B] (B ⊗[R] F.obj k) :=
      AlgHom.liftEquiv R B B (B ⊗[R] F.obj k) idB
    ∃ (l : J) (hkl : k ⟶ l),
      compBB.toUnder ≫ FB.map hkl = idBB.toUnder ≫ FB.map hkl := by
  intro R₀ B₀ tB FB compB idB compBB idBB
  exact exists_baseChange_algHom_eq_stage (A := B ⊗[R] B) F c hc k compBB idBB
    (stage_comp_identity_at_colimit F c k e φₖ ψₖ hφₖ hψₖ)

/-- A later finite stage makes both descended composites the identity. -/
private theorem exists_common_stage_for_inverse_equations
    {R B D : Type u} [CommRing R] [CommRing B] [CommRing D]
    [Algebra R B] [Algebra R D]
    [Algebra.FinitePresentation R B] [Algebra.FinitePresentation R D]
    {J : Type u} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ Under (CommRingCat.of R))
    (c : Cocone F) (hc : IsColimit c) (k : J)
    (e : (c.pt ⊗[R] B) ≃ₐ[c.pt] (c.pt ⊗[R] D))
    (φₖ : (F.obj k ⊗[R] B) →ₐ[F.obj k] (F.obj k ⊗[R] D))
    (ψₖ : (F.obj k ⊗[R] D) →ₐ[F.obj k] (F.obj k ⊗[R] B))
    (hφₖ :
      (filteredTensorToColimitAlgHom c k (A := D)).comp
          (φₖ.restrictScalars R) =
        (e.toAlgHom.restrictScalars R).comp
          (filteredTensorToColimitAlgHom c k (A := B)))
    (hψₖ :
      (filteredTensorToColimitAlgHom c k (A := B)).comp
          (ψₖ.restrictScalars R) =
        (e.symm.toAlgHom.restrictScalars R).comp
          (filteredTensorToColimitAlgHom c k (A := D))) :
    let R₀ : CommRingCat.{u} := CommRingCat.of R
    let B₀ : CommRingCat.{u} := CommRingCat.of B
    let D₀ : CommRingCat.{u} := CommRingCat.of D
    let tB : Under R₀ ⥤ Under B₀ := CommRingCat.tensorProd R₀ B₀
    let tD : Under R₀ ⥤ Under D₀ := CommRingCat.tensorProd R₀ D₀
    let FB : J ⥤ Under B₀ := F ⋙ tB
    let FD : J ⥤ Under D₀ := F ⋙ tD
    let compB : B →ₐ[R] (B ⊗[R] F.obj k) :=
      (Algebra.TensorProduct.comm R (F.obj k) B).toAlgHom.comp
        (((ψₖ.comp φₖ).restrictScalars R).comp
          Algebra.TensorProduct.includeRight)
    let idB : B →ₐ[R] (B ⊗[R] F.obj k) :=
      Algebra.TensorProduct.includeLeft
    let compBB : (B ⊗[R] B) →ₐ[B] (B ⊗[R] F.obj k) :=
      AlgHom.liftEquiv R B B (B ⊗[R] F.obj k) compB
    let idBB : (B ⊗[R] B) →ₐ[B] (B ⊗[R] F.obj k) :=
      AlgHom.liftEquiv R B B (B ⊗[R] F.obj k) idB
    let compD : D →ₐ[R] (D ⊗[R] F.obj k) :=
      (Algebra.TensorProduct.comm R (F.obj k) D).toAlgHom.comp
        (((φₖ.comp ψₖ).restrictScalars R).comp
          Algebra.TensorProduct.includeRight)
    let idD : D →ₐ[R] (D ⊗[R] F.obj k) :=
      Algebra.TensorProduct.includeLeft
    let compDD : (D ⊗[R] D) →ₐ[D] (D ⊗[R] F.obj k) :=
      AlgHom.liftEquiv R D D (D ⊗[R] F.obj k) compD
    let idDD : (D ⊗[R] D) →ₐ[D] (D ⊗[R] F.obj k) :=
      AlgHom.liftEquiv R D D (D ⊗[R] F.obj k) idD
    ∃ (m : J) (hkm' : k ⟶ m),
      compBB.toUnder ≫ FB.map hkm' = idBB.toUnder ≫ FB.map hkm' ∧
      compDD.toUnder ≫ FD.map hkm' = idDD.toUnder ≫ FD.map hkm' ∧
      (filteredTensorToColimitAlgHom c m (A := B)).comp
          (Algebra.TensorProduct.map
            (CommRingCat.toAlgHom (F.map hkm')) (AlgHom.id R B)) =
        filteredTensorToColimitAlgHom c k ∧
      (filteredTensorToColimitAlgHom c m (A := D)).comp
          (Algebra.TensorProduct.map
            (CommRingCat.toAlgHom (F.map hkm')) (AlgHom.id R D)) =
        filteredTensorToColimitAlgHom c k := by
  classical
  let R₀ : CommRingCat.{u} := CommRingCat.of R
  let B₀ : CommRingCat.{u} := CommRingCat.of B
  let D₀ : CommRingCat.{u} := CommRingCat.of D
  let tB : Under R₀ ⥤ Under B₀ := CommRingCat.tensorProd R₀ B₀
  let tD : Under R₀ ⥤ Under D₀ := CommRingCat.tensorProd R₀ D₀
  let FB : J ⥤ Under B₀ := F ⋙ tB
  let FD : J ⥤ Under D₀ := F ⋙ tD
  let compB : B →ₐ[R] (B ⊗[R] F.obj k) :=
    (Algebra.TensorProduct.comm R (F.obj k) B).toAlgHom.comp
      (((ψₖ.comp φₖ).restrictScalars R).comp
        Algebra.TensorProduct.includeRight)
  let idB : B →ₐ[R] (B ⊗[R] F.obj k) :=
    Algebra.TensorProduct.includeLeft
  let compBB : (B ⊗[R] B) →ₐ[B] (B ⊗[R] F.obj k) :=
    AlgHom.liftEquiv R B B (B ⊗[R] F.obj k) compB
  let idBB : (B ⊗[R] B) →ₐ[B] (B ⊗[R] F.obj k) :=
    AlgHom.liftEquiv R B B (B ⊗[R] F.obj k) idB
  let compD : D →ₐ[R] (D ⊗[R] F.obj k) :=
    (Algebra.TensorProduct.comm R (F.obj k) D).toAlgHom.comp
      (((φₖ.comp ψₖ).restrictScalars R).comp
        Algebra.TensorProduct.includeRight)
  let idD : D →ₐ[R] (D ⊗[R] F.obj k) :=
    Algebra.TensorProduct.includeLeft
  let compDD : (D ⊗[R] D) →ₐ[D] (D ⊗[R] F.obj k) :=
    AlgHom.liftEquiv R D D (D ⊗[R] F.obj k) compD
  let idDD : (D ⊗[R] D) →ₐ[D] (D ⊗[R] F.obj k) :=
    AlgHom.liftEquiv R D D (D ⊗[R] F.obj k) idD
  obtain ⟨lB, hklB, hB⟩ :=
    exists_stage_comp_identity F c hc k e φₖ ψₖ hφₖ hψₖ
  obtain ⟨lD, hklD, hD⟩ :=
    exists_stage_comp_identity (B := D) (D := B)
      F c hc k e.symm ψₖ φₖ hψₖ hφₖ
  let l := IsFiltered.max lB lD
  let hlBl : lB ⟶ l := IsFiltered.leftToMax lB lD
  let hlDl : lD ⟶ l := IsFiltered.rightToMax lB lD
  let hkB : k ⟶ l := hklB ≫ hlBl
  let hkD : k ⟶ l := hklD ≫ hlDl
  let m := IsFiltered.coeq hkB hkD
  let hlm : l ⟶ m := IsFiltered.coeqHom hkB hkD
  have hkm : hkB ≫ hlm = hkD ≫ hlm :=
    IsFiltered.coeq_condition hkB hkD
  let hkm' : k ⟶ m := hkB ≫ hlm
  let fkm : F.obj k →ₐ[R] F.obj m := CommRingCat.toAlgHom (F.map hkm')
  have hclegApply (x : F.obj k) :
      CommRingCat.toAlgHom (c.ι.app m) (fkm x) =
        CommRingCat.toAlgHom (c.ι.app k) x := by
    have h := congrArg (fun q ↦ q.right x) (c.w hkm')
    change CommRingCat.toAlgHom (c.ι.app m)
        (CommRingCat.toAlgHom (F.map hkm') x) =
      CommRingCat.toAlgHom (c.ι.app k) x at h
    simpa only [fkm] using h
  have hcTensorB :
      (filteredTensorToColimitAlgHom c m (A := B)).comp
          (Algebra.TensorProduct.map fkm (AlgHom.id R B)) =
        filteredTensorToColimitAlgHom c k := by
    apply Algebra.TensorProduct.ext
    · ext x
      change CommRingCat.toAlgHom (c.ι.app m) (fkm x) ⊗ₜ[R] (1 : B) =
        CommRingCat.toAlgHom (c.ι.app k) x ⊗ₜ[R] (1 : B)
      rw [hclegApply]
    · ext b
      simp [filteredTensorToColimitAlgHom]
  have hcTensorD :
      (filteredTensorToColimitAlgHom c m (A := D)).comp
          (Algebra.TensorProduct.map fkm (AlgHom.id R D)) =
        filteredTensorToColimitAlgHom c k := by
    apply Algebra.TensorProduct.ext
    · ext x
      change CommRingCat.toAlgHom (c.ι.app m) (fkm x) ⊗ₜ[R] (1 : D) =
        CommRingCat.toAlgHom (c.ι.app k) x ⊗ₜ[R] (1 : D)
      rw [hclegApply]
    · ext d
      simp [filteredTensorToColimitAlgHom]
  have hB_m :
      compBB.toUnder ≫ FB.map hkm' = idBB.toUnder ≫ FB.map hkm' := by
    have hpath : hkm' = hklB ≫ (hlBl ≫ hlm) := by
      simp only [hkm', hkB, Category.assoc]
    rw [hpath]
    have h := congrArg (fun q ↦ q ≫ FB.map (hlBl ≫ hlm)) hB
    have hmap := FB.map_comp hklB (hlBl ≫ hlm)
    dsimp only [FB, tB, Functor.comp, CommRingCat.tensorProd] at hmap h ⊢
    simp only [Category.assoc] at h
    rw [← hmap] at h
    exact h
  have hD_m :
      compDD.toUnder ≫ FD.map hkm' = idDD.toUnder ≫ FD.map hkm' := by
    have hpath : hkm' = hklD ≫ (hlDl ≫ hlm) := by
      rw [show hkm' = hkD ≫ hlm from hkm]
      simp only [hkD, Category.assoc]
    rw [hpath]
    have h := congrArg (fun q ↦ q ≫ FD.map (hlDl ≫ hlm)) hD
    have hmap := FD.map_comp hklD (hlDl ≫ hlm)
    dsimp only [FD, tD, Functor.comp, CommRingCat.tensorProd] at hmap h ⊢
    simp only [Category.assoc] at h
    rw [← hmap] at h
    exact h
  exact ⟨m, hkm', hB_m, hD_m, hcTensorB, hcTensorD⟩
/-- An equivalence between two fixed finitely presented algebras after base
change to a filtered colimit already exists at one finite stage.

Both displayed equalities use the literal tensor maps induced by the cocone,
so the descended equivalence and its inverse recover the supplied equivalence
at the colimit.  In particular every distinguished coordinate in `B` or `D`
is preserved without an additional comparison hypothesis.

This endpoint deliberately uses one universe for the rings and the filtered
index category.  That is the universe in which Mathlib currently exposes
`CommRingCat.isFinitelyPresentable_under`; applications with a larger index
universe must first choose an equivalent small filtered presentation. -/
theorem exists_tensorProduct_algEquiv_stage_of_filteredColimit
    {R B D : Type u} [CommRing R] [CommRing B] [CommRing D]
    [Algebra R B] [Algebra R D]
    [Algebra.FinitePresentation R B]
    [Algebra.FinitePresentation R D]
    {J : Type u} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ Under (CommRingCat.of R))
    (c : Cocone F) (hc : IsColimit c)
    (e : (c.pt ⊗[R] B) ≃ₐ[c.pt] (c.pt ⊗[R] D)) :
    ∃ (i : J)
      (eᵢ : (F.obj i ⊗[R] B) ≃ₐ[F.obj i] (F.obj i ⊗[R] D)),
      (filteredTensorToColimitAlgHom c i (A := D)).comp
          (eᵢ.toAlgHom.restrictScalars R) =
        (e.toAlgHom.restrictScalars R).comp
          (filteredTensorToColimitAlgHom c i (A := B)) ∧
      (filteredTensorToColimitAlgHom c i (A := B)).comp
          (eᵢ.symm.toAlgHom.restrictScalars R) =
        (e.symm.toAlgHom.restrictScalars R).comp
          (filteredTensorToColimitAlgHom c i (A := D)) := by
  classical
  let R₀ : CommRingCat.{u} := CommRingCat.of R
  let B₀ : CommRingCat.{u} := CommRingCat.of B
  let D₀ : CommRingCat.{u} := CommRingCat.of D
  let tB : Under R₀ ⥤ Under B₀ := CommRingCat.tensorProd R₀ B₀
  let tD : Under R₀ ⥤ Under D₀ := CommRingCat.tensorProd R₀ D₀
  let FB : J ⥤ Under B₀ := F ⋙ tB
  let FD : J ⥤ Under D₀ := F ⋙ tD
  obtain ⟨k, fₖ, gₖ, hφₖ, hψₖ⟩ :=
    exists_stage_algHom_pair_of_filteredColimit F c hc e
  let φₖ : (F.obj k ⊗[R] B) →ₐ[F.obj k] (F.obj k ⊗[R] D) :=
    AlgHom.liftEquiv R (F.obj k) B (F.obj k ⊗[R] D) fₖ
  let ψₖ : (F.obj k ⊗[R] D) →ₐ[F.obj k] (F.obj k ⊗[R] B) :=
    AlgHom.liftEquiv R (F.obj k) D (F.obj k ⊗[R] B) gₖ
  let compB : B →ₐ[R] (B ⊗[R] F.obj k) :=
    (Algebra.TensorProduct.comm R (F.obj k) B).toAlgHom.comp
      (((ψₖ.comp φₖ).restrictScalars R).comp
        Algebra.TensorProduct.includeRight)
  let idB : B →ₐ[R] (B ⊗[R] F.obj k) :=
    Algebra.TensorProduct.includeLeft
  let compBB : (B ⊗[R] B) →ₐ[B] (B ⊗[R] F.obj k) :=
    AlgHom.liftEquiv R B B (B ⊗[R] F.obj k) compB
  let idBB : (B ⊗[R] B) →ₐ[B] (B ⊗[R] F.obj k) :=
    AlgHom.liftEquiv R B B (B ⊗[R] F.obj k) idB
  let compD : D →ₐ[R] (D ⊗[R] F.obj k) :=
    (Algebra.TensorProduct.comm R (F.obj k) D).toAlgHom.comp
      (((φₖ.comp ψₖ).restrictScalars R).comp
        Algebra.TensorProduct.includeRight)
  let idD : D →ₐ[R] (D ⊗[R] F.obj k) :=
    Algebra.TensorProduct.includeLeft
  let compDD : (D ⊗[R] D) →ₐ[D] (D ⊗[R] F.obj k) :=
    AlgHom.liftEquiv R D D (D ⊗[R] F.obj k) compD
  let idDD : (D ⊗[R] D) →ₐ[D] (D ⊗[R] F.obj k) :=
    AlgHom.liftEquiv R D D (D ⊗[R] F.obj k) idD
  obtain ⟨m, hkm', hB_m, hD_m, hcTensorB, hcTensorD⟩ :=
    exists_common_stage_for_inverse_equations F c hc k e φₖ ψₖ hφₖ hψₖ
  let fkm : F.obj k →ₐ[R] F.obj m := CommRingCat.toAlgHom (F.map hkm')
  let fₘ : B →ₐ[R] (F.obj m ⊗[R] D) :=
    (Algebra.TensorProduct.map fkm (AlgHom.id R D)).comp fₖ
  let gₘ : D →ₐ[R] (F.obj m ⊗[R] B) :=
    (Algebra.TensorProduct.map fkm (AlgHom.id R B)).comp gₖ
  let φₘ : (F.obj m ⊗[R] B) →ₐ[F.obj m] (F.obj m ⊗[R] D) :=
    AlgHom.liftEquiv R (F.obj m) B (F.obj m ⊗[R] D) fₘ
  let ψₘ : (F.obj m ⊗[R] D) →ₐ[F.obj m] (F.obj m ⊗[R] B) :=
    AlgHom.liftEquiv R (F.obj m) D (F.obj m ⊗[R] B) gₘ
  have hφBaseChange :
      (φₘ.restrictScalars R).comp
          (Algebra.TensorProduct.map fkm (AlgHom.id R B)) =
        (Algebra.TensorProduct.map fkm (AlgHom.id R D)).comp
          (φₖ.restrictScalars R) := by
    apply Algebra.TensorProduct.ext
    · ext x
      simp [φₘ, φₖ, Algebra.smul_def]
    · ext b
      simp [φₘ, φₖ, fₘ]
  have hψBaseChange :
      (ψₘ.restrictScalars R).comp
          (Algebra.TensorProduct.map fkm (AlgHom.id R D)) =
        (Algebra.TensorProduct.map fkm (AlgHom.id R B)).comp
          (ψₖ.restrictScalars R) := by
    apply Algebra.TensorProduct.ext
    · ext x
      simp [ψₘ, ψₖ, Algebra.smul_def]
    · ext d
      simp [ψₘ, ψₖ, gₘ]
  have hleft : ψₘ.comp φₘ = AlgHom.id (F.obj m) _ := by
    apply Algebra.TensorProduct.ext_ring
    ext b
    have hcoord := congrArg
      (fun h ↦ CommRingCat.toAlgHom h (1 ⊗ₜ[R] b)) hB_m
    have hcoord' :
        (Algebra.TensorProduct.map (AlgHom.id B B) fkm)
            ((Algebra.TensorProduct.comm R (F.obj k) B)
              (ψₖ (φₖ (1 ⊗ₜ[R] b)))) =
          (b ⊗ₜ[R] (1 : F.obj m) : B ⊗[R] F.obj m) := by
      calc
        _ = (Algebra.TensorProduct.map (AlgHom.id B B) fkm)
              (b ⊗ₜ[R] (1 : F.obj k)) := by
                change (CommRingCat.toAlgHom (FB.map hkm'))
                    ((Algebra.TensorProduct.comm R (F.obj k) B)
                      (ψₖ (φₖ (1 ⊗ₜ[R] b)))) =
                  (CommRingCat.toAlgHom (FB.map hkm'))
                    (b ⊗ₜ[R] (1 : F.obj k))
                change (CommRingCat.toAlgHom (FB.map hkm'))
                    (compBB (1 ⊗ₜ[R] b)) =
                  (CommRingCat.toAlgHom (FB.map hkm'))
                    (idBB (1 ⊗ₜ[R] b)) at hcoord
                simpa only [AlgEquiv.toAlgHom_apply,
                  AlgHom.liftEquiv_tmul, one_smul,
                  AlgHom.comp_apply, AlgHom.restrictScalars_apply,
                  Algebra.TensorProduct.includeRight_apply,
                  Algebra.TensorProduct.includeLeft_apply,
                  compBB, idBB, compB, idB] using hcoord
        _ = (b ⊗ₜ[R] (1 : F.obj m) : B ⊗[R] F.obj m) := by
              simp
    have hφ := congrArg (fun h ↦ h (1 ⊗ₜ[R] b)) hφBaseChange
    have hψ := congrArg (fun h ↦ h (φₖ (1 ⊗ₜ[R] b))) hψBaseChange
    have hstage :
        ψₘ (φₘ (1 ⊗ₜ[R] b)) =
          (Algebra.TensorProduct.map fkm (AlgHom.id R B))
            (ψₖ (φₖ (1 ⊗ₜ[R] b))) := by
      calc
        ψₘ (φₘ (1 ⊗ₜ[R] b)) =
            ψₘ ((Algebra.TensorProduct.map fkm (AlgHom.id R D))
              (φₖ (1 ⊗ₜ[R] b))) := by
                congr 1
                simpa only [AlgHom.comp_apply,
                  AlgHom.restrictScalars_apply,
                  Algebra.TensorProduct.map_tmul, map_one,
                  AlgHom.id_apply] using hφ
        _ = (Algebra.TensorProduct.map fkm (AlgHom.id R B))
              (ψₖ (φₖ (1 ⊗ₜ[R] b))) := by
                simpa only [AlgHom.comp_apply,
                  AlgHom.restrictScalars_apply] using hψ
    apply (Algebra.TensorProduct.comm R (F.obj m) B).injective
    calc
      (Algebra.TensorProduct.comm R (F.obj m) B)
          (ψₘ (φₘ (1 ⊗ₜ[R] b))) =
        (Algebra.TensorProduct.comm R (F.obj m) B)
          ((Algebra.TensorProduct.map fkm (AlgHom.id R B))
            (ψₖ (φₖ (1 ⊗ₜ[R] b)))) := congrArg _ hstage
      _ = (Algebra.TensorProduct.map (AlgHom.id B B) fkm)
            ((Algebra.TensorProduct.comm R (F.obj k) B)
              (ψₖ (φₖ (1 ⊗ₜ[R] b)))) :=
        Algebra.TensorProduct.comm_comp_map_apply fkm (AlgHom.id R B) _
      _ = (b ⊗ₜ[R] (1 : F.obj m) : B ⊗[R] F.obj m) := hcoord'
      _ = (Algebra.TensorProduct.comm R (F.obj m) B)
            (1 ⊗ₜ[R] b) := by simp
  have hright : φₘ.comp ψₘ = AlgHom.id (F.obj m) _ := by
    apply Algebra.TensorProduct.ext_ring
    ext d
    have hcoord := congrArg
      (fun h ↦ CommRingCat.toAlgHom h (1 ⊗ₜ[R] d)) hD_m
    have hcoord' :
        (Algebra.TensorProduct.map (AlgHom.id D D) fkm)
            ((Algebra.TensorProduct.comm R (F.obj k) D)
              (φₖ (ψₖ (1 ⊗ₜ[R] d)))) =
          (d ⊗ₜ[R] (1 : F.obj m) : D ⊗[R] F.obj m) := by
      calc
        _ = (Algebra.TensorProduct.map (AlgHom.id D D) fkm)
              (d ⊗ₜ[R] (1 : F.obj k)) := by
                change (CommRingCat.toAlgHom (FD.map hkm'))
                    ((Algebra.TensorProduct.comm R (F.obj k) D)
                      (φₖ (ψₖ (1 ⊗ₜ[R] d)))) =
                  (CommRingCat.toAlgHom (FD.map hkm'))
                    (d ⊗ₜ[R] (1 : F.obj k))
                change (CommRingCat.toAlgHom (FD.map hkm'))
                    (compDD (1 ⊗ₜ[R] d)) =
                  (CommRingCat.toAlgHom (FD.map hkm'))
                    (idDD (1 ⊗ₜ[R] d)) at hcoord
                simpa only [AlgEquiv.toAlgHom_apply,
                  AlgHom.liftEquiv_tmul, one_smul,
                  AlgHom.comp_apply, AlgHom.restrictScalars_apply,
                  Algebra.TensorProduct.includeRight_apply,
                  Algebra.TensorProduct.includeLeft_apply,
                  compDD, idDD, compD, idD] using hcoord
        _ = (d ⊗ₜ[R] (1 : F.obj m) : D ⊗[R] F.obj m) := by
              simp
    have hψ := congrArg (fun h ↦ h (1 ⊗ₜ[R] d)) hψBaseChange
    have hφ := congrArg (fun h ↦ h (ψₖ (1 ⊗ₜ[R] d))) hφBaseChange
    have hstage :
        φₘ (ψₘ (1 ⊗ₜ[R] d)) =
          (Algebra.TensorProduct.map fkm (AlgHom.id R D))
            (φₖ (ψₖ (1 ⊗ₜ[R] d))) := by
      calc
        φₘ (ψₘ (1 ⊗ₜ[R] d)) =
            φₘ ((Algebra.TensorProduct.map fkm (AlgHom.id R B))
              (ψₖ (1 ⊗ₜ[R] d))) := by
                congr 1
                simpa only [AlgHom.comp_apply,
                  AlgHom.restrictScalars_apply,
                  Algebra.TensorProduct.map_tmul, map_one,
                  AlgHom.id_apply] using hψ
        _ = (Algebra.TensorProduct.map fkm (AlgHom.id R D))
              (φₖ (ψₖ (1 ⊗ₜ[R] d))) := by
                simpa only [AlgHom.comp_apply,
                  AlgHom.restrictScalars_apply] using hφ
    apply (Algebra.TensorProduct.comm R (F.obj m) D).injective
    calc
      (Algebra.TensorProduct.comm R (F.obj m) D)
          (φₘ (ψₘ (1 ⊗ₜ[R] d))) =
        (Algebra.TensorProduct.comm R (F.obj m) D)
          ((Algebra.TensorProduct.map fkm (AlgHom.id R D))
            (φₖ (ψₖ (1 ⊗ₜ[R] d)))) := congrArg _ hstage
      _ = (Algebra.TensorProduct.map (AlgHom.id D D) fkm)
            ((Algebra.TensorProduct.comm R (F.obj k) D)
              (φₖ (ψₖ (1 ⊗ₜ[R] d)))) :=
        Algebra.TensorProduct.comm_comp_map_apply fkm (AlgHom.id R D) _
      _ = (d ⊗ₜ[R] (1 : F.obj m) : D ⊗[R] F.obj m) := hcoord'
      _ = (Algebra.TensorProduct.comm R (F.obj m) D)
            (1 ⊗ₜ[R] d) := by simp
  let eₘ : (F.obj m ⊗[R] B) ≃ₐ[F.obj m] (F.obj m ⊗[R] D) :=
    AlgEquiv.ofAlgHom φₘ ψₘ hright hleft
  refine ⟨m, eₘ, ?_, ?_⟩
  · apply Algebra.TensorProduct.ext
    · ext x
      convert (e.commutes
        (CommRingCat.toAlgHom (c.ι.app m) x)).symm using 1 <;>
        simp [eₘ, φₘ, filteredTensorToColimitAlgHom,
          Algebra.TensorProduct.algebraMap_apply, Algebra.smul_def]
    · ext b
      have hnat := congrArg (fun h ↦ h (fₖ b)) hcTensorD
      have hφ := congrArg (fun h ↦ h (1 ⊗ₜ[R] b)) hφₖ
      calc
        filteredTensorToColimitAlgHom c m
              (eₘ (1 ⊗ₜ[R] b)) =
            filteredTensorToColimitAlgHom c k (fₖ b) := by
              simpa [eₘ, φₘ, fₘ] using hnat
        _ = filteredTensorToColimitAlgHom c k
              (φₖ (1 ⊗ₜ[R] b)) := by simp [φₖ]
        _ = e (filteredTensorToColimitAlgHom c k
              (1 ⊗ₜ[R] b)) := by
                convert hφ using 1 <;> rfl
        _ = e (filteredTensorToColimitAlgHom c m
              (1 ⊗ₜ[R] b)) := by
                simp [filteredTensorToColimitAlgHom]
  · apply Algebra.TensorProduct.ext
    · ext x
      convert (e.symm.commutes
        (CommRingCat.toAlgHom (c.ι.app m) x)).symm using 1 <;>
        simp [eₘ, ψₘ, filteredTensorToColimitAlgHom,
          Algebra.TensorProduct.algebraMap_apply, Algebra.smul_def]
    · ext d
      have hnat := congrArg (fun h ↦ h (gₖ d)) hcTensorB
      have hψ := congrArg (fun h ↦ h (1 ⊗ₜ[R] d)) hψₖ
      calc
        filteredTensorToColimitAlgHom c m
              (eₘ.symm (1 ⊗ₜ[R] d)) =
            filteredTensorToColimitAlgHom c k (gₖ d) := by
              simpa [eₘ, ψₘ, gₘ] using hnat
        _ = filteredTensorToColimitAlgHom c k
              (ψₖ (1 ⊗ₜ[R] d)) := by simp [ψₖ]
        _ = e.symm (filteredTensorToColimitAlgHom c k
              (1 ⊗ₜ[R] d)) := by
                convert hψ using 1 <;> rfl
        _ = e.symm (filteredTensorToColimitAlgHom c m
              (1 ⊗ₜ[R] d)) := by
                simp [filteredTensorToColimitAlgHom]

/-- A finite family of equalities after tensor passage to the filtered
colimit holds after one common stage transition. The auxiliary source is a
polynomial algebra in finitely many variables over the fixed tensor factor;
no finite presentation of that fixed factor over the original base is used. -/
theorem exists_tensorProduct_family_eq_stage_of_filteredColimit
    {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
    {J : Type u} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ Under (CommRingCat.of R))
    (c : Cocone F) (hc : IsColimit c) (k : J)
    {ι : Type*} [Finite ι] (x y : ι → (F.obj k ⊗[R] B))
    (hxy : ∀ a, filteredTensorToColimitAlgHom c k (x a) =
      filteredTensorToColimitAlgHom c k (y a)) :
    ∃ (l : J) (u : k ⟶ l), ∀ a,
      Algebra.TensorProduct.map (CommRingCat.toAlgHom (F.map u)) (AlgHom.id R B) (x a) =
        Algebra.TensorProduct.map (CommRingCat.toAlgHom (F.map u)) (AlgHom.id R B) (y a) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let enum : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let f : MvPolynomial (Fin (Fintype.card ι)) B →ₐ[B] (B ⊗[R] F.obj k) :=
    MvPolynomial.aeval (fun a => Algebra.TensorProduct.comm R (F.obj k) B (x (enum a)))
  let g : MvPolynomial (Fin (Fintype.card ι)) B →ₐ[B] (B ⊗[R] F.obj k) :=
    MvPolynomial.aeval (fun a => Algebra.TensorProduct.comm R (F.obj k) B (y (enum a)))
  have hfg : (filteredBaseChangeCoconeLegAlgHom c k (A := B)).comp f =
      (filteredBaseChangeCoconeLegAlgHom c k (A := B)).comp g := by
    apply MvPolynomial.algHom_ext
    intro a
    simp only [AlgHom.comp_apply, f, g, MvPolynomial.aeval_X]
    rw [filteredBaseChangeCoconeLegAlgHom_comm, filteredBaseChangeCoconeLegAlgHom_comm,
      hxy (enum a)]
  obtain ⟨l, u, hu⟩ := exists_baseChange_algHom_eq_stage F c hc k f g hfg
  refine ⟨l, u, ?_⟩
  intro a
  have hcoord := congrArg (fun h => h.right (MvPolynomial.X (enum.symm a))) hu
  change Algebra.TensorProduct.map (AlgHom.id B B) (CommRingCat.toAlgHom (F.map u))
      (f (MvPolynomial.X (enum.symm a))) =
    Algebra.TensorProduct.map (AlgHom.id B B) (CommRingCat.toAlgHom (F.map u))
      (g (MvPolynomial.X (enum.symm a))) at hcoord
  simp only [f, g, MvPolynomial.aeval_X, enum.apply_symm_apply] at hcoord
  apply (Algebra.TensorProduct.comm R (F.obj l) B).injective
  rw [Algebra.TensorProduct.comm_comp_map_apply, Algebra.TensorProduct.comm_comp_map_apply]
  exact hcoord

end EtaleFundamentalGroups

end
