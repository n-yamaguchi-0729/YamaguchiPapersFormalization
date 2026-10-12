/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.GeometricFiber.GenericPointSurjective
import Nyll.EtaleFundamentalGroups.GeometricFiber.BasePoint
import Nyll.EtaleFundamentalGroups.GeometricFiber.FiniteGaloisSets
import Nyll.EtaleFundamentalGroups.ContinuousActions.RestrictionEssentialImage
import Nyll.EtaleFundamentalGroups.Inertia.NormalSubgroupEmbeddings
import Mathlib.CategoryTheory.EssentialImage
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.RingTheory.Etale.Field
import Nyll.SchemeTheory.Pi1.FiniteEtale.Basic

/-!
# Generic Galois maps using the supplied separable closure

The field source is a dominant preimmersion, so it is the actual generic
point, rather than a further extension of the function field. The ambient
separable closure is supplied explicitly. Finite fixed subfields are
characterized using their literal spectra and finite étale models.
-/

noncomputable section

open CategoryTheory CategoryTheory.PreGaloisCategory
open scoped FintypeCatDiscrete

namespace AlgebraicGeometry.FiniteEtale

universe u

variable (F Ω : Type u) [Field F] [Field Ω] [Algebra F Ω]
  [IsSepClosure F Ω] [IsSepClosed Ω]

/-- The canonical topological comparison for the supplied separable closure. -/
def suppliedGaloisEquivFundamentalGroup : Gal(Ω/F) ≃ₜ* Aut (fib F Ω) :=
  ContinuousMulEquiv.mk'
    (toAutHomeo (fib F Ω) Gal(Ω/F))
    (fun g h ↦ by
      simpa only [toAutHomeo_apply] using
        (toAut (fib F Ω) Gal(Ω/F)).map_mul g h)

variable {X : Scheme.{u}} [IsIntegral X]
  (j : Spec (.of F) ⟶ X)

/-- The actual map induced by the given generic-point morphism. -/
def fieldSourceAbsoluteGaloisHom : Gal(Ω/F) →ₜ* π₁ᵉᵗ(ξ F Ω ≫ j) :=
  (fundamentalGroupHom j (ξ F Ω)).comp
    (ContinuousMonoidHom.toContinuousMonoidHom
      (suppliedGaloisEquivFundamentalGroup F Ω))

/-- Dominant preimmersion of the field source supplies surjectivity. -/
theorem fieldSourceAbsoluteGaloisHom_surjective [IsNormalIntegral X]
    [IsPreimmersion j] [IsDominant j] [QuasiCompact j] :
    Function.Surjective (fieldSourceAbsoluteGaloisHom F Ω j) :=
  (fundamentalGroupHom_surjective_of_isPreimmersion_of_isDominant j (ξ F Ω)).comp
    (suppliedGaloisEquivFundamentalGroup F Ω).surjective

/-- Generic pullback agrees with restriction of the supplied Galois action. -/
def fieldSourcePullbackContActionIso :
    pullback j ⋙ (equivContAction F Ω).functor ≅
      functorToContAction (fiber (ξ F Ω ≫ j)) ⋙
        ContAction.res FintypeCat (fieldSourceAbsoluteGaloisHom F Ω j) := by
  let E := ContinuousMonoidHom.toContinuousMonoidHom
    (suppliedGaloisEquivFundamentalGroup F Ω)
  let R := ContAction.res FintypeCat E
  let G := functorToContAction (fiber (ξ F Ω ≫ j))
  let q := fundamentalGroupHom j (ξ F Ω)
  exact (Functor.associator (pullback j) (functorToContAction (fib F Ω)) R).symm.trans
    ((Functor.isoWhiskerRight (pullbackContActionIso j (ξ F Ω)) R).trans
      ((Functor.associator G (ContAction.res FintypeCat q) R).trans
        (Functor.isoWhiskerLeft G (ContAction.resComp FintypeCat E q).symm)))

/-- A finite continuous action extends to X exactly when the actual kernel acts trivially. -/
theorem fieldSourcePullback_essImage_iff_ker_le_ker_ρAut [IsNormalIntegral X]
    [IsPreimmersion j] [IsDominant j] [QuasiCompact j]
    (Y : ContAction FintypeCat.{u} Gal(Ω/F)) :
    (pullback j ⋙ (equivContAction F Ω).functor).essImage Y ↔
      (fieldSourceAbsoluteGaloisHom F Ω j).toMonoidHom.ker ≤ (Action.ρAut Y.obj).ker := by
  rw [Functor.essImage_eq_of_natIso (fieldSourcePullbackContActionIso F Ω j)]
  rw [Functor.essImage_comp_apply_of_essSurj]
  exact ContAction.essImage_res_iff_ker_le_ker_ρAut
    (fieldSourceAbsoluteGaloisHom F Ω j)
    (fieldSourceAbsoluteGaloisHom_surjective F Ω j) Y

/-- The preceding criterion on actual finite étale objects over F. -/
theorem fieldSourcePullback_obj_essImage_iff_ker_le_ker_ρAut [IsNormalIntegral X]
    [IsPreimmersion j] [IsDominant j] [QuasiCompact j]
    (W : FiniteEtale (Spec (.of F))) :
    (pullback j).essImage W ↔
      (fieldSourceAbsoluteGaloisHom F Ω j).toMonoidHom.ker ≤
        (Action.ρAut (((equivContAction F Ω).functor.obj W).obj)).ker := by
  let E := (equivContAction F Ω).functor
  rw [← fieldSourcePullback_essImage_iff_ker_le_ker_ρAut F Ω j (E.obj W)]
  constructor
  · rintro ⟨Z, ⟨e⟩⟩
    exact ⟨Z, ⟨E.mapIso e⟩⟩
  · rintro ⟨Z, ⟨e⟩⟩
    exact ⟨Z, ⟨E.preimageIso e⟩⟩

private def finiteSubfieldCover (K Ω : Type u) [Field K] [Field Ω] [Algebra K Ω]
    [IsSepClosure K Ω] [IsSepClosed Ω]
    (L : IntermediateField K Ω) [FiniteDimensional K L] :
    FiniteEtale (Spec (.of K)) := by
  let : Algebra.Etale K L :=
    ⟨Algebra.FormallyEtale.of_isSeparable K L,
      Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩
  let : IsFiniteEtale (ξ K L) := by
    rw [IsFiniteEtale.SpecMap_iff, CommRingCat.hom_ofHom,
      RingHom.finiteEtale_algebraMap_iff]
    exact ⟨⟩
  exact FiniteEtale.mk (ξ K L)

private def subfieldPointEquiv (K Ω : Type u) [Field K] [Field Ω] [Algebra K Ω]
    [IsSepClosure K Ω] [IsSepClosed Ω]
    (L : IntermediateField K Ω) [FiniteDimensional K L] :
    (Over.mk (ξ K Ω) ⟶ (finiteSubfieldCover K Ω L).toComma) ≃
      (L →ₐ[K] Ω) :=
  ({ toFun := fun x ↦ ⟨x.left, x.w⟩
     invFun := fun x ↦ Over.homMk x.val x.property
     left_inv := fun _ ↦ Over.OverMorphism.ext rfl
     right_inv := fun _ ↦ Subtype.ext rfl } :
    (Over.mk (ξ K Ω) ⟶ (finiteSubfieldCover K Ω L).toComma) ≃
      {f : Spec (.of Ω) ⟶ Spec (.of L) //
        f ≫ Spec.algebraMap K L = Spec.algebraMap K Ω}).trans
    Spec.homEquivAlgHom

private theorem subfieldPointEquiv_smul (K Ω : Type u) [Field K] [Field Ω] [Algebra K Ω]
    [IsSepClosure K Ω] [IsSepClosed Ω]
    (L : IntermediateField K Ω) [FiniteDimensional K L]
    (g : Ω ≃ₐ[K] Ω)
    (x : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) ⟶
      (finiteSubfieldCover K Ω L).toComma) :
    subfieldPointEquiv K Ω L (g • x) = g.toAlgHom.comp (subfieldPointEquiv K Ω L x) := by
  let y : Spec (.of Ω) ⟶ Spec (.of L) := x.left
  apply AlgHom.coe_ringHom_injective
  change (Spec.preimage
    (Spec.map (CommRingCat.ofHom g.toRingHom) ≫ y)).hom =
      g.toRingHom.comp (Spec.preimage y).hom
  rw [Spec.preimage_comp, Spec.preimage_map]
  rfl

private theorem subfieldAction_ker_iff (K Ω : Type u) [Field K] [Field Ω] [Algebra K Ω]
    [IsSepClosure K Ω] [IsSepClosed Ω]
    (L : IntermediateField K Ω) [FiniteDimensional K L]
    (g : Ω ≃ₐ[K] Ω) :
    g ∈ (Action.ρAut
      (((equivContAction K Ω).functor.obj
        (finiteSubfieldCover K Ω L)).obj)).ker ↔
      ∀ φ : L →ₐ[K] Ω, g.toAlgHom.comp φ = φ := by
  let W := finiteSubfieldCover K Ω L
  let e := (fiberObjEquivHom (ξ K Ω) W).trans
    (subfieldPointEquiv K Ω L)
  have he (x : (fib K Ω).obj W) :
      e (g • x) = g.toAlgHom.comp (e x) := by
    change subfieldPointEquiv K Ω L (fiberObjEquivHom (ξ K Ω) W
      (g • x)) = _
    rw [algEquiv_smul_fiber_def, Equiv.apply_symm_apply]
    exact subfieldPointEquiv_smul K Ω L g _
  constructor
  · intro h φ
    have hg := congrArg (fun a ↦ a.hom) (MonoidHom.mem_ker.mp h)
    have hx : g • e.symm φ = e.symm φ := by
      exact ConcreteCategory.congr_hom hg (e.symm φ)
    have hx' := congrArg e hx
    rw [he, Equiv.apply_symm_apply] at hx'
    exact hx'
  · intro h
    apply MonoidHom.mem_ker.mpr
    apply Iso.ext
    apply FintypeCat.hom_ext
    intro x
    change g • x = x
    apply e.injective
    exact (he x).trans (h (e x))

private theorem fieldSourceSubfieldCover_essImage_iff [IsNormalIntegral X]
    [IsPreimmersion j] [IsDominant j] [QuasiCompact j]
    (E : IntermediateField F Ω) [FiniteDimensional F E] :
    (pullback j).essImage (finiteSubfieldCover F Ω E) ↔
      (fieldSourceAbsoluteGaloisHom F Ω j).toMonoidHom.ker ≤ E.fixingSubgroup := by
  rw [fieldSourcePullback_obj_essImage_iff_ker_le_ker_ρAut F Ω j]
  rw [← EtaleFundamentalGroups.normalSubgroup_fixes_embeddings_iff_le_fixingSubgroup]
  constructor
  · intro h g hg
    exact (subfieldAction_ker_iff F Ω E g).mp (h hg)
  · intro h g hg
    exact (subfieldAction_ker_iff F Ω E g).mpr (h g hg)

/-- A literal finite subfield is fixed by the actual kernel exactly when
its spectrum is the actual generic fibre of a finite étale cover of X. -/
theorem fieldSourceKernel_le_fixingSubgroup_iff_exists_finiteEtale_genericFiber
    [IsNormalIntegral X] [IsPreimmersion j] [IsDominant j] [QuasiCompact j]
    (E : IntermediateField F Ω) [FiniteDimensional F E] :
    (fieldSourceAbsoluteGaloisHom F Ω j).toMonoidHom.ker ≤ E.fixingSubgroup ↔
      ∃ (Y : Scheme.{u}) (f : Y ⟶ X), IsFinite f ∧ Etale f ∧
        ∃ e : Limits.pullback f j ≅ Spec (.of E),
          e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap F E)) =
            Limits.pullback.snd f j := by
  rw [← fieldSourceSubfieldCover_essImage_iff F Ω j E]
  constructor
  · rintro ⟨Z, ⟨e⟩⟩
    refine ⟨Z.left, Z.hom, inferInstance, inferInstance, ?_⟩
    exact ⟨((forget _).comp (Over.forget _)).mapIso e, e.hom.w⟩
  · rintro ⟨Y, f, hFinite, hEtale, e, he⟩
    let : IsFinite f := hFinite
    let : Etale f := hEtale
    let : IsFiniteEtale f := ⟨⟩
    exact ⟨FiniteEtale.mk f, ⟨MorphismProperty.Over.isoMk e he⟩⟩

end AlgebraicGeometry.FiniteEtale
