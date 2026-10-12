/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.GeometricFiber.GenericPointEssentialImage
import Nyll.EtaleFundamentalGroups.Inertia.NormalSubgroupEmbeddings
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.RingTheory.Etale.Field
import Nyll.SchemeTheory.Pi1.FiniteEtale.Basic

/-!
# Finite subfields fixed by the generic Galois kernel

A finite subfield of the separable closure is fixed by the generic kernel
exactly when its spectrum occurs as the generic fiber of a finite étale cover.
The comparison uses the literal spectrum and postcomposition of field embeddings.
-/

noncomputable section

open CategoryTheory CategoryTheory.PreGaloisCategory
open scoped FintypeCatDiscrete

namespace AlgebraicGeometry.FiniteEtale

universe u

private def finiteSubfieldCover (K : Type u) [Field K]
    (L : IntermediateField K (SeparableClosure K)) [FiniteDimensional K L] :
    FiniteEtale (Spec (.of K)) := by
  let : Algebra.Etale K L :=
    ⟨Algebra.FormallyEtale.of_isSeparable K L,
      Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩
  let : IsFiniteEtale (ξ K L) := by
    rw [IsFiniteEtale.SpecMap_iff, CommRingCat.hom_ofHom,
      RingHom.finiteEtale_algebraMap_iff]
    exact ⟨⟩
  exact FiniteEtale.mk (ξ K L)

private def subfieldPointEquiv (K : Type u) [Field K]
    (L : IntermediateField K (SeparableClosure K)) [FiniteDimensional K L] :
    (Over.mk (ξ K (SeparableClosure K)) ⟶ (finiteSubfieldCover K L).toComma) ≃
      (L →ₐ[K] SeparableClosure K) :=
  ({ toFun := fun x ↦ ⟨x.left, x.w⟩
     invFun := fun x ↦ Over.homMk x.val x.property
     left_inv := fun _ ↦ Over.OverMorphism.ext rfl
     right_inv := fun _ ↦ Subtype.ext rfl } :
    (Over.mk (ξ K (SeparableClosure K)) ⟶ (finiteSubfieldCover K L).toComma) ≃
      {f : Spec (.of (SeparableClosure K)) ⟶ Spec (.of L) //
        f ≫ Spec.algebraMap K L = Spec.algebraMap K (SeparableClosure K)}).trans
    Spec.homEquivAlgHom

private theorem subfieldPointEquiv_smul (K : Type u) [Field K]
    (L : IntermediateField K (SeparableClosure K)) [FiniteDimensional K L]
    (g : SeparableClosure K ≃ₐ[K] SeparableClosure K)
    (x : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K (SeparableClosure K)))) ⟶
      (finiteSubfieldCover K L).toComma) :
    subfieldPointEquiv K L (g • x) = g.toAlgHom.comp (subfieldPointEquiv K L x) := by
  let y : Spec (.of (SeparableClosure K)) ⟶ Spec (.of L) := x.left
  apply AlgHom.coe_ringHom_injective
  change (Spec.preimage
    (Spec.map (CommRingCat.ofHom g.toRingHom) ≫ y)).hom =
      g.toRingHom.comp (Spec.preimage y).hom
  rw [Spec.preimage_comp, Spec.preimage_map]
  rfl

private theorem subfieldAction_ker_iff (K : Type u) [Field K]
    (L : IntermediateField K (SeparableClosure K)) [FiniteDimensional K L]
    (g : SeparableClosure K ≃ₐ[K] SeparableClosure K) :
    g ∈ (Action.ρAut
      (((equivContAction K (SeparableClosure K)).functor.obj
        (finiteSubfieldCover K L)).obj)).ker ↔
      ∀ φ : L →ₐ[K] SeparableClosure K, g.toAlgHom.comp φ = φ := by
  let W := finiteSubfieldCover K L
  let e := (fiberObjEquivHom (ξ K (SeparableClosure K)) W).trans
    (subfieldPointEquiv K L)
  have he (x : (fib K (SeparableClosure K)).obj W) :
      e (g • x) = g.toAlgHom.comp (e x) := by
    change subfieldPointEquiv K L (fiberObjEquivHom (ξ K (SeparableClosure K)) W
      (g • x)) = _
    rw [algEquiv_smul_fiber_def, Equiv.apply_symm_apply]
    exact subfieldPointEquiv_smul K L g _
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

private theorem subfieldCover_essImage_iff (X : Scheme.{u})
    [IsIntegral X] [IsNormalIntegral X]
    (L : IntermediateField X.functionField (SeparableClosure X.functionField))
    [FiniteDimensional X.functionField L] :
    (pullback (X.fromSpecStalk (genericPoint X))).essImage
      (finiteSubfieldCover X.functionField L) ↔
        (genericAbsoluteGaloisHom X).toMonoidHom.ker ≤ L.fixingSubgroup := by
  rw [genericPullback_obj_essImage_iff_ker_le_ker_ρAut]
  rw [← EtaleFundamentalGroups.normalSubgroup_fixes_embeddings_iff_le_fixingSubgroup]
  constructor
  · intro h g hg
    exact (subfieldAction_ker_iff X.functionField L g).mp (h hg)
  · intro h g hg
    exact (subfieldAction_ker_iff X.functionField L g).mpr (h g hg)

/-- A finite intermediate field is fixed by the generic Galois kernel
exactly when its literal spectrum is the generic fiber of a finite étale
cover. The cover and its generic-fiber isomorphism are actually constructed. -/
theorem genericKernel_le_fixingSubgroup_iff_exists_finiteEtale_genericFiber
    (X : Scheme.{u}) [IsIntegral X] [IsNormalIntegral X]
    (L : IntermediateField X.functionField (SeparableClosure X.functionField))
    [FiniteDimensional X.functionField L] :
    (genericAbsoluteGaloisHom X).toMonoidHom.ker ≤ L.fixingSubgroup ↔
      ∃ (Y : Scheme.{u}) (f : Y ⟶ X), IsFinite f ∧ Etale f ∧
        ∃ e : Limits.pullback f (X.fromSpecStalk (genericPoint X)) ≅ Spec (.of L),
          e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap X.functionField L)) =
            Limits.pullback.snd f (X.fromSpecStalk (genericPoint X)) := by
  rw [← subfieldCover_essImage_iff X L]
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
