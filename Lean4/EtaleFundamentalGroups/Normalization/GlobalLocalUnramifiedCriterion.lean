/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Normalization.LocalUnramifiedCriterion
import EtaleFundamentalGroups.Normalization.GenericExtensionFiber
import SchemeTheory.Affine.ChartStalkLocalization
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-!
# The global local-ring criterion for unramified normalization

The actual affine normalization square and the affine-chart stalk
isomorphism identify each base-prime localization with the literal pullback
over the original scheme stalk. The non-Noetherian ring criterion then
supplies étaleness on every affine open, hence globally.

This proves the original implication `(5) ⇒ (4)` in Stacks Project Tag 0BTF
for an arbitrary finite function-field extension.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace EtaleFundamentalGroups

open scoped TensorProduct

universe u

private local instance fieldSpecQuasiCompact
    {K : Type u} [Field K] {S : Scheme.{u}} (f : Spec (.of K) ⟶ S) :
    QuasiCompact f where
  isCompact_preimage U _ _ := (Set.toFinite (f ⁻¹' U)).isCompact

private theorem localized_normalizationChart_unramified_of_stalk
    (X : Scheme.{u}) [IsIntegral X]
    (L : Type u) [Field L] [Algebra X.functionField L]
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U]
    (p : PrimeSpectrum Γ(X, U))
    (hlocal : FormallyUnramified (pullback.snd
        (X.genericExtensionMorphism L).fromNormalization
        (X.fromSpecStalk (hU.fromSpec p))) ∧
      LocallyOfFiniteType (pullback.snd
        (X.genericExtensionMorphism L).fromNormalization
        (X.fromSpecStalk (hU.fromSpec p)))) :
    let : Algebra Γ(X, U) L := X.affineExtensionAlgebra U L
    Algebra.FiniteType (Localization.AtPrime p.asIdeal)
        (Localization.AtPrime p.asIdeal ⊗[Γ(X, U)] integralClosure Γ(X, U) L) ∧
      Algebra.FormallyUnramified (Localization.AtPrime p.asIdeal)
        (Localization.AtPrime p.asIdeal ⊗[Γ(X, U)] integralClosure Γ(X, U) L) := by
  intro actualAlgebra
  let R := Γ(X, U)
  let B := integralClosure R L
  let Rp := Localization.AtPrime p.asIdeal
  let BP := Rp ⊗[R] B
  let f := (X.genericExtensionMorphism L).fromNormalization
  let b := X.fromSpecStalk (hU.fromSpec p)
  let a := Spec.map (hU.stalkIsoLocalization p).hom
  let v := Spec.map (CommRingCat.ofHom (algebraMap R Rp))
  let q := Spec.map (CommRingCat.ofHom (algebraMap Rp BP))
  let d := Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.includeRight : B →ₐ[R] BP).toRingHom)
  let P : MorphismProperty Scheme.{u} := @FormallyUnramified ⊓ @LocallyOfFiniteType
  have : MorphismProperty.IsStableUnderBaseChange
      (@FormallyUnramified : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.isStableUnderBaseChange
      RingHom.FormallyUnramified.isStableUnderBaseChange
  have : P.IsStableUnderBaseChange := MorphismProperty.IsStableUnderBaseChange.inf
  have : P.RespectsIso :=
    inferInstanceAs (MorphismProperty.RespectsIso
      ((@FormallyUnramified : MorphismProperty Scheme.{u}) ⊓ @LocallyOfFiniteType))
  have hbase : P (pullback.snd (pullback.snd f b) a) :=
    MorphismProperty.of_isPullback
      (IsPullback.of_hasPullback (pullback.snd f b) a) hlocal
  have hpaste : P (pullback.snd (pullback.snd f b) a) ↔
      P (pullback.snd f (a ≫ b)) := by
    rw [← pullbackLeftPullbackSndIso_hom_snd f b a]
    exact P.cancel_left_of_respectsIso (pullbackLeftPullbackSndIso f b a).hom _
  have hab : a ≫ b = v ≫ hU.fromSpec :=
    hU.SpecMap_stalkIsoLocalization_fromSpecStalk p
  have hcanonical : P (pullback.snd f (v ≫ hU.fromSpec)) := by
    rw [← hab]
    exact hpaste.mp hbase
  have htensor : IsPullback q d v
      (Spec.map (CommRingCat.ofHom (algebraMap R B))) :=
    isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct R Rp B)
  have htotal := htensor.paste_vert (isPullback_genericNormalizationChart X L U hU)
  have hq : P q := by
    rw [← htotal.flip.isoPullback_hom_snd]
    exact (P.cancel_left_of_respectsIso htotal.flip.isoPullback.hom _).mpr hcanonical
  exact ⟨RingHom.finiteType_algebraMap.mp
      ((HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp hq.2),
    RingHom.formallyUnramified_algebraMap.mp
      ((HasRingHomProperty.Spec_iff (P := @FormallyUnramified)).mp hq.1)⟩

/-- Original Tag 0BTF `(5) ⇒ (4)`: if the actual normalization becomes
unramified over every scheme local ring, it is globally finite étale.
The finite function-field extension need not be Galois or separable. -/
theorem finiteEtale_normalization_of_stalk_unramified
    (X : Scheme.{u}) [IsIntegral X] [IsNormalIntegral X]
    (L : Type u) [Field L] [Algebra X.functionField L]
    [FiniteDimensional X.functionField L]
    (hlocal : ∀ x : X,
      FormallyUnramified (pullback.snd
          (X.genericExtensionMorphism L).fromNormalization (X.fromSpecStalk x)) ∧
        LocallyOfFiniteType (pullback.snd
          (X.genericExtensionMorphism L).fromNormalization (X.fromSpecStalk x))) :
    IsFinite (X.genericExtensionMorphism L).fromNormalization ∧
      Etale (X.genericExtensionMorphism L).fromNormalization := by
  let f := (X.genericExtensionMorphism L).fromNormalization
  have hAffine : HasAffineProperty (@Etale : MorphismProperty Scheme.{u})
      (sourceAffineLocally RingHom.Etale) :=
    HasRingHomProperty.HasAffineProperty (@Etale : MorphismProperty Scheme.{u})
  have hLocal : IsZariskiLocalAtTarget (@Etale : MorphismProperty Scheme.{u}) :=
    ((HasAffineProperty.iff (P := (@Etale : MorphismProperty Scheme.{u}))
      (Q := sourceAffineLocally RingHom.Etale)).mp hAffine).1
  have hIso : MorphismProperty.RespectsIso (@Etale : MorphismProperty Scheme.{u}) := by
    have hAffineLocal := hAffine.isLocal_affineProperty
    rw [hAffine.eq_targetAffineLocally']
    infer_instance
  have hEtale : Etale f := by
    apply IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict
      (P := (@Etale : MorphismProperty Scheme.{u})) (f := f)
    intro x
    obtain ⟨U, hU, hxU, _⟩ :=
      exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤) (x := x) (by trivial)
    have : Nonempty U := ⟨⟨x, hxU⟩⟩
    let : Algebra Γ(X, U) L := X.affineExtensionAlgebra U L
    have : IsScalarTower Γ(X, U) X.functionField L :=
      IsScalarTower.of_algebraMap_eq' rfl
    have : IsIntegrallyClosed Γ(X, U) :=
      IsNormalIntegral.affine_isIntegrallyClosed U hU
    have : IsFractionRing Γ(X, U) X.functionField :=
      functionField_isFractionRing_of_isAffineOpen X U hU
    have hring : Algebra.Etale Γ(X, U) (integralClosure Γ(X, U) L) :=
      (finite_etale_normalization_of_localized_unramified Γ(X, U) X.functionField L
        (fun p => localized_normalizationChart_unramified_of_stalk X L U hU p
          (hlocal (hU.fromSpec p)))).2
    have hSpec : Etale (Spec.map (CommRingCat.ofHom
        (algebraMap Γ(X, U) (integralClosure Γ(X, U) L)))) :=
      (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
        (RingHom.etale_algebraMap.mpr hring)
    have H := (isPullback_genericNormalizationChart X L U hU).flip
    have hcomp : Etale (H.isoPullback.hom ≫ pullback.snd f hU.fromSpec) := by
      rw [H.isoPullback_hom_snd]
      exact hSpec
    have hpullback : Etale (pullback.snd f hU.fromSpec) :=
      (MorphismProperty.cancel_left_of_respectsIso
        (@Etale : MorphismProperty Scheme.{u}) H.isoPullback.hom
        (pullback.snd f hU.fromSpec)).mp hcomp
    have hrestrict : Etale (f ∣_ U) := by
      have h := (MorphismProperty.arrow_mk_iso_iff
        (P := (@Etale : MorphismProperty Scheme.{u}))
        (morphismRestrictOpensRange f hU.fromSpec)).mpr hpullback
      exact (congrArg (fun V : X.Opens => Etale (f ∣_ V)) hU.opensRange_fromSpec).mp h
    exact ⟨U, hxU, hrestrict⟩
  have : Etale f := hEtale
  exact ⟨(IsFinite.iff_isIntegralHom_and_locallyOfFiniteType f).mpr
    ⟨inferInstance, inferInstance⟩, hEtale⟩

end EtaleFundamentalGroups
