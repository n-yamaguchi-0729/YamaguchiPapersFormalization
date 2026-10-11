/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.FiniteGaloisTrivialInertiaEtale
import EtaleFundamentalGroups.Normalization.GenericExtensionFiber
import EtaleFundamentalGroups.Normalization.GenericNormalizationChartAction
import EtaleFundamentalGroups.Normalization.UnramifiedGeometricInertia
import EtaleFundamentalGroups.Inertia.AffineGeometricPoint
import EtaleFundamentalGroups.Inertia.OriginalNormalizationInertiaAction
import SchemeTheory.Morphisms.ResiduePointFixedness
import SchemeTheory.Normalization.FiniteSeparable
import SchemeTheory.Normalization.Normal
import Mathlib.AlgebraicGeometry.Morphisms.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.CategoryTheory.MorphismProperty.Basic
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.Algebra.Group.Subgroup.Lattice

/-!
# Original affine inertia criterion for the actual global normalization

The actual genericNormalizationChart pullback identifies etaleness of the
global normalization with etaleness of its literal integral-closure charts.
For a finite Galois field extension, the proved affine inertia criterion
therefore identifies global etaleness with trivial original ideal inertia
at every prime on every nonempty affine chart. No scheme/affine comparison
is assumed and no Noetherian hypothesis is added. The final theorem uses
proved chart equivariance and residue-field naturality to identify this with
the original global fixed-point and trivial-residue-action condition.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace EtaleFundamentalGroups

universe u

private local instance fieldSpecQuasiCompact
    {K : Type u} [Field K] {S : Scheme.{u}} (f : Spec (.of K) ⟶ S) :
    QuasiCompact f where
  isCompact_preimage U _ _ := (Set.toFinite (f ⁻¹' U)).isCompact

/-- Etaleness of the actual global normalization is equivalent to
etaleness of its original integral closures on all nonempty affine charts. -/
theorem etale_genericNormalization_iff_affineIntegralClosure_etale
    (X : Scheme.{u}) [IsIntegral X]
    (L : Type u) [Field L] [Algebra X.functionField L] :
    Etale (X.genericExtensionMorphism L).fromNormalization ↔
      ∀ (U : X.affineOpens) [Nonempty U.1],
        let : Algebra Γ(X, U.1) L := X.affineExtensionAlgebra U.1 L
        Algebra.Etale Γ(X, U.1) (integralClosure Γ(X, U.1) L) := by
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
  have hBase : MorphismProperty.IsStableUnderBaseChange
      (@Etale : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.isStableUnderBaseChange
      (P := (@Etale : MorphismProperty Scheme.{u})) RingHom.Etale.isStableUnderBaseChange
  constructor
  · intro hEtale U hNonempty actualAlgebra
    have hSpec : Etale (Spec.map (CommRingCat.ofHom
        (algebraMap Γ(X, U.1) (integralClosure Γ(X, U.1) L)))) :=
      MorphismProperty.of_isPullback (P := (@Etale : MorphismProperty Scheme.{u}))
        (isPullback_genericNormalizationChart X L U.1 U.2).flip hEtale
    exact RingHom.etale_algebraMap.mp
      ((HasRingHomProperty.Spec_iff (P := (@Etale : MorphismProperty Scheme.{u}))).mp hSpec)
  · intro hlocal
    let F := (X.genericExtensionMorphism L).fromNormalization
    apply IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict
      (P := (@Etale : MorphismProperty Scheme.{u})) (f := F)
    intro x
    obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset
      (X := X) (U := ⊤) (x := x) (by trivial)
    have : Nonempty U := ⟨⟨x, hxU⟩⟩
    let : Algebra Γ(X, U) L := X.affineExtensionAlgebra U L
    have hSpec : Etale (Spec.map (CommRingCat.ofHom
        (algebraMap Γ(X, U) (integralClosure Γ(X, U) L)))) :=
      (HasRingHomProperty.Spec_iff (P := (@Etale : MorphismProperty Scheme.{u}))).mpr
        (RingHom.etale_algebraMap.mpr (hlocal ⟨U, hU⟩))
    have H := (isPullback_genericNormalizationChart X L U hU).flip
    have hcomp : Etale (H.isoPullback.hom ≫ pullback.snd F hU.fromSpec) := by
      rw [H.isoPullback_hom_snd]
      exact hSpec
    have hpull : Etale (pullback.snd F hU.fromSpec) :=
      (MorphismProperty.cancel_left_of_respectsIso
        (@Etale : MorphismProperty Scheme.{u}) H.isoPullback.hom
        (pullback.snd F hU.fromSpec)).mp hcomp
    have hrestrict : Etale (F ∣_ U) := by
      have h := (MorphismProperty.arrow_mk_iso_iff (P := (@Etale : MorphismProperty Scheme.{u}))
        (morphismRestrictOpensRange F hU.fromSpec)).mpr hpull
      exact (congrArg (fun V : X.Opens => Etale (F ∣_ V))
        hU.opensRange_fromSpec).mp h
    exact ⟨U, hxU, hrestrict⟩

/-- For the original finite Galois function-field extension of an integral
normal scheme, global etaleness of the literal normalization is equivalent
to trivial original inertia at every prime in every nonempty affine chart. -/
theorem etale_genericNormalization_iff_all_affine_inertia_eq_bot
    (X : Scheme.{u}) [IsIntegral X] [IsNormalIntegral X]
    (L : Type u) [Field L] [Algebra X.functionField L]
    [FiniteDimensional X.functionField L] [IsGalois X.functionField L] :
    Etale (X.genericExtensionMorphism L).fromNormalization ↔
      ∀ (U : X.affineOpens) [Nonempty U.1],
        let : Algebra Γ(X, U.1) L := X.affineExtensionAlgebra U.1 L
        let : IsFractionRing Γ(X, U.1) X.functionField :=
          functionField_isFractionRing_of_isAffineOpen X U.1 U.2
        let : IsScalarTower Γ(X, U.1) X.functionField L :=
          IsScalarTower.of_algebraMap_eq' rfl
        let : MulSemiringAction Gal(L/X.functionField) (integralClosure Γ(X, U.1) L) :=
          IsIntegralClosure.MulSemiringAction Γ(X, U.1) X.functionField L
            (integralClosure Γ(X, U.1) L)
        ∀ (Q : Ideal (integralClosure Γ(X, U.1) L)) [Q.IsPrime],
          Q.inertia Gal(L/X.functionField) = ⊥ := by
  apply (etale_genericNormalization_iff_affineIntegralClosure_etale X L).trans
  constructor
  · intro hlocal U hNonempty actualAlgebra actualFraction actualTower actualAction
    have : IsIntegrallyClosed Γ(X, U.1) :=
      IsNormalIntegral.affine_isIntegrallyClosed U.1 U.2
    exact (Inertia.integralClosure_etale_iff_all_inertia_eq_bot
      Γ(X, U.1) X.functionField L).mp (hlocal U)
  · intro hI U hNonempty actualAlgebra
    have : IsIntegrallyClosed Γ(X, U.1) :=
      IsNormalIntegral.affine_isIntegrallyClosed U.1 U.2
    have : IsFractionRing Γ(X, U.1) X.functionField :=
      functionField_isFractionRing_of_isAffineOpen X U.1 U.2
    have : IsScalarTower Γ(X, U.1) X.functionField L :=
      IsScalarTower.of_algebraMap_eq' rfl
    exact (Inertia.integralClosure_etale_iff_all_inertia_eq_bot
      Γ(X, U.1) X.functionField L).mpr (hI U)

/-- For the original finite Galois function-field extension, the literal
global normalization is etale exactly when every original automorphism
fixing a normalization point and acting trivially on its residue field is
identity. This is the equivalence of (3) and (9) in Stacks Tag 0BTF. -/
theorem etale_genericNormalization_iff_trivial_point_residue_inertia
    (X : Scheme.{u}) [IsIntegral X] [IsNormalIntegral X]
    (L : Type u) [Field L] [Algebra X.functionField L]
    [FiniteDimensional X.functionField L] [IsGalois X.functionField L] :
    Etale (X.genericExtensionMorphism L).fromNormalization ↔
      ∀ (σ : L ≃ₐ[X.functionField] L)
        (y : (X.genericExtensionMorphism L).normalization)
        (hy : Inertia.normalizationEndomorphism (X.genericExtensionMorphism L)
          (Spec.map (CommRingCat.ofHom σ.toRingHom))
          (genericExtensionMorphism_specMap_algEquiv X L σ) y = y),
        (Inertia.normalizationEndomorphism (X.genericExtensionMorphism L)
            (Spec.map (CommRingCat.ofHom σ.toRingHom))
            (genericExtensionMorphism_specMap_algEquiv X L σ)).residueFieldMap y =
          ((X.genericExtensionMorphism L).normalization.residueFieldCongr hy).hom → σ = 1 := by
  constructor
  · intro hEtale σ y hy hres
    have : Etale (X.genericExtensionMorphism L).fromNormalization := hEtale
    exact genericNormalization_automorphism_eq_one_of_trivial_residue X L
      ⟨inferInstance, inferInstance⟩ σ y hy hres
  · intro hI
    apply (etale_genericNormalization_iff_all_affine_inertia_eq_bot X L).mpr
    intro U hNonempty actualAlgebra actualFraction actualTower actualAction Q hQ
    apply (Subgroup.eq_bot_iff_forall (Q.inertia Gal(L/X.functionField))).mpr
    intro σ hσ
    let B := integralClosure Γ(X, U.1) L
    let f : Spec (.of L) ⟶ X := X.genericExtensionMorphism L
    let c : Spec (.of B) ⟶ f.normalization := genericNormalizationChart X L U.1 U.2
    let e : f.normalization ⟶ f.normalization :=
      Inertia.normalizationEndomorphism f (Spec.map (CommRingCat.ofHom σ.toRingHom))
        (genericExtensionMorphism_specMap_algEquiv X L σ)
    let φ : B →+* Q.ResidueField := algebraMap B Q.ResidueField
    let z₀ : Spec (.of Q.ResidueField) ⟶ Spec (.of B) := Spec.map (CommRingCat.ofHom φ)
    let z : Spec (.of Q.ResidueField) ⟶ f.normalization := z₀ ≫ c
    have hker : RingHom.ker φ = Q := Ideal.ker_algebraMap_residueField Q
    have hσker : σ ∈ (RingHom.ker φ).inertia Gal(L/X.functionField) := by
      rw [hker]
      exact hσ
    have hfix : z₀ ≫ Spec.map (CommRingCat.ofHom
        (MulSemiringAction.toRingHom Gal(L/X.functionField) B σ)) = z₀ :=
      (Inertia.mem_idealInertia_iff_fixes_affineGeometricPoint
        Gal(L/X.functionField) φ σ).mp hσker
    have haction : MulSemiringAction.toRingHom Gal(L/X.functionField) B σ =
        (σ.restrictScalars Γ(X, U.1)).mapIntegralClosure.toRingHom :=
      (Inertia.normalizationGaloisRingHom_eq_original Γ(X, U.1) X.functionField L σ).symm
    rw [haction] at hfix
    have hchart : Spec.map (CommRingCat.ofHom
        (σ.restrictScalars Γ(X, U.1)).mapIntegralClosure.toRingHom) ≫ c = c ≫ e :=
      genericNormalizationChart_endomorphism X L U.1 U.2 σ
    have hz : z ≫ e = z := by
      change (z₀ ≫ c) ≫ e = z₀ ≫ c
      rw [Category.assoc, ← hchart, ← Category.assoc, hfix]
    let t : Spec (.of Q.ResidueField) := IsLocalRing.closedPoint Q.ResidueField
    obtain ⟨hy, hres⟩ := Scheme.Hom.residueFieldMap_eq_of_comp_eq_self e z hz t
    exact hI σ (z t) hy hres

end EtaleFundamentalGroups
