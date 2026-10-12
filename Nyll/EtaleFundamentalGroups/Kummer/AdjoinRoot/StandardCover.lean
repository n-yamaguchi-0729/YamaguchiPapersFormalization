/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.Defs
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.RingHom.Finite
import Mathlib.RingTheory.RingHom.FinitePresentation
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.RingTheory.Spectrum.Prime.Basic
import Mathlib.RingTheory.TensorProduct.Maps
import Nyll.EtaleFundamentalGroups.Kummer.AdjoinRoot.FormallyEtale
import Nyll.EtaleFundamentalGroups.Kummer.UnitAbsorption.HigherRadicalActualFactor

/-!
# The standard Kummer morphism and its étale restriction

For a positive exponent `n` invertible in `A`, the actual map
`Spec (A[X] / (X ^ n - f)) → Spec A` is finite, flat, and locally of finite
presentation, with rank `n` at every point. Its coordinate algebra is free.
The actual localization map `A_f → (A[X] / (X ^ n - f))_f` is finite étale.

The étale proof identifies the localization map itself with the scalar
extension of the root equation. The equivalence is checked on coefficients
before transporting étaleness, so it respects the specified maps of rings.

This supplies the finite-locally-free and étale-away conclusions of Stacks
Project, Example 58.31.4. The codimension-one normalization and ramification
calculations are in `ReducedBoundary`; the scheme-level tame conclusion is
not asserted here.
https://stacks.math.columbia.edu/tag/0EYF
-/

noncomputable section

namespace EtaleFundamentalGroups.Kummer

open Polynomial AlgebraicGeometry
open scoped TensorProduct

universe u

/-- Inverting the radicand in the original root algebra gives a finite
étale map from the corresponding localization of the original base. -/
theorem finite_etale_awayMap_adjoinRoot
    {A : Type u} [CommRing A] {n : ℕ} (hn : 0 < n)
    (hnUnit : IsUnit (n : A)) (f : A) :
    let B := AdjoinRoot (X ^ n - C f)
    (Localization.awayMap (algebraMap A B) f).Finite ∧
      (Localization.awayMap (algebraMap A B) f).Etale := by
  intro B
  have : Module.Finite A B := (Polynomial.monic_X_pow_sub_C f hn.ne').finite_adjoinRoot
  refine ⟨RingHom.localization_away_map_finite A B
    (Localization.Away f) (Localization.Away (algebraMap A B f))
    (algebraMap A B) f (RingHom.finite_algebraMap.mpr inferInstance), ?_⟩
  let Af := Localization.Away f
  let Bf := Localization.Away (algebraMap A B f)
  let T := Af ⊗[A] B
  let D := AdjoinRoot (X ^ n - C (algebraMap A Af f))
  let eRoot : T ≃ₐ[Af] D :=
    (adjoinRootBaseChangeAlgEquiv (S := Af) (X ^ n - C f)).trans
      (AdjoinRoot.algEquivOfEq Af _ _ (by
        rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]))
  have hformal : Algebra.FormallyEtale Af D :=
    formallyEtale_adjoinRoot_X_pow_sub_C hn
      (by simpa only [map_natCast] using hnUnit.map (algebraMap A Af))
      (IsLocalization.Away.algebraMap_isUnit f)
  have : Algebra.Etale Af D := { formallyEtale := hformal }
  have : Algebra.Etale Af T := Algebra.Etale.of_equiv eRoot.symm
  let : Algebra B T := Algebra.TensorProduct.rightAlgebra
  let eAway : T ≃ₐ[B] Bf :=
    IsLocalization.Away.tensorRightEquiv (R := A) (S := B) (r := f) (A := Af)
  have hmap : eAway.toRingHom.comp (algebraMap Af T) =
      Localization.awayMap (algebraMap A B) f := by
    apply IsLocalization.ringHom_ext (Submonoid.powers f)
    ext a
    change eAway (algebraMap A Af a ⊗ₜ[A] (1 : B)) =
      Localization.awayMap (algebraMap A B) f (algebraMap A Af a)
    rw [Algebra.TensorProduct.tmul_one_eq_one_tmul]
    change eAway (algebraMap B T (algebraMap A B a)) = _
    rw [eAway.commutes]
    change algebraMap B Bf (algebraMap A B a) =
      IsLocalization.map Bf (algebraMap A B) _ (algebraMap A Af a)
    symm
    exact IsLocalization.map_eq _ a
  rw [← hmap]
  exact RingHom.Etale.respectsIso.1 (algebraMap Af T) eAway.toRingEquiv
    (RingHom.etale_algebraMap.mpr inferInstance)

/-- The literal standard Kummer morphism is finite locally free of rank
`n`, expressed by freeness of its affine coordinate algebra and the native
finite, flat, finite-presentation, and scheme-rank predicates. Its literal
localization away from `f` is finite étale.

The ambient ring may be reducible or even the zero ring; the rank assertion
is quantified over its points. -/
theorem standardKummerCover_finiteFlat_and_etaleAway
    {A : Type u} [CommRing A] {n : ℕ} (hn : 0 < n)
    (hnUnit : IsUnit (n : A)) (f : A) :
    let B := AdjoinRoot (X ^ n - C f)
    let π := Spec.map (CommRingCat.ofHom (algebraMap A B))
    let πAway := Spec.map (CommRingCat.ofHom (Localization.awayMap (algebraMap A B) f))
    Module.Free A B ∧ IsFinite π ∧ Flat π ∧ LocallyOfFinitePresentation π ∧
      (∀ x : PrimeSpectrum A, π.finrank x = n) ∧ IsFinite πAway ∧ Etale πAway := by
  intro B π πAway
  have hmonic : (X ^ n - C f).Monic := Polynomial.monic_X_pow_sub_C f hn.ne'
  have : Module.Free A B := hmonic.free_adjoinRoot
  have : Module.Finite A B := hmonic.finite_adjoinRoot
  have hfinite : IsFinite π :=
    (IsFinite.SpecMap_iff (CommRingCat.ofHom (algebraMap A B))).mpr
      (RingHom.finite_algebraMap.mpr inferInstance)
  have hflat : Flat π := Flat.SpecMap_iff.mpr
    (RingHom.flat_algebraMap_iff.mpr inferInstance)
  have hfp : LocallyOfFinitePresentation π :=
    (LocallyOfFinitePresentation.SpecMap_iff
      (CommRingCat.ofHom (algebraMap A B))).mpr
        (RingHom.finitePresentation_algebraMap.mpr inferInstance)
  obtain ⟨hAwayFinite, hAwayEtale⟩ := finite_etale_awayMap_adjoinRoot hn hnUnit f
  refine ⟨inferInstance, hfinite, hflat, hfp, ?_, ?_, ?_⟩
  · intro x
    have : Nontrivial A := x.nontrivial
    change (Spec.map (CommRingCat.ofHom (algebraMap A B))).finrank x = n
    rw [Scheme.Hom.finrank_SpecMap_algebraMap, Module.rankAtStalk_eq_finrank_of_free]
    change Module.finrank A B = n
    rw [Module.finrank_eq_card_basis (AdjoinRoot.powerBasisAux' hmonic),
      Fintype.card_fin, Polynomial.natDegree_X_pow_sub_C]
  · exact (IsFinite.SpecMap_iff
      (CommRingCat.ofHom (Localization.awayMap (algebraMap A B) f))).mpr hAwayFinite
  · exact (HasRingHomProperty.Spec_iff (P := @Etale)).mpr hAwayEtale

end EtaleFundamentalGroups.Kummer
