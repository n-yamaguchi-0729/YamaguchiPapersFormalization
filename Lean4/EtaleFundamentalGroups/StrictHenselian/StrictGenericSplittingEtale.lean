/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.StrictHenselian.GeometricStalkTensorDescent
import EtaleFundamentalGroups.StrictHenselian.GeometricStalkFractionTensor
import EtaleFundamentalGroups.StrictHenselian.AffineNeighborhoodFaithfullyFlat
import SchemeTheory.RingTheory.DVRFractionFieldAway
import Mathlib.RingTheory.Polynomial.RationalRoot
import SchemeTheory.RingTheory.IntegralClosureEtaleOfSplit
import Mathlib.RingTheory.Localization.Away.AdjoinRoot
import Mathlib.RingTheory.TensorProduct.Pi
import Mathlib.RingTheory.FinitePresentation


/-!
# Strict generic splitting implies étale normalization

A splitting into copies of the actual fraction field of the actual geometric
stalk descends to an actual pointed affine étale neighborhood. Its sections
are faithfully flat over the original local ring. The descended splitting
and smooth base change of integral closure then prove that the original
normalization is étale. No normalization comparison for the infinite
strict-henselization map is assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct

namespace EtaleFundamentalGroups.StrictHenselian

universe u

/-- An actual strict generic splitting of a finitely presented algebra over
a DVR forces its actual integral closure to be étale over that DVR. -/
theorem integralClosure_etale_of_geometricStalk_generic_split
    {R Ω B : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field Ω] [IsSepClosed Ω] [CommRing B] [Algebra R B]
    [Algebra.FinitePresentation R B]
    (φ : R →+* Ω) [IsLocalHom φ] (ι : Type u) [Finite ι] :
    letI : Algebra R (geometricStalk (Spec.map (CommRingCat.ofHom φ))) :=
      (geometricStalkStructureMap φ).toAlgebra
    Nonempty ((geometricStalk (Spec.map (CommRingCat.ofHom φ)) ⊗[R] B) ≃ₐ[
      geometricStalk (Spec.map (CommRingCat.ofHom φ))]
      (ι → FractionRing (geometricStalk (Spec.map (CommRingCat.ofHom φ))))) →
    Algebra.Etale R (integralClosure R B) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let A := geometricStalk (Spec.map (CommRingCat.ofHom φ))
  let : Algebra R A := (geometricStalkStructureMap φ).toAlgebra
  rintro ⟨e⟩
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  let : IsLocalization.Away π (FractionRing R) :=
    SchemeTheory.isLocalizationAway_fractionField_of_isDiscreteValuationRing
      R (FractionRing R) π hπ.ne_zero hπ.not_isUnit
  let : Algebra.FinitePresentation R (FractionRing R) :=
    IsLocalization.Away.finitePresentation π
  let : Algebra.FinitePresentation R (ι → FractionRing R) :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  let eD : (A ⊗[R] (ι → FractionRing R)) ≃ₐ[A] (ι → FractionRing A) :=
    (Algebra.TensorProduct.piRight R A A (fun _ : ι => FractionRing R)).trans
      (AlgEquiv.piCongrRight (fun _ : ι => geometricStalkFractionTensorEquiv φ))
  obtain ⟨V, v, hV, heV⟩ := geometricStalk_exists_affine_tensorProduct_algEquiv
    (B := B) (D := ι → FractionRing R) φ ⟨e.trans eD.symm⟩
  let : IsAffine V.left := hV
  let S := Γ(V.left, ⊤)
  let β : R →+* S :=
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ V.hom.appTop).hom
  let : Algebra R S := β.toAlgebra
  obtain ⟨hβ, hβfaithful⟩ := affineNeighborhood_structure_etale_faithfullyFlat φ V v
  let : Algebra.Etale R S := hβ
  let : Module.FaithfullyFlat R S := hβfaithful
  obtain ⟨eV⟩ := heV
  let eSplit : (S ⊗[R] B) ≃ₐ[S] (ι → S ⊗[R] FractionRing R) :=
    eV.trans (Algebra.TensorProduct.piRight R S S (fun _ : ι => FractionRing R))
  exact SchemeTheory.integralClosure_etale_of_split_after_faithfullyFlat_etale
    R S B (S ⊗[R] FractionRing R) ι π hπ.ne_zero eSplit

/-- For an actual finite algebra over the fraction field of the DVR, finite
presentation over the original DVR is constructed by inverting a uniformizer. -/
theorem integralClosure_etale_of_finite_fractionAlgebra_geometricStalk_generic_split
    {R Ω K B : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field Ω] [IsSepClosed Ω] [Field K] [Algebra R K] [IsFractionRing R K]
    [CommRing B] [Algebra R B] [Algebra K B] [IsScalarTower R K B] [Module.Finite K B]
    (φ : R →+* Ω) [IsLocalHom φ] (ι : Type u) [Finite ι] :
    letI : Algebra R (geometricStalk (Spec.map (CommRingCat.ofHom φ))) :=
      (geometricStalkStructureMap φ).toAlgebra
    Nonempty ((geometricStalk (Spec.map (CommRingCat.ofHom φ)) ⊗[R] B) ≃ₐ[
      geometricStalk (Spec.map (CommRingCat.ofHom φ))]
      (ι → FractionRing (geometricStalk (Spec.map (CommRingCat.ofHom φ))))) →
    Algebra.Etale R (integralClosure R B) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  let : IsLocalization.Away π K :=
    SchemeTheory.isLocalizationAway_fractionField_of_isDiscreteValuationRing
      R K π hπ.ne_zero hπ.not_isUnit
  let : Algebra.FinitePresentation R K := IsLocalization.Away.finitePresentation π
  let : Algebra.FinitePresentation K B :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  let : Algebra.FinitePresentation R B := Algebra.FinitePresentation.trans R K B
  exact integralClosure_etale_of_geometricStalk_generic_split φ ι

end EtaleFundamentalGroups.StrictHenselian
