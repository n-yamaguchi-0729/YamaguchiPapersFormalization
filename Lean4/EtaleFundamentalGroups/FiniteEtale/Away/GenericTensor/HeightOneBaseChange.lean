/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.FiniteEtale.Away.GenericTensor.HeightOne
import EtaleFundamentalGroups.Kummer.GenericTensor.IntegralClosure.Product

/-!
# Away height-one points after changing the base ring

Let `A → C` be finite etale away from `f`, and let a normal domain `D`
carry an `A`-algebra structure.  At a prime of `D` disjoint from the image
of `f`, the original away algebra base-changes directly to the local ring
`D_q`.  Consequently every fixed component of the corresponding generic
tensor product has etale local normalization.  The result is returned in
the localized-normalization form consumed by height-two purity.

This avoids introducing a generally nonexistent literal finite-etale
algebra over the whole full root cover.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups

universe uA uC uD uF uE uK

/-- The height-one away input for purity after an arbitrary normal base
change `A → D`.

The finite-etale algebra is only required on the original open `A[1/f]`.
Disjointness constructs the unit in `D_q`; the local finite-etale
normalization and the canonical localization comparison are then produced
internally while preserving the specified tensor component `m`. -/
theorem
    localization_integralClosure_genericTensorFieldComponent_etale_of_base_away
    {A : Type uA} {C : Type uC} {D : Type uD}
    {F : Type uF} {E : Type uE} {K : Type uK}
    [CommRing A] [IsDomain A]
    [CommRing C] [IsDomain C] [Algebra A C] [FaithfulSMul A C]
    (f : A)
    [Algebra (Localization.Away f)
      (Localization.Away (algebraMap A C f))]
    [Module.Finite (Localization.Away f)
      (Localization.Away (algebraMap A C f))]
    [Algebra.Etale (Localization.Away f)
      (Localization.Away (algebraMap A C f))]
    [Field F] [Algebra (Localization.Away f) F]
    [IsFractionRing (Localization.Away f) F]
    [Algebra A F] [IsScalarTower A (Localization.Away f) F]
    [Field E] [Algebra (Localization.Away (algebraMap A C f)) E]
    [IsFractionRing (Localization.Away (algebraMap A C f)) E]
    [Algebra (Localization.Away f) E]
    [IsScalarTower (Localization.Away f)
      (Localization.Away (algebraMap A C f)) E]
    [Algebra F E] [IsScalarTower (Localization.Away f) F E]
    [CommRing D] [IsDomain D] [IsIntegrallyClosed D] [Algebra A D]
    [Field K] [Algebra D K] [IsFractionRing D K]
    [Algebra A K] [IsScalarTower A D K]
    [Algebra F K] [IsScalarTower A F K]
    (q : Ideal D) [q.IsPrime]
    (hdisj : Disjoint
      ((Submonoid.powers (algebraMap A D f) : Submonoid D) : Set D)
      (q : Set D)) :
    ∀ (m : Ideal (K ⊗[F] E)), [m.IsMaximal] →
      let M := GenericTensorFieldComponent m
      letI : Algebra D M :=
        genericTensorFieldComponentLeftScalarAlgebra (R := D) m
      letI : SMul D M :=
        (genericTensorFieldComponentLeftScalarAlgebra (R := D) m).toSMul
      letI : IsScalarTower D K M :=
        IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
      let canonicalBM : Algebra (Localization.AtPrime q) M :=
        localizationAtPrimeToExtensionAlgebra (K := K) (L := M) q
      letI : Algebra (Localization.AtPrime q) M := canonicalBM
      letI : SMul (Localization.AtPrime q) M := canonicalBM.toSMul
      letI := localizationAtPrimeToExtension_isScalarTower
        (K := K) (L := M) q
      letI := integralClosureLocalizationAlgebra (L := M) q
      Algebra.Etale (Localization.AtPrime q)
        (Localization (Algebra.algebraMapSubmonoid
          (integralClosure D M) q.primeCompl)) := by
  classical
  let B := Localization.AtPrime q
  let : IsScalarTower A D B := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    rfl
  let : Algebra B K :=
    localizationAtPrimeToFractionFieldAlgebra (K := K) q
  let : IsScalarTower D B K :=
    localizationAtPrimeToFractionField_isScalarTower (K := K) q
  let : IsFractionRing B K :=
    localizationAtPrimeToFractionField_isFractionRing (K := K) q
  let : IsIntegrallyClosed B :=
    isIntegrallyClosed_of_isLocalization B q.primeCompl
      q.primeCompl_le_nonZeroDivisors
  let : IsScalarTower A B K := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    calc
      algebraMap A K x = algebraMap D K (algebraMap A D x) :=
        IsScalarTower.algebraMap_apply A D K x
      _ = algebraMap B K (algebraMap D B (algebraMap A D x)) :=
        IsScalarTower.algebraMap_apply D B K (algebraMap A D x)
      _ = algebraMap B K (algebraMap A B x) := rfl
  have hf : IsUnit (algebraMap A B f) := by
    change IsUnit (algebraMap D B (algebraMap A D f))
    exact isUnit_localizationAtPrime_of_disjoint_powers
      (algebraMap A D f) q hdisj
  intro m _
  let M := GenericTensorFieldComponent m
  have hlocalOld :=
    integralClosure_genericTensorFieldComponent_etale_of_away_isUnit
      (R := A) (C := C) (B := B) (F := F) (E := E) (K := K)
      f hf m
  let : Algebra D M :=
    genericTensorFieldComponentLeftScalarAlgebra (R := D) m
  let : SMul D M :=
    (genericTensorFieldComponentLeftScalarAlgebra (R := D) m).toSMul
  let : IsScalarTower D K M :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let quotientPrimeComponentAlgebra : Algebra B M :=
    Ideal.instAlgebraQuotient B m
  let canonicalPrimeComponentAlgebra : Algebra B M :=
    localizationAtPrimeToExtensionAlgebra (K := K) (L := M) q
  have hAlgebra : quotientPrimeComponentAlgebra =
      canonicalPrimeComponentAlgebra := by
    apply Algebra.algebra_ext
    intro z
    rfl
  have hlocalCanonical :
      @Algebra.Etale B
        (@integralClosure B M _ _ canonicalPrimeComponentAlgebra)
        _ _
        (@integralClosure B M _ _ canonicalPrimeComponentAlgebra).algebra := by
    exact hAlgebra ▸ hlocalOld
  let : Algebra B M := canonicalPrimeComponentAlgebra
  let : SMul B M := canonicalPrimeComponentAlgebra.toSMul
  let : IsScalarTower B K M :=
    localizationAtPrimeToFractionFieldToExtension_isScalarTower
      (K := K) (L := M) q
  let : IsScalarTower D B M :=
    localizationAtPrimeToExtension_isScalarTower
      (K := K) (L := M) q
  let := integralClosureLocalizationAlgebra (L := M) q
  exact localization_integralClosure_etale_of_local_integralClosure_etale
    (A := D) (K := K) (L := M) q hlocalCanonical

end EtaleFundamentalGroups

end
