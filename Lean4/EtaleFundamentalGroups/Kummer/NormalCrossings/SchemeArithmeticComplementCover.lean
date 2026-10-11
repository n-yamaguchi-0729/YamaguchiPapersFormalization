/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SchemeTheory.Divisors.LocalComplement
import EtaleFundamentalGroups.FiniteEtale.DominantPreimmersionPullback
import EtaleFundamentalGroups.Kummer.NormalCrossings.SchemeArithmeticChart
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Finite-etale covers on local normal-crossings complements

A finite-etale cover of the complement of a divisor support restricts to the
principal local chart supplied by a normal-crossings boundary equation.  The
resulting object has exactly the base scheme used by the local finite-quotient
inertia statement.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory EtaleFundamentalGroups TopologicalSpace
open CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry

universe u

private theorem SpecMap_genericPoint_of_injective
    {R S : CommRingCat.{u}} [IsDomain R] [IsDomain S]
    (φ : R ⟶ S) (hφ : Function.Injective φ) :
    Spec.map φ (genericPoint (Spec S)) = genericPoint (Spec R) := by
  rw [genericPoint_eq_bot_of_affine, genericPoint_eq_bot_of_affine]
  apply PrimeSpectrum.ext
  change Ideal.comap φ.hom ⊥ = ⊥
  exact Ideal.comap_bot_of_injective φ.hom hφ

private theorem Scheme.fromSpecStalk_genericPoint_eq
    {X : Scheme.{u}} [IsIntegral X] (x : X) :
    X.fromSpecStalk x (genericPoint (Spec (X.presheaf.stalk x))) =
      genericPoint X := by
  let h := genericPoint_specializes x
  let K := X.functionField
  have hK : genericPoint (Spec K) = IsLocalRing.closedPoint K := by
    apply PrimeSpectrum.ext
    rw [genericPoint_eq_bot_of_affine]
    exact IsLocalRing.maximalIdeal_eq_bot.symm
  have hmap : Spec.map (X.presheaf.stalkSpecializes h)
      (genericPoint (Spec K)) =
      genericPoint (Spec (X.presheaf.stalk x)) := by
    apply SpecMap_genericPoint_of_injective
    change Function.Injective
      (algebraMap (X.presheaf.stalk x) X.functionField)
    exact IsFractionRing.injective (X.presheaf.stalk x) X.functionField
  have hcomp := X.SpecMap_stalkSpecializes_fromSpecStalk h
  have happ := congrArg (fun g ↦ g (genericPoint (Spec K))) hcomp
  change X.fromSpecStalk x
      (Spec.map (X.presheaf.stalkSpecializes h) (genericPoint (Spec K))) =
    X.fromSpecStalk (genericPoint X) (genericPoint (Spec K)) at happ
  rw [hmap, hK, X.fromSpecStalk_closedPoint] at happ
  exact happ

namespace Scheme.IdealSheafData

variable {X : Scheme.{u}}

/-- The canonical map from an away localization of a prime-localized stalk
to an integral ambient scheme is dominant whenever the inverted element is
nonzero. -/
theorem localizationAwayToAmbient_isDominant
    [IsIntegral X] (x : X)
    (P : Ideal (X.presheaf.stalk x)) [P.IsPrime]
    (f : Localization.AtPrime P) (hf : f ≠ 0) :
    IsDominant
      (Spec.map (CommRingCat.ofHom
          (algebraMap (Localization.AtPrime P) (Localization.Away f))) ≫
        Scheme.localizationAtPrimeTo X x P) := by
  let A := X.presheaf.stalk x
  let V := Localization.AtPrime P
  let S := Localization.Away f
  let : IsDomain V := inferInstance
  let : IsDomain S := IsLocalization.Away.isDomain S hf
  have hAV : Function.Injective (algebraMap A V) :=
    IsLocalization.injective (M := P.primeCompl) V (by
      intro a ha
      change a ∉ P at ha
      exact mem_nonZeroDivisors_iff_ne_zero.mpr (by
        intro ha0
        exact ha (ha0 ▸ P.zero_mem)))
  have hVS : Function.Injective (algebraMap V S) :=
    IsLocalization.injective (M := Submonoid.powers f) S
      (Submonoid.powers_le.mpr
        (mem_nonZeroDivisors_iff_ne_zero.mpr hf))
  have hgenericVS :
      Spec.map (CommRingCat.ofHom (algebraMap V S))
          (genericPoint (Spec (.of S))) =
        genericPoint (Spec (.of V)) :=
    SpecMap_genericPoint_of_injective _ hVS
  have hgenericAV :
      Spec.map (CommRingCat.ofHom (algebraMap A V))
          (genericPoint (Spec (.of V))) =
        genericPoint (Spec A) :=
    SpecMap_genericPoint_of_injective _ hAV
  have hgeneric :
      (Spec.map (CommRingCat.ofHom (algebraMap V S)) ≫
          Scheme.localizationAtPrimeTo X x P)
        (genericPoint (Spec (.of S))) = genericPoint X := by
    change X.fromSpecStalk x
      (Spec.map (CommRingCat.ofHom (algebraMap A V))
        (Spec.map (CommRingCat.ofHom (algebraMap V S))
          (genericPoint (Spec (.of S))))) = genericPoint X
    rw [hgenericVS, hgenericAV, Scheme.fromSpecStalk_genericPoint_eq]
  constructor
  rw [DenseRange, dense_iff_closure_eq]
  apply Set.Subset.antisymm
  · exact Set.subset_univ _
  · rw [← (genericPoint_spec X).def]
    apply closure_mono
    rintro _ rfl
    exact ⟨genericPoint (Spec (.of S)), hgeneric⟩

/-- The local principal-complement map is a preimmersion. -/
theorem localizationAwayToSupportComplement_isPreimmersion
    (I : X.IdealSheafData) (x : X)
    (P : Ideal (X.presheaf.stalk x)) [P.IsPrime]
    (f : Localization.AtPrime P)
    (hboundary :
      (I.stalkIdeal x).map
          (algebraMap (X.presheaf.stalk x) (Localization.AtPrime P)) =
        Ideal.span {f}) :
    IsPreimmersion
      (localizationAwayToSupportComplement I x P f hboundary) := by
  rw [← IsPreimmersion.comp_iff
    (localizationAwayToSupportComplement I x P f hboundary)
    I.supportComplement.ι]
  rw [localizationAwayToSupportComplement_comp_ι]
  rw [Scheme.localizationAtPrimeTo]
  let : IsPreimmersion
      (Spec.map (CommRingCat.ofHom
        (algebraMap (Localization.AtPrime P) (Localization.Away f)))) :=
    IsPreimmersion.of_isLocalization
      (R := Localization.AtPrime P) (S := Localization.Away f)
      (Submonoid.powers f)
  let : IsPreimmersion
      (Spec.map (CommRingCat.ofHom
        (algebraMap (X.presheaf.stalk x) (Localization.AtPrime P)))) :=
    IsPreimmersion.of_isLocalization
      (R := X.presheaf.stalk x) (S := Localization.AtPrime P)
      P.primeCompl
  infer_instance

/-- The local principal-complement map is dominant over an integral ambient
scheme when its boundary equation is nonzero. -/
theorem localizationAwayToSupportComplement_isDominant
    [IsIntegral X]
    (I : X.IdealSheafData) (x : X)
    (P : Ideal (X.presheaf.stalk x)) [P.IsPrime]
    (f : Localization.AtPrime P) (hf : f ≠ 0)
    (hboundary :
      (I.stalkIdeal x).map
          (algebraMap (X.presheaf.stalk x) (Localization.AtPrime P)) =
        Ideal.span {f}) :
    IsDominant
      (localizationAwayToSupportComplement I x P f hboundary) := by
  let j := localizationAwayToSupportComplement I x P f hboundary
  let : IsDominant (j ≫ I.supportComplement.ι) := by
    rw [localizationAwayToSupportComplement_comp_ι]
    exact localizationAwayToAmbient_isDominant x P f hf
  exact IsDominant.of_comp_of_isOpenImmersion j I.supportComplement.ι

/-- A nonzero local boundary equation makes the global support complement
nonempty. -/
theorem supportComplement_nonempty_of_localizationAway
    [IsIntegral X]
    (I : X.IdealSheafData) (x : X)
    (P : Ideal (X.presheaf.stalk x)) [P.IsPrime]
    (f : Localization.AtPrime P) (hf : f ≠ 0)
    (hboundary :
      (I.stalkIdeal x).map
          (algebraMap (X.presheaf.stalk x) (Localization.AtPrime P)) =
        Ideal.span {f}) :
    Nonempty I.supportComplement := by
  let V := Localization.AtPrime P
  let S := Localization.Away f
  let : IsDomain V := inferInstance
  let : IsDomain S := IsLocalization.Away.isDomain S hf
  exact ⟨localizationAwayToSupportComplement I x P f hboundary
    (genericPoint (Spec (.of S)))⟩

/-- The local principal-complement map is quasi-compact over a locally
Noetherian ambient scheme. -/
theorem localizationAwayToSupportComplement_quasiCompact
    [IsLocallyNoetherian X]
    (I : X.IdealSheafData) (x : X)
    (P : Ideal (X.presheaf.stalk x)) [P.IsPrime]
    (f : Localization.AtPrime P)
    (hboundary :
      (I.stalkIdeal x).map
          (algebraMap (X.presheaf.stalk x) (Localization.AtPrime P)) =
        Ideal.span {f}) :
    QuasiCompact
      (localizationAwayToSupportComplement I x P f hboundary) := by
  infer_instance

/-- Pull a finite-etale cover of a support complement to the local chart
obtained by inverting the normal-crossings boundary product. -/
def pullbackSupportComplementCoverToBoundaryAway
    (I : X.IdealSheafData) (x : X)
    (P : PrimeSpectrum (X.presheaf.stalk x)) {r : ℕ}
    (t : Fin 2 → Localization.AtPrime P.asIdeal)
    (hboundary :
      (I.stalkIdeal x).map
          (algebraMap (X.presheaf.stalk x)
            (Localization.AtPrime P.asIdeal)) =
        Ideal.span {boundaryProduct t r})
    (W : FiniteEtale I.supportComplement) :
    FiniteEtale
      (Spec (.of (Localization.Away (boundaryProduct t r)))) :=
  (FiniteEtale.pullback
    (localizationAwayToSupportComplement I x P.asIdeal
      (boundaryProduct t r) hboundary)).obj W

private theorem boundaryProduct_ne_zero_of_splitStrictNormalCrossings
    {V : Type u} [CommRing V] [IsDomain V] [IsLocalRing V]
    {r : ℕ} {t : Fin 2 → V}
    (hNC : IsSplitStrictNormalCrossingsAt
      (boundaryProduct t r) t r) :
    boundaryProduct t r ≠ 0 := by
  apply (hNC.2.2.2.2.1.ne_zero_iff).mpr
  rw [boundaryProduct]
  exact Finset.prod_ne_zero_iff.mpr fun j hj ↦
    (hNC.2.2.2.1 j (Finset.mem_filter.mp hj).2).ne_zero

/-- Pullback along the canonical localization-away map preserves connected
Galois covers when the inverted boundary equation is nonzero. -/
theorem localizationAwayToSupportComplement_pullback_isGalois
    [IsIntegral X] [IsNormalIntegral X] [IsLocallyNoetherian X]
    (I : X.IdealSheafData) (x : X)
    (P : Ideal (X.presheaf.stalk x)) [P.IsPrime]
    (f : Localization.AtPrime P) (hf : f ≠ 0)
    (hboundary :
      (I.stalkIdeal x).map
          (algebraMap (X.presheaf.stalk x) (Localization.AtPrime P)) =
        Ideal.span {f})
    [Nonempty I.supportComplement]
    [IsDomain (Localization.Away f)]
    (W : FiniteEtale I.supportComplement) (hW : IsGalois W) :
    IsGalois ((FiniteEtale.pullback
      (localizationAwayToSupportComplement I x P f hboundary)).obj W) := by
  let V := Localization.AtPrime P
  let j := localizationAwayToSupportComplement I x P f hboundary
  let : IsDomain V := inferInstance
  let : IsIntegral I.supportComplement :=
    isIntegral_of_isOpenImmersion I.supportComplement.ι
  let : IsNormalIntegral I.supportComplement := inferInstance
  let : IsLocallyNoetherian I.supportComplement := inferInstance
  let : IsPreimmersion j :=
    localizationAwayToSupportComplement_isPreimmersion
      I x P f hboundary
  let : IsDominant j :=
    localizationAwayToSupportComplement_isDominant
      I x P f hf hboundary
  let : QuasiCompact j :=
    localizationAwayToSupportComplement_quasiCompact
      I x P f hboundary
  exact FiniteEtale.pullback_obj_isGalois_of_isPreimmersion_of_isDominant
    j W hW

/-- The nonzero local equation itself supplies the connected source and
nonempty target required by Galois pullback. -/
theorem localizationAwayToSupportComplement_pullback_isGalois_of_ne_zero
    [IsIntegral X] [IsNormalIntegral X] [IsLocallyNoetherian X]
    (I : X.IdealSheafData) (x : X)
    (P : Ideal (X.presheaf.stalk x)) [P.IsPrime]
    (f : Localization.AtPrime P) (hf : f ≠ 0)
    (hboundary :
      (I.stalkIdeal x).map
          (algebraMap (X.presheaf.stalk x) (Localization.AtPrime P)) =
        Ideal.span {f}) :
    letI : IsDomain (Localization.Away f) :=
      IsLocalization.Away.isDomain (Localization.Away f) hf
    letI : Nonempty I.supportComplement :=
      supportComplement_nonempty_of_localizationAway
        I x P f hf hboundary
    ∀ (W : FiniteEtale I.supportComplement), IsGalois W →
      IsGalois ((FiniteEtale.pullback
        (localizationAwayToSupportComplement I x P f hboundary)).obj W) := by
  let : IsDomain (Localization.Away f) :=
    IsLocalization.Away.isDomain (Localization.Away f) hf
  let : Nonempty I.supportComplement :=
    supportComplement_nonempty_of_localizationAway
      I x P f hf hboundary
  intro W hW
  exact localizationAwayToSupportComplement_pullback_isGalois
    I x P f hf hboundary W hW

/-- Pullback from a global support complement to a local split
normal-crossings chart preserves connected Galois covers. -/
theorem pullbackSupportComplementCoverToBoundaryAway_isGalois
    [IsIntegral X] [IsNormalIntegral X] [IsLocallyNoetherian X]
    (I : X.IdealSheafData) (x : X)
    (P : PrimeSpectrum (X.presheaf.stalk x)) {r : ℕ}
    (t : Fin 2 → Localization.AtPrime P.asIdeal)
    (hboundary :
      (I.stalkIdeal x).map
          (algebraMap (X.presheaf.stalk x)
            (Localization.AtPrime P.asIdeal)) =
        Ideal.span {boundaryProduct t r})
    (hNC : IsSplitStrictNormalCrossingsAt
      (boundaryProduct t r) t r) :
    let hf := boundaryProduct_ne_zero_of_splitStrictNormalCrossings hNC
    letI : IsDomain (Localization.Away (boundaryProduct t r)) :=
      IsLocalization.Away.isDomain
        (Localization.Away (boundaryProduct t r)) hf
    letI : Nonempty I.supportComplement :=
      supportComplement_nonempty_of_localizationAway
        I x P.asIdeal (boundaryProduct t r) hf hboundary
    ∀ (W : FiniteEtale I.supportComplement), IsGalois W →
      IsGalois
        (pullbackSupportComplementCoverToBoundaryAway
          I x P t hboundary W) := by
  dsimp only
  let hf := boundaryProduct_ne_zero_of_splitStrictNormalCrossings hNC
  let : IsDomain (Localization.Away (boundaryProduct t r)) :=
    IsLocalization.Away.isDomain
      (Localization.Away (boundaryProduct t r)) hf
  let : Nonempty I.supportComplement :=
    supportComplement_nonempty_of_localizationAway
      I x P.asIdeal (boundaryProduct t r) hf hboundary
  intro W hW
  exact localizationAwayToSupportComplement_pullback_isGalois
    I x P.asIdeal (boundaryProduct t r) hf hboundary W hW

end AlgebraicGeometry.Scheme.IdealSheafData

end
