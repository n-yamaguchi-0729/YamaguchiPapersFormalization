/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.Localized.Basic

/-!
# Normalization inertia and localization

Localizing a normalization at a prime below `Q` does not change its inertia
subgroup.  This is the comparison needed to state the final one-point theorem
using the original normalization prime, while applying the existing
height-one cardinality theorem to the localized normalization.

Only the canonical generic action on integral closures is used.  In
particular, this file introduces no global action, algebra, or scalar-tower
instances and needs no finiteness, Galois, regularity, or height hypotheses.
-/

noncomputable section

namespace EtaleFundamentalGroups

universe uA uK uL

variable {A : Type uA} {K : Type uK} {L : Type uL}
variable [CommRing A]
variable [Field K] [Field L]
variable [Algebra A K] [IsFractionRing A K]
variable [Algebra K L] [Algebra A L] [IsScalarTower A K L]

/-- Inertia at a normalization prime is unchanged after localizing the base
at any larger prime.  The contraction of `Q` need only be contained in the
localization prime; it need not equal it. -/
theorem normalizationInertia_eq_localizedNormalizationInertia_of_under_le
    (P : Ideal A) [P.IsPrime]
    (Q : Ideal (integralClosure A L)) [Q.IsPrime]
    (hQP : Q.under A ≤ P) :
    Q.toAddSubgroup.inertia Gal(L/K) =
      localizedNormalizationInertia (K := K) (L := L) P Q := by
  let V := Localization.AtPrime P
  let B := integralClosure A L
  let : Algebra V K :=
    localizationAtPrimeToFractionFieldAlgebra (K := K) P
  let : Algebra V L :=
    localizationAtPrimeToExtensionAlgebra (K := K) (L := L) P
  let : IsScalarTower V K L :=
    localizationAtPrimeToFractionFieldToExtension_isScalarTower
      (K := K) (L := L) P
  let : IsScalarTower A V L :=
    localizationAtPrimeToExtension_isScalarTower (K := K) (L := L) P
  let : SMulCommClass Gal(L/K) V L :=
    localizationAtPrime_galois_smulCommClass (K := K) (L := L) P
  let Bp := integralClosure V L
  let := integralClosureLocalizationAlgebra (L := L) P
  let M := Algebra.algebraMapSubmonoid B P.primeCompl
  let : IsLocalization M Bp :=
    isLocalization_integralClosure_localizationAtPrime
      (K := K) (L := L) P
  let Qp := localizedNormalizationPrime (K := K) (L := L) P Q
  have hdisj : Disjoint (M : Set B) (Q : Set B) := by
    exact Set.disjoint_image_left.mpr
      (Set.disjoint_compl_left_iff_subset.mpr hQP)
  have hunder : (Q.map (algebraMap B Bp)).under B = Q :=
    IsLocalization.under_map_of_isPrime_disjoint M Bp inferInstance hdisj
  have hmap_smul (sigma : Gal(L/K)) (b : B) :
      algebraMap B Bp (sigma • b) = sigma • algebraMap B Bp b := by
    apply Subtype.ext
    rfl
  change Q.toAddSubgroup.inertia Gal(L/K) =
    Qp.toAddSubgroup.inertia Gal(L/K)
  ext sigma
  change
    (forall b : B, sigma • b - b ∈ Q) ↔
      (forall z : Bp, sigma • z - z ∈ Qp)
  constructor
  · intro hsigma z
    obtain ⟨⟨b, s⟩, hz⟩ := IsLocalization.surj M z
    have hs_fixed_B : sigma • (s : B) = (s : B) := by
      obtain ⟨a, _ha, ha⟩ := s.property
      rw [← ha]
      exact smul_algebraMap sigma a
    have hs_fixed :
        sigma • algebraMap B Bp (s : B) = algebraMap B Bp (s : B) := by
      rw [← hmap_smul, hs_fixed_B]
    have hsigma_z :
        (sigma • z) * algebraMap B Bp (s : B) =
          algebraMap B Bp (sigma • b) := by
      calc
        (sigma • z) * algebraMap B Bp (s : B) =
            (sigma • z) * (sigma • algebraMap B Bp (s : B)) := by
              rw [hs_fixed]
        _ = sigma • (z * algebraMap B Bp (s : B)) := by
              exact (smul_mul' sigma z (algebraMap B Bp (s : B))).symm
        _ = sigma • algebraMap B Bp b := congrArg (sigma • ·) hz
        _ = algebraMap B Bp (sigma • b) := (hmap_smul sigma b).symm
    rw [← Ideal.unit_mul_mem_iff_mem Qp (IsLocalization.map_units Bp s)]
    have heq :
        algebraMap B Bp (s : B) * (sigma • z - z) =
          algebraMap B Bp (sigma • b - b) := by
      calc
        algebraMap B Bp (s : B) * (sigma • z - z) =
            (sigma • z) * algebraMap B Bp (s : B) -
              z * algebraMap B Bp (s : B) := by ring
        _ = algebraMap B Bp (sigma • b) - algebraMap B Bp b := by
              rw [hsigma_z, hz]
        _ = algebraMap B Bp (sigma • b - b) := by rw [map_sub]
    rw [heq]
    exact Ideal.mem_map_of_mem (algebraMap B Bp) (hsigma b)
  · intro hsigma b
    have hmem : algebraMap B Bp (sigma • b - b) ∈ Qp := by
      rw [map_sub, hmap_smul]
      exact hsigma (algebraMap B Bp b)
    change sigma • b - b ∈ Q
    rw [← hunder]
    exact hmem

/-- Inertia at a normalization prime is unchanged after localizing the base
at its contraction.  Both sides use the canonical action obtained by
restricting the action of `Gal(L/K)` on `L` to the relevant integral closure.
-/
theorem normalizationInertia_eq_localizedNormalizationInertia
    (P : Ideal A) [P.IsPrime]
    (Q : Ideal (integralClosure A L)) [Q.IsPrime] [Q.LiesOver P] :
    Q.toAddSubgroup.inertia Gal(L/K) =
      localizedNormalizationInertia (K := K) (L := L) P Q := by
  let V := Localization.AtPrime P
  let B := integralClosure A L
  let : Algebra V K :=
    localizationAtPrimeToFractionFieldAlgebra (K := K) P
  let : Algebra V L :=
    localizationAtPrimeToExtensionAlgebra (K := K) (L := L) P
  let : IsScalarTower V K L :=
    localizationAtPrimeToFractionFieldToExtension_isScalarTower
      (K := K) (L := L) P
  let : IsScalarTower A V L :=
    localizationAtPrimeToExtension_isScalarTower (K := K) (L := L) P
  let : SMulCommClass Gal(L/K) V L :=
    localizationAtPrime_galois_smulCommClass (K := K) (L := L) P
  let Bp := integralClosure V L
  let := integralClosureLocalizationAlgebra (L := L) P
  let M := Algebra.algebraMapSubmonoid B P.primeCompl
  let : IsLocalization M Bp :=
    isLocalization_integralClosure_localizationAtPrime
      (K := K) (L := L) P
  let Qp := localizedNormalizationPrime (K := K) (L := L) P Q
  have hdisj : Disjoint (M : Set B) (Q : Set B) := by
    exact Set.disjoint_image_left.mpr
      (Set.disjoint_compl_left_iff_subset.mpr
        (show Q.under A ≤ P by rw [Q.over_def P]))
  have hunder : (Q.map (algebraMap B Bp)).under B = Q :=
    IsLocalization.under_map_of_isPrime_disjoint M Bp inferInstance hdisj
  have hmap_smul (sigma : Gal(L/K)) (b : B) :
      algebraMap B Bp (sigma • b) = sigma • algebraMap B Bp b := by
    apply Subtype.ext
    rfl
  change Q.toAddSubgroup.inertia Gal(L/K) =
    Qp.toAddSubgroup.inertia Gal(L/K)
  ext sigma
  change
    (forall b : B, sigma • b - b ∈ Q) ↔
      (forall x : Bp, sigma • x - x ∈ Qp)
  constructor
  · intro hsigma x
    obtain ⟨⟨b, s⟩, hx⟩ := IsLocalization.surj M x
    have hs_fixed_B : sigma • (s : B) = (s : B) := by
      obtain ⟨a, _ha, ha⟩ := s.property
      rw [← ha]
      exact smul_algebraMap sigma a
    have hs_fixed :
        sigma • algebraMap B Bp (s : B) = algebraMap B Bp (s : B) := by
      rw [← hmap_smul, hs_fixed_B]
    have hsigma_x :
        (sigma • x) * algebraMap B Bp (s : B) =
          algebraMap B Bp (sigma • b) := by
      calc
        (sigma • x) * algebraMap B Bp (s : B) =
            (sigma • x) * (sigma • algebraMap B Bp (s : B)) := by
              rw [hs_fixed]
        _ = sigma • (x * algebraMap B Bp (s : B)) := by
              exact (smul_mul' sigma x (algebraMap B Bp (s : B))).symm
        _ = sigma • algebraMap B Bp b := congrArg (sigma • ·) hx
        _ = algebraMap B Bp (sigma • b) := (hmap_smul sigma b).symm
    rw [← Ideal.unit_mul_mem_iff_mem Qp (IsLocalization.map_units Bp s)]
    have heq :
        algebraMap B Bp (s : B) * (sigma • x - x) =
          algebraMap B Bp (sigma • b - b) := by
      calc
        algebraMap B Bp (s : B) * (sigma • x - x) =
            (sigma • x) * algebraMap B Bp (s : B) -
              x * algebraMap B Bp (s : B) := by ring
        _ = algebraMap B Bp (sigma • b) - algebraMap B Bp b := by
              rw [hsigma_x, hx]
        _ = algebraMap B Bp (sigma • b - b) := by rw [map_sub]
    rw [heq]
    exact Ideal.mem_map_of_mem (algebraMap B Bp) (hsigma b)
  · intro hsigma b
    have hmem : algebraMap B Bp (sigma • b - b) ∈ Qp := by
      rw [map_sub, hmap_smul]
      exact hsigma (algebraMap B Bp b)
    change sigma • b - b ∈ Q
    rw [← hunder]
    exact hmem

end EtaleFundamentalGroups
