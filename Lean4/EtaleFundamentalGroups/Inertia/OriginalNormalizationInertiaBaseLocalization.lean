/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SchemeTheory.RingTheory.Ramification.FiniteLevelInertiaImage
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Localization.AtPrime.Extension
import Mathlib.Tactic.Ring

/-!
# Original normalization inertia over an actual localized base

The localization model is arbitrary, so the theorem applies directly to
the local ring of a scheme with its actual germ map. The normalization
inclusion is the literal inclusion of integral elements in the same field,
and both actions are the original integral-closure Galois actions.

The fraction argument extends the one in
`EtaleFundamentalGroups.Inertia.Normalization.Localization` to an arbitrary
model of the base localization, retaining the original actions throughout.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

universe u v w z

/-- The literal normalization inclusion induced by an extension of the
base ring inside the same ambient ring. -/
def normalizationBaseLocalizationRingMap
    (A : Type u) (R : Type v) (L : Type w)
    [CommRing A] [CommRing R] [CommRing L]
    [Algebra A R] [Algebra A L] [Algebra R L] [IsScalarTower A R L] :
    integralClosure A L →+* integralClosure R L where
  toFun b := ⟨b.val, b.property.tower_top⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

attribute [local instance] normalizationInertiaImageAction

/-- Passing to the actual local ring of the base preserves original
normalization inertia. The prime over the chosen base prime becomes
maximal, and the Galois subgroup stays literally the same. -/
theorem originalNormalizationInertia_eq_of_primeLocalization
    (A : Type u) (R : Type v) (K : Type w) (L : Type z)
    [CommRing A] [CommRing R] [IsLocalRing R] [Field K] [Field L]
    [Algebra A R] [Algebra A K] [Algebra R K]
    [IsFractionRing A K] [IsFractionRing R K]
    [Algebra K L] [Algebra A L] [Algebra R L]
    [IsScalarTower A K L] [IsScalarTower R K L] [IsScalarTower A R L]
    [IsGalois K L]
    (P : Ideal A) [P.IsPrime] [IsLocalization.AtPrime R P]
    (Q : Ideal (integralClosure A L)) [Q.IsPrime] [Q.LiesOver P] :
    let q := Q.map (normalizationBaseLocalizationRingMap A R L)
    q.IsMaximal ∧ Q.inertia Gal(L/K) = q.inertia Gal(L/K) := by
  intro q
  let B := integralClosure A L
  let C := integralClosure R L
  let f : B →+* C := normalizationBaseLocalizationRingMap A R L
  let : Algebra B C := f.toAlgebra
  have : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower B C L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower A R C :=
    IsScalarTower.of_algebraMap_eq fun a =>
      Subtype.ext (IsScalarTower.algebraMap_apply A R L a)
  let M := Algebra.algebraMapSubmonoid B P.primeCompl
  have : IsLocalization (Algebra.algebraMapSubmonoid L P.primeCompl) L :=
    IsLocalization.of_le_isUnit fun y hy => by
      obtain ⟨a, ha, rfl⟩ := hy
      change IsUnit (algebraMap A L a)
      rw [isUnit_iff_ne_zero, IsScalarTower.algebraMap_apply A K L,
        map_ne_zero_iff _ (algebraMap K L).injective,
        map_ne_zero_iff _ (IsFractionRing.injective A K)]
      exact fun h => ha (h ▸ P.zero_mem)
  have : IsLocalization M C :=
    IsLocalization.integralClosure (R := A) (S := L) (Rf := R) (Sf := L) P.primeCompl
  have hq : q.IsPrime :=
    IsLocalization.AtPrime.isPrime_map_of_liesOver B P C Q
  have : q.IsPrime := hq
  have : q.LiesOver (IsLocalRing.maximalIdeal R) :=
    IsLocalization.AtPrime.liesOver_map_of_liesOver P R C Q
  refine ⟨Ideal.IsMaximal.of_liesOver_isMaximal q (IsLocalRing.maximalIdeal R), ?_⟩
  have hdisj : Disjoint (M : Set B) (Q : Set B) :=
    Set.disjoint_image_left.mpr
      (Set.disjoint_compl_left_iff_subset.mpr
        (show Q.under A ≤ P by rw [Q.over_def P]))
  have hunder : (Q.map (algebraMap B C)).under B = Q :=
    IsLocalization.under_map_of_isPrime_disjoint M C inferInstance hdisj
  have hmap_smul (σ : Gal(L/K)) (b : B) :
      algebraMap B C (σ • b) = σ • algebraMap B C b := by
    apply Subtype.ext
    change algebraMap B L (galRestrict A K L B σ b) =
      algebraMap C L (galRestrict R K L C σ (algebraMap B C b))
    rw [algebraMap_galRestrict_apply A, algebraMap_galRestrict_apply R]
    rfl
  apply Subgroup.ext
  intro σ
  change (∀ b : B, σ • b - b ∈ Q) ↔ (∀ c : C, σ • c - c ∈ q)
  constructor
  · intro hσ c
    obtain ⟨⟨b, s⟩, hc⟩ := IsLocalization.surj M c
    have hsB : σ • (s : B) = (s : B) := by
      obtain ⟨a, _ha, haeq⟩ := s.property
      rw [← haeq]
      apply Subtype.ext
      change algebraMap B L
          (galRestrict A K L B σ (algebraMap A B a)) = algebraMap A L a
      rw [algebraMap_galRestrict_apply A,
        ← IsScalarTower.algebraMap_apply A B L,
        IsScalarTower.algebraMap_apply A K L, AlgEquiv.commutes]
    have hsC : σ • algebraMap B C (s : B) = algebraMap B C (s : B) := by
      rw [← hmap_smul, hsB]
    have hσc : (σ • c) * algebraMap B C (s : B) = algebraMap B C (σ • b) := by
      calc
        (σ • c) * algebraMap B C (s : B) =
            (σ • c) * (σ • algebraMap B C (s : B)) := by rw [hsC]
        _ = σ • (c * algebraMap B C (s : B)) := (smul_mul' σ c _).symm
        _ = σ • algebraMap B C b := congrArg (σ • ·) hc
        _ = algebraMap B C (σ • b) := (hmap_smul σ b).symm
    rw [← Ideal.unit_mul_mem_iff_mem q (IsLocalization.map_units C s)]
    have hdiff : algebraMap B C (s : B) * (σ • c - c) =
        algebraMap B C (σ • b - b) := by
      calc
        algebraMap B C (s : B) * (σ • c - c) =
            (σ • c) * algebraMap B C (s : B) -
              c * algebraMap B C (s : B) := by ring
        _ = algebraMap B C (σ • b) - algebraMap B C b := by rw [hσc, hc]
        _ = algebraMap B C (σ • b - b) := (map_sub (algebraMap B C) _ _).symm
    rw [hdiff]
    exact Ideal.mem_map_of_mem (algebraMap B C) (hσ b)
  · intro hσ b
    have hmem : algebraMap B C (σ • b - b) ∈ q := by
      rw [map_sub, hmap_smul]
      exact hσ (algebraMap B C b)
    rw [← hunder]
    exact hmem

end EtaleFundamentalGroups.Inertia
