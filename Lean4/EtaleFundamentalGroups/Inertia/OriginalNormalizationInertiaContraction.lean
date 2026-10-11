/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.OriginalNormalizationInertiaBaseLocalization
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Ideal.GoingUp

/-!
# Every local normalization inertia comes from the original affine prime

A maximal prime of the actual localized normalization lies over the local
base's maximal ideal. Its literal contraction therefore lies over the
original base prime. Localization returns the same prime, and the original
Galois inertia subgroups agree.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

universe u v w z

attribute [local instance] normalizationInertiaImageAction

/-- A maximal prime of a normalized prime localization contracts to an
original prime with exactly the same inertia. The contracted prime and its
extension are the literal ring-theoretic comap and map. -/
theorem originalNormalizationInertia_eq_of_local_prime_contraction
    (A : Type u) (R : Type v) (K : Type w) (L : Type z)
    [CommRing A] [CommRing R] [IsLocalRing R] [Field K] [Field L]
    [Algebra A R] [Algebra A K] [Algebra R K]
    [IsFractionRing A K] [IsFractionRing R K]
    [Algebra K L] [Algebra A L] [Algebra R L]
    [IsScalarTower A K L] [IsScalarTower R K L] [IsScalarTower A R L]
    [IsGalois K L]
    (P : Ideal A) [P.IsPrime] [IsLocalization.AtPrime R P]
    (q : Ideal (integralClosure R L)) [q.IsMaximal] :
    let Q := q.comap (normalizationBaseLocalizationRingMap A R L)
    Q.IsPrime ∧ Q.LiesOver P ∧
      Q.map (normalizationBaseLocalizationRingMap A R L) = q ∧
      Q.inertia Gal(L/K) = q.inertia Gal(L/K) := by
  intro Q
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
  have hQ : Q.IsPrime := Ideal.IsPrime.comap f
  have : Q.IsPrime := hQ
  have : q.LiesOver (IsLocalRing.maximalIdeal R) :=
    (Ideal.liesOver_iff q (IsLocalRing.maximalIdeal R)).mpr
      (IsLocalRing.eq_maximalIdeal (Ideal.IsMaximal.under R q)).symm
  have hOver : Q.LiesOver P :=
    IsLocalization.AtPrime.liesOver_comap_of_liesOver (S := B) P R q
  have : Q.LiesOver P := hOver
  have hmap : Q.map f = q := IsLocalization.map_under M C q
  refine ⟨hQ, hOver, hmap, ?_⟩
  exact (originalNormalizationInertia_eq_of_primeLocalization A R K L P Q).2.trans
    (congrArg (fun J : Ideal C => J.inertia Gal(L/K)) hmap)

end EtaleFundamentalGroups.Inertia
