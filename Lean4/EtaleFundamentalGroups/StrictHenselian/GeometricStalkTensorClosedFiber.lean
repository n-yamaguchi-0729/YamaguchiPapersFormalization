/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.StrictHenselian.GeometricStalkTensorLocal
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.RingTheory.Localization.Ideal

/-!
# Closed points in the closed fiber of a base-changed geometric stalk

The local-ring comparison with a strictly Henselian base implies that every
prime over its closed point is maximal. Given a maximal ideal containing
the prime, localize there. The two primes then have the same contraction
along the proved isomorphism from the base, so they agree. This supplies
the closed-complement requirement in the overlap argument of Stacks 0BSB.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct

namespace EtaleFundamentalGroups.StrictHenselian

universe u

/-- Every point of the closed fiber of a base-changed actual geometric
stalk over a strictly Henselian local ring is a closed point. -/
theorem geometricStalk_tensor_isMaximal_of_liesOver
    {R Ω T : Type u} [CommRing R] [Field Ω] [CommRing T] [Algebra R T]
    [HenselianLocalRing T] [IsSepClosed (IsLocalRing.ResidueField T)]
    (φ : R →+* Ω) :
    let H := geometricStalk (Spec.map (CommRingCat.ofHom φ))
    let : Algebra R H := (geometricStalkStructureMap φ).toAlgebra
    ∀ (q : Ideal (T ⊗[R] H)) [q.IsPrime]
      [q.LiesOver (IsLocalRing.maximalIdeal T)], q.IsMaximal := by
  intro H hH q hq hqover
  let B := T ⊗[R] H
  obtain ⟨M, hM, hqM⟩ := Ideal.exists_le_maximal q hq.ne_top
  have : M.IsMaximal := hM
  have : M.LiesOver (IsLocalRing.maximalIdeal T) := by
    constructor
    apply (IsLocalRing.maximalIdeal.isMaximal T).eq_of_le
      (Ideal.comap_isPrime (algebraMap T B) M).ne_top
    rw [q.over_def (IsLocalRing.maximalIdeal T)]
    exact Ideal.comap_mono hqM
  let L := Localization.AtPrime M
  have hsurj : Function.Surjective (algebraMap T L) :=
    (geometricStalk_tensor_localizationAtPrime_bijective φ M).surjective
  have hdisjoint : Disjoint (M.primeCompl : Set B) (q : Set B) := by
    apply Set.disjoint_left.mpr
    intro b hbM hbq
    exact hbM (hqM hbq)
  let qL : Ideal L := q.map (algebraMap B L)
  have hqLunder : qL.under B = q :=
    IsLocalization.under_map_of_isPrime_disjoint M.primeCompl L hq hdisjoint
  have hqLbase : qL.under T = IsLocalRing.maximalIdeal T := by
    rw [← Ideal.under_under (B := B), hqLunder]
    exact (q.over_def (IsLocalRing.maximalIdeal T)).symm
  have hmaxbase : (IsLocalRing.maximalIdeal L).under T =
      IsLocalRing.maximalIdeal T := by
    rw [← Ideal.under_under (B := B), Localization.AtPrime.under_maximalIdeal]
    exact (M.over_def (IsLocalRing.maximalIdeal T)).symm
  have hqL : qL = IsLocalRing.maximalIdeal L :=
    Ideal.comap_injective_of_surjective (algebraMap T L) hsurj
      (hqLbase.trans hmaxbase.symm)
  have hqeq : q = M := by
    rw [← hqLunder, hqL, Localization.AtPrime.under_maximalIdeal]
  exact hqeq.symm ▸ hM

end EtaleFundamentalGroups.StrictHenselian
