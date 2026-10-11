/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.FiniteIdealTameOrder
import Nyll.EtaleFundamentalGroups.Inertia.PrimeToRootsInverseSystem
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# The actual finite ideal tame order is an invertible base-residue exponent

The coefficient map from the original local ring into the prime localization
is local because the prime lies over the maximal ideal. Hence invertibility
of the actual tame order in the upper local residue reflects to the original
ring and then descends to its residue field. This constructs its literal
index in the full prime-to-characteristic roots system.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

universe u v w

/-- The original coefficient composite is local at a prime over the base
maximal ideal. No A-action on the localization is installed. -/
private theorem coefficientComposite_isLocalHom
    (A : Type u) (B : Type v) [CommRing A] [CommRing B]
    [IsLocalRing A] [Algebra A B]
    (Q : Ideal B) [Q.IsPrime] [Q.LiesOver (IsLocalRing.maximalIdeal A)] :
    IsLocalHom ((algebraMap B (Localization.AtPrime Q)).comp (algebraMap A B)) := by
  constructor
  intro a ha
  by_contra hA
  have hmemA : a ∈ IsLocalRing.maximalIdeal A := hA
  have hmemB : algebraMap A B a ∈ Q := by
    change a ∈ Q.under A
    rw [← Q.over_def (IsLocalRing.maximalIdeal A)]
    exact hmemA
  have hmemS : algebraMap B (Localization.AtPrime Q) (algebraMap A B a) ∈
      IsLocalRing.maximalIdeal (Localization.AtPrime Q) :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime Q) Q
      (algebraMap A B a)).mpr hmemB
  exact hmemS ha

/-- Residue invertibility reflects through the actual local coefficient
map, using only its ring-homomorphism data. -/
private theorem nat_isUnit_of_isUnit_residue_of_localHom
    {A : Type u} {R : Type v} [CommRing A] [CommRing R] [IsLocalRing R]
    (f : A →+* R) [IsLocalHom f] (n : ℕ)
    (hn : IsUnit (n : IsLocalRing.ResidueField R)) : IsUnit (n : A) := by
  have hnR : IsUnit (n : R) :=
    (IsLocalRing.residue_ne_zero_iff_isUnit (n : R)).mp (by
      simpa only [map_natCast] using hn.ne_zero)
  apply isUnit_of_map_unit f (n : A)
  simpa only [map_natCast] using hnR

/-- The actual finite tame order is invertible in the original local base
ring. Its upper residue invertibility is supplied by the genuine character. -/
theorem finiteIdealTameOrder_isUnit_base
    (A : Type u) (B : Type v) [CommRing A] [CommRing B]
    [IsLocalRing A] [Algebra A B] [IsDedekindDomain B]
    (G : Type w) [Group G] [Finite G] [MulSemiringAction G B]
    (Q : Ideal B) [Q.IsPrime] [Q.LiesOver (IsLocalRing.maximalIdeal A)]
    (hQ : Q ≠ ⊥) : IsUnit (finiteIdealTameOrder B G Q hQ : A) := by
  have : IsLocalHom
      ((algebraMap B (Localization.AtPrime Q)).comp (algebraMap A B)) :=
    coefficientComposite_isLocalHom A B Q
  exact nat_isUnit_of_isUnit_residue_of_localHom
    ((algebraMap B (Localization.AtPrime Q)).comp (algebraMap A B))
    (finiteIdealTameOrder B G Q hQ) (finiteIdealTameOrder_isUnit B G Q hQ)

/-- The actual finite ideal tame order, as a literal index of the full
roots-of-unity system over the original residue field. -/
def finiteIdealTameIndex
    (A : Type u) (B : Type v) [CommRing A] [CommRing B]
    [IsLocalRing A] [Algebra A B] [IsDedekindDomain B]
    (G : Type w) [Group G] [Finite G] [MulSemiringAction G B]
    (Q : Ideal B) [Q.IsPrime] [Q.LiesOver (IsLocalRing.maximalIdeal A)]
    (hQ : Q ≠ ⊥) : InvertibleExponent (IsLocalRing.ResidueField A) :=
  ⟨finiteIdealTameOrder B G Q hQ, by
    simpa only [map_natCast] using
      (finiteIdealTameOrder_isUnit_base A B G Q hQ).map (IsLocalRing.residue A)⟩

end EtaleFundamentalGroups.Inertia

end
