/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Normalization.Primes.AtLargerPrime
import SchemeTheory.Normalization.Products.LocalRingFactor

/-!
# Ramification in a selected product coordinate

The maximal prime selected by one coordinate of a product has the same
ramification index as the maximal ideal in that coordinate.  This is the
ideal-theoretic transport needed after a completed finite algebra has been
decomposed into its local factors.
-/

noncomputable section

namespace EtaleFundamentalGroups

universe uR uι uA

variable {R : Type uR} [CommRing R]
variable {ι : Type uι} (A : ι → Type uA)
variable [∀ j, CommRing (A j)] [∀ j, IsLocalRing (A j)]
variable [∀ j, Algebra R (A j)]

/-- Ramification at a prime selecting one product coordinate is exactly
ramification at the maximal ideal of that coordinate. -/
theorem productCoordinatePrime_ramificationIdx_eq (i : ι) :
    (productCoordinatePrime A i).ramificationIdx R =
      (IsLocalRing.maximalIdeal (A i)).ramificationIdx R := by
  let S := ∀ j, A j
  let q := productCoordinatePrime A i
  let : Algebra S (A i) := productCoordinateAlgebra A i
  let : IsScalarTower R S (A i) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : IsLocalization q.primeCompl (A i) :=
    productCoordinate_isLocalization A i
  have hdisj : Disjoint (q.primeCompl : Set S) (q : Set S) := by
    exact disjoint_compl_left
  have hram := ramificationIdx_map_eq_of_isLocalization
    (R := R) (S := S) (R' := R) (S' := A i)
    (IsUnit.submonoid R) q.primeCompl q hdisj
  have hmap : q.map (algebraMap S (A i)) =
      IsLocalRing.maximalIdeal (A i) := by
    change ((IsLocalRing.maximalIdeal (A i)).comap
      (Pi.evalRingHom A i)).map (Pi.evalRingHom A i) =
        IsLocalRing.maximalIdeal (A i)
    exact Ideal.map_comap_of_surjective _ (Pi.evalRingHom A i).surjective
      (IsLocalRing.maximalIdeal (A i))
  rw [hmap] at hram
  exact hram.symm

section RingEquivTransport

universe uU uB

variable {U : Type uU} [CommRing U] [Algebra R U]
variable (B : ι → Type uB)
variable [∀ j, CommRing (B j)] [∀ j, IsLocalRing (B j)]

/-- Ramification is unchanged when a product-coordinate localization is
pulled back along a ring equivalence. -/
theorem ringEquivProductCoordinatePrime_ramificationIdx_eq
    (e : U ≃+* (∀ j, B j)) (i : ι) :
    letI : Algebra U (B i) := ringEquivProductCoordinateAlgebra B i e
    letI : Algebra R (B i) :=
      ringEquivProductCoordinateBaseAlgebra (R := R) B i e
    (ringEquivProductCoordinatePrime B i e).ramificationIdx R =
      (IsLocalRing.maximalIdeal (B i)).ramificationIdx R := by
  let q := ringEquivProductCoordinatePrime B i e
  let : Algebra U (B i) := ringEquivProductCoordinateAlgebra B i e
  let : Algebra R (B i) :=
    ringEquivProductCoordinateBaseAlgebra (R := R) B i e
  let : IsScalarTower R U (B i) :=
    ringEquivProductCoordinate_isScalarTower (R := R) B i e
  let : IsLocalization q.primeCompl (B i) :=
    ringEquivProductCoordinate_isLocalization B i e
  have hdisj : Disjoint (q.primeCompl : Set U) (q : Set U) :=
    disjoint_compl_left
  have hram := ramificationIdx_map_eq_of_isLocalization
    (R := R) (S := U) (R' := R) (S' := B i)
    (IsUnit.submonoid R) q.primeCompl q hdisj
  rw [ringEquivProductCoordinatePrime_map B i e] at hram
  exact hram.symm

end RingEquivTransport

end EtaleFundamentalGroups

end
