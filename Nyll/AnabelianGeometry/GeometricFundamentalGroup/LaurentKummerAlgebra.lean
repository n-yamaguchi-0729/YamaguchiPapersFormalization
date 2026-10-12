/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Kummer.AdjoinRoot.FormallyEtale
import Nyll.EtaleFundamentalGroups.Kummer.Obstructions.LocalDerivative
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.GroupTheory.MonoidLocalization.UniqueFactorization
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.PowerBasis

/-!
# Connected Kummer algebras over the Laurent chart

The algebra is the actual quotient adjoining an `n`th root of the Laurent coordinate.
Eisenstein irreducibility before localization proves that it is a domain. The monic
power basis gives its rank, and the invertible derivative proves etaleness.
-/

noncomputable section

open Polynomial

namespace AnabelianGeometry.GeometricFundamentalGroup

universe u

/-- The actual algebra adjoining an `n`th root of the invertible Laurent coordinate. -/
abbrev LaurentKummerAlgebra (K : Type u) [Field K] (n : ℕ) :=
  AdjoinRoot (X ^ n - C (LaurentPolynomial.T 1 : LaurentPolynomial K))

/-- The Kummer polynomial stays prime on the punctured affine line. -/
theorem prime_laurentKummerPolynomial (K : Type u) [Field K] {n : ℕ} (hn : 0 < n) :
    Prime (X ^ n - C (LaurentPolynomial.T 1 : LaurentPolynomial K)) := by
  have laurentUFD : UniqueFactorizationMonoid (LaurentPolynomial K) :=
    UniqueFactorizationMonoid.of_isLocalization
      (Submonoid.powers (X : K[X])) (LaurentPolynomial K)
  have hirr := EtaleFundamentalGroups.Kummer.irreducible_X_pow_sub_C_away_of_prime
    (R := K[X]) (S := LaurentPolynomial K) (K := RatFunc K) Polynomial.prime_X hn
  rw [LaurentPolynomial.algebraMap_eq_toLaurent, Polynomial.toLaurent_X] at hirr
  exact hirr.prime

/-- The actual Kummer quotient is an integral domain; no connectedness is assumed. -/
theorem isDomain_laurentKummerAlgebra (K : Type u) [Field K] {n : ℕ} (hn : 0 < n) :
    IsDomain (LaurentKummerAlgebra K n) :=
  AdjoinRoot.isDomain_of_prime (prime_laurentKummerPolynomial K hn)

/-- The monic power basis makes the Kummer algebra finite and free of the stated rank. -/
theorem finite_free_finrank_laurentKummerAlgebra (K : Type u) [Field K]
    {n : ℕ} (hn : 0 < n) :
    Module.Finite (LaurentPolynomial K) (LaurentKummerAlgebra K n) ∧
      Module.Free (LaurentPolynomial K) (LaurentKummerAlgebra K n) ∧
      Module.finrank (LaurentPolynomial K) (LaurentKummerAlgebra K n) = n := by
  let hm : (X ^ n - C (LaurentPolynomial.T 1 : LaurentPolynomial K)).Monic :=
    Polynomial.monic_X_pow_sub_C _ hn.ne'
  refine ⟨hm.finite_adjoinRoot, hm.free_adjoinRoot, ?_⟩
  exact (AdjoinRoot.powerBasis' hm).finrank.trans Polynomial.natDegree_X_pow_sub_C

/-- In characteristic zero every positive-degree Kummer algebra is etale. -/
theorem etale_laurentKummerAlgebra (K : Type u) [Field K] [CharZero K]
    {n : ℕ} (hn : 0 < n) :
    Algebra.Etale (LaurentPolynomial K) (LaurentKummerAlgebra K n) := by
  have hnK : IsUnit (n : K) := isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr hn.ne')
  have hnA : IsUnit (n : LaurentPolynomial K) := by
    simpa only [map_natCast] using hnK.map (algebraMap K (LaurentPolynomial K))
  exact ⟨EtaleFundamentalGroups.Kummer.formallyEtale_adjoinRoot_X_pow_sub_C hn
    hnA (LaurentPolynomial.isUnit_T 1), inferInstance⟩

end AnabelianGeometry.GeometricFundamentalGroup
