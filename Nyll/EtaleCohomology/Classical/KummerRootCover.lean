/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Foundations.FieldTheory.AdjoinRoot_etale_and_finite_X_pow_sub_C_of_isUnit
import Nyll.SchemeTheory.FiniteEtale.Geometry
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

/-!
# Actual finite étale covers extracting roots of units

The cover is the spectrum of the actual monic quotient R[T]/(T^n-u).
Its étaleness is reused from the algebraic-curve library. Lying over proves
surjectivity, and the adjoined root is explicitly a unit. These are the
geometric local inputs to the Kummer sequence; no cohomology comparison
or local lifting assumption is used.
-/

noncomputable section
universe u
open AlgebraicGeometry CategoryTheory Polynomial

namespace EtaleCohomology

/-- The actual algebra used to extract an nth root of a unit. -/
abbrev kummerRootAlgebra {R : Type u} [CommRing R] (n : ℕ) (a : Rˣ) :=
  AdjoinRoot (X ^ n - C (a : R))

/-- The defining relation in the actual root algebra. -/
theorem kummerRootAlgebra_root_pow {R : Type u} [CommRing R] (n : ℕ) (a : Rˣ) :
    AdjoinRoot.root (X ^ n - C (a : R)) ^ n =
      algebraMap R (kummerRootAlgebra n a) (a : R) := by
  have h := AdjoinRoot.eval₂_root (X ^ n - C (a : R))
  rw [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
    Polynomial.eval₂_C, sub_eq_zero] at h
  exact h

/-- The adjoined root is an actual unit, with inverse t^(n-1) u^(-1). -/
def kummerRootUnit {R : Type u} [CommRing R] {n : ℕ} (hn : 0 < n) (a : Rˣ) :
    (kummerRootAlgebra n a)ˣ := by
  let t : kummerRootAlgebra n a := AdjoinRoot.root (X ^ n - C (a : R))
  let b : kummerRootAlgebra n a :=
    t ^ (n - 1) * algebraMap R (kummerRootAlgebra n a) (↑a⁻¹ : R)
  have h : t * b = 1 := by
    dsimp only [b]
    rw [← mul_assoc, ← pow_succ', Nat.sub_add_cancel hn,
      kummerRootAlgebra_root_pow, ← map_mul]
    change algebraMap R (kummerRootAlgebra n a) ((a : R) * a.inv) = 1
    rw [a.val_inv, map_one]
  exact ⟨t, b, h, (mul_comm b t).trans h⟩

theorem kummerRootUnit_pow {R : Type u} [CommRing R] {n : ℕ}
    (hn : 0 < n) (a : Rˣ) :
    kummerRootUnit hn a ^ n =
      Units.map (algebraMap R (kummerRootAlgebra n a)).toMonoidHom a := by
  apply Units.ext
  exact kummerRootAlgebra_root_pow n a

/-- The actual root cover is finite étale when n is invertible. -/
theorem kummerRootCover_isFiniteEtale {R : Type u} [CommRing R]
    (n : ℕ) (a : Rˣ) (hn : IsUnit (n : R)) :
    IsFiniteEtale (Spec.map (CommRingCat.ofHom
      (algebraMap R (kummerRootAlgebra n a)))) := by
  rw [IsFiniteEtale.SpecMap_iff]
  change (algebraMap R (kummerRootAlgebra n a)).FiniteEtale
  rw [RingHom.finiteEtale_algebraMap_iff, Algebra.finiteEtale_iff]
  exact AdjoinRoot.etale_and_finite_X_pow_sub_C_of_isUnit n (a : R) hn a.isUnit

/-- Lying over proves that every point of the affine base is covered.
No irreducibility of the Kummer polynomial is required. -/
theorem kummerRootCover_surjective {R : Type u} [CommRing R]
    {n : ℕ} (hn : 0 < n) (a : Rˣ) :
    Function.Surjective (Spec.map (CommRingCat.ofHom
      (algebraMap R (kummerRootAlgebra n a)))) := by
  change Function.Surjective (PrimeSpectrum.comap
    (algebraMap R (kummerRootAlgebra n a)))
  intro p
  have : Nontrivial R := p.nontrivial
  have hm : (X ^ n - C (a : R)).Monic := Polynomial.monic_X_pow_sub_C _ hn.ne'
  have : Module.Finite R (kummerRootAlgebra n a) := hm.finite_adjoinRoot
  have : FaithfulSMul R (kummerRootAlgebra n a) :=
    AdjoinRoot.faithfulSMul_of_monic_of_degree_pos hm (by
      rw [Polynomial.degree_X_pow_sub_C hn]
      exact_mod_cast hn)
  have hk : RingHom.ker (algebraMap R (kummerRootAlgebra n a)) = ⊥ :=
    (RingHom.injective_iff_ker_eq_bot _).mp
      (FaithfulSMul.algebraMap_injective R (kummerRootAlgebra n a))
  obtain ⟨Q, _, hQ, hQP⟩ := Ideal.exists_ideal_over_prime_of_isIntegral
    p.asIdeal (⊥ : Ideal (kummerRootAlgebra n a)) (by
      change RingHom.ker (algebraMap R (kummerRootAlgebra n a)) ≤ p.asIdeal
      rw [hk]
      exact bot_le)
  exact ⟨⟨Q, hQ⟩, PrimeSpectrum.ext hQP⟩

/-- The actual root cover has constant degree n, including when it is
disconnected. This follows from the monic power basis, not from an
assumed degree comparison. -/
theorem kummerRootCover_finrank {R : Type u} [CommRing R]
    {n : ℕ} (hn : 0 < n) (a : Rˣ) (x : Spec (.of R)) :
    (Spec.map (CommRingCat.ofHom
      (algebraMap R (kummerRootAlgebra n a)))).finrank x = n := by
  have : Nontrivial R := x.nontrivial
  have hm : (Polynomial.X ^ n - Polynomial.C (a : R)).Monic :=
    Polynomial.monic_X_pow_sub_C _ hn.ne'
  have : Module.Finite R (kummerRootAlgebra n a) := hm.finite_adjoinRoot
  have : Module.Free R (kummerRootAlgebra n a) := hm.free_adjoinRoot
  have hr : Module.finrank R (kummerRootAlgebra n a) = n :=
    (AdjoinRoot.powerBasis' hm).finrank.trans Polynomial.natDegree_X_pow_sub_C
  exact (Scheme.Hom.finrank_SpecMap_algebraMap R (kummerRootAlgebra n a) x).trans
    ((congrFun (Module.rankAtStalk_eq_finrank_of_free
      (R := R) (M := kummerRootAlgebra n a)) x).trans hr)

end EtaleCohomology
