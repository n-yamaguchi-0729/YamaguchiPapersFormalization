/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Yamaguchi26AbfaithfulGalois.FormalHilbert90.FieldSlim
import Yamaguchi26AbfaithfulGalois.HigherLocalField.Properties
import Yamaguchi26AbfaithfulGalois.HigherLocalField.Basic
import GaloisCohomology.Kummer.Concrete.PrimaryRootsDivisibility
import ValuedFieldTheory.Valuation.DiscreteValuationField.ArtinSchreierNonSurjective
import Yamaguchi26AbfaithfulGalois.FieldExamples.FinitelyGeneratedConsequences
import Yamaguchi26AbfaithfulGalois.FieldExamples.Subpadic
import GaloisCohomology.FieldTheory.FinitelyGeneratedPositiveChar
import GaloisCohomology.FieldTheory.FinitelyGeneratedRoots
import Mathlib.Algebra.CharP.Basic
import Mathlib.FieldTheory.Galois.Profinite

/-!
# Applications of the field slimness criterion

Example 6.7 (ex:cf-field-slim) of AbfatifhulGalois.tex.
The toral Kummer condition is imposed on actual units of every finite extension.
The higher-local-field Artin--Schreier condition follows directly from the
first discrete valuation, using a reciprocal uniformizer.
-/

namespace Yamaguchi26AbfaithfulGalois

open ProCGroups.FiniteStepSolvableQuotients

universe u v

/-- The unit formulation of toral Kummer-faithfulness: no finite extension has a
nonidentity unit in every positive-power subgroup. The characteristic-zero
hypothesis of Example 6.7(1) is imposed in the application below. -/
def IsTorallyKummerFaithful (K : Type u) [Field K] : Prop :=
  ∀ (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L],
    ∀ z : Lˣ, (∀ n : ℕ, 0 < n → ∃ y : Lˣ, y ^ n = z) → z = 1

/-- The roots-of-unity hypothesis in Corollary 6.6 follows from the toral
Kummer condition on the actual finite extension. -/
theorem IsTorallyKummerFaithful.finite_primaryComponent
    {K : Type u} [Field K] (hK : IsTorallyKummerFaithful K)
    (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L]
    (p : ℕ) [Fact p.Prime] :
    Finite (CommGroup.primaryComponent Lˣ p) :=
  KummerTheory.finite_primaryComponent_of_no_infinitely_divisible_units (hK L) p

/-- Example 6.7(1): an ab-faithful torally Kummer-faithful field of
characteristic zero has slim finite-step solvable Galois quotients. -/
theorem torallyKummerFaithful_finiteStepSolvable_slim
    (K : Type u) [Field K] [CharZero K]
    (hK : IsTorallyKummerFaithful K)
    (hG : IsAbFaithful Gal(AlgebraicClosure K/K)) :
    ∀ m : ℕ, 2 ≤ m →
      IsSlim (MaxSolvQuot Gal(AlgebraicClosure K/K) m) := by
  apply absoluteGalois_finiteStepSolvable_slim_of_roots_and_artinSchreier K hG
  · intro L hL p hp _hne
    have : FiniteDimensional K L := hL
    have : Fact p.Prime := ⟨hp⟩
    exact hK.finite_primaryComponent L p
  · intro hchar
    exact (hchar ringChar.eq_zero).elim

/-- Example 6.7(2): every field embedding into a finitely generated extension
of Q_p has slim finite-step solvable absolute Galois quotients. -/
theorem subpadic_finiteStepSolvable_slim
    (p : ℕ) [Fact p.Prime] (K : Type u) (E : Type v)
    [Field K] [Field E] [Algebra (Padic p) E] [Algebra.EssFiniteType (Padic p) E]
    (f : K →+* E) :
    ∀ m : ℕ, 2 ≤ m → IsSlim (MaxSolvQuot Gal(AlgebraicClosure K/K) m) := by
  have : CharZero E := charZero_of_injective_algebraMap (algebraMap (Padic p) E).injective
  have : CharZero K := charZero_of_inj_zero (fun n hn => by
    apply (Nat.cast_eq_zero (R := E)).mp
    rw [← map_natCast f n, hn, map_zero])
  obtain ⟨hfaith, hroots⟩ := subpadic_isAbFaithful_and_finite_roots p K E f
  apply absoluteGalois_finiteStepSolvable_slim_of_roots_and_artinSchreier K hfaith
  · intro L hL ℓ hℓ _
    have : FiniteDimensional K L := hL
    have : Fact ℓ.Prime := ⟨hℓ⟩
    exact hroots L ℓ
  · intro hchar
    exact (hchar ringChar.eq_zero).elim

/-- An earlier application: every infinite field finitely generated over its prime
field has slim finite-step solvable absolute Galois quotients. -/
theorem finitelyGenerated_finiteStepSolvable_slim
    (K : Type u) [Field K] [Infinite K] (hfg : Field.FG K) :
    ∀ m : ℕ, 2 ≤ m → IsSlim (MaxSolvQuot Gal(AlgebraicClosure K/K) m) := by
  apply absoluteGalois_finiteStepSolvable_slim_of_roots_and_artinSchreier K
    (finitelyGenerated_isAbFaithful K hfg)
  · intro L hL p hp _hne
    have : FiniteDimensional K L := hL
    have : Fact p.Prime := ⟨hp⟩
    exact FieldTheory.finite_primaryComponent_finiteExtension_of_fg K hfg L p
  · exact FieldTheory.exists_not_artinSchreier_of_fg_posChar K hfg


/-- A positive-dimensional higher local field satisfies the Artin--Schreier
condition needed for the field criterion, in positive characteristic. -/
theorem higherLocalField_exists_not_artinSchreier
    (n : ℕ) (K : Type u) [Field K]
    (hK : ValuationTheory.IsHigherLocalField.{u, v} n K) (hn : 0 < n)
    (hchar : ringChar K ≠ 0) :
    ∃ a : K, ∀ x : K, x ^ ringChar K - x ≠ a := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  obtain ⟨D, _⟩ := hK
  exact D.toDVF.exists_not_pow_sub (ringChar K)
    ((CharP.char_is_prime_or_zero K (ringChar K)).resolve_right hchar).one_lt

/-- Example 6.7(3): positive-dimensional higher local fields have slim
finite-step solvable absolute Galois quotients. -/
theorem higherLocalField_finiteStepSolvable_slim
    (n : ℕ) (K : Type u) [Field K]
    (hK : ValuationTheory.IsHigherLocalField.{u, v} n K) (hn : 0 < n) :
    ∀ m : ℕ, 2 ≤ m →
      IsSlim (MaxSolvQuot Gal(AlgebraicClosure K/K) m) := by
  apply absoluteGalois_finiteStepSolvable_slim_of_roots_and_artinSchreier K
    ((higher_local_field_roots_and_abFaithful n K hK).2 hn)
  · intro L hL p hp _hne
    have : FiniteDimensional K L := hL
    exact (higher_local_field_roots_and_abFaithful n L
      (ValuationTheory.IsHigherLocalField.of_finiteExtension n K L hK)).1 p hp
  · exact higherLocalField_exists_not_artinSchreier n K hK hn

end Yamaguchi26AbfaithfulGalois
