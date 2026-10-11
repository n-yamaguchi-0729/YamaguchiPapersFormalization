/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.GaloisCohomology.Kummer.Concrete.CyclotomicInvariantKummerTrace
import Nyll.GaloisCohomology.Kummer.Concrete.PrimeCyclicEigenunit
import Nyll.GaloisCohomology.Kummer.Concrete.LastPrimePowerRoot
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.FinitePrimePowerRoots
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.CyclotomicCompositumDegree
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.NormalCyclotomicTower
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.Ring.CharZero
import Mathlib.FieldTheory.Perfect
import Mathlib.Data.Fintype.Card

/-!
# Constructing an invariant moved Kummer trace at the last root level

The original prime degree and the two cyclotomic extensions supply the upper
prime-degree Galois extension. A nonidentity automorphism, an eigenunit with
primitive eigenvalue, and the last positive root level are chosen internally.
If the roots at that level descend, their actual Kummer trace is invariant
under the cyclotomic group and moved by the chosen automorphism.
-/

namespace ClassFieldTower.Martinet.Shafarevich

open KummerTheory ValuationTheory.DiscreteValuationField

-- Four fields, five algebras and two towers give eleven supplied data structures.
-- The valuation is an ordinary bundle. Only finite-dimensionality, normality,
-- characteristic, Galoisness and nontriviality propositions are added locally.
/-- A mixed-characteristic discrete valuation and the original prime-degree
extension produce a last root level and, in the roots-downstairs branch, an
actual invariant character moved by an internally selected automorphism. -/
theorem exists_lastLevel_invariant_moved_cyclotomicKummerTrace
    (F K L E : Type*) [Field F] [Field K] [Field L] [Field E]
    [Algebra F K] [Algebra F L] [Algebra F E] [Algebra K E] [Algebra L E]
    [IsScalarTower F K E] [IsScalarTower F L E] [Normal F K] [CharZero E]
    (p : ℕ) [Fact p.Prime]
    [IsCyclotomicExtension {p} F L] [IsCyclotomicExtension {p} K E]
    (hdegree : Module.finrank F K = p)
    (V : DVF E) [hres : CharP V.residueField p] :
    ∃ s : ℕ, (primitiveRoots (p ^ (s + 1)) E).Nonempty ∧
      (∀ m : ℕ, (primitiveRoots (p ^ m) E).Nonempty → m ≤ s + 1) ∧
      ¬ (primitiveRoots (p ^ (s + 2)) E).Nonempty ∧
      ((∀ ξ : E, ξ ^ (p ^ (s + 1)) = 1 → ξ ∈ Set.range (algebraMap L E)) →
        ∃ (τ : E ≃ₐ[L] E)
          (T : Gal(AlgebraicClosure E/E) →ₜ* Multiplicative (ZMod (p ^ (s + 1)))),
          (∀ δ : E ≃ₐ[K] E,
            absoluteContinuousCharacterAction (K := E)
              (A := Multiplicative (ZMod (p ^ (s + 1)))) δ.toRingEquiv T = T) ∧
          absoluteContinuousCharacterAction (K := E)
            (A := Multiplicative (ZMod (p ^ (s + 1)))) τ.toRingEquiv T ≠ T) := by
  have hp : p.Prime := Fact.out
  have hdeg : Module.finrank L E = p :=
    cyclotomic_compositum_finrank_eq_prime F K L E p hdegree
  have : FiniteDimensional L E :=
    FiniteDimensional.of_finrank_pos (hdeg.symm ▸ hp.pos)
  have : IsGalois L E := by
    have : Normal F E := by
      have : FiniteDimensional F K :=
        FiniteDimensional.of_finrank_pos (hdegree.symm ▸ hp.pos)
      exact normal_cyclotomic_tower F K E p
    have : CharZero L := (algebraMap L E).charZero
    exact { to_normal := Normal.tower_top_of_normal F L E }
  have hcard : Nat.card Gal(E/L) = p :=
    (IsGalois.card_aut_eq_finrank L E).trans hdeg
  have : Nontrivial Gal(E/L) :=
    Finite.one_lt_card_iff_nontrivial.mp (hcard.symm ▸ hp.one_lt)
  obtain ⟨τ, hτ⟩ := exists_ne (1 : Gal(E/L))
  obtain ⟨η, hη⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot F L
    (Set.mem_singleton p) hp.ne_zero
  have hmuL : (primitiveRoots p L).Nonempty :=
    ⟨η, (mem_primitiveRoots hp.pos).mpr hη⟩
  obtain ⟨α, ζ, hζ, hα⟩ :=
    exists_primitive_eigenunit_of_prime_degree hp hdeg hmuL τ hτ
  obtain ⟨q, hq, hmu, hmax, hnext, hclass⟩ :=
    exists_last_primePowerRoot_nontrivial_class hp (V.finite_primePowerRoots p) hζ
  have hqzero : q ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hq)
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hqzero
  refine ⟨s, hmu, hmax, hnext, ?_⟩
  intro hdown
  have hζroot : (ζ : E) ^ p = 1 := (IsPrimitiveRoot.coe_units_iff.mpr hζ).pow_eq_one
  obtain ⟨T, hinvariant, hmoved⟩ := exists_invariant_moved_cyclotomicKummerTrace
    (F := F) (K := K) (L := L) (E := E) p s hmu hdown τ α ζ hα hζroot hclass
  exact ⟨τ, T, hinvariant, hmoved⟩

end ClassFieldTower.Martinet.Shafarevich
