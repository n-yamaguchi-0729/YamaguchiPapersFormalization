/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import ProCGroups.Abelian.PrimePowerCharacters
import ProCGroups.ProC.Quotients.ClosedNormal
import ProCGroups.Topologies.ContinuousMonoidHom

/-!
# Detecting prime-power divisibility by continuous characters

For a compact totally disconnected abelian group, failure to be a prime-power
power is detected by a continuous character of prime-power order.
-/

namespace Yamaguchi26AbfaithfulGalois

open ProCGroups ProCGroups.ProC ProCGroups.Abelian

universe u

/-- Failure of divisibility by a prime power is detected by a continuous
character of prime-power order. -/
theorem exists_primePower_character_of_not_pow
    {A : Type u} [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A]
    [CompactSpace A] [T2Space A] [TotallyDisconnectedSpace A]
    (p : ℕ) [Fact p.Prime] (s : ℕ) (a : A)
    (ha : ¬ ∃ b : A, b ^ (p ^ s) = a) :
    ∃ n : ℕ, 0 < n ∧ ∃ χ : A →ₜ* Multiplicative (ZMod (p ^ n)), χ a ≠ 1 := by
  let P : Subgroup A := (powMonoidHom (α := A) (p ^ s)).range
  let powerMap : A →ₜ* A := ⟨powMonoidHom (p ^ s), continuous_id.pow _⟩
  have hP : IsClosed (P : Set A) := ContinuousMonoidHom.isClosed_range powerMap
  have : IsClosed (P : Set A) := hP
  have : TotallyDisconnectedSpace (A ⧸ P) :=
    ProCGroups.totallyDisconnectedSpace_quotient_closedNormal P hP
  have hQ : HasOpenNormalBasisInClass (FiniteGroupClass.pGroup p) (A ⧸ P) := by
    apply HasOpenNormalBasisInClass.of_allOpenNormalQuotients
    intro U
    refine ⟨inferInstance, ?_⟩
    apply isPGroup_iff_pow_pow_eq_one.mpr
    intro q
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (U : Subgroup (A ⧸ P)) q
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective P b
    refine ⟨s, ?_⟩
    rw [← map_pow, ← map_pow]
    have hb : QuotientGroup.mk' P (b ^ (p ^ s)) = 1 :=
      (QuotientGroup.eq_one_iff (N := P) _).mpr ⟨b, rfl⟩
    rw [hb, map_one]
  have hqa : QuotientGroup.mk' P a ≠ 1 := by
    intro h
    exact ha ((QuotientGroup.eq_one_iff (N := P) a).mp h)
  obtain ⟨n, hn, χ, hχ⟩ := exists_primePower_character_proP hQ hqa
  let q : A →ₜ* A ⧸ P := ⟨QuotientGroup.mk' P, QuotientGroup.continuous_mk⟩
  exact ⟨n, hn, χ.comp q, hχ⟩

end Yamaguchi26AbfaithfulGalois
