/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.KummerTheory.PowerSeparation

/-!
# Separation by prime-power quotients

Prime powers suffice to recover subgroups of finitely generated abelian
groups. The saturated-subgroup version also applies to S-unit groups.
-/

namespace AnabelianGeometry.KummerTheory

variable {G : Type*} [CommGroup G] [Group.FG G]

/-- A finitely generated abelian group has no nontrivial element divisible
by every power of every prime. -/
theorem eq_one_of_forall_exists_prime_pow (x : G)
    (h : ∀ p : ℕ, p.Prime → ∀ r : ℕ, ∃ y : G, y ^ (p ^ r) = x) : x = 1 := by
  classical
  obtain ⟨ι, j, _, _, p, hp, e, ⟨f⟩⟩ :=
    CommGroup.equiv_free_prod_prod_multiplicative_zmod G
  apply f.injective
  rw [map_one]
  apply Prod.ext
  · funext k
    apply Multiplicative.toAdd.injective
    let z : ℤ := Multiplicative.toAdd ((f x).1 k)
    change z = 0
    obtain ⟨y, hy⟩ := h 2 Nat.prime_two z.natAbs
    have hz : ((2 ^ z.natAbs : ℕ) : ℤ) ∣ z := by
      refine ⟨Multiplicative.toAdd ((f y).1 k), ?_⟩
      have heq := congrArg (fun t : G => Multiplicative.toAdd ((f t).1 k)) hy
      rw [map_pow] at heq
      change (2 ^ z.natAbs) • Multiplicative.toAdd ((f y).1 k) = z at heq
      rw [nsmul_eq_mul] at heq
      exact heq.symm
    exact Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hz (by
      rw [Int.natAbs_natCast]
      exact Nat.lt_two_pow_self)
  · funext k
    apply Multiplicative.toAdd.injective
    change Multiplicative.toAdd ((f x).2 k) = 0
    obtain ⟨y, hy⟩ := h (p k) (hp k) (e k)
    have heq := congrArg (fun t : G => Multiplicative.toAdd ((f t).2 k)) hy
    rw [map_pow] at heq
    change (p k ^ e k) • Multiplicative.toAdd ((f y).2 k) =
      Multiplicative.toAdd ((f x).2 k) at heq
    rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul] at heq
    exact heq.symm

/-- Membership in every power enlargement already implies membership in
the original subgroup. The ambient group is finitely generated and abelian. -/
theorem mem_of_forall_mem_sup_prime_powers (H : Subgroup G) (x : G)
    (h : ∀ p : ℕ, p.Prime → ∀ r : ℕ,
      x ∈ H ⊔ (powMonoidHom (α := G) (p ^ r)).range) : x ∈ H := by
  apply (QuotientGroup.eq_one_iff x).mp
  apply eq_one_of_forall_exists_prime_pow
  intro p hp r
  obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup.mp (h p hp r)
  obtain ⟨y, hy⟩ := hb
  refine ⟨(QuotientGroup.mk' H) y, ?_⟩
  rw [← map_pow]
  change (QuotientGroup.mk' H) (y ^ (p ^ r)) = (QuotientGroup.mk' H) x
  change y ^ (p ^ r) = b at hy
  have hqa : (QuotientGroup.mk' H) a = 1 := (QuotientGroup.eq_one_iff a).mpr ha
  rw [hy, ← hab, map_mul, hqa, one_mul]

omit [Group.FG G] in
/-- Power separation can be checked in a finitely generated subgroup that
contains every root of each of its elements. -/
theorem mem_of_forall_mem_sup_prime_powers_of_saturated
    (S H : Subgroup G) [Group.FG S] (hHS : H ≤ S)
    (hsat : ∀ (n : ℕ+) (y : G), y ^ (n : ℕ) ∈ S → y ∈ S)
    (x : G) (hx : x ∈ S)
    (h : ∀ p : ℕ, p.Prime → ∀ r : ℕ,
      x ∈ H ⊔ (powMonoidHom (α := G) (p ^ r)).range) : x ∈ H := by
  let xS : S := ⟨x, hx⟩
  have hlocal : ∀ p : ℕ, p.Prime → ∀ r : ℕ, xS ∈ H.subgroupOf S ⊔
      (powMonoidHom (α := S) (p ^ r)).range := by
    intro p hp r
    obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup.mp (h p hp r)
    obtain ⟨y, hy⟩ := hb
    change y ^ (p ^ r) = b at hy
    have hbS : b ∈ S := by
      have ht := S.mul_mem (S.inv_mem (hHS ha)) hx
      rw [← hab, inv_mul_cancel_left] at ht
      exact ht
    have hyS : y ∈ S := hsat ⟨p ^ r, pow_pos hp.pos r⟩ y (hy.symm ▸ hbS)
    apply Subgroup.mem_sup.mpr
    refine ⟨⟨a, hHS ha⟩, ha, (⟨y, hyS⟩ : S) ^ (p ^ r), ⟨⟨y, hyS⟩, rfl⟩, ?_⟩
    apply Subtype.ext
    change a * y ^ (p ^ r) = x
    rw [hy, hab]
  exact mem_of_forall_mem_sup_prime_powers (H.subgroupOf S) xS hlocal

end AnabelianGeometry.KummerTheory
