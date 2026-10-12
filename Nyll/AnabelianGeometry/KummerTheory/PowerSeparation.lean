/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.Data.Int.Basic

/-!
# Separation by power quotients

In a finitely generated abelian group, an element divisible by every
positive integer is trivial. Applying this to a quotient shows that every
subgroup is the intersection of its enlargements by ambient power subgroups.
-/

namespace AnabelianGeometry.KummerTheory

variable {G : Type*} [CommGroup G] [Group.FG G]

/-- A finitely generated abelian group has no nontrivial element divisible
by every positive integer. -/
theorem eq_one_of_forall_exists_pow (x : G)
    (h : ∀ n : ℕ+, ∃ y : G, y ^ (n : ℕ) = x) : x = 1 := by
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
    obtain ⟨y, hy⟩ := h ⟨z.natAbs + 1, Nat.succ_pos _⟩
    have hz : ((z.natAbs + 1 : ℕ) : ℤ) ∣ z := by
      refine ⟨Multiplicative.toAdd ((f y).1 k), ?_⟩
      have heq := congrArg (fun t : G => Multiplicative.toAdd ((f t).1 k)) hy
      rw [map_pow] at heq
      change (z.natAbs + 1) • Multiplicative.toAdd ((f y).1 k) = z at heq
      rw [nsmul_eq_mul] at heq
      exact heq.symm
    exact Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hz (by
      rw [Int.natAbs_natCast]
      exact Nat.lt_succ_self _)
  · funext k
    apply Multiplicative.toAdd.injective
    change Multiplicative.toAdd ((f x).2 k) = 0
    obtain ⟨y, hy⟩ := h ⟨p k ^ e k, pow_pos (hp k).pos _⟩
    have heq := congrArg (fun t : G => Multiplicative.toAdd ((f t).2 k)) hy
    rw [map_pow] at heq
    change (p k ^ e k) • Multiplicative.toAdd ((f y).2 k) =
      Multiplicative.toAdd ((f x).2 k) at heq
    rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul] at heq
    exact heq.symm

/-- Membership in every power enlargement already implies membership in
the original subgroup. The ambient group is finitely generated and abelian. -/
theorem mem_of_forall_mem_sup_powers (H : Subgroup G) (x : G)
    (h : ∀ n : ℕ+, x ∈ H ⊔ (powMonoidHom (α := G) (n : ℕ)).range) : x ∈ H := by
  apply (QuotientGroup.eq_one_iff x).mp
  apply eq_one_of_forall_exists_pow
  intro n
  obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup.mp (h n)
  obtain ⟨y, hy⟩ := hb
  refine ⟨(QuotientGroup.mk' H) y, ?_⟩
  rw [← map_pow]
  change (QuotientGroup.mk' H) (y ^ (n : ℕ)) = (QuotientGroup.mk' H) x
  change y ^ (n : ℕ) = b at hy
  have hqa : (QuotientGroup.mk' H) a = 1 := (QuotientGroup.eq_one_iff a).mpr ha
  rw [hy, ← hab, map_mul, hqa, one_mul]

/-- A subgroup of a finitely generated abelian group is recovered from all
its finite power quotients. -/
theorem iInf_sup_powers_eq (H : Subgroup G) :
    (⨅ n : ℕ+, H ⊔ (powMonoidHom (α := G) (n : ℕ)).range) = H := by
  apply le_antisymm
  · intro x hx
    exact mem_of_forall_mem_sup_powers H x (Subgroup.mem_iInf.mp hx)
  · exact le_iInf fun _ => le_sup_left

/-- Equal cyclic subgroups in every power quotient determine the same
cyclic subgroup in the original finitely generated abelian group. -/
theorem zpowers_eq_of_forall_sup_powers_eq (a b : G)
    (h : ∀ n : ℕ+,
      Subgroup.zpowers a ⊔ (powMonoidHom (α := G) (n : ℕ)).range =
      Subgroup.zpowers b ⊔ (powMonoidHom (α := G) (n : ℕ)).range) :
    Subgroup.zpowers a = Subgroup.zpowers b := by
  rw [← iInf_sup_powers_eq (Subgroup.zpowers a),
    ← iInf_sup_powers_eq (Subgroup.zpowers b)]
  exact iInf_congr h

omit [Group.FG G] in
/-- Power separation can be checked in a finitely generated subgroup that
contains every root of each of its elements. -/
theorem mem_of_forall_mem_sup_powers_of_saturated
    (S H : Subgroup G) [Group.FG S] (hHS : H ≤ S)
    (hsat : ∀ (n : ℕ+) (y : G), y ^ (n : ℕ) ∈ S → y ∈ S)
    (x : G) (hx : x ∈ S)
    (h : ∀ n : ℕ+, x ∈ H ⊔ (powMonoidHom (α := G) (n : ℕ)).range) : x ∈ H := by
  let xS : S := ⟨x, hx⟩
  have hlocal : ∀ n : ℕ+, xS ∈ H.subgroupOf S ⊔
      (powMonoidHom (α := S) (n : ℕ)).range := by
    intro n
    obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup.mp (h n)
    obtain ⟨y, hy⟩ := hb
    change y ^ (n : ℕ) = b at hy
    have hbS : b ∈ S := by
      have ht := S.mul_mem (S.inv_mem (hHS ha)) hx
      rw [← hab, inv_mul_cancel_left] at ht
      exact ht
    have hyS : y ∈ S := hsat n y (hy.symm ▸ hbS)
    apply Subgroup.mem_sup.mpr
    refine ⟨⟨a, hHS ha⟩, ha, (⟨y, hyS⟩ : S) ^ (n : ℕ), ⟨⟨y, hyS⟩, rfl⟩, ?_⟩
    apply Subtype.ext
    change a * y ^ (n : ℕ) = x
    rw [hy, hab]
  exact mem_of_forall_mem_sup_powers (H.subgroupOf S) xS hlocal

end AnabelianGeometry.KummerTheory
