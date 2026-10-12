/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.KummerTheory.CyclotomicPowerDescent
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Power classes of radicals in abelian extensions

If an n-th radical lies in an abelian Galois extension containing the n-th
roots of unity, its power-class order is the order of a root of unity in
the original base field. This follows from the explicit cyclotomic descent
calculation for every Galois automorphism; no uniform cyclotomic-image
hypothesis is supplied as an assumption.
-/

noncomputable section

open scoped IsMulCommutative

namespace AnabelianGeometry.KummerTheory

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- Every automorphism acts on the n-th roots of unity by a positive power.
The exponent is obtained from a primitive root, rather than assumed. -/
theorem exists_cyclotomic_displacement
    (n : ℕ+) (ζ : L) (hζ : IsPrimitiveRoot ζ (n : ℕ)) (σ : L ≃ₐ[K] L) :
    ∃ m : ℕ, ∀ ξ : L, ξ ^ (n : ℕ) = 1 → σ ξ = ξ ^ (m + 1) := by
  have : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  obtain ⟨e, -, he⟩ := hζ.eq_pow_of_pow_eq_one (ξ := σ ζ) (by
    rw [← map_pow, hζ.pow_eq_one, map_one])
  let m := e + (n : ℕ) - 1
  have hm : m + 1 = e + (n : ℕ) :=
    Nat.sub_add_cancel (Nat.succ_le_of_lt (Nat.add_pos_right e n.pos))
  refine ⟨m, ?_⟩
  intro ξ hξ
  have haction : σ ξ = ξ ^ e := by
    obtain ⟨j, -, hj⟩ := hζ.eq_pow_of_pow_eq_one hξ
    rw [← hj, map_pow, ← he, pow_right_comm]
  rw [haction, hm, pow_add, hξ, mul_one]

/-- The order of a radical power class in an abelian Galois extension is
realized by a primitive root of unity in the original field. -/
theorem exists_primitiveRoot_powerClass_order_of_abelian
    [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)]
    (n : ℕ+) (ζ : L) (hζ : IsPrimitiveRoot ζ (n : ℕ))
    (a : Kˣ) (r : L) (hr : r ≠ 0)
    (ha : r ^ (n : ℕ) = algebraMap K L (a : K)) :
    ∃ η : K, IsPrimitiveRoot η
      (orderOf ((QuotientGroup.mk' (powMonoidHom (α := Kˣ) (n : ℕ)).range) a)) := by
  let P : Subgroup Kˣ := (powMonoidHom (α := Kˣ) (n : ℕ)).range
  let q : Kˣ ⧸ P := (QuotientGroup.mk' P) a
  let t : ℕ := orderOf q
  have hqn : q ^ (n : ℕ) = 1 := by
    rw [show q = (QuotientGroup.mk' P) a from rfl, ← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr ⟨a, rfl⟩
  have htn : t ∣ (n : ℕ) := orderOf_dvd_of_pow_eq_one hqn
  let η : L := ζ ^ ((n : ℕ) / t)
  have hη : IsPrimitiveRoot η t :=
    IsPrimitiveRoot.pow n.pos hζ (Nat.div_mul_cancel htn).symm
  have hfixed : ∀ σ : L ≃ₐ[K] L, σ η = η := by
    intro σ
    obtain ⟨m, hσ⟩ := exists_cyclotomic_displacement n ζ hζ σ
    obtain ⟨c, hc⟩ := exists_unit_power_eq_of_abelian_cyclotomic
      n m a r hr ha σ hσ
    have hqm : q ^ m = 1 := by
      rw [show q = (QuotientGroup.mk' P) a from rfl, ← map_pow]
      exact (QuotientGroup.eq_one_iff _).mpr ⟨c, hc⟩
    have htm : t ∣ m := orderOf_dvd_of_pow_eq_one hqm
    rw [hσ η ((hη.pow_eq_one_iff_dvd (n : ℕ)).mpr htn), pow_succ,
      (hη.pow_eq_one_iff_dvd m).mpr htm, one_mul]
  obtain ⟨b, hb⟩ :=
    (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := K) (K := L) η).mpr hfixed
  refine ⟨b, ?_⟩
  have hbprim : IsPrimitiveRoot (algebraMap K L b) t := hb.symm ▸ hη
  exact hbprim.of_map_of_injective (algebraMap K L).injective

end AnabelianGeometry.KummerTheory
