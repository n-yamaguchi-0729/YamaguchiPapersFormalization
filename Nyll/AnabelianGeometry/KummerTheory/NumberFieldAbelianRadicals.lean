/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.KummerTheory.AbelianRadicalPowerClasses
import Mathlib.NumberTheory.NumberField.Units.Basic
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic

/-!
# A uniform bound for radicals in abelian extensions of number fields

The number of roots of unity in the original number field annihilates
any power class that acquires a radical in an abelian Galois extension
containing the relevant roots of unity. The bound is independent of the
radical exponent and the extension.
-/

noncomputable section

open scoped NumberField IsMulCommutative

namespace AnabelianGeometry.KummerTheory

variable {K : Type*} [Field K]

/-- The order of a primitive root in a number field divides the number of
roots of unity of that field. -/
theorem primitiveRoot_order_dvd_torsionOrder
    (n : ℕ+) (ζ : K) (hζ : IsPrimitiveRoot ζ (n : ℕ)) :
    (n : ℕ) ∣ NumberField.Units.torsionOrder K := by
  let ζO : 𝓞 K := hζ.toInteger
  have hζO : IsPrimitiveRoot ζO (n : ℕ) := hζ.toInteger_isPrimitiveRoot
  let hu : IsUnit ζO := hζO.isUnit n.ne_zero
  let u : (𝓞 K)ˣ := hu.unit
  have huprim : IsPrimitiveRoot u (n : ℕ) := by
    rw [← IsPrimitiveRoot.coe_units_iff]
    change IsPrimitiveRoot (hu.unit : 𝓞 K) (n : ℕ)
    rw [hu.unit_spec]
    exact hζO
  have hut : u ∈ NumberField.Units.torsion K := by
    rw [NumberField.Units.torsion, CommGroup.mem_torsion, isOfFinOrder_iff_pow_eq_one]
    exact ⟨n, n.pos, huprim.pow_eq_one⟩
  exact huprim.dvd_of_pow_eq_one _ (NumberField.Units.pow_torsionOrder_eq_one K hut)

/-- The roots-of-unity order of the original number field uniformly kills
the power class of every radical in an abelian Galois extension containing
all roots of unity of the relevant order. -/
theorem exists_unit_power_torsionOrder_of_abelian
    [NumberField K] {L : Type*} [Field L] [Algebra K L] [IsGalois K L]
    [IsMulCommutative (L ≃ₐ[K] L)]
    (n : ℕ+) (ζ : L) (hζ : IsPrimitiveRoot ζ (n : ℕ))
    (a : Kˣ) (r : L) (hr : r ≠ 0)
    (ha : r ^ (n : ℕ) = algebraMap K L (a : K)) :
    ∃ c : Kˣ, c ^ (n : ℕ) = a ^ NumberField.Units.torsionOrder K := by
  let P : Subgroup Kˣ := (powMonoidHom (α := Kˣ) (n : ℕ)).range
  let q : Kˣ ⧸ P := (QuotientGroup.mk' P) a
  let t : ℕ := orderOf q
  have hqn : q ^ (n : ℕ) = 1 := by
    rw [show q = (QuotientGroup.mk' P) a from rfl, ← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr ⟨a, rfl⟩
  have htn : t ∣ (n : ℕ) := orderOf_dvd_of_pow_eq_one hqn
  have ht : 0 < t := Nat.pos_of_ne_zero (by
    intro ht0
    rw [ht0, zero_dvd_iff] at htn
    exact n.ne_zero htn)
  obtain ⟨η, hη⟩ := exists_primitiveRoot_powerClass_order_of_abelian n ζ hζ a r hr ha
  have htw : t ∣ NumberField.Units.torsionOrder K :=
    primitiveRoot_order_dvd_torsionOrder ⟨t, ht⟩ η hη
  have hqw : q ^ NumberField.Units.torsionOrder K = 1 := by
    obtain ⟨k, hk⟩ := htw
    rw [hk]
    change q ^ (orderOf q * k) = 1
    rw [pow_mul, pow_orderOf_eq_one, one_pow]
  have haPow : a ^ NumberField.Units.torsionOrder K ∈ P := by
    apply (QuotientGroup.eq_one_iff _).mp
    change (QuotientGroup.mk' P) (a ^ NumberField.Units.torsionOrder K) = 1
    rw [map_pow]
    exact hqw
  exact haPow

end AnabelianGeometry.KummerTheory
