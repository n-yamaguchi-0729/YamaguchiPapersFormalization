/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.Yamaguchi26AbfaithfulGalois.Theorem6Dot1FormalHilbert90
import Nyll.GaloisCohomology.ProfiniteIntegers.ZModPowerExact

/-! # Arithmetic operations on finite oriented cocycles -/

namespace Yamaguchi26AbfaithfulGalois.FiniteCocycle

universe u

variable {ℓ : ℕ} [Fact ℓ.Prime]
variable {G : Type u} [Group G] [TopologicalSpace G]
variable {θ : Orientation ℓ G} {H : Subgroup G}

/-- Reduce the coefficient values of a finite oriented cocycle to a smaller prime-power quotient. -/
def reduce {m n : ℕ} (c : FiniteCocycle θ H n) (hmn : m ≤ n) :
    FiniteCocycle θ H m where
  toFun := fun x => ZMod.castHom (pow_dvd_pow ℓ hmn) (ZMod (ℓ ^ m)) (c.toFun x)
  continuous_toFun := continuous_of_discreteTopology.comp c.continuous_toFun
  cocycle := by
    intro x y
    rw [c.cocycle, map_add, map_mul]
    congr 1
    congr 1
    exact RingHom.congr_fun (PadicInt.zmod_cast_comp_toZModPow m n hmn)
      (θ (x : G) : PadicInt ℓ)

/-- The pointwise sum of two finite oriented cocycles. -/
def add {n : ℕ} (c d : FiniteCocycle θ H n) : FiniteCocycle θ H n where
  toFun := fun x => c.toFun x + d.toFun x
  continuous_toFun := c.continuous_toFun.add d.continuous_toFun
  cocycle := by
    intro x y
    rw [c.cocycle, d.cocycle, mul_add]
    abel

/-- The pointwise difference of two finite oriented cocycles. -/
def sub {n : ℕ} (c d : FiniteCocycle θ H n) : FiniteCocycle θ H n where
  toFun := fun x => c.toFun x - d.toFun x
  continuous_toFun := c.continuous_toFun.sub d.continuous_toFun
  cocycle := by
    intro x y
    rw [c.cocycle, d.cocycle, mul_sub]
    abel

/-- The coefficient embedding induced by multiplication by ℓ. -/
def mulPrime {n : ℕ} (c : FiniteCocycle θ H n) : FiniteCocycle θ H (n + 1) where
  toFun := fun x => ZMod.mulPow ℓ n (c.toFun x)
  continuous_toFun := continuous_of_discreteTopology.comp c.continuous_toFun
  cocycle := by
    intro x y
    rw [c.cocycle, map_add]
    congr 1
    have hc := RingHom.congr_fun (PadicInt.zmod_cast_comp_toZModPow n (n + 1)
      (Nat.le_succ n)) (θ (x : G) : PadicInt ℓ)
    change ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ n)) (ZMod (ℓ ^ n))
      (PadicInt.toZModPow (n + 1) (θ (x : G) : PadicInt ℓ)) = _ at hc
    rw [← hc, ZMod.mulPow_mul_castHom]

/-- A cocycle that is zero modulo ℓ divides uniquely by ℓ. -/
theorem exists_divPrime {n : ℕ} (c : FiniteCocycle θ H (n + 1))
    (hc : ∀ x : H, ZMod.castHom (pow_dvd_pow ℓ (Nat.succ_le_succ (Nat.zero_le n)))
      (ZMod (ℓ ^ 1)) (c.toFun x) = 0) :
    ∃ d : FiniteCocycle θ H n, ∀ x : H, ZMod.mulPow ℓ n (d.toFun x) = c.toFun x := by
  classical
  let f : H → ZMod (ℓ ^ n) := fun x => Function.invFun (ZMod.mulPow ℓ n) (c.toFun x)
  have hf (x : H) : ZMod.mulPow ℓ n (f x) = c.toFun x :=
    Function.invFun_eq (ZMod.exists_mulPow_eq_of_castHom_eq_zero ℓ n (c.toFun x) (hc x))
  have hfcont : Continuous f :=
    (show Continuous (Function.invFun (ZMod.mulPow ℓ n)) from
      continuous_of_discreteTopology).comp c.continuous_toFun
  refine ⟨⟨f, hfcont, ?_⟩, hf⟩
  intro x y
  apply ZMod.mulPow_injective (Fact.out : ℓ.Prime).ne_zero n
  rw [hf, map_add]
  have hcast := RingHom.congr_fun (PadicInt.zmod_cast_comp_toZModPow n (n + 1)
    (Nat.le_succ n)) (θ (x : G) : PadicInt ℓ)
  change ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ n)) (ZMod (ℓ ^ n))
    (PadicInt.toZModPow (n + 1) (θ (x : G) : PadicInt ℓ)) = _ at hcast
  rw [← hcast, ZMod.mulPow_mul_castHom, hf, hf]
  exact c.cocycle x y

end Yamaguchi26AbfaithfulGalois.FiniteCocycle
