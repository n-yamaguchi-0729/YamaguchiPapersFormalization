/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Yamaguchi26AbfaithfulGalois.FormalHilbert90.FiniteCohomology
import Yamaguchi26AbfaithfulGalois.FormalHilbert90.FiniteCocycleOperations
import GaloisCohomology.ProfiniteIntegers.PadicInverseLimit

/-!
# Lifting cocycles for one fixed group

These are the cocycle lifting assertions used in the earlier manuscript. The
hypothesis concerns this `H` alone; no lifting on its open subgroups is
assumed. Compatible successive lifts give a continuous p-adic cocycle.
-/

namespace Yamaguchi26AbfaithfulGalois

universe u

theorem finiteCocycle_lift_succ_of_fixed_group
    {ℓ : ℕ} [Fact ℓ.Prime]
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (θ : Orientation ℓ G) (H : Subgroup G)
    (hH : ∀ n : ℕ, ∀ hn : 1 ≤ n,
      HasH1ReductionSurjective θ H n hn)
    (n : ℕ) (hn : 1 ≤ n) (c : FiniteCocycle θ H n) :
    ∃ d : FiniteCocycle θ H (n + 1),
      ∀ x : H,
        ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ n))
          (ZMod (ℓ ^ n)) (d.toFun x) = c.toFun x := by
  induction n with
  | zero => omega
  | succ n ih =>
    cases n with
    | zero =>
      exact finiteCocycle_lift_mod_one_of_h1 θ H 2 (by decide) (hH 2 (by decide)) c
    | succ k =>
      let c₁ := c.reduce (Nat.succ_le_succ (Nat.zero_le (k + 1)))
      obtain ⟨a, ha⟩ := finiteCocycle_lift_mod_one_of_h1 θ H ((k + 1) + 1 + 1)
        (by omega) (hH _ (by omega)) c₁
      let e := c.sub (a.reduce (Nat.le_succ ((k + 1) + 1)))
      have he (x : H) :
          ZMod.castHom (pow_dvd_pow ℓ (Nat.succ_le_succ (Nat.zero_le (k + 1))))
            (ZMod (ℓ ^ 1)) (e.toFun x) = 0 := by
        change ZMod.castHom _ (ZMod (ℓ ^ 1))
          (c.toFun x - ZMod.castHom _ (ZMod (ℓ ^ ((k + 1) + 1))) (a.toFun x)) = 0
        rw [map_sub]
        have hcomp :
            ZMod.castHom (pow_dvd_pow ℓ (Nat.succ_le_succ (Nat.zero_le (k + 1))))
              (ZMod (ℓ ^ 1))
              (ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ ((k + 1) + 1)))
                (ZMod (ℓ ^ ((k + 1) + 1))) (a.toFun x)) =
            ZMod.castHom (pow_dvd_pow ℓ (by omega : 1 ≤ (k + 1) + 1 + 1))
              (ZMod (ℓ ^ 1)) (a.toFun x) := by
          exact RingHom.congr_fun (ZMod.castHom_comp
            (pow_dvd_pow ℓ (Nat.succ_le_succ (Nat.zero_le (k + 1))))
            (pow_dvd_pow ℓ (Nat.le_succ ((k + 1) + 1)))) (a.toFun x)
        rw [hcomp, ha]
        exact sub_self _
      obtain ⟨b, hb⟩ := e.exists_divPrime he
      obtain ⟨b', hb'⟩ := ih (by omega) b
      refine ⟨a.add b'.mulPrime, ?_⟩
      intro x
      change ZMod.castHom _ (ZMod (ℓ ^ ((k + 1) + 1)))
        (a.toFun x + ZMod.mulPow ℓ ((k + 1) + 1) (b'.toFun x)) = c.toFun x
      rw [map_add, ZMod.castHom_mulPow, hb', hb]
      change ZMod.castHom _ (ZMod (ℓ ^ ((k + 1) + 1))) (a.toFun x) +
        (c.toFun x - ZMod.castHom _ (ZMod (ℓ ^ ((k + 1) + 1))) (a.toFun x)) = c.toFun x
      abel

theorem finiteCocycle_lift_padic_of_fixed_group
    {ℓ : ℕ} [Fact ℓ.Prime]
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (θ : Orientation ℓ G) (H : Subgroup G)
    (hH : ∀ n : ℕ, ∀ hn : 1 ≤ n,
      HasH1ReductionSurjective θ H n hn)
    (n : ℕ) (hn : 1 ≤ n) (c : FiniteCocycle θ H n) :
    ∃ d : PadicCocycle θ H,
      ∀ x : H, PadicInt.toZModPow n (d.toFun x) = c.toFun x := by
  classical
  let lift (m : ℕ) (hm : 1 ≤ m) (b : FiniteCocycle θ H m) :=
    Classical.choose (finiteCocycle_lift_succ_of_fixed_group θ H hH m hm b)
  have hlift (m : ℕ) (hm : 1 ≤ m) (b : FiniteCocycle θ H m) (x : H) :
      ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ m)) (ZMod (ℓ ^ m))
        ((lift m hm b).toFun x) = b.toFun x :=
    Classical.choose_spec (finiteCocycle_lift_succ_of_fixed_group θ H hH m hm b) x
  let seq : ∀ k : ℕ, FiniteCocycle θ H (n + k) :=
    fun k => Nat.rec c (fun k b => lift (n + k) (hn.trans (Nat.le_add_right n k)) b) k
  have hseq (k : ℕ) (x : H) :
      ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ (n + k))) (ZMod (ℓ ^ (n + k)))
        ((seq (k + 1)).toFun x) = (seq k).toFun x :=
    hlift (n + k) (hn.trans (Nat.le_add_right n k)) (seq k) x
  let f (k : ℕ) (x : H) : ZMod (ℓ ^ k) :=
    ZMod.castHom (pow_dvd_pow ℓ (Nat.le_add_left k n)) (ZMod (ℓ ^ k))
      ((seq k).toFun x)
  have hcast {a b d : ℕ} (hab : a ≤ b) (hbd : b ≤ d) (z : ZMod (ℓ ^ d)) :
      ZMod.castHom (pow_dvd_pow ℓ hab) (ZMod (ℓ ^ a))
        (ZMod.castHom (pow_dvd_pow ℓ hbd) (ZMod (ℓ ^ b)) z) =
      ZMod.castHom (pow_dvd_pow ℓ (hab.trans hbd)) (ZMod (ℓ ^ a)) z :=
    by
      change ((ZMod.castHom (pow_dvd_pow ℓ hab) (ZMod (ℓ ^ a))).comp
        (ZMod.castHom (pow_dvd_pow ℓ hbd) (ZMod (ℓ ^ b)))) z = _
      exact RingHom.congr_fun (Subsingleton.elim _ _) z
  have hfcompat (k : ℕ) (x : H) :
      ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ k)) (ZMod (ℓ ^ k))
        (f (k + 1) x) = f k x := by
    dsimp only [f]
    rw [hcast (Nat.le_succ k) (Nat.le_add_left (k + 1) n), ← hseq k x,
      hcast (Nat.le_add_left k n) (Nat.le_succ (n + k))]
  obtain ⟨d, hdcont, hd⟩ := PadicInt.exists_continuous_of_compatible_residues f
    (fun k => (continuous_of_discreteTopology).comp (seq k).continuous_toFun) hfcompat
  have hdcocycle (x y : H) : d (x * y) = d x + (θ (x : G) : PadicInt ℓ) * d y := by
    apply PadicInt.ext_of_toZModPow.mp
    intro k
    rw [map_add, map_mul, hd, hd, hd]
    dsimp only [f]
    rw [(seq k).cocycle, map_add, map_mul]
    congr 1
    congr 1
    exact RingHom.congr_fun (PadicInt.zmod_cast_comp_toZModPow k (n + k)
      (Nat.le_add_left k n)) (θ (x : G) : PadicInt ℓ)
  refine ⟨⟨d, hdcont, hdcocycle⟩, ?_⟩
  intro x
  change PadicInt.toZModPow n (d x) = c.toFun x
  rw [hd]
  have hbase (k : ℕ) :
      ZMod.castHom (pow_dvd_pow ℓ (Nat.le_add_right n k)) (ZMod (ℓ ^ n))
        ((seq k).toFun x) = c.toFun x := by
    induction k with
    | zero =>
      change (ZMod.castHom (dvd_refl (ℓ ^ n)) (ZMod (ℓ ^ n))) (c.toFun x) = c.toFun x
      exact RingHom.congr_fun (Subsingleton.elim _ (RingHom.id (ZMod (ℓ ^ n)))) _
    | succ k ih =>
      rw [← ih, ← hseq k x, hcast (Nat.le_add_right n k) (Nat.le_succ (n + k))]
  exact hbase n

end Yamaguchi26AbfaithfulGalois
