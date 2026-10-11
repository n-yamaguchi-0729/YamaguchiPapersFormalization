/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Yamaguchi26AbfaithfulGalois.FormalHilbert90.FiniteH1Surjectivity
import Yamaguchi26AbfaithfulGalois.FormalHilbert90.PadicCharacters
import GaloisCohomology.ProfiniteIntegers.CyclicCharacterLifting
import ProCGroups.Abelian.PrimaryTorsion

/-! # Fixed-group comparison for the trivial orientation -/

namespace Yamaguchi26AbfaithfulGalois

open ProCGroups.Abelian ProCGroups.ProC

universe u

/-- No prime torsion in the abelianization implies formal H¹ reduction
surjectivity for the trivial orientation at the fixed subgroup. -/
theorem h1Reduction_trivial_of_no_prime_torsion
    {ℓ : ℕ} [Fact ℓ.Prime]
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (H : Subgroup G) [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]
    (hH : ∀ a : TopologicalAbelianization H, a ^ ℓ = 1 → a = 1)
    (n : ℕ) (hn : 1 ≤ n) : HasH1ReductionSurjective (1 : Orientation ℓ G) H n hn := by
  let A := TopologicalAbelianization H
  have : TotallyDisconnectedSpace A :=
    ProCGroups.totallyDisconnectedSpace_quotient_closedNormal
      (Subgroup.closedCommutator H) (Subgroup.isClosed_closedCommutator H)
  have hpinj : Function.Injective (fun a : A => a ^ ℓ) := by
    intro a b hab
    change a ^ ℓ = b ^ ℓ at hab
    apply mul_inv_eq_one.mp
    apply hH
    rw [mul_pow, inv_pow, hab, mul_inv_cancel]
  have hpow (k : ℕ) : Function.Injective (fun a : A => a ^ (ℓ ^ k)) := by
    induction k with
    | zero =>
      intro a b hab
      simpa only [pow_zero, pow_one] using hab
    | succ k ih =>
      intro a b hab
      apply ih
      apply hpinj
      simpa only [← pow_mul, pow_succ] using hab
  apply h1_reduction_surjective_of_finiteCocycle_lifting
  intro c
  let χH : H →ₜ* Multiplicative (ZMod (ℓ ^ 1)) :=
    { toFun := fun h => Multiplicative.ofAdd (c.toFun h)
      map_one' := by
        have hh := c.cocycle 1 1
        simp only [one_mul, Subgroup.coe_one, Units.val_one, map_one] at hh
        exact add_eq_left.mp hh.symm
      map_mul' := by
        intro a b
        change c.toFun (a * b) = c.toFun a + c.toFun b
        exact c.cocycle a b |>.trans (by
          rw [ContinuousMonoidHom.coe_one, Pi.one_apply, Units.val_one, map_one, one_mul])
      continuous_toFun := c.continuous_toFun }
  let χ := TopologicalAbelianization.lift χH
  cases n with
  | zero => omega
  | succ k =>
    have : NeZero (ℓ ^ 1) := ⟨pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero⟩
    have : NeZero (ℓ ^ k) := ⟨pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero⟩
    have hlift (M : ℕ) (hM : ℓ ^ 1 ∣ M) (hEq : M = ℓ ^ 1 * ℓ ^ k) :
        ∃ ψ : A →ₜ* Multiplicative (ZMod M), ∀ a : A,
          ZMod.castHom hM (ZMod (ℓ ^ 1)) (ψ a).toAdd = (χ a).toAdd := by
      subst M
      exact exists_cyclic_character_lift_of_power_injective (ℓ ^ 1) (ℓ ^ k) (hpow k) χ
    obtain ⟨ψ, hψ⟩ := hlift (ℓ ^ (k + 1)) (pow_dvd_pow ℓ hn)
      (by rw [pow_one, pow_succ'])
    let d : FiniteCocycle (1 : Orientation ℓ G) H (k + 1) :=
      { toFun := fun h => (ψ (TopologicalAbelianization.mk H h)).toAdd
        continuous_toFun := ψ.continuous.comp (TopologicalAbelianization.mkₜ H).continuous
        cocycle := by
          intro a b
          rw [ContinuousMonoidHom.coe_one, Pi.one_apply, Units.val_one, map_one, one_mul]
          rw [map_mul]
          exact congrArg (fun z : Multiplicative (ZMod (ℓ ^ (k + 1))) => z.toAdd)
            (map_mul ψ _ _) }
    exact ⟨d, fun h => hψ (TopologicalAbelianization.mk H h)⟩

/-- Formal H¹ reduction surjectivity at a fixed subgroup excludes prime torsion
in its actual topological abelianization. -/
theorem no_prime_torsion_of_h1Reduction_trivial
    {ℓ : ℕ} [Fact ℓ.Prime]
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (H : Subgroup G) [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]
    (hH : ∀ n : ℕ, ∀ hn : 1 ≤ n, HasH1ReductionSurjective (1 : Orientation ℓ G) H n hn)
    (a : TopologicalAbelianization H) (ha : a ^ ℓ = 1) : a = 1 := by
  let A := TopologicalAbelianization H
  have : TotallyDisconnectedSpace A :=
    ProCGroups.totallyDisconnectedSpace_quotient_closedNormal
      (Subgroup.closedCommutator H) (Subgroup.isClosed_closedCommutator H)
  let R := proCResidualCore (ProCGroups.FiniteGroupClass.pGroup ℓ) A
  have : IsClosed (R : Set A) := proCResidualCore_isClosed _ _
  let q : A →ₜ* A ⧸ R := ⟨QuotientGroup.mk' R, QuotientGroup.continuous_mk⟩
  by_contra hne
  have hqa : q a ≠ 1 := fun h => hne
    (eq_one_of_prime_torsion_of_primaryQuotient_eq_one a ha h)
  have hP : HasOpenNormalBasisInClass (ProCGroups.FiniteGroupClass.pGroup ℓ) (A ⧸ R) :=
    proCResidualCoreQuotient_hasOpenNormalBasisInClass
      (ProCGroups.FiniteGroupClass.pGroup_formation ℓ)
  obtain ⟨n, hn, χ, hχ⟩ := exists_primePower_character_proP hP hqa
  let χA := χ.comp q
  let χH := χA.comp (TopologicalAbelianization.mkₜ H)
  let c : FiniteCocycle (1 : Orientation ℓ G) H n :=
    { toFun := fun h => (χH h).toAdd
      continuous_toFun := χH.continuous
      cocycle := by
        intro x y
        rw [ContinuousMonoidHom.coe_one, Pi.one_apply, Units.val_one, map_one, one_mul]
        exact congrArg Multiplicative.toAdd (map_mul χH x y) }
  obtain ⟨d, hd⟩ := finiteCocycle_lift_padic_of_fixed_group (1 : Orientation ℓ G) H hH n hn c
  let f : H →ₜ* Multiplicative (PadicInt ℓ) :=
    { toFun := fun h => Multiplicative.ofAdd (d.toFun h)
      map_one' := d.map_one
      map_mul' := by
        intro x y
        change d.toFun (x * y) = d.toFun x + d.toFun y
        exact d.cocycle x y |>.trans (by
          rw [ContinuousMonoidHom.coe_one, Pi.one_apply, Units.val_one, one_mul])
      continuous_toFun := d.continuous_toFun }
  let fA := TopologicalAbelianization.lift f
  have hfa : fA a = 1 := by
    apply (pow_eq_one_iff_left (a := fA a) (Fact.out : ℓ.Prime).ne_zero).mp
    rw [← map_pow, ha, map_one]
  obtain ⟨b, hb⟩ := TopologicalAbelianization.surjective_mk H a
  have hzero : d.toFun b = 0 := by
    have heq := congrArg Multiplicative.toAdd hfa
    rw [← hb] at heq
    exact heq
  apply hχ
  apply Multiplicative.toAdd.injective
  have hh := hd b
  change PadicInt.toZModPow n (d.toFun b) = (χ (q (TopologicalAbelianization.mk H b))).toAdd at hh
  rw [hzero, map_zero, hb] at hh
  exact hh.symm

/-- Under trivial-orientation lifting, p-adic characters separate every primary class. -/
theorem exists_padic_character_detecting_primary_of_h1_trivial
    {ℓ : ℕ} [Fact ℓ.Prime]
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (H : Subgroup G) [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]
    (hH : ∀ n : ℕ, ∀ hn : 1 ≤ n, HasH1ReductionSurjective (1 : Orientation ℓ G) H n hn)
    (a : PrimaryAbelianization ℓ H) (ha : a ≠ 1) :
    ∃ f : PrimaryAbelianization ℓ H →ₜ* Multiplicative (PadicInt ℓ), f a ≠ 1 := by
  let A := TopologicalAbelianization H
  have : TotallyDisconnectedSpace A :=
    ProCGroups.totallyDisconnectedSpace_quotient_closedNormal
      (Subgroup.closedCommutator H) (Subgroup.isClosed_closedCommutator H)
  let R := proCResidualCore (ProCGroups.FiniteGroupClass.pGroup ℓ) A
  have : IsClosed (R : Set A) := proCResidualCore_isClosed _ _
  let q : A →ₜ* A ⧸ R := ⟨QuotientGroup.mk' R, QuotientGroup.continuous_mk⟩
  have hP : HasOpenNormalBasisInClass (ProCGroups.FiniteGroupClass.pGroup ℓ) (A ⧸ R) :=
    proCResidualCoreQuotient_hasOpenNormalBasisInClass
      (ProCGroups.FiniteGroupClass.pGroup_formation ℓ)
  obtain ⟨n, hn, χ, hχ⟩ := exists_primePower_character_proP hP ha
  let χH := (χ.comp q).comp (TopologicalAbelianization.mkₜ H)
  let c : FiniteCocycle (1 : Orientation ℓ G) H n :=
    { toFun := fun h => (χH h).toAdd
      continuous_toFun := χH.continuous
      cocycle := by
        intro x y
        rw [ContinuousMonoidHom.coe_one, Pi.one_apply, Units.val_one, map_one, one_mul]
        exact congrArg Multiplicative.toAdd (map_mul χH x y) }
  obtain ⟨d, hd⟩ := finiteCocycle_lift_padic_of_fixed_group (1 : Orientation ℓ G) H hH n hn c
  let f : H →ₜ* Multiplicative (PadicInt ℓ) :=
    { toFun := fun h => Multiplicative.ofAdd (d.toFun h)
      map_one' := d.map_one
      map_mul' := by
        intro x y
        change d.toFun (x * y) = d.toFun x + d.toFun y
        exact d.cocycle x y |>.trans (by
          rw [ContinuousMonoidHom.coe_one, Pi.one_apply, Units.val_one, one_mul])
      continuous_toFun := d.continuous_toFun }
  let fA := liftPadicCharacter (TopologicalAbelianization.lift f)
  refine ⟨fA, ?_⟩
  intro hfa
  obtain ⟨b, hb⟩ := QuotientGroup.mk'_surjective R a
  obtain ⟨e, he⟩ := TopologicalAbelianization.surjective_mk H b
  have hzero : d.toFun e = 0 := by
    have heq := congrArg Multiplicative.toAdd hfa
    rw [← hb, ← he] at heq
    exact heq
  apply hχ
  apply Multiplicative.toAdd.injective
  have hh := hd e
  change PadicInt.toZModPow n (d.toFun e) = (χ (q (TopologicalAbelianization.mk H e))).toAdd at hh
  rw [hzero, map_zero, he] at hh
  exact (hh.trans (congrArg (fun z => (χ z).toAdd) hb)).symm

/-- The primary abelianization is torsion-free under fixed-group trivial-orientation lifting. -/
theorem primaryAbelianization_isMulTorsionFree_of_h1_trivial
    {ℓ : ℕ} [Fact ℓ.Prime]
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (H : Subgroup G) [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]
    (hH : ∀ n : ℕ, ∀ hn : 1 ≤ n, HasH1ReductionSurjective (1 : Orientation ℓ G) H n hn) :
    IsMulTorsionFree (PrimaryAbelianization ℓ H) := by
  constructor
  intro n hn x y hxy
  by_contra hne
  obtain ⟨f, hf⟩ := exists_padic_character_detecting_primary_of_h1_trivial H hH
    (x * y⁻¹) (fun h => hne (mul_inv_eq_one.mp h))
  have heq : f x = f y := by
    apply IsMulTorsionFree.pow_left_injective hn
    change f x ^ n = f y ^ n
    rw [← map_pow, ← map_pow]
    exact congrArg f hxy
  apply hf
  rw [map_mul, map_inv, heq, mul_inv_cancel]

end Yamaguchi26AbfaithfulGalois
