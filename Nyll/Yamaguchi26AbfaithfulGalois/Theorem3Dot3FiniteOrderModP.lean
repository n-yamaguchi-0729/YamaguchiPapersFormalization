/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.LocalField.Analytic.AugmentationDivisibility
import Nyll.ValuedFieldTheory.LocalField.Analytic.PrimeOrderDivisibility
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.GroupTheory.OrderOfElement

/-! # Lemma 3.3: finite-order automorphisms trivial modulo an odd prime

Source: [Yamaguchi, arXiv:2610.05634v1](https://arxiv.org/abs/2610.05634v1), Lemma 3.3.
The separation hypothesis is stated elementwise; no finite generation is assumed.
-/

namespace Yamaguchi26AbfaithfulGalois

open LocalFieldTheory.DiscreteValuationField

universe u

private theorem pow_action_sub_divisible
    {p : ℕ} [Fact p.Prime] {M : Type u} [AddCommGroup M] [Module ℤ_[p] M]
    (T : M ≃ₗ[ℤ_[p]] M)
    (hT : ∀ x : M, ∃ y : M, T x - x = (p : ℤ_[p]) • y) :
    ∀ n : ℕ, ∀ x : M, ∃ y : M, (T ^ n) x - x = (p : ℤ_[p]) • y := by
  intro n
  induction n with
  | zero =>
      intro x
      exact ⟨0, by change x - x = (p : ℤ_[p]) • (0 : M); rw [sub_self, smul_zero]⟩
  | succ n ih =>
      intro x
      obtain ⟨a, ha⟩ := ih x
      obtain ⟨b, hb⟩ := hT ((T ^ n) x)
      refine ⟨b + a, ?_⟩
      rw [smul_add, ← ha, ← hb, pow_succ']
      change T ((T ^ n) x) - x = (T ((T ^ n) x) - (T ^ n) x) + ((T ^ n) x - x)
      abel

private theorem divisible_subgroup_eq_bot
    {p : ℕ} [Fact p.Prime] {M : Type u} [AddCommGroup M] [Module ℤ_[p] M]
    (hsep : ∀ x : M, (∀ n : ℕ, 0 < n → ∃ y : M, (p : ℤ_[p]) ^ n • y = x) → x = 0)
    (J : AddSubgroup M)
    (hJ : ∀ x : M, x ∈ J → ∃ y : M, y ∈ J ∧ (p : ℤ_[p]) • y = x) : J = ⊥ := by
  have hiter : ∀ n : ℕ, ∀ x : M, x ∈ J →
      ∃ y : M, y ∈ J ∧ (p : ℤ_[p]) ^ n • y = x := by
    intro n
    induction n with
    | zero => exact fun x hx => ⟨x, hx, by rw [pow_zero, one_smul]⟩
    | succ n ih =>
        intro x hx
        obtain ⟨y, hy, hpy⟩ := hJ x hx
        obtain ⟨z, hz, hpz⟩ := ih y hy
        exact ⟨z, hz, by rw [pow_succ', mul_smul, hpz, hpy]⟩
  apply (AddSubgroup.eq_bot_iff_forall _).mpr
  intro x hx
  exact hsep x (fun n _ => let ⟨y, _, hy⟩ := hiter n x hx; ⟨y, hy⟩)

private theorem prime_order_mod_p_eq_one
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {M : Type u} [AddCommGroup M] [Module ℤ_[p] M] [Module.IsTorsionFree ℤ_[p] M]
    (hsep : ∀ x : M, (∀ n : ℕ, 0 < n → ∃ y : M, (p : ℤ_[p]) ^ n • y = x) → x = 0)
    (T : M ≃ₗ[ℤ_[p]] M) (q : ℕ) (hq : q.Prime) (horder : orderOf T = q)
    (hdiv : ∀ x : M, ∃ y : M, T x - x = (p : ℤ_[p]) • y) : T = 1 := by
  classical
  by_cases hqp : q = p
  · rw [hqp] at horder
    have : IsAddTorsionFree M := IsAddTorsionFree.of_isTorsionFree ℤ_[p] M
    let forget : (M ≃ₗ[ℤ_[p]] M) →* AddMonoid.End M :=
      { toFun := fun e => e.toLinearMap.toAddMonoidHom
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    let U : AddMonoid.End M := forget T
    have hU : U ^ p = 1 := by
      have hTp : T ^ p = 1 := by simpa only [horder] using pow_orderOf_eq_one T
      change (forget T) ^ p = 1
      rw [← map_pow, hTp, map_one]
    have haug := primeOrder_action_sub_divisible U p (Fact.out : p.Prime) hp2 hU
      (fun x => by
        change ∃ y : M, T x - x = p • y
        simpa only [Nat.cast_smul_eq_nsmul] using hdiv x)
    let J : AddSubgroup M := (U - 1).range
    have hJ : J = ⊥ := divisible_subgroup_eq_bot hsep J (by
      rintro x ⟨a, rfl⟩
      obtain ⟨b, hb⟩ := haug a
      refine ⟨U b - b, ⟨b, rfl⟩, ?_⟩
      change (p : ℤ_[p]) • (U b - b) = U a - a
      simpa only [Nat.cast_smul_eq_nsmul] using hb.symm)
    apply LinearEquiv.ext
    intro x
    exact sub_eq_zero.mp (AddSubgroup.mem_bot.mp (hJ ▸
      (show T x - x ∈ J from ⟨x, rfl⟩)))
  · have hfinite : IsOfFinOrder T := orderOf_pos_iff.mp (horder ▸ hq.pos)
    let Γ := Subgroup.zpowers T
    let e : Fin (orderOf T) ≃ Γ := finEquivZPowers hfinite
    let : Fintype Γ := Fintype.ofEquiv (Fin (orderOf T)) e
    have hcard : Fintype.card Γ = q := by
      rw [Fintype.card_congr e.symm, Fintype.card_fin, horder]
    have hunit : IsUnit (Fintype.card Γ : ℤ_[p]) :=
      PadicInt.isUnit_iff.mpr (PadicInt.norm_natCast_eq_one_iff.mpr
        (hcard ▸ (Fact.out : p.Prime).coprime_iff_not_dvd.mpr
          (fun h => hqp ((hq.dvd_iff_eq (Fact.out : p.Prime).ne_one).mp h))))
    let : Invertible (Fintype.card Γ : ℤ_[p]) := hunit.invertible
    let ρ : Representation ℤ_[p] Γ M :=
      { toFun := fun g => g.val.toLinearMap
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hρ : ∀ (g : Γ) (x : M), ∃ y : M, ρ g x - x = (p : ℤ_[p]) • y := by
      intro g x
      have hg := pow_finEquivZPowers_symm_apply hfinite g
      change ∃ y : M, g.val x - x = (p : ℤ_[p]) • y
      rw [← hg]
      exact pow_action_sub_divisible T hdiv _ x
    let J : AddSubgroup M := (LinearMap.ker ρ.averageMap).toAddSubgroup
    have hJ : J = ⊥ := divisible_subgroup_eq_bot hsep J
      (fun x hx => averageMap_ker_divisible_of_action_sub_divisible ρ (p : ℤ_[p]) hρ x hx)
    have havg (x : M) : ρ.averageMap x = x := by
      have hx : x - ρ.averageMap x ∈ J := by
        change ρ.averageMap (x - ρ.averageMap x) = 0
        rw [map_sub, ρ.averageMap_id (ρ.averageMap x) (ρ.averageMap_invariant x), sub_self]
      exact (sub_eq_zero.mp (AddSubgroup.mem_bot.mp (hJ ▸ hx))).symm
    apply LinearEquiv.ext
    intro x
    rw [← havg x]
    exact ρ.averageMap_invariant x (⟨T, Subgroup.mem_zpowers T⟩ : Γ)

/-- A finite-order automorphism of a separated torsion-free `ℤ_p`-module
which acts trivially modulo the odd prime `p` is the identity. -/
theorem finite_order_mod_p_3_3
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {M : Type u} [AddCommGroup M] [Module ℤ_[p] M] [Module.IsTorsionFree ℤ_[p] M]
    (hsep : ∀ x : M, (∀ n : ℕ, 0 < n → ∃ y : M, (p : ℤ_[p]) ^ n • y = x) → x = 0)
    (T : M ≃ₗ[ℤ_[p]] M) (hfinite : IsOfFinOrder T)
    (hdiv : ∀ x : M, ∃ y : M, T x - x = (p : ℤ_[p]) • y) : T = 1 := by
  by_contra hne
  have hn : orderOf T ≠ 1 := fun h => hne (orderOf_eq_one_iff.mp h)
  obtain ⟨q, hq, hqdvd⟩ := Nat.exists_prime_and_dvd hn
  have horder : orderOf (T ^ (orderOf T / q)) = q :=
    orderOf_pow_orderOf_div (ne_of_gt hfinite.orderOf_pos) hqdvd
  have heq := prime_order_mod_p_eq_one hp2 hsep (T ^ (orderOf T / q)) q hq horder
    (pow_action_sub_divisible T hdiv _)
  rw [heq, orderOf_one] at horder
  exact hq.ne_one horder.symm

end Yamaguchi26AbfaithfulGalois
