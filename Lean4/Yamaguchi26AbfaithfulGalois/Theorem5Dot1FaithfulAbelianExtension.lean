/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.ULift
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.Basic.Finite.Prod
import Mathlib.Data.Fintype.Pi

/-!
# Lemma 5.1: faithful abelian extensions with bounded derived length

TeX label: `lem:faithful-abelian-extension-solvable-length`.
We use the finite group of functions with constant right differences along the
last derived subgroup. It contains the manuscript's `W` and transversal function.
Its difference map is invariant under left translation; its kernel consists of
functions on the quotient. This gives the same bound on the derived length.
-/

namespace Yamaguchi26AbfaithfulGalois
namespace FaithfulAbelianExtension

universe u v

variable {A : Type u} [Group A] (D : Subgroup A)
variable (M : Type v) [CommGroup M]

/-- Functions whose right difference along `D` is independent of the base point. -/
def functions : Subgroup (A → M) where
  carrier := {f | ∀ (x y : A) (d : D), f (x * d) * f y = f (y * d) * f x}
  one_mem' := by
    intro x y d
    rfl
  mul_mem' := by
    intro f g hf hg x y d
    change (f (x * d) * g (x * d)) * (f y * g y) =
      (f (y * d) * g (y * d)) * (f x * g x)
    calc
      _ = (f (x * d) * f y) * (g (x * d) * g y) := by ac_rfl
      _ = (f (y * d) * f x) * (g (y * d) * g x) := by rw [hf x y d, hg x y d]
      _ = _ := by ac_rfl
  inv_mem' := by
    intro f hf x y d
    change (f (x * d))⁻¹ * (f y)⁻¹ = (f (y * d))⁻¹ * (f x)⁻¹
    rw [← mul_inv, ← mul_inv, hf x y d]

/-- Left translation preserves constant right differences. -/
def translate (a : A) : MulAut (functions D M) where
  toFun f := ⟨fun x => f.val (a⁻¹ * x), by
    intro x y d
    simpa only [mul_assoc] using f.property (a⁻¹ * x) (a⁻¹ * y) d⟩
  invFun f := ⟨fun x => f.val (a * x), by
    intro x y d
    simpa only [mul_assoc] using f.property (a * x) (a * y) d⟩
  left_inv f := by
    apply Subtype.ext
    funext x
    change f.val (a⁻¹ * (a * x)) = f.val x
    rw [inv_mul_cancel_left]
  right_inv f := by
    apply Subtype.ext
    funext x
    change f.val (a * (a⁻¹ * x)) = f.val x
    rw [mul_inv_cancel_left]
  map_mul' f g := rfl

/-- The translation action on the constructed abelian group. -/
def action : A →* MulAut (functions D M) where
  toFun := translate D M
  map_one' := by
    apply MulEquiv.ext
    intro f
    apply Subtype.ext
    funext x
    change f.val ((1 : A)⁻¹ * x) = f.val x
    rw [inv_one, one_mul]
  map_mul' a b := by
    apply MulEquiv.ext
    intro f
    apply Subtype.ext
    funext x
    change f.val ((a * b)⁻¹ * x) = f.val (b⁻¹ * (a⁻¹ * x))
    rw [mul_inv_rev, mul_assoc]

/-- The right differences, regarded as a homomorphism to an abelian function group. -/
def difference : functions D M →* (D → M) where
  toFun f d := f.val d / f.val 1
  map_one' := by
    funext d
    exact one_div_one
  map_mul' f g := by
    funext d
    change (f.val d * g.val d) / (f.val 1 * g.val 1) = (f.val d / f.val 1) * (g.val d / g.val 1)
    rw [div_mul_div_comm]

/-- Left translation leaves every right difference unchanged. -/
theorem difference_action (a : A) (f : functions D M) :
    difference D M (action D M a f) = difference D M f := by
  funext d
  change f.val (a⁻¹ * d) / f.val (a⁻¹ * 1) = f.val d / f.val 1
  rw [mul_one, div_eq_div_iff_mul_eq_mul]
  simpa only [one_mul] using f.property a⁻¹ 1 d

/-- Trivial right differences mean that a function is constant on right cosets. -/
theorem constant_of_difference_eq_one (f : functions D M)
    (hf : difference D M f = 1) (x : A) (d : D) :
    f.val (x * d) = f.val x := by
  have hd : f.val d = f.val 1 := div_eq_one.mp (congrFun hf d)
  have h := f.property x 1 d
  rw [one_mul, hd, mul_comm (f.val 1)] at h
  exact mul_right_cancel h

/-- Normality identifies left and right cosets, so `D` fixes the difference kernel. -/
theorem action_eq_self_of_difference_eq_one [D.Normal]
    (a : D) (f : functions D M) (hf : difference D M f = 1) :
    action D M (a : A) f = f := by
  apply Subtype.ext
  funext x
  let d : D := ⟨x⁻¹ * (a : A)⁻¹ * x,
    by
      simpa only [inv_inv] using
        (inferInstance : D.Normal).conj_mem (a : A)⁻¹ (D.inv_mem a.property) x⁻¹⟩
  have h := constant_of_difference_eq_one D M f hf x d
  change f.val (x * (x⁻¹ * (a : A)⁻¹ * x)) = f.val x at h
  rw [← mul_assoc x, mul_inv_cancel_left] at h
  exact h

/-- The coordinate of an element relative to a chosen right-coset representative. -/
noncomputable def coordinate [D.Normal] (x : A) : D :=
  ⟨(QuotientGroup.mk' D x).out⁻¹ * x, by
    apply (QuotientGroup.eq_one_iff (N := D) _).mp
    change QuotientGroup.mk' D ((QuotientGroup.mk' D x).out⁻¹ * x) = 1
    rw [map_mul, map_inv]
    have hout : QuotientGroup.mk' D (QuotientGroup.mk' D x).out =
        QuotientGroup.mk' D x := Quotient.out_eq _
    rw [hout, inv_mul_cancel]⟩

/-- Right multiplication by `D` multiplies the transversal coordinate by the same element. -/
theorem coordinate_mul [D.Normal] (x : A) (d : D) :
    coordinate D (x * d) = coordinate D x * d := by
  apply Subtype.ext
  change (QuotientGroup.mk' D (x * d)).out⁻¹ * (x * d) =
    ((QuotientGroup.mk' D x).out⁻¹ * x) * d
  have hd : QuotientGroup.mk' D (d : A) = 1 :=
    (QuotientGroup.eq_one_iff (N := D) _).mpr d.property
  rw [map_mul, hd, mul_one, mul_assoc]

/-- A coefficient group containing `D` detects the part of the action missed
by quotient functions. -/
theorem action_injective [D.Normal] [Nontrivial M]
    (ι : D →* M) (hι : Function.Injective ι) :
    Function.Injective (action D M) := by
  classical
  apply (injective_iff_map_eq_one (action D M)).mpr
  intro a ha
  have hfix (f : functions D M) : f.val (a⁻¹) = f.val 1 := by
    have h := congrArg (fun e : MulAut (functions D M) => (e f).val 1) ha
    change f.val (a⁻¹ * 1) = f.val 1 at h
    simpa only [mul_one] using h
  obtain ⟨c, hc⟩ := exists_ne (1 : M)
  let w : functions D M := ⟨fun x => if QuotientGroup.mk' D x = 1 then c else 1, by
    intro x y d
    have hd : QuotientGroup.mk' D (d : A) = 1 :=
      (QuotientGroup.eq_one_iff (N := D) _).mpr d.property
    simp only [map_mul, hd, mul_one]
    exact mul_comm _ _⟩
  have haD : a ∈ D := by
    have hw := hfix w
    change (if QuotientGroup.mk' D a⁻¹ = 1 then c else 1) =
      (if QuotientGroup.mk' D 1 = 1 then c else 1) at hw
    rw [map_one, ite_eq_left rfl] at hw
    have hinv : QuotientGroup.mk' D a⁻¹ = 1 := by
      by_contra h
      rw [ite_eq_right h] at hw
      exact hc hw.symm
    exact D.inv_mem_iff.mp ((QuotientGroup.eq_one_iff (N := D) _).mp hinv)
  let f : functions D M := ⟨fun x => ι (coordinate D x), by
    intro x y d
    change ι (coordinate D (x * d)) * ι (coordinate D y) =
      ι (coordinate D (y * d)) * ι (coordinate D x)
    rw [coordinate_mul, coordinate_mul, map_mul, map_mul]
    calc
      _ = (ι (coordinate D x) * ι (coordinate D y)) * ι d := mul_right_comm _ _ _
      _ = (ι (coordinate D y) * ι (coordinate D x)) * ι d := by
        rw [mul_comm (ι (coordinate D x)) (ι (coordinate D y))]
      _ = _ := (mul_right_comm _ _ _).symm⟩
  have hf := hι (hfix f)
  have hcoord := coordinate_mul D 1 (⟨a⁻¹, D.inv_mem haD⟩ : D)
  rw [one_mul] at hcoord
  rw [hcoord] at hf
  have hi : (⟨a⁻¹, D.inv_mem haD⟩ : D) = 1 := mul_left_cancel (hf.trans (mul_one _).symm)
  exact inv_eq_one.mp (congrArg Subtype.val hi)

/-- The difference homomorphism extends across the semidirect product
because its action is trivial. -/
def extensionDifference : (functions D M) ⋊[action D M] A →* (D → M) where
  toFun b := difference D M b.left
  map_one' := map_one (difference D M)
  map_mul' b c := by
    change difference D M (b.left * action D M b.right c.left) = _
    rw [map_mul, difference_action]

/-- The first derived subgroup has trivial differences. -/
theorem difference_eq_one_of_mem_derived
    {b : (functions D M) ⋊[action D M] A}
    (hb : b ∈ derivedSeries ((functions D M) ⋊[action D M] A) 1) :
    difference D M b.left = 1 :=
  Abelianization.commutator_subset_ker (extensionDifference D M) hb

end FaithfulAbelianExtension

universe u

/-- Lemma 5.1: every finite group of derived length at most `m ≥ 2` has a
faithful action on a finite abelian group whose semidirect product has the same bound. -/
theorem faithful_abelian_extension_solvable_length
    (A : Type u) [Group A] [Finite A] (m : ℕ) (hm : 2 ≤ m)
    (hA : derivedSeries A m = ⊥) :
    ∃ (C : Type u) (_ : CommGroup C) (_ : Finite C) (φ : A →* MulAut C),
      Function.Injective φ ∧ derivedSeries (C ⋊[φ] A) m = ⊥ := by
  classical
  let D := derivedSeries A (m - 1)
  have hD : ⁅D, D⁆ = ⊥ := by
    change derivedSeries A ((m - 1) + 1) = ⊥
    rw [Nat.sub_add_cancel (by omega)]
    exact hA
  let : CommGroup D :=
    { (inferInstance : Group D) with
      mul_comm := by
        intro x y
        apply Subtype.ext
        apply commutatorElement_eq_one_iff_mul_comm.mp
        have h := Subgroup.commutator_mem_commutator x.property y.property
        rw [hD] at h
        exact Subgroup.mem_bot.mp h }
  let M := D × ULift.{u} (Multiplicative (ZMod 2))
  let C := FaithfulAbelianExtension.functions D M
  let φ : A →* MulAut C := FaithfulAbelianExtension.action D M
  let ι : D →* M := (MonoidHom.id D).prod (1 : D →* ULift.{u} (Multiplicative (ZMod 2)))
  have hι : Function.Injective ι := by
    intro x y h
    exact congrArg Prod.fst h
  refine ⟨C, inferInstance, inferInstance,
    φ, FaithfulAbelianExtension.action_injective D M ι hι, ?_⟩
  have hright {b : C ⋊[φ] A} (hb : b ∈ derivedSeries (C ⋊[φ] A) (m - 1)) :
      b.right ∈ D :=
    map_derivedSeries_le_derivedSeries (SemidirectProduct.rightHom : C ⋊[φ] A →* A)
      (m - 1) ⟨b, hb, rfl⟩
  have hdiff {b : C ⋊[φ] A} (hb : b ∈ derivedSeries (C ⋊[φ] A) (m - 1)) :
      FaithfulAbelianExtension.difference D M b.left = 1 :=
    FaithfulAbelianExtension.difference_eq_one_of_mem_derived D M
      (derivedSeries_antitone (C ⋊[φ] A) (by omega : 1 ≤ m - 1) hb)
  rw [show m = (m - 1) + 1 from (Nat.sub_add_cancel (by omega)).symm,
    derivedSeries_succ]
  apply le_antisymm _ bot_le
  apply Subgroup.commutator_le.mpr
  intro x hx y hy
  apply Subgroup.mem_bot.mpr
  apply commutatorElement_eq_one_iff_mul_comm.mpr
  apply SemidirectProduct.ext
  · change x.left * φ x.right y.left = y.left * φ y.right x.left
    rw [FaithfulAbelianExtension.action_eq_self_of_difference_eq_one D M
      ⟨x.right, hright hx⟩ y.left (hdiff hy),
      FaithfulAbelianExtension.action_eq_self_of_difference_eq_one D M
        ⟨y.right, hright hy⟩ x.left (hdiff hx), mul_comm]
  · exact congrArg Subtype.val (mul_comm (⟨x.right, hright hx⟩ : D) ⟨y.right, hright hy⟩)

end Yamaguchi26AbfaithfulGalois
