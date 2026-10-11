/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.AbelianSchemePropertyBundle
import Nyll.AlgebraicCurves.Geometry.Picard.exists_comp_eq_of_isOpenImmersion_of_abelianSchemePropertyBundle
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Smooth.Basic

/-!
# Constancy of morphisms from the affine line to an abelian variety

Extend the map `(x,y) ↦ q(x/y)` from `D(y)` to the affine plane. Pulling
this extension back by `(x,y) ↦ (xy,y)` agrees with `q(x)` on `D(y)`, hence
everywhere by separatedness. Restriction to `y = 0` proves constancy.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Polynomial

namespace GoodReductionJacobian

namespace AffineLineConstancy

variable (k : Type u) [Field k]

private abbrev Plane := k[X][X]
private abbrev Chart := Localization.Away (Polynomial.X : Plane k)

private def scaling : Plane k →+* Plane k :=
  Polynomial.eval₂RingHom
    (Polynomial.eval₂RingHom (algebraMap k (Plane k))
      (Polynomial.C Polynomial.X * Polynomial.X)) Polynomial.X

private lemma scaling_X : scaling k Polynomial.X = Polynomial.X :=
  Polynomial.eval₂_X _ _

private lemma scaling_C (p : k[X]) : scaling k (Polynomial.C p) =
    Polynomial.eval₂RingHom (algebraMap k (Plane k))
      (Polynomial.C Polynomial.X * Polynomial.X) p :=
  Polynomial.eval₂_C _ _

private lemma scaling_C_C (a : k) :
    scaling k (Polynomial.C (Polynomial.C a)) = Polynomial.C (Polynomial.C a) := by
  rw [scaling_C, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
  rfl

private def scalingChart : Chart k →+* Chart k :=
  IsLocalization.Away.lift (Polynomial.X : Plane k)
    (show IsUnit (((algebraMap (Plane k) (Chart k)).comp (scaling k)) Polynomial.X) by
      change IsUnit (algebraMap (Plane k) (Chart k) (scaling k Polynomial.X))
      rw [scaling_X]
      exact IsLocalization.Away.algebraMap_isUnit (Polynomial.X : Plane k))

private lemma scalingChart_comp :
    (scalingChart k).comp (algebraMap (Plane k) (Chart k)) =
      (algebraMap (Plane k) (Chart k)).comp (scaling k) :=
  IsLocalization.Away.lift_comp _ _

private lemma scalingChart_apply (p : Plane k) :
    scalingChart k (algebraMap (Plane k) (Chart k) p) =
      algebraMap (Plane k) (Chart k) (scaling k p) :=
  RingHom.congr_fun (scalingChart_comp k) p

private lemma scalingChart_invSelf :
    scalingChart k (IsLocalization.Away.invSelf (Polynomial.X : Plane k)) =
      IsLocalization.Away.invSelf (Polynomial.X : Plane k) := by
  apply (IsLocalization.Away.algebraMap_isUnit
    (S := Chart k) (Polynomial.X : Plane k)).mul_left_cancel
  have h := congrArg (scalingChart k)
    (IsLocalization.Away.mul_invSelf (S := Chart k) (Polynomial.X : Plane k))
  rw [map_mul, map_one, scalingChart_apply, scaling_X] at h
  exact h.trans (IsLocalization.Away.mul_invSelf (S := Chart k)
    (Polynomial.X : Plane k)).symm

private def ratio : k[X] →+* Chart k :=
  Polynomial.eval₂RingHom (algebraMap k (Chart k))
    (algebraMap (Plane k) (Chart k) (Polynomial.C Polynomial.X) *
      IsLocalization.Away.invSelf (Polynomial.X : Plane k))

private lemma ratio_C (a : k) : ratio k (Polynomial.C a) = algebraMap k (Chart k) a :=
  Polynomial.eval₂_C _ _

private lemma scalingChart_ratio :
    (scalingChart k).comp (ratio k) =
      (algebraMap (Plane k) (Chart k)).comp Polynomial.C := by
  apply Polynomial.ringHom_ext'
  · apply RingHom.ext
    intro a
    change scalingChart k (ratio k (Polynomial.C a)) =
      algebraMap (Plane k) (Chart k) (Polynomial.C (Polynomial.C a))
    rw [ratio_C, IsScalarTower.algebraMap_apply k (Plane k) (Chart k),
      scalingChart_apply]
    change algebraMap (Plane k) (Chart k)
      (scaling k (Polynomial.C (Polynomial.C a))) = _
    rw [scaling_C_C]
  · change scalingChart k (ratio k Polynomial.X) =
      algebraMap (Plane k) (Chart k) (Polynomial.C Polynomial.X)
    rw [ratio, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, map_mul,
      scalingChart_apply, scaling_C,
      Polynomial.coe_eval₂RingHom,
      Polynomial.eval₂_X, map_mul, scalingChart_invSelf, mul_assoc,
      IsLocalization.Away.mul_invSelf, mul_one]

private lemma scaling_comp_base :
    (scaling k).comp (algebraMap k (Plane k)) = algebraMap k (Plane k) := by
  apply RingHom.ext
  intro a
  exact scaling_C_C k a

private lemma ratio_comp_base :
    (ratio k).comp (algebraMap k k[X]) = algebraMap k (Chart k) := by
  apply RingHom.ext
  intro a
  exact ratio_C k a

private def zeroLine : Plane k →+* k[X] := Polynomial.evalRingHom 0
private def origin : Plane k →+* k := (Polynomial.evalRingHom 0).comp (zeroLine k)

private lemma zeroLine_comp_scaling :
    (zeroLine k).comp (scaling k) =
      (algebraMap k k[X]).comp (origin k) := by
  apply Polynomial.ringHom_ext'
  · apply Polynomial.ringHom_ext'
    · apply RingHom.ext
      intro a
      simp only [RingHom.comp_apply, scaling_C_C, zeroLine, origin,
        Polynomial.coe_evalRingHom, Polynomial.eval_C, Polynomial.algebraMap_eq]
    · simp only [RingHom.comp_apply, scaling_C, Polynomial.coe_eval₂RingHom,
        Polynomial.eval₂_X, zeroLine,
        origin, Polynomial.coe_evalRingHom, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_X, mul_zero, Polynomial.algebraMap_eq, map_zero]
  · simp only [RingHom.comp_apply, scaling_X, zeroLine, origin,
      Polynomial.coe_evalRingHom, Polynomial.eval_X, map_zero]

private lemma zeroLine_comp_C : (zeroLine k).comp Polynomial.C = RingHom.id k[X] := by
  apply RingHom.ext
  intro p
  exact Polynomial.eval_C

private lemma origin_comp_base :
    (origin k).comp (algebraMap k (Plane k)) = RingHom.id k := by
  ext a
  change Polynomial.eval 0 (Polynomial.eval 0 (Polynomial.C (Polynomial.C a))) = a
  rw [Polynomial.eval_C, Polynomial.eval_C]

end AffineLineConstancy

open AffineLineConstancy in
/-- Every morphism over a field from the affine line to an abelian variety is constant. -/
theorem exists_eq_const_of_affineLine
    (k : Type u) [Field k] {A : Scheme.{u}} {fA : A ⟶ Spec (CommRingCat.of k)}
    (hA : AbelianSchemePropertyBundle k fA)
    (q : Spec (CommRingCat.of k[X]) ⟶ A)
    (hq : q ≫ fA = Spec.map (CommRingCat.ofHom (algebraMap k k[X]))) :
    ∃ a : Spec (CommRingCat.of k) ⟶ A,
      a ≫ fA = 𝟙 _ ∧ q = Spec.map (CommRingCat.ofHom (algebraMap k k[X])) ≫ a := by
  let π₁ := Spec.map (CommRingCat.ofHom (algebraMap k k[X]))
  let π₂ := Spec.map (CommRingCat.ofHom (algebraMap k (Plane k)))
  let i := Spec.map (CommRingCat.ofHom (algebraMap (Plane k) (Chart k)))
  let ρ := Spec.map (CommRingCat.ofHom (ratio k))
  let s := Spec.map (CommRingCat.ofHom (scaling k))
  let s' := Spec.map (CommRingCat.ofHom (scalingChart k))
  let p := Spec.map (CommRingCat.ofHom (Polynomial.C : k[X] →+* Plane k))
  let z := Spec.map (CommRingCat.ofHom (zeroLine k))
  let o := Spec.map (CommRingCat.ofHom (origin k))
  have hpi : p ≫ π₁ = π₂ := by
    rw [← Spec.map_comp]
    rfl
  have hsi : s ≫ π₂ = π₂ := by
    change Spec.map (CommRingCat.ofHom (scaling k)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k (Plane k))) = _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, scaling_comp_base]
  have hρi : ρ ≫ π₁ = i ≫ π₂ := by
    change Spec.map (CommRingCat.ofHom (ratio k)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k k[X])) = _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ratio_comp_base]
    change _ = Spec.map (CommRingCat.ofHom (algebraMap (Plane k) (Chart k))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k (Plane k)))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  have his : i ≫ s = s' ≫ i := by
    change Spec.map (CommRingCat.ofHom (algebraMap (Plane k) (Chart k))) ≫
      Spec.map (CommRingCat.ofHom (scaling k)) =
      Spec.map (CommRingCat.ofHom (scalingChart k)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (Plane k) (Chart k)))
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp, scalingChart_comp]
  have hsρ : s' ≫ ρ = i ≫ p := by
    change Spec.map (CommRingCat.ofHom (scalingChart k)) ≫
      Spec.map (CommRingCat.ofHom (ratio k)) =
      Spec.map (CommRingCat.ofHom (algebraMap (Plane k) (Chart k))) ≫
      Spec.map (CommRingCat.ofHom (Polynomial.C : k[X] →+* Plane k))
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp, scalingChart_ratio]
  have hz : z ≫ p = 𝟙 _ := by
    change Spec.map (CommRingCat.ofHom (zeroLine k)) ≫
      Spec.map (CommRingCat.ofHom (Polynomial.C : k[X] →+* Plane k)) = _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, zeroLine_comp_C]
    exact Spec.map_id _
  have hzs : z ≫ s = π₁ ≫ o := by
    change Spec.map (CommRingCat.ofHom (zeroLine k)) ≫
      Spec.map (CommRingCat.ofHom (scaling k)) =
      Spec.map (CommRingCat.ofHom (algebraMap k k[X])) ≫
      Spec.map (CommRingCat.ofHom (origin k))
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp, zeroLine_comp_scaling]
  have ho : o ≫ π₂ = 𝟙 _ := by
    change Spec.map (CommRingCat.ofHom (origin k)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k (Plane k))) = _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, origin_comp_base]
    exact Spec.map_id _
  have : Algebra.Smooth k k[X] := ⟨inferInstance, inferInstance⟩
  have : Algebra.Smooth k[X] (Plane k) := ⟨inferInstance, inferInstance⟩
  have : Algebra.Smooth k (Plane k) := Algebra.Smooth.comp k k[X] (Plane k)
  have : Smooth π₂ := by
    rw [HasRingHomProperty.Spec_iff (P := @Smooth), CommRingCat.hom_ofHom,
      RingHom.smooth_algebraMap]
    infer_instance
  have : IsDomain (Chart k) := IsLocalization.Away.isDomain
    (R := Plane k) (x := Polynomial.X) (Chart k) Polynomial.X_ne_zero
  have : IsOpenImmersion i := inferInstance
  have : IsDominant i := ⟨(i.opensRange).2.dense
    ⟨i (Classical.arbitrary (Spec (CommRingCat.of (Chart k)))),
      ⟨Classical.arbitrary (Spec (CommRingCat.of (Chart k))), rfl⟩⟩⟩
  have : IsProper fA := hA.proper
  obtain ⟨ψ, hψbase, hψ⟩ :=
    AlgebraicGeometry.exists_comp_eq_of_isOpenImmersion_of_abelianSchemePropertyBundle
      π₂ hA i (ρ ≫ q) (by rw [Category.assoc, hq]; exact hρi)
  have hscale : s ≫ ψ = p ≫ q := by
    refine ext_of_isDominant_of_isSeparated fA ?_ i ?_
    · rw [Category.assoc, hψbase, hsi, Category.assoc, hq, hpi]
    · rw [← Category.assoc i s, his, Category.assoc, hψ,
        ← Category.assoc s' ρ, hsρ, Category.assoc]
  refine ⟨o ≫ ψ, ?_, ?_⟩
  · rw [Category.assoc, hψbase, ho]
  · change q = π₁ ≫ o ≫ ψ
    calc
      q = (z ≫ p) ≫ q := by rw [hz, Category.id_comp]
      _ = z ≫ (s ≫ ψ) := by rw [hscale, Category.assoc]
      _ = π₁ ≫ o ≫ ψ := by rw [← Category.assoc, hzs, Category.assoc]

end GoodReductionJacobian
