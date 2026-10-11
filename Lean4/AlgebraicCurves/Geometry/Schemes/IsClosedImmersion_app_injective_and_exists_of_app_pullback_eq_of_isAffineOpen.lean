/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_IsClosedImmersion_app_injective_and_exists_of_app_pullback_eq_of_isAffineOpen.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
import Mathlib.CategoryTheory.EqToHom
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Set

/-!
# Is Closed Immersion app injective and exists of app pullback eq of is Affine Open
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs
namespace IsClosedImmersion_app_injective_and_exists_of_app_pullback_eq_of_isAffineOpen


open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry


universe u

namespace AlgebraicGeometry

export _root_.AlgebraicGeometry (Scheme.Hom.congr_app Scheme.IdealSheafData.ideal_bot
  Scheme.IdealSheafData.ideal_mul Scheme.Hom.le_ker_comp Scheme.Hom Scheme
  Scheme.IdealSheafData.ker_subschemeι IsClosedImmersion IsReduced Scheme.Hom.comp_app
  IsClosedImmersion.lift IsClosedImmersion.lift_fac Scheme.IdealSheafData.support_mul IsAffineOpen
  Scheme.Hom.ker_apply Scheme.Hom.comp_preimage Scheme.IdealSheafData.support_eq_top_iff
  Scheme.IdealSheafData.ideal_sup Scheme.IdealSheafData)

namespace TwoClosedAux

open _root_.AlgebraicGeometry


variable {X Y₁ Y₂ : Scheme.{u}} (i₁ : Y₁ ⟶ X) (i₂ : Y₂ ⟶ X) [IsClosedImmersion i₁]
  [IsClosedImmersion i₂]

theorem ker_pullback_fst_comp :
    (pullback.fst i₁ i₂ ≫ i₁).ker = i₁.ker ⊔ i₂.ker := by
  apply le_antisymm
  · set J : X.IdealSheafData := i₁.ker ⊔ i₂.ker
    have h₁ : i₁.ker ≤ J.subschemeι.ker :=
      by rw [Scheme.IdealSheafData.ker_subschemeι]; exact le_sup_left
    have h₂ : i₂.ker ≤ J.subschemeι.ker :=
      by rw [Scheme.IdealSheafData.ker_subschemeι]; exact le_sup_right
    let z : J.subscheme ⟶ pullback i₁ i₂ :=
      pullback.lift (IsClosedImmersion.lift i₁ J.subschemeι h₁) (IsClosedImmersion.lift i₂
        J.subschemeι h₂)
        (by rw [IsClosedImmersion.lift_fac, IsClosedImmersion.lift_fac])
    have hz : z ≫ (pullback.fst i₁ i₂ ≫ i₁) = J.subschemeι := by
      rw [← Category.assoc, pullback.lift_fst, IsClosedImmersion.lift_fac]
    calc (pullback.fst i₁ i₂ ≫ i₁).ker ≤ (z ≫ (pullback.fst i₁ i₂ ≫ i₁)).ker :=
      Scheme.Hom.le_ker_comp _ _
      _ = J := by rw [hz, Scheme.IdealSheafData.ker_subschemeι]
  · refine sup_le (Scheme.Hom.le_ker_comp _ _) ?_
    rw [pullback.condition]
    exact Scheme.Hom.le_ker_comp _ _
omit [IsClosedImmersion i₁] [IsClosedImmersion i₂] in
theorem ker_mul_ker_eq_bot [IsReduced X] (hcover : Set.range i₁.base ∪ Set.range i₂.base =
  Set.univ) :
    i₁.ker * i₂.ker = ⊥ := by
  rw [← Scheme.IdealSheafData.support_eq_top_iff, Scheme.IdealSheafData.support_mul, eq_top_iff]
  rintro x -
  rcases (Set.eq_univ_iff_forall.mp hcover x) with h | h
  · exact Or.inl (i₁.range_subset_ker_support h)
  · exact Or.inr (i₂.range_subset_ker_support h)

end AlgebraicGeometry.TwoClosedAux

end IsClosedImmersion_app_injective_and_exists_of_app_pullback_eq_of_isAffineOpen
end AlgebraicCurves.Geometry.Schemes.Proofs

namespace AlgebraicGeometry.IsClosedImmersion

universe u

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open _root_.AlgebraicCurves.Geometry.Schemes.Proofs in
open IsClosedImmersion_app_injective_and_exists_of_app_pullback_eq_of_isAffineOpen in
open AlgebraicGeometry.TwoClosedAux in
theorem app_injective_and_exists_of_app_pullback_eq_of_isAffineOpen
    {X Y₁ Y₂ : Scheme.{u}} [IsReduced X] (i₁ : Y₁ ⟶ X) (i₂ : Y₂ ⟶ X)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂]
    (hcover : Set.range i₁.base ∪ Set.range i₂.base = Set.univ)
    (U : X.Opens) (hU : IsAffineOpen U) :
    Function.Injective (fun f : Γ(X, U) => ((i₁.app U) f, (i₂.app U) f)) ∧
      ∀ (g₁ : Γ(Y₁, i₁ ⁻¹ᵁ U)) (g₂ : Γ(Y₂, i₂ ⁻¹ᵁ U)),
        (pullback i₁ i₂).presheaf.map
            (eqToHom (show (pullback.snd i₁ i₂) ⁻¹ᵁ (i₂ ⁻¹ᵁ U) = (pullback.fst i₁ i₂) ⁻¹ᵁ (i₁ ⁻¹ᵁ
              U) by
              rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, pullback.condition])).op
          ((pullback.fst i₁ i₂).app (i₁ ⁻¹ᵁ U) g₁) =
          (pullback.snd i₁ i₂).app (i₂ ⁻¹ᵁ U) g₂ →
        ∃ f : Γ(X, U), (i₁.app U) f = g₁ ∧ (i₂.app U) f = g₂ := by
  have hk₁ : RingHom.ker (i₁.app U).hom = i₁.ker.ideal ⟨U, hU⟩ := (Scheme.Hom.ker_apply i₁ ⟨U,
    hU⟩).symm
  have hk₂ : RingHom.ker (i₂.app U).hom = i₂.ker.ideal ⟨U, hU⟩ := (Scheme.Hom.ker_apply i₂ ⟨U,
    hU⟩).symm
  have hkπ : RingHom.ker ((pullback.fst i₁ i₂ ≫ i₁).app U).hom = i₁.ker.ideal ⟨U, hU⟩ ⊔
    i₂.ker.ideal ⟨U, hU⟩ := by
    rw [← Scheme.Hom.ker_apply _ ⟨U, hU⟩, ker_pullback_fst_comp, Scheme.IdealSheafData.ideal_sup]
    rfl
  refine ⟨?_, ?_⟩
  · intro f g hfg
    simp only [Prod.mk.injEq] at hfg
    rw [← sub_eq_zero]
    have hmem₁ : f - g ∈ i₁.ker.ideal ⟨U, hU⟩ :=
      by rw [← hk₁, RingHom.mem_ker, map_sub, sub_eq_zero]; exact hfg.1
    have hmem₂ : f - g ∈ i₂.ker.ideal ⟨U, hU⟩ :=
      by rw [← hk₂, RingHom.mem_ker, map_sub, sub_eq_zero]; exact hfg.2
    have hsq : (f - g) * (f - g) ∈ (i₁.ker * i₂.ker).ideal ⟨U, hU⟩ := by
      rw [Scheme.IdealSheafData.ideal_mul]; exact Ideal.mul_mem_mul hmem₁ hmem₂
    rw [ker_mul_ker_eq_bot i₁ i₂ hcover, Scheme.IdealSheafData.ideal_bot] at hsq
    have h0 : (f - g) * (f - g) = 0 := hsq
    exact IsReduced.eq_zero _ ⟨2, by rw [pow_two, h0]⟩
  · intro g₁ g₂ h
    obtain ⟨a₁, rfl⟩ := i₁.app_surjective U hU g₁
    obtain ⟨a₂, rfl⟩ := i₂.app_surjective U hU g₂
    have key : ∀ a : Γ(X, U), (pullback i₁ i₂).presheaf.map
        (eqToHom (show (pullback.snd i₁ i₂) ⁻¹ᵁ (i₂ ⁻¹ᵁ U) = (pullback.fst i₁ i₂) ⁻¹ᵁ (i₁ ⁻¹ᵁ U) by
          rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, pullback.condition])).op
        ((pullback.fst i₁ i₂).app (i₁ ⁻¹ᵁ U) ((i₁.app U) a)) = (pullback.snd i₁ i₂).app (i₂ ⁻¹ᵁ U)
          ((i₂.app U) a) := by
      intro a
      change ((i₁.app U ≫ (pullback.fst i₁ i₂).app (i₁ ⁻¹ᵁ U)) ≫ (pullback i₁ i₂).presheaf.map
        (eqToHom _).op) a =
        (i₂.app U ≫ (pullback.snd i₁ i₂).app (i₂ ⁻¹ᵁ U)) a
      rw [← Scheme.Hom.comp_app, ← Scheme.Hom.comp_app,
        Scheme.Hom.congr_app (pullback.condition (f := i₁) (g := i₂)).symm U]
      rfl
    have hF : (pullback.fst i₁ i₂).app (i₁ ⁻¹ᵁ U) ((i₁.app U) a₁) = (pullback.fst i₁ i₂).app (i₁
      ⁻¹ᵁ U) ((i₁.app U) a₂) := by
      rw [← key a₂] at h
      have : IsIso ((pullback i₁ i₂).presheaf.map (eqToHom (show (pullback.snd i₁ i₂) ⁻¹ᵁ (i₂ ⁻¹ᵁ
        U) =
          (pullback.fst i₁ i₂) ⁻¹ᵁ (i₁ ⁻¹ᵁ U) by
            rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, pullback.condition])).op)
              := by
        rw [eqToHom_op, eqToHom_map]; infer_instance
      exact (ConcreteCategory.bijective_of_isIso _).1 h
    have hπ : ((pullback.fst i₁ i₂ ≫ i₁).app U) a₁ = ((pullback.fst i₁ i₂ ≫ i₁).app U) a₂ := by
      rw [Scheme.Hom.comp_app]
      exact hF
    have hdiff : a₁ - a₂ ∈ i₁.ker.ideal ⟨U, hU⟩ ⊔ i₂.ker.ideal ⟨U, hU⟩ := by
      rw [← hkπ, RingHom.mem_ker, map_sub, sub_eq_zero]; exact hπ
    obtain ⟨u₁, hu₁, u₂, hu₂, hu⟩ := Submodule.mem_sup.mp hdiff
    refine ⟨a₁ - u₁, ?_, ?_⟩
    · rw [map_sub, sub_eq_self]
      exact (RingHom.mem_ker.mp (hk₁ ▸ hu₁ : u₁ ∈ RingHom.ker (i₁.app U).hom))
    · have : a₁ - u₁ = a₂ + u₂ := by linear_combination -hu
      rw [this, map_add, add_eq_left]
      exact (RingHom.mem_ker.mp (hk₂ ▸ hu₂ : u₂ ∈ RingHom.ker (i₂.app U).hom))
end AlgebraicGeometry.IsClosedImmersion
end ProofImplementation
