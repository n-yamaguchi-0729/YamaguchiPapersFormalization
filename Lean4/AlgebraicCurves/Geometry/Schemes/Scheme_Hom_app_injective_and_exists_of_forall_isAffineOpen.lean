/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Hom_app_injective_and_exists_of_forall_isAffineOpen.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.ConcreteCategory.Basic
import Mathlib.CategoryTheory.EqToHom
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Opposites
import Mathlib.Tactic.Choose
import Mathlib.Topology.Category.TopCat.Opens
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import Mathlib.Topology.Sets.Opens

/-!
# Scheme Hom app injective and exists of forall is Affine Open
-/

section ProofImplementation


namespace AlgebraicCurves.Geometry.Schemes.Proofs
namespace Scheme_Hom_app_injective_and_exists_of_forall_isAffineOpen


open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry


universe u

open TopologicalSpace Opposite

namespace Aux



open _root_.AlgebraicGeometry


namespace Scheme
end Scheme

open scoped _root_.AlgebraicGeometry.Scheme in
theorem iSup_affineOpens_le {X : Scheme.{u}} (U : X.Opens) :
    ⨆ (V : {V : X.Opens // IsAffineOpen V ∧ V ≤ U}), (V : X.Opens) = U := by
  apply le_antisymm
  · exact iSup_le fun V => V.2.2
  · intro x hx
    obtain ⟨W, hW, hxW, hWU⟩ := exists_isAffineOpen_mem_and_subset (X := X) (x := x) (U := U) hx
    exact Opens.mem_iSup.mpr ⟨⟨W, hW, hWU⟩, hxW⟩

namespace Scheme
namespace Hom
end Scheme.Hom

open scoped _root_.AlgebraicGeometry.Scheme in
open scoped _root_.AlgebraicGeometry.Scheme.Hom in
theorem app_apply_map_homOfLE {X Y : Scheme.{u}} (f : Y ⟶ X) {U V : X.Opens} (e : V ≤ U)
    (s : Γ(X, U)) :
    f.app V (X.presheaf.map (homOfLE e).op s) =
      Y.presheaf.map (homOfLE (show f ⁻¹ᵁ V ≤ f ⁻¹ᵁ U from fun _ hx => e hx)).op (f.app U s) := by
  have h := CategoryTheory.ConcreteCategory.congr_hom (f.naturality (homOfLE e).op) s
  rw [CategoryTheory.ConcreteCategory.comp_apply, CategoryTheory.ConcreteCategory.comp_apply] at h
  rw [h]
  rfl


open scoped _root_.AlgebraicGeometry.Scheme in
open scoped _root_.AlgebraicGeometry.Scheme.Hom in
theorem app_prod_injective_of_forall_isAffineOpen {X Y₁ Y₂ : Scheme.{u}} (i₁ : Y₁ ⟶ X)
    (i₂ : Y₂ ⟶ X) (U : X.Opens)
    (h : ∀ V : X.Opens, IsAffineOpen V → V ≤ U →
      Function.Injective (fun f : Γ(X, V) => ((i₁.app V) f, (i₂.app V) f)))
    {W : X.Opens} (hW : W ≤ U) :
    Function.Injective (fun f : Γ(X, W) => ((i₁.app W) f, (i₂.app W) f)) := by
  intro f f' hff'
  simp only [Prod.mk.injEq] at hff'
  fapply X.sheaf.eq_of_locally_eq' (fun V : {V : X.Opens // IsAffineOpen V ∧ V ≤ W} => (V :
    X.Opens)) W
    (fun V => homOfLE V.2.2) (le_of_eq (iSup_affineOpens_le W).symm)
  intro V
  change X.presheaf.map (homOfLE V.2.2).op f = X.presheaf.map (homOfLE V.2.2).op f'
  apply h V.1 V.2.1 (V.2.2.trans hW)
  simp only [Prod.mk.injEq]
  constructor
  · rw [app_apply_map_homOfLE, app_apply_map_homOfLE, hff'.1]
  · rw [app_apply_map_homOfLE, app_apply_map_homOfLE, hff'.2]


open scoped _root_.AlgebraicGeometry.Scheme in
open scoped _root_.AlgebraicGeometry.Scheme.Hom in
theorem app_apply_map_op {X Y : Scheme.{u}} (f : Y ⟶ X) {U V : X.Opens} (ι : V ⟶ U)
    (s : Γ(X, U)) :
    f.app V (X.presheaf.map ι.op s) =
      Y.presheaf.map ((Opens.map f.base).map ι).op (f.app U s) := by
  have h := CategoryTheory.ConcreteCategory.congr_hom (f.naturality ι.op) s
  rw [CategoryTheory.ConcreteCategory.comp_apply, CategoryTheory.ConcreteCategory.comp_apply] at h
  exact h

end Aux

theorem _root_.AlgebraicGeometry.Scheme.Hom.app_injective_and_exists_of_forall_isAffineOpen
    {X Y₁ Y₂ : Scheme.{u}} (i₁ : Y₁ ⟶ X) (i₂ : Y₂ ⟶ X) (U : X.Opens)
    (h : ∀ (V : X.Opens), IsAffineOpen V → V ≤ U →
      Function.Injective (fun f : Γ(X, V) => ((i₁.app V) f, (i₂.app V) f)) ∧
        ∀ (g₁ : Γ(Y₁, i₁ ⁻¹ᵁ V)) (g₂ : Γ(Y₂, i₂ ⁻¹ᵁ V)),
          (pullback i₁ i₂).presheaf.map
              (eqToHom (show (pullback.snd i₁ i₂) ⁻¹ᵁ (i₂ ⁻¹ᵁ V) = (pullback.fst i₁ i₂) ⁻¹ᵁ (i₁ ⁻¹ᵁ
                V) by
                rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, pullback.condition])).op
            ((pullback.fst i₁ i₂).app (i₁ ⁻¹ᵁ V) g₁) =
            (pullback.snd i₁ i₂).app (i₂ ⁻¹ᵁ V) g₂ →
          ∃ f : Γ(X, V), (i₁.app V) f = g₁ ∧ (i₂.app V) f = g₂) :
    Function.Injective (fun f : Γ(X, U) => ((i₁.app U) f, (i₂.app U) f)) ∧
      ∀ (g₁ : Γ(Y₁, i₁ ⁻¹ᵁ U)) (g₂ : Γ(Y₂, i₂ ⁻¹ᵁ U)),
        (pullback i₁ i₂).presheaf.map
            (eqToHom (show (pullback.snd i₁ i₂) ⁻¹ᵁ (i₂ ⁻¹ᵁ U) = (pullback.fst i₁ i₂) ⁻¹ᵁ (i₁ ⁻¹ᵁ
              U) by
              rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, pullback.condition])).op
          ((pullback.fst i₁ i₂).app (i₁ ⁻¹ᵁ U) g₁) =
          (pullback.snd i₁ i₂).app (i₂ ⁻¹ᵁ U) g₂ →
        ∃ f : Γ(X, U), (i₁.app U) f = g₁ ∧ (i₂.app U) f = g₂ := by
  classical
  have hinj : ∀ W : X.Opens, W ≤ U →
      Function.Injective (fun f : Γ(X, W) => ((i₁.app W) f, (i₂.app W) f)) :=
    fun W hW => Aux.app_prod_injective_of_forall_isAffineOpen i₁ i₂ U
      (fun V hV hVU => (h V hV hVU).1) hW
  refine ⟨hinj U le_rfl, ?_⟩
  intro g₁ g₂ hagree
  let ι : Type u := {V : X.Opens // IsAffineOpen V ∧ V ≤ U}
  let V : ι → X.Opens := fun j => j.1
  let r₁ : ∀ j : ι, Γ(Y₁, i₁ ⁻¹ᵁ V j) := fun j =>
    Y₁.presheaf.map (homOfLE (i₁.preimage_mono j.2.2)).op g₁
  let r₂ : ∀ j : ι, Γ(Y₂, i₂ ⁻¹ᵁ V j) := fun j =>
    Y₂.presheaf.map (homOfLE (i₂.preimage_mono j.2.2)).op g₂
  have hagreeV : ∀ j : ι,
      (pullback i₁ i₂).presheaf.map
          (eqToHom (show (pullback.snd i₁ i₂) ⁻¹ᵁ (i₂ ⁻¹ᵁ V j) =
              (pullback.fst i₁ i₂) ⁻¹ᵁ (i₁ ⁻¹ᵁ V j) by
            rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage,
              pullback.condition])).op
        ((pullback.fst i₁ i₂).app (i₁ ⁻¹ᵁ V j) (r₁ j)) =
        (pullback.snd i₁ i₂).app (i₂ ⁻¹ᵁ V j) (r₂ j) := by
    intro j
    simp only [r₁, r₂]
    rw [Aux.app_apply_map_op, Aux.app_apply_map_op, ← hagree]
    generalize (pullback.fst i₁ i₂).app (i₁ ⁻¹ᵁ U) g₁ = t
    simp only [← CategoryTheory.ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
    rfl
  choose fV hfV₁ hfV₂ using fun j : ι => (h (V j) j.2.1 j.2.2).2 (r₁ j) (r₂ j) (hagreeV j)
  have hcompat : TopCat.Presheaf.IsCompatible X.sheaf.1 V fV := by
    intro j j'
    apply hinj (V j ⊓ V j') (inf_le_left.trans j.2.2)
    change ((i₁.app _) (X.presheaf.map _ (fV j)), (i₂.app _) (X.presheaf.map _ (fV j))) =
      ((i₁.app _) (X.presheaf.map _ (fV j')), (i₂.app _) (X.presheaf.map _ (fV j')))
    simp only [Prod.mk.injEq]
    refine ⟨?_, ?_⟩
    · rw [Aux.app_apply_map_op, Aux.app_apply_map_op, hfV₁, hfV₁]
      simp only [r₁, ← CategoryTheory.ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
      rfl
    · rw [Aux.app_apply_map_op, Aux.app_apply_map_op, hfV₂, hfV₂]
      simp only [r₂, ← CategoryTheory.ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
      rfl
  obtain ⟨f, hf, -⟩ := X.sheaf.existsUnique_gluing' V U (fun j => homOfLE j.2.2)
    (le_of_eq (Aux.iSup_affineOpens_le U).symm) fV hcompat
  refine ⟨f, ?_, ?_⟩
  · fapply Y₁.sheaf.eq_of_locally_eq' (fun j : ι => i₁ ⁻¹ᵁ V j) (i₁ ⁻¹ᵁ U)
      (fun j => homOfLE (i₁.preimage_mono j.2.2))
    · rw [← Scheme.Hom.preimage_iSup]
      exact i₁.preimage_mono (le_of_eq (Aux.iSup_affineOpens_le U).symm)
    · intro j
      have e1 : (i₁.app (V j)) (X.presheaf.map (homOfLE j.2.2).op f) = r₁ j := by
        have := hf j
        change X.presheaf.map (homOfLE j.2.2).op f = fV j at this
        rw [this, hfV₁]
      have hn := Aux.app_apply_map_op i₁ (homOfLE j.2.2) (show Γ(X, U) from f)
      exact hn.symm.trans e1
  · fapply Y₂.sheaf.eq_of_locally_eq' (fun j : ι => i₂ ⁻¹ᵁ V j) (i₂ ⁻¹ᵁ U)
      (fun j => homOfLE (i₂.preimage_mono j.2.2))
    · rw [← Scheme.Hom.preimage_iSup]
      exact i₂.preimage_mono (le_of_eq (Aux.iSup_affineOpens_le U).symm)
    · intro j
      have e2 : (i₂.app (V j)) (X.presheaf.map (homOfLE j.2.2).op f) = r₂ j := by
        have := hf j
        change X.presheaf.map (homOfLE j.2.2).op f = fV j at this
        rw [this, hfV₂]
      have hn := Aux.app_apply_map_op i₂ (homOfLE j.2.2) (show Γ(X, U) from f)
      exact hn.symm.trans e2
end Scheme_Hom_app_injective_and_exists_of_forall_isAffineOpen
end AlgebraicCurves.Geometry.Schemes.Proofs
end ProofImplementation
