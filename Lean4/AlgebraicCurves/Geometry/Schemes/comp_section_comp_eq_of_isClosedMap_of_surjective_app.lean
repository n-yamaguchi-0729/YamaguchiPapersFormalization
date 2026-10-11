/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_comp_section_comp_eq_of_isClosedMap_of_surjective_app.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.Tactic.CategoryTheory.Reassoc

/-!
# comp section comp eq of is Closed Map of surjective app
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs
namespace comp_section_comp_eq_of_isClosedMap_of_surjective_app

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace SolRigidityBase

theorem appLE_self_eq_id_of_eq_id {B : Scheme.{u}} (q : B ⟶ B) (hq : q = 𝟙 B) (U : B.Opens)
    (e : U ≤ q ⁻¹ᵁ U) : q.appLE U U e = 𝟙 _ := by
  subst hq
  rw [Scheme.Hom.appLE, Scheme.Hom.id_app]
  erw [Category.id_comp]
  exact B.presheaf.map_id _

theorem main
    {X B Y : Scheme.{u}} (p : X ⟶ B) (ε : B ⟶ X) (hε : ε ≫ p = 𝟙 B)
    (hp : IsClosedMap p)
    (hH0 : ∀ U : B.Opens, IsAffineOpen U → Function.Surjective (p.app U))
    (f : X ⟶ Y) (hf : ∀ x : X, f (ε (p x)) = f x) :
    p ≫ ε ≫ f = f := by
  refine Scheme.hom_ext_of_forall _ _ fun x ↦ ?_
  obtain ⟨V, hV, hxV, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := Y) (x := f x) (U := ⊤) trivial
  have hC : IsClosed (p '' ((f ⁻¹ᵁ V : Set X)ᶜ)) :=
    hp _ (f ⁻¹ᵁ V).isOpen.isClosed_compl
  have hbC : p x ∈ (⟨(p '' ((f ⁻¹ᵁ V : Set X)ᶜ))ᶜ, hC.isOpen_compl⟩ : B.Opens) := by
    rintro ⟨x', hx', e⟩
    apply hx'
    change f x' ∈ V
    rw [← hf x', e, hf x]
    exact hxV
  obtain ⟨U, hU, hbU, hUC⟩ := exists_isAffineOpen_mem_and_subset hbC
  have e₁ : p ⁻¹ᵁ U ≤ f ⁻¹ᵁ V := by
    intro x' hx'
    by_contra h
    exact hUC hx' ⟨x', h, rfl⟩
  have e₂ : p ⁻¹ᵁ U ≤ (p ≫ ε ≫ f) ⁻¹ᵁ V := by
    intro x' hx'
    change (p ≫ ε ≫ f) x' ∈ V
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hf]
    exact e₁ hx'
  refine ⟨p ⁻¹ᵁ U, hbU, ?_⟩
  rw [← Scheme.Hom.resLE_comp_ι _ e₂, ← Scheme.Hom.resLE_comp_ι _ e₁]
  congr 1
  let _ : IsAffine V := hV
  apply ext_of_isAffine
  simp only [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top]
  congr 2
  have e₄ : U ≤ ε ⁻¹ᵁ (p ⁻¹ᵁ U) := by
    intro b hb
    change p (ε b) ∈ U
    rwa [← Scheme.Hom.comp_apply, hε]
  have key : p.app U ≫ ε.appLE (p ⁻¹ᵁ U) U e₄ = 𝟙 _ := by
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
    exact appLE_self_eq_id_of_eq_id _ hε _ _
  have dec : (p ≫ ε ≫ f).appLE V (p ⁻¹ᵁ U) e₂ =
      f.appLE V (p ⁻¹ᵁ U) e₁ ≫ ε.appLE (p ⁻¹ᵁ U) U e₄ ≫ p.app U := by
    rw [Scheme.Hom.app_eq_appLE p, Scheme.Hom.appLE_comp_appLE_assoc ε f,
      Scheme.Hom.appLE_comp_appLE p (ε ≫ f)]
  rw [dec]
  set θ := ε.appLE (p ⁻¹ᵁ U) U e₄ ≫ p.app U with hθ
  have hθid : θ = 𝟙 _ := by
    ext t
    obtain ⟨r, rfl⟩ := hH0 U hU t
    change (p.app U ≫ θ) r = p.app U r
    rw [hθ, reassoc_of% key]
  rw [hθid, Category.comp_id]

end SolRigidityBase

theorem _root_.AlgebraicGeometry.comp_section_comp_eq_of_isClosedMap_of_surjective_app
    {X B Y : Scheme.{u}} (p : X ⟶ B) (ε : B ⟶ X) (hε : ε ≫ p = 𝟙 B)
    (hp : IsClosedMap p)
    (hH0 : ∀ U : B.Opens, IsAffineOpen U → Function.Surjective (p.app U))
    (f : X ⟶ Y) (hf : ∀ x : X, f (ε (p x)) = f x) :
    p ≫ ε ≫ f = f :=
  SolRigidityBase.main p ε hε hp hH0 f hf
end AlgebraicCurves.Geometry.Schemes.Proofs.comp_section_comp_eq_of_isClosedMap_of_surjective_app
end ProofImplementation
