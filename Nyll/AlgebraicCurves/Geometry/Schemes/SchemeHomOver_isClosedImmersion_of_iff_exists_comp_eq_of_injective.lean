/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_SchemeHomOver_isClosedImmersion_of_iff_exists_comp_eq_of_injective.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver_ext_of_forall_algebraicClosure_point_of_isReduced_of_flat

/-!
# Scheme Hom Over is Closed Immersion of iff exists comp eq of injective
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs
namespace SchemeHomOver_isClosedImmersion_of_iff_exists_comp_eq_of_injective

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

theorem _root_.AlgebraicGeometry.SchemeHomOver.isClosedImmersion_of_iff_exists_comp_eq_of_injective
    {k : Type u} [Field k] [IsAlgClosed k] {G D K : Scheme.{u}}
    (g : G ⟶ Spec (CommRingCat.of k)) [IsReduced G] [LocallyOfFiniteType g] [Flat g] [IsSeparated g]
    (d : D ⟶ Spec (CommRingCat.of k)) (f : SchemeHomOver g d) (j : K ⟶ D) [IsClosedImmersion j]
    (hpts : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (a : SchemeHomOver t d),
      (∃ b : T ⟶ K, b ≫ j = a.1) ↔ ∃ y : SchemeHomOver t g, NeronModelInfra.schemeHomOverComp y f =
        a)
    (hinj : ∀ y y' : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) g,
      NeronModelInfra.schemeHomOverComp y f = NeronModelInfra.schemeHomOverComp y' f → y = y') :
    IsClosedImmersion f.1 := by
  obtain ⟨b, hb⟩ := (hpts g f).mpr ⟨⟨𝟙 G, Category.id_comp _⟩, Subtype.ext (Category.id_comp _)⟩
  obtain ⟨σ, hσ⟩ := (hpts (j ≫ d) ⟨j, rfl⟩).mp ⟨𝟙 K, Category.id_comp _⟩
  have hσ' : σ.1 ≫ f.1 = j := congrArg Subtype.val hσ
  have he_over : (b ≫ σ.1) ≫ g = g := by
    rw [Category.assoc, σ.2, ← Category.assoc, hb, f.2]
  have hef : (b ≫ σ.1) ≫ f.1 = f.1 := by rw [Category.assoc, hσ', hb]
  have key : (⟨b ≫ σ.1, he_over⟩ : SchemeHomOver g g) = ⟨𝟙 G, Category.id_comp _⟩ := by
    apply AlgebraicGeometry.SchemeHomOver.ext_of_forall_algebraicClosure_point_of_isReduced_of_flat
      (R := k) k k
    intro y
    have hy1 : y.1 ≫ g = 𝟙 _ := by
      have := y.2
      simpa only [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id] using this
    let y₀ : SchemeHomOver (𝟙 _) g := ⟨y.1, hy1⟩
    let y₁ : SchemeHomOver (𝟙 _) g := ⟨y.1 ≫ b ≫ σ.1, by rw [Category.assoc, he_over, hy1]⟩
    have h01 : y₁ = y₀ := hinj y₁ y₀ (Subtype.ext (by
      change (y.1 ≫ b ≫ σ.1) ≫ f.1 = y.1 ≫ f.1
      rw [Category.assoc, hef]))
    have := congrArg Subtype.val h01
    simp only [y₀, y₁] at this
    change y.1 ≫ b ≫ σ.1 = y.1 ≫ 𝟙 G
    rw [this, Category.comp_id]
  have e_id : b ≫ σ.1 = 𝟙 G := congrArg Subtype.val key
  have e_id' : σ.1 ≫ b = 𝟙 K := by
    rw [← cancel_mono j, Category.assoc, hb, hσ', Category.id_comp]
  have : IsIso b := ⟨σ.1, e_id, e_id'⟩
  rw [← hb]
  infer_instance
end SchemeHomOver_isClosedImmersion_of_iff_exists_comp_eq_of_injective
end AlgebraicCurves.Geometry.Schemes.Proofs
end ProofImplementation
