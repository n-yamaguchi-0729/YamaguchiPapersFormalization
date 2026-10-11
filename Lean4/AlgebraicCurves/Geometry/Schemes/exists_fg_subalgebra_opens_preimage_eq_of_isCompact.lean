/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_exists_fg_subalgebra_opens_preimage_eq_of_isCompact.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.RingTheory.Adjoin.FG
import SchemeTheory.Descent.SubalgebraStages
import SchemeTheory.Descent.SubalgebraStages_nonempty_isLimit_cone

/-!
# exists fg subalgebra opens preimage eq of is Compact
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs
namespace exists_fg_subalgebra_opens_preimage_eq_of_isCompact

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem _root_.AlgebraicGeometry.exists_fg_subalgebra_opens_preimage_eq_of_isCompact
    {A₀ : Type u} [CommRing A₀] {A : Type u} [CommRing A] [Algebra A₀ A]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A₀)) [QuasiCompact f] [QuasiSeparated f]
    (W : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap A₀ A)))).Opens)
    (hW : IsCompact (W : Set ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap A₀ A)))))) (s :
      Finset A) :
    ∃ (T : Subalgebra A₀ A), T.FG ∧ (↑s : Set A) ⊆ T ∧
      ∃ W₀ : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥T)))).Opens,
        IsCompact (W₀ : Set ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥T))))) ∧
        ∀ q : pullback f (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))) ⟶
            pullback f (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥T))),
          q ≫ pullback.fst f _ = pullback.fst f _ →
          q ≫ pullback.snd f _ = pullback.snd f _ ≫ Spec.map (CommRingCat.ofHom T.val.toRingHom) →
          q ⁻¹ᵁ W₀ = W := by
  classical
  let ι : Type u := {T : Subalgebra A₀ A // T.FG ∧ (↑s : Set A) ⊆ T}
  have : Nonempty ι := ⟨⟨Algebra.adjoin A₀ ↑s, Subalgebra.fg_adjoin_finset s,
    Algebra.subset_adjoin⟩⟩
  have : IsDirected ι (· ≤ ·) := ⟨fun T₁ T₂ =>
    ⟨⟨T₁.1 ⊔ T₂.1, T₁.2.1.sup T₂.2.1, T₁.2.2.trans (SetLike.coe_subset_coe.mpr le_sup_left)⟩,
      (le_sup_left : T₁.1 ≤ T₁.1 ⊔ T₂.1), (le_sup_right : T₂.1 ≤ T₁.1 ⊔ T₂.1)⟩⟩
  let S : ι →o Subalgebra A₀ A := ⟨fun T => T.1, fun _ _ h => h⟩
  have hS : ∀ a : A, ∃ i, a ∈ S i := fun a =>
    ⟨⟨Algebra.adjoin A₀ ↑(insert a s), Subalgebra.fg_adjoin_finset _,
        fun x hx => Algebra.subset_adjoin (by simp [hx])⟩,
      Algebra.subset_adjoin (by simp)⟩
  obtain ⟨hc⟩ := SubalgebraStages.nonempty_isLimit_cone S hS f
  obtain ⟨i, W₀, hW₀c, hW₀⟩ :=
    exists_preimage_eq (SubalgebraStages.diagram S f) (SubalgebraStages.cone S f) hc W hW
  refine ⟨(Opposite.unop i).1, (Opposite.unop i).2.1, (Opposite.unop i).2.2, W₀, hW₀c, fun q hq₁
    hq₂ => ?_⟩
  have hq : q = SubalgebraStages.leg S f (Opposite.unop i) := by
    apply pullback.hom_ext
    · rw [hq₁, SubalgebraStages.leg_fst]
    · rw [hq₂, SubalgebraStages.leg_snd]
  rw [hq]
  exact hW₀
end AlgebraicCurves.Geometry.Schemes.Proofs.exists_fg_subalgebra_opens_preimage_eq_of_isCompact
end ProofImplementation

attribute [-instance] AlgebraicGeometry.SubalgebraStages.compactSpace_pullback
  AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback
  AlgebraicGeometry.SubalgebraStages.compactSpace_obj
  AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj
  AlgebraicGeometry.SubalgebraStages.quasiCompact_snd
  AlgebraicGeometry.SubalgebraStages.isAffineHom_leg
  AlgebraicGeometry.SubalgebraStages.isAffineHom_trans
  AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map
  AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd
  AlgebraicGeometry.SubalgebraStages.isCofiltered_op
attribute [-simp] AlgebraicGeometry.SubalgebraStages.specCone_π_app
  AlgebraicGeometry.SubalgebraStages.specLeg_specHom
  AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt
  AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj
  AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map
  AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd
  AlgebraicGeometry.SubalgebraStages.specTrans_specHom
  AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app
  AlgebraicGeometry.SubalgebraStages.specDiagram_map
  AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst
  AlgebraicGeometry.SubalgebraStages.leg_trans
