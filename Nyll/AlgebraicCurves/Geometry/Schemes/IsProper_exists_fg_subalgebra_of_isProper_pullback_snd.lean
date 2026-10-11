/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_IsProper_exists_fg_subalgebra_of_isProper_pullback_snd.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.RingTheory.Adjoin.FG
import Mathlib.Tactic.CategoryTheory.Reassoc
import Mathlib.Tactic.Set
import Mathlib.Tactic.Tauto
import Mathlib.Topology.QuasiSeparated
import Nyll.SchemeTheory.Descent.SubalgebraStages
import Nyll.SchemeTheory.Descent.SubalgebraStages_nonempty_isLimit_cone
import Nyll.AlgebraicCurves.Geometry.Schemes.exists_isProper_surjective_isOpenImmersion_comp_eq_of_isSeparated

/-!
# Is Proper exists fg subalgebra of is Proper pullback snd
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs
namespace IsProper_exists_fg_subalgebra_of_isProper_pullback_snd
attribute [-instance] AlgebraicGeometry.ChowDatum.hι_closed
  AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper
  AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper
  AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ
  AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π
  AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial
attribute [-simp] AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec
  AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq
  AlgebraicGeometry.ChowDatum.mk.injEq

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

universe u

namespace ProperDesc

section envelope

variable {A₀ : Type u} [CommRing A₀] {X X' P Y : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of A₀)) (π : X' ⟶ X) (j : X' ⟶ P) (q : P ⟶ Spec (CommRingCat.of A₀))
  (hjq : j ≫ q = π ≫ f) (ι' : Y ⟶ Spec (CommRingCat.of A₀))

/-- The projection from the iterated pullback to the first base-changed scheme. -/
noncomputable abbrev jY := pullback.fst (pullback.fst q ι') j

/--
The projection from the iterated pullback to the scheme along which the second pullback is
taken.
-/
noncomputable abbrev σY := pullback.snd (pullback.fst q ι') j

/-- The comparison morphism between the iterated pullback and the base-changed target. -/
noncomputable def ρ : pullback (pullback.fst q ι') j ⟶ pullback f ι' :=
  pullback.lift (σY j q ι' ≫ π) (jY j q ι' ≫ pullback.snd q ι')
    (by rw [Category.assoc, ← hjq, ← Category.assoc, ← pullback.condition,
      Category.assoc, pullback.condition,
      Category.assoc])

@[reassoc] lemma ρ_fst : ρ f π j q hjq ι' ≫ pullback.fst f ι' = σY j q ι' ≫ π := pullback.lift_fst
  _ _ _
@[reassoc] lemma ρ_snd : ρ f π j q hjq ι' ≫ pullback.snd f ι' = jY j q ι' ≫ pullback.snd q ι' :=
  pullback.lift_snd _ _ _

lemma isPullback_ρ : IsPullback (σY j q ι') (ρ f π j q hjq ι') π (pullback.fst f ι') := by
  have big : IsPullback (σY j q ι') (jY j q ι' ≫ pullback.snd q ι') (j ≫ q) ι' :=
    IsPullback.paste_vert (IsPullback.of_hasPullback (pullback.fst q ι') j).flip
      (IsPullback.of_hasPullback q ι')
  rw [hjq] at big
  exact IsPullback.of_bot
    (by rwa [ρ_snd]) (ρ_fst f π j q hjq ι').symm (IsPullback.of_hasPullback f ι')

scoped instance surjective_ρ [Surjective π] : Surjective (ρ f π j q hjq ι') :=
  MorphismProperty.of_isPullback (P := @Surjective) (isPullback_ρ f π j q hjq ι') inferInstance

scoped instance isProper_ρ [IsProper π] : IsProper (ρ f π j q hjq ι') :=
  MorphismProperty.of_isPullback (P := @IsProper) (isPullback_ρ f π j q hjq ι') inferInstance

lemma range_jY : Set.range ⇑(jY j q ι') = ⇑(pullback.fst q ι') ⁻¹' Set.range ⇑j :=
  Scheme.Pullback.range_fst _ _
include hjq in
lemma isClosed_range_jY [IsProper π] [IsSeparated q] [IsProper (pullback.snd f ι')] :
    IsClosed (Set.range ⇑(jY j q ι')) := by
  have h1 : IsProper (ρ f π j q hjq ι' ≫ pullback.snd f ι') := inferInstance
  rw [ρ_snd] at h1
  have : IsSeparated (pullback.snd q ι') := inferInstance
  have : IsProper (jY j q ι') := IsProper.of_comp (jY j q ι') (pullback.snd q ι')
  exact (jY j q ι').isClosedMap.isClosed_range
include hjq in
lemma isProper_snd_of_isClosed_range [IsOpenImmersion j] [IsProper q] [Surjective π] [IsSeparated f]
    [LocallyOfFiniteType f] (h : IsClosed (Set.range ⇑(jY j q ι'))) : IsProper (pullback.snd f ι')
      := by
  have : IsClosedImmersion (jY j q ι') := IsClosedImmersion.of_isPreimmersion _ h
  have : IsProper (pullback.snd q ι') := inferInstance
  have h1 : IsProper (jY j q ι' ≫ pullback.snd q ι') := inferInstance
  rw [← ρ_snd f π j q hjq ι'] at h1
  have : UniversallyClosed (ρ f π j q hjq ι' ≫ pullback.snd f ι') := inferInstance
  have : UniversallyClosed (pullback.snd f ι') := UniversallyClosed.of_comp_surjective (ρ f π j q
    hjq ι') _
  have : IsSeparated (pullback.snd f ι') := inferInstance
  have : LocallyOfFiniteType (pullback.snd f ι') :=
    inferInstance
  exact ⟨⟩

end envelope

end ProperDesc

open _root_.AlgebraicCurves.Geometry in
attribute [local instance]
  Schemes.Proofs.IsProper_exists_fg_subalgebra_of_isProper_pullback_snd.ProperDesc.surjective_ρ
open _root_.AlgebraicCurves.Geometry in
attribute [local instance]
  Schemes.Proofs.IsProper_exists_fg_subalgebra_of_isProper_pullback_snd.ProperDesc.isProper_ρ


open ProperDesc _root_.AlgebraicGeometry.SubalgebraStages in
theorem _root_.AlgebraicGeometry.IsProper.exists_fg_subalgebra_of_isProper_pullback_snd
    {A₀ : Type u} [CommRing A₀] [IsNoetherianRing A₀] {A : Type u} [CommRing A] [Algebra A₀ A]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A₀)) [IsSeparated f] [QuasiCompact f]
      [LocallyOfFiniteType f]
    [IsProper (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))))] (s : Finset A) :
    ∃ (T : Subalgebra A₀ A), T.FG ∧ (↑s : Set A) ⊆ T ∧
      IsProper (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥T)))) := by
  classical
  obtain ⟨X', P, π, j, q, hπ, hsurj, hj, hq, hjq⟩ :=
    AlgebraicGeometry.exists_isProper_surjective_isOpenImmersion_comp_eq_of_isSeparated f
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
  obtain ⟨hc⟩ := SubalgebraStages.nonempty_isLimit_cone S hS q
  have : CompactSpace ↥X := QuasiCompact.compactSpace_of_compactSpace f
  have : CompactSpace ↥X' := QuasiCompact.compactSpace_of_compactSpace π
  have : CompactSpace ↥(cone S q).pt :=
    @QuasiCompact.compactSpace_of_compactSpace _ _ (pullback.snd q specHomTop)
      (inferInstanceAs (QuasiCompact (pullback.snd q specHomTop)))
      (inferInstance : CompactSpace (PrimeSpectrum A))
  let U : P.Opens := j.opensRange
  have hUc : IsCompact (U : Set ↥P) := isCompact_range j.continuous
  have hU : ∀ {Y : Scheme.{u}} (g : Y ⟶ P), ((g ⁻¹ᵁ U : Y.Opens) : Set ↥Y) = ⇑g ⁻¹' Set.range ⇑j :=
    fun _ => rfl
  let UA : (cone S q).pt.Opens := pullback.fst q specHomTop ⁻¹ᵁ U
  have hUA : IsClosed (UA : Set ↥(cone S q).pt) := by
    have e : (UA : Set ↥(cone S q).pt) = Set.range ⇑(jY j q (specHomTop (A₀ := A₀) (A := A))) := by
      rw [range_jY]; rfl
    rw [e]; exact isClosed_range_jY f π j q hjq specHomTop
  let Z : (cone S q).pt.Opens := ⟨(UA : Set ↥(cone S q).pt)ᶜ, hUA.isOpen_compl⟩
  have hZc : IsCompact (Z : Set ↥(cone S q).pt) := (UA.isOpen.isClosed_compl).isCompact
  obtain ⟨i₁, W, hWc, hW⟩ := exists_preimage_eq (diagram S q) (cone S q) hc Z hZc
  let Ui : ∀ i : ιᵒᵖ, ((diagram S q).obj i).Opens := fun i => pullback.fst q (specHom S i.unop) ⁻¹ᵁ
    U
  have hUi_c : ∀ i, IsCompact (Ui i : Set ↥((diagram S q).obj i)) := fun i =>
    QuasiCompact.isCompact_preimage (f := pullback.fst q (specHom S i.unop)) _ U.isOpen hUc
  have hUi_map : ∀ {i i' : ιᵒᵖ} (h : i ⟶ i'), (diagram S q).map h ⁻¹ᵁ Ui i' = Ui i := fun h => by
    change (diagram S q).map h ⁻¹ᵁ (pullback.fst q (specHom S _) ⁻¹ᵁ U) = pullback.fst q (specHom S
      _) ⁻¹ᵁ U
    rw [← Scheme.Hom.comp_preimage, diagram_map_fst]
  have hUi_π : ∀ i : ιᵒᵖ, (cone S q).π.app i ⁻¹ᵁ Ui i = UA := fun i => by
    change (cone S q).π.app i ⁻¹ᵁ (pullback.fst q (specHom S _) ⁻¹ᵁ U) = pullback.fst q specHomTop
      ⁻¹ᵁ U
    rw [← Scheme.Hom.comp_preimage, cone_π_app_fst]
  have hdisjA : (cone S q).π.app i₁ ⁻¹ᵁ (Ui i₁ ⊓ W) = (cone S q).π.app i₁ ⁻¹ᵁ ⊥ := by
    rw [Scheme.Hom.preimage_inf, hUi_π, hW, Scheme.Hom.preimage_bot]
    exact eq_bot_iff.mpr fun x hx => ((Opens.mem_inf.mp hx).2 (Opens.mem_inf.mp hx).1).elim
  obtain ⟨i₂, h₂₁, h₂⟩ := exists_map_preimage_eq_map_preimage (diagram S q) (cone S q) hc
    (QuasiSeparatedSpace.inter_isCompact _ _ (Ui i₁).isOpen (hUi_c i₁) W.isOpen hWc)
      isCompact_empty hdisjA
  rw [Scheme.Hom.preimage_inf, hUi_map, Scheme.Hom.preimage_bot] at h₂
  set W₂ := (diagram S q).map h₂₁ ⁻¹ᵁ W with hW₂
  have hW₂π : (cone S q).π.app i₂ ⁻¹ᵁ W₂ = Z := by
    rw [hW₂, ← Scheme.Hom.comp_preimage, ← hW]
    exact congrArg (fun g => g ⁻¹ᵁ W) ((cone S q).w h₂₁)
  have hcovA : (cone S q).π.app i₂ ⁻¹ᵁ (Ui i₂ ⊔ W₂) = (cone S q).π.app i₂ ⁻¹ᵁ ⊤ := by
    rw [Scheme.Hom.preimage_sup, hUi_π, hW₂π, Scheme.Hom.preimage_top]
    exact eq_top_iff.mpr fun x _ => Opens.mem_sup.mpr (em (x ∈ UA))
  have hW₂c : IsCompact (W₂ : Set ↥((diagram S q).obj i₂)) := by
    rw [hW₂]; exact QuasiCompact.isCompact_preimage (f := (diagram S q).map h₂₁) _ W.isOpen hWc
  obtain ⟨i₃, h₃₂, h₃⟩ := exists_map_preimage_eq_map_preimage (diagram S q) (cone S q) hc
    ((hUi_c i₂).union hW₂c) isCompact_univ hcovA
  rw [Scheme.Hom.preimage_sup, hUi_map, Scheme.Hom.preimage_top] at h₃
  have h₃' : Ui i₃ ⊓ (diagram S q).map h₃₂ ⁻¹ᵁ W₂ = ⊥ := by
    rw [← hUi_map h₃₂, ← Scheme.Hom.preimage_inf, h₂, Scheme.Hom.preimage_bot]
  have hclosed : IsClosed (Ui i₃ : Set ↥((diagram S q).obj i₃)) := by
    have e : (Ui i₃ : Set ↥((diagram S q).obj i₃)) = (((diagram S q).map h₃₂ ⁻¹ᵁ W₂ : ((diagram S
      q).obj i₃).Opens) : Set _)ᶜ := by
      ext x
      have a := SetLike.ext_iff.mp h₃' x
      have b := SetLike.ext_iff.mp h₃ x
      simp only [Opens.mem_inf, Opens.mem_sup, Opens.mem_bot, Opens.mem_top, iff_false, iff_true,
        not_and] at a b
      simp only [SetLike.mem_coe, Set.mem_compl_iff]
      tauto
    rw [e, isClosed_compl_iff]
    exact Opens.isOpen _
  refine ⟨S i₃.unop, i₃.unop.2.1, i₃.unop.2.2, ?_⟩
  have := hπ; have := hsurj; have := hj; have := hq
  apply isProper_snd_of_isClosed_range f π j q hjq (specHom S i₃.unop)
  rw [range_jY, ← hU]
  exact hclosed
end AlgebraicCurves.Geometry.Schemes.Proofs.IsProper_exists_fg_subalgebra_of_isProper_pullback_snd
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
  AlgebraicGeometry.SubalgebraStages.isCofiltered_op AlgebraicGeometry.ChowDatum.hι_closed
  AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper
  AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper
  AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ
  AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π
  AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial
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
  AlgebraicGeometry.SubalgebraStages.leg_trans AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec
  AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq
  AlgebraicGeometry.ChowDatum.mk.injEq
