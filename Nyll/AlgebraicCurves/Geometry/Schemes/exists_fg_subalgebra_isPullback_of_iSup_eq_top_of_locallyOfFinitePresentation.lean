/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_exists_fg_subalgebra_isPullback_of_iSup_eq_top_of_locallyOfFinitePresentation.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Lean.Elab.Command
import Mathlib.Tactic.Ext
import Nyll.AlgebraicCurves.Geometry.Schemes.exists_fg_subalgebra_opens_preimage_eq_of_isCompact
import Nyll.AlgebraicCurves.Geometry.Schemes.exists_fg_subalgebra_iso_pullback_of_iso_pullback_of_locallyOfFinitePresentation
import Nyll.AlgebraicCurves.Geometry.Schemes.exists_isPullback_glue_of_isPullback_of_isOpenImmersion
import Nyll.AlgebraicCurves.Foundations.Algebra.Subalgebra_fg_restrictScalars_and_le_of_fg

/-!
# Descent of a scheme obtained by gluing two quasi-compact open models
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs.UnionDescent
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

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace UnionModel

variable {A : Type u} [CommRing A]

private noncomputable abbrev _root_.UnionModel.ι (A B : Type u) [CommRing A] [CommRing B] [Algebra
  B A] :
    Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of B) :=
  Spec.map (CommRingCat.ofHom (algebraMap B A))

export _root_.UnionModel (ι)

omit [CommRing A] in
theorem ι_comp (A : Type u) [CommRing A] (B : Type u) [CommRing B] [Algebra B A] (B' : Type u)
  [CommRing B'] [Algebra B' A]
    (φ : B →+* B') (hφ : (algebraMap B' A).comp φ = algebraMap B A) :
    ι A B' ≫ Spec.map (CommRingCat.ofHom φ) = ι A B := by
  rw [ι, ι, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hφ]

/-- A finitely presented model together with its base-change identification. -/
structure Model (B : Type u) [CommRing B] [Algebra B A] {Y : Scheme.{u}} (gY : Y ⟶ Spec
  (CommRingCat.of A)) where
  /-- The scheme over the smaller coefficient ring. -/
  X₀ : Scheme.{u}
  /-- The structure morphism of the model. -/
  f₀ : X₀ ⟶ Spec (CommRingCat.of B)
  /-- The comparison morphism from the original scheme. -/
  π : Y ⟶ X₀
  /-- Finite presentation of the structure morphism. -/
  lfp : LocallyOfFinitePresentation f₀
  /-- Quasi-compactness of the structure morphism. -/
  qc : QuasiCompact f₀
  /-- Quasi-separatedness of the structure morphism. -/
  qs : QuasiSeparated f₀
  /-- The square identifying the original scheme with the base change. -/
  sq : IsPullback π gY f₀ (ι A B)

attribute [scoped instance] Model.lfp Model.qc Model.qs

namespace Model

variable {B : Type u} [CommRing B] [Algebra B A] {Y : Scheme.{u}} {gY : Y ⟶ Spec (CommRingCat.of A)}

section map
variable (M : Model B gY) (B' : Type u) [CommRing B'] [Algebra B' A] (φ : B →+* B')
  (hφ : (algebraMap B' A).comp φ = algebraMap B A)

/-- The comparison between the two pullbacks after extending coefficients. -/
noncomputable def q : pullback M.f₀ (ι A B) ⟶ pullback M.f₀ (Spec.map (CommRingCat.ofHom φ)) :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ ι A B')
    (by rw [pullback.condition, Category.assoc, ι_comp A B B' φ hφ])

@[scoped simp] theorem q_fst : M.q B' φ hφ ≫ pullback.fst _ _ = pullback.fst _ _ :=
  pullback.lift_fst _ _ _
@[scoped simp] theorem q_snd : M.q B' φ hφ ≫ pullback.snd _ _ = pullback.snd _ _ ≫ ι A B' :=
  pullback.lift_snd _ _ _

/-- Extension of the coefficient ring of a model. -/
noncomputable def map : Model B' gY where
  X₀ := pullback M.f₀ (Spec.map (CommRingCat.ofHom φ))
  f₀ := pullback.snd _ _
  π := M.sq.isoPullback.hom ≫ M.q B' φ hφ
  lfp := inferInstance
  qc := inferInstance
  qs := inferInstance
  sq := by
    have h1 : IsPullback (M.q B' φ hφ) (pullback.snd M.f₀ (ι A B))
        (pullback.snd M.f₀ (Spec.map (CommRingCat.ofHom φ))) (ι A B') := by
      refine IsPullback.of_right ?_ (M.q_snd B' φ hφ) (IsPullback.of_hasPullback _ _)
      rw [q_fst, ι_comp A B B' φ hφ]
      exact IsPullback.of_hasPullback _ _
    have h2 : IsPullback M.sq.isoPullback.hom (M.sq.isoPullback.hom ≫ pullback.snd M.f₀ (ι A B))
        (pullback.snd M.f₀ (ι A B)) (𝟙 _) :=
      IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id]⟩
    have := h2.paste_horiz h1
    rw [Category.id_comp, IsPullback.isoPullback_hom_snd] at this
    exact this

@[scoped simp] theorem map_X₀ : (M.map B' φ hφ).X₀ = pullback M.f₀ (Spec.map (CommRingCat.ofHom φ))
  := rfl
@[scoped simp] theorem map_f₀ : (M.map B' φ hφ).f₀ = pullback.snd _ _ := rfl
theorem map_π : (M.map B' φ hφ).π = M.sq.isoPullback.hom ≫ M.q B' φ hφ := rfl

@[scoped simp] theorem map_π_fst : (M.map B' φ hφ).π ≫ pullback.fst _ _ = M.π := by
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun t => M.sq.isoPullback.hom ≫ t) (M.q_fst B' φ hφ)).trans
      M.sq.isoPullback_hom_fst)

@[scoped simp] theorem map_π_snd : (M.map B' φ hφ).π ≫ pullback.snd _ _ = gY ≫ ι A B' := by
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun t => M.sq.isoPullback.hom ≫ t) (M.q_snd B' φ hφ)).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (fun t => t ≫ ι A B') M.sq.isoPullback_hom_snd)))

theorem map_π_preimage (W₀ : M.X₀.Opens) :
    (M.map B' φ hφ).π ⁻¹ᵁ ((pullback.fst M.f₀ (Spec.map (CommRingCat.ofHom φ))) ⁻¹ᵁ W₀) = M.π ⁻¹ᵁ
      W₀ := by
  exact (Scheme.Hom.comp_preimage (M.map B' φ hφ).π
    (pullback.fst M.f₀ (Spec.map (CommRingCat.ofHom φ))) W₀).symm.trans
      (congrArg (fun t : Y ⟶ M.X₀ => t ⁻¹ᵁ W₀) (M.map_π_fst B' φ hφ))

theorem isCompact_fst_preimage (W₀ : M.X₀.Opens) (hc : IsCompact (W₀ : Set ↥M.X₀)) :
    IsCompact (((pullback.fst M.f₀ (Spec.map (CommRingCat.ofHom φ))) ⁻¹ᵁ W₀ : (M.map B' φ
      hφ).X₀.Opens) :
      Set ↥(M.map B' φ hφ).X₀) := by
  have : QuasiCompact (Spec.map (CommRingCat.ofHom φ)) :=
    (quasiCompact_iff_compactSpace (Spec.map (CommRingCat.ofHom φ))).mpr inferInstance
  have : QuasiCompact (pullback.fst M.f₀ (Spec.map (CommRingCat.ofHom φ))) :=
    by
      have : MorphismProperty.IsStableUnderBaseChange
          (@QuasiCompact : MorphismProperty Scheme.{u}) := quasiCompact_isStableUnderBaseChange
      exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (P := (@QuasiCompact : MorphismProperty Scheme.{u}))
        (IsPullback.of_hasPullback M.f₀ (Spec.map (CommRingCat.ofHom φ))).flip inferInstance
  exact QuasiCompact.isCompact_preimage
    (f := pullback.fst M.f₀ (Spec.map (CommRingCat.ofHom φ))) _ W₀.2 hc

end map

section restrictOpen
variable (M : Model B gY) (W₀ : M.X₀.Opens) (hc : IsCompact (W₀ : Set ↥M.X₀))
  {W : Scheme.{u}} (k : W ⟶ Y) [IsOpenImmersion k] (h : M.π ⁻¹ᵁ W₀ = k.opensRange)
  (gW : W ⟶ Spec (CommRingCat.of A)) (hgW : gW = k ≫ gY)

include h in
theorem range_subset : Set.range (k ≫ M.π).base ⊆ Set.range W₀.ι.base := by
  rintro _ ⟨w, rfl⟩
  rw [Scheme.Opens.range_ι]
  show (k ≫ M.π).base w ∈ (W₀ : Set _)
  have : k.base w ∈ k.opensRange := ⟨w, rfl⟩
  rw [← h] at this
  exact this

/-- Restriction of a model to a compatible quasi-compact open. -/
noncomputable def restrictOpen : Model B gW where
  X₀ := W₀
  f₀ := W₀.ι ≫ M.f₀
  π := IsOpenImmersion.lift W₀.ι (k ≫ M.π) (M.range_subset W₀ k h)
  lfp := inferInstance
  qc := by
    have : CompactSpace ↥W₀ := isCompact_iff_compactSpace.mp hc
    exact (quasiCompact_iff_compactSpace (W₀.ι ≫ M.f₀)).mpr ‹_›
  qs := inferInstance
  sq := by
    have top : IsPullback (IsOpenImmersion.lift W₀.ι (k ≫ M.π) (M.range_subset W₀ k h)) k W₀.ι M.π
      :=
      IsOpenImmersion.isPullback _ _ _ _ (IsOpenImmersion.lift_fac _ _ _).symm
        (by rw [Scheme.Opens.opensRange_ι]; exact h)
    rw [hgW]
    exact top.paste_vert M.sq

@[scoped simp] theorem restrictOpen_X₀ : (M.restrictOpen W₀ hc k h gW hgW).X₀ = W₀ := rfl
@[scoped simp] theorem restrictOpen_f₀ : (M.restrictOpen W₀ hc k h gW hgW).f₀ = W₀.ι ≫ M.f₀ := rfl
@[scoped simp] theorem restrictOpen_π_ι : (M.restrictOpen W₀ hc k h gW hgW).π ≫ W₀.ι = k ≫ M.π :=
  IsOpenImmersion.lift_fac W₀.ι (k ≫ M.π) (M.range_subset W₀ k h)

end restrictOpen

section dock
variable (M : Model B gY)

/-- The model over an intermediate finitely generated subalgebra. -/
noncomputable abbrev toStage (T' : Subalgebra B A) : Model ↥T' gY :=
  M.map ↥T' (algebraMap B ↥T') (IsScalarTower.algebraMap_eq B ↥T' A).symm

theorem exists_open (W : Y.Opens) (hW : IsCompact (W : Set ↥Y)) (s : Finset A) :
    ∃ (T' : Subalgebra B A), T'.FG ∧ (↑s : Set A) ⊆ T' ∧
      ∃ W₀ : (M.toStage T').X₀.Opens, IsCompact (W₀ : Set ↥(M.toStage T').X₀) ∧ (M.toStage T').π
        ⁻¹ᵁ W₀ = W := by
  let e := M.sq.isoPullback
  have hWP : IsCompact ((e.inv ⁻¹ᵁ W : (pullback M.f₀ (ι A B)).Opens) : Set ↥(pullback M.f₀ (ι A
    B))) :=
    QuasiCompact.isCompact_preimage (f := e.inv) _ W.2 hW
  obtain ⟨T', hT', hs, W₀, hW₀, hq⟩ :=
    AlgebraicGeometry.exists_fg_subalgebra_opens_preimage_eq_of_isCompact (A₀ := B) (A := A) M.f₀
      (e.inv ⁻¹ᵁ W) hWP s
  refine ⟨T', hT', hs, W₀, hW₀, ?_⟩
  have hq' := hq (M.q ↥T' (algebraMap B ↥T') (IsScalarTower.algebraMap_eq B ↥T' A).symm) (M.q_fst _
    _ _)
    (by rw [q_snd]; rfl)
  change (e.hom ≫ M.q ↥T' _ _) ⁻¹ᵁ W₀ = W
  rw [Scheme.Hom.comp_preimage, hq']
  change (e.hom ≫ e.inv) ⁻¹ᵁ W = W
  rw [Iso.hom_inv_id]; rfl

theorem exists_iso (M₁ M₂ : Model B gY) (s : Finset A) :
    ∃ (T' : Subalgebra B A), T'.FG ∧ (↑s : Set A) ⊆ T' ∧
      ∃ e₀ : (M₁.toStage T').X₀ ≅ (M₂.toStage T').X₀,
        e₀.hom ≫ (M₂.toStage T').f₀ = (M₁.toStage T').f₀ ∧ (M₁.toStage T').π ≫ e₀.hom = (M₂.toStage
          T').π := by
  let e₁ := M₁.sq.isoPullback
  let e₂ := M₂.sq.isoPullback
  let e : pullback M₁.f₀ (ι A B) ≅ pullback M₂.f₀ (ι A B) := e₁.symm ≪≫ e₂
  have he : e.hom ≫ pullback.snd M₂.f₀ _ = pullback.snd M₁.f₀ _ := by
    change (e₁.inv ≫ e₂.hom) ≫ _ = _
    rw [Category.assoc, IsPullback.isoPullback_hom_snd, Iso.inv_comp_eq,
      IsPullback.isoPullback_hom_snd]
  obtain ⟨T', hT', hs, e₀, he₀, hcomp⟩ :=
    exists_fg_subalgebra_iso_pullback_of_iso_pullback_of_locallyOfFinitePresentation
      (A₀ := B) (A := A) M₁.f₀ M₂.f₀ e he s
  refine ⟨T', hT', hs, e₀, he₀, ?_⟩
  have hc := hcomp (M₁.q ↥T' (algebraMap B ↥T') (IsScalarTower.algebraMap_eq B ↥T' A).symm)
    (M₂.q ↥T' (algebraMap B ↥T') (IsScalarTower.algebraMap_eq B ↥T' A).symm)
    (M₁.q_fst _ _ _) (by rw [q_snd]; rfl) (M₂.q_fst _ _ _) (by rw [q_snd]; rfl)
  change (e₁.hom ≫ M₁.q ↥T' _ _) ≫ e₀.hom = e₂.hom ≫ M₂.q ↥T' _ _
  rw [Category.assoc, hc]
  change e₁.hom ≫ (e₁.inv ≫ e₂.hom) ≫ _ = _
  rw [← Category.assoc, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

end dock

section inc
variable (M : Model B gY) (W₀ : M.X₀.Opens) (hc : IsCompact (W₀ : Set ↥M.X₀))
  {W : Scheme.{u}} (k : W ⟶ Y) [IsOpenImmersion k] (h : M.π ⁻¹ᵁ W₀ = k.opensRange)
  (gW : W ⟶ Spec (CommRingCat.of A)) (hgW : gW = k ≫ gY)
  (B' : Type u) [CommRing B'] [Algebra B' A] (φ : B →+* B') (hφ : (algebraMap B' A).comp φ =
    algebraMap B A)

/-- The open immersion between base-changed models induced by restriction. -/
noncomputable def inc :
    ((M.restrictOpen W₀ hc k h gW hgW).map B' φ hφ).X₀ ⟶ (M.map B' φ hφ).X₀ :=
  (pullbackRightPullbackFstIso M.f₀ (Spec.map (CommRingCat.ofHom φ)) W₀.ι).inv ≫
    pullback.snd W₀.ι (pullback.fst M.f₀ (Spec.map (CommRingCat.ofHom φ)))

scoped instance : IsOpenImmersion (M.inc W₀ hc k h gW hgW B' φ hφ) := by
  change IsOpenImmersion
    ((pullbackRightPullbackFstIso M.f₀ (Spec.map (CommRingCat.ofHom φ)) W₀.ι).inv ≫
      pullback.snd W₀.ι (pullback.fst M.f₀ (Spec.map (CommRingCat.ofHom φ))))
  exact IsOpenImmersion.comp _ _

@[scoped simp] theorem inc_fst : M.inc W₀ hc k h gW hgW B' φ hφ ≫ pullback.fst M.f₀ (Spec.map
  (CommRingCat.ofHom φ)) =
    pullback.fst (W₀.ι ≫ M.f₀) (Spec.map (CommRingCat.ofHom φ)) ≫ W₀.ι := by
  exact (Category.assoc _ _ _).trans
    (pullbackRightPullbackFstIso_inv_snd_fst M.f₀ (Spec.map (CommRingCat.ofHom φ)) W₀.ι)

@[scoped simp] theorem inc_snd : M.inc W₀ hc k h gW hgW B' φ hφ ≫ pullback.snd M.f₀ (Spec.map
  (CommRingCat.ofHom φ)) =
    pullback.snd (W₀.ι ≫ M.f₀) (Spec.map (CommRingCat.ofHom φ)) := by
  exact (Category.assoc _ _ _).trans
    (pullbackRightPullbackFstIso_inv_snd_snd M.f₀ (Spec.map (CommRingCat.ofHom φ)) W₀.ι)

theorem inc_f₀ : M.inc W₀ hc k h gW hgW B' φ hφ ≫ (M.map B' φ hφ).f₀ =
    ((M.restrictOpen W₀ hc k h gW hgW).map B' φ hφ).f₀ :=
  M.inc_snd W₀ hc k h gW hgW B' φ hφ

theorem inc_opensRange : (M.inc W₀ hc k h gW hgW B' φ hφ).opensRange =
    (pullback.fst M.f₀ (Spec.map (CommRingCat.ofHom φ))) ⁻¹ᵁ W₀ := by
  refine (Scheme.Hom.opensRange_comp_of_isIso
    (pullbackRightPullbackFstIso M.f₀ (Spec.map (CommRingCat.ofHom φ)) W₀.ι).inv
    (pullback.snd W₀.ι (pullback.fst M.f₀ (Spec.map (CommRingCat.ofHom φ))))).trans ?_
  apply TopologicalSpace.Opens.ext
  rw [Scheme.Hom.coe_opensRange, Scheme.Pullback.range_snd, Scheme.Opens.range_ι]
  rfl

theorem rmap_π_fst : ((M.restrictOpen W₀ hc k h gW hgW).map B' φ hφ).π ≫
    pullback.fst (W₀.ι ≫ M.f₀) (Spec.map (CommRingCat.ofHom φ)) = (M.restrictOpen W₀ hc k h gW
      hgW).π :=
  map_π_fst (M.restrictOpen W₀ hc k h gW hgW) B' φ hφ

theorem rmap_π_snd : ((M.restrictOpen W₀ hc k h gW hgW).map B' φ hφ).π ≫
    pullback.snd (W₀.ι ≫ M.f₀) (Spec.map (CommRingCat.ofHom φ)) = gW ≫ ι A B' :=
  map_π_snd (M.restrictOpen W₀ hc k h gW hgW) B' φ hφ

theorem sq_inc : IsPullback k ((M.restrictOpen W₀ hc k h gW hgW).map B' φ hφ).π (M.map B' φ hφ).π
    (M.inc W₀ hc k h gW hgW B' φ hφ) := by
  apply IsPullback.flip
  apply IsOpenImmersion.isPullback
  · apply pullback.hom_ext
    · have hl := (Category.assoc k (M.map B' φ hφ).π
          (pullback.fst M.f₀ (Spec.map (CommRingCat.ofHom φ)))).trans
            (congrArg (fun t => k ≫ t) (M.map_π_fst B' φ hφ))
      have hr := (Category.assoc ((M.restrictOpen W₀ hc k h gW hgW).map B' φ hφ).π
          (M.inc W₀ hc k h gW hgW B' φ hφ)
          (pullback.fst M.f₀ (Spec.map (CommRingCat.ofHom φ)))).trans
            ((congrArg (fun t => ((M.restrictOpen W₀ hc k h gW hgW).map B' φ hφ).π ≫ t)
              (M.inc_fst W₀ hc k h gW hgW B' φ hφ)).trans
                ((Category.assoc _ _ _).symm.trans
                  ((congrArg (fun t => t ≫ W₀.ι)
                    (M.rmap_π_fst W₀ hc k h gW hgW B' φ hφ)).trans
                      (M.restrictOpen_π_ι W₀ hc k h gW hgW))))
      exact hl.trans hr.symm
    · have hl := (Category.assoc k (M.map B' φ hφ).π
          (pullback.snd M.f₀ (Spec.map (CommRingCat.ofHom φ)))).trans
            (congrArg (fun t => k ≫ t) (M.map_π_snd B' φ hφ))
      have hr := (Category.assoc ((M.restrictOpen W₀ hc k h gW hgW).map B' φ hφ).π
          (M.inc W₀ hc k h gW hgW B' φ hφ)
          (pullback.snd M.f₀ (Spec.map (CommRingCat.ofHom φ)))).trans
            ((congrArg (fun t => ((M.restrictOpen W₀ hc k h gW hgW).map B' φ hφ).π ≫ t)
              (M.inc_snd W₀ hc k h gW hgW B' φ hφ)).trans
                ((M.rmap_π_snd W₀ hc k h gW hgW B' φ hφ).trans
                  ((congrArg (fun t => t ≫ ι A B') hgW).trans (Category.assoc _ _ _))))
      exact hl.trans hr.symm
  · exact (congrArg (fun t => (M.map B' φ hφ).π ⁻¹ᵁ t)
      (M.inc_opensRange W₀ hc k h gW hgW B' φ hφ)).trans
        ((M.map_π_preimage B' φ hφ W₀).trans h)

end inc

end Model

open Lean Elab Command in
run_cmd
  for word in
      (["AlgebraicCurves.Geometry.Schemes.Proofs.UnionDescent.UnionModel.Model"] : List String) do
    let ns := word.toName
    for ext in (← scopedEnvExtensionsRef.get) do
      modifyEnv fun env =>
        let st := ext.ext.getState env
        match st.stateStack with
        | top :: stack =>
          let top := { top with activeScopes := top.activeScopes.erase ns }
          ext.activateScoped (ext.ext.setState env { st with stateStack := top :: stack }) ns
        | _ => env

end UnionModel

open Lean Elab Command in
run_cmd
  for word in
      (["AlgebraicCurves.Geometry.Schemes.Proofs.UnionDescent.UnionModel.Model",
        "AlgebraicCurves.Geometry.Schemes.Proofs.UnionDescent.UnionModel"] : List String) do
    let ns := word.toName
    for ext in (← scopedEnvExtensionsRef.get) do
      modifyEnv fun env =>
        let st := ext.ext.getState env
        match st.stateStack with
        | top :: stack =>
          let top := { top with activeScopes := top.activeScopes.erase ns }
          ext.activateScoped (ext.ext.setState env { st with stateStack := top :: stack }) ns
        | _ => env

end AlgebraicCurves.Geometry.Schemes.Proofs.UnionDescent

namespace AlgebraicGeometry

open scoped
  AlgebraicCurves.Geometry.Schemes.Proofs.UnionDescent.UnionModel.Model

open CategoryTheory CategoryTheory.Limits
open AlgebraicCurves.Geometry.Schemes.Proofs.UnionDescent

universe u

open _root_.AlgebraicCurves.Geometry.Schemes.Proofs.UnionDescent.UnionModel UnionModel.Model

theorem exists_fg_subalgebra_isPullback_of_iSup_eq_top_of_locallyOfFinitePresentation
    {A₀ R A : Type u} [CommRing A₀] [CommRing R] [CommRing A] [Algebra A₀ R] [Algebra R A] [Algebra
      A₀ A]
    [IsScalarTower A₀ R A] [Algebra.FiniteType A₀ R]
    {X : Scheme.{u}} (g : X ⟶ Spec (CommRingCat.of A))
    [QuasiCompact g] [QuasiSeparated g] [LocallyOfFinitePresentation g]
    (U V : X.Opens) (hUV : U ⊔ V = ⊤) (hUc : IsCompact (U : Set ↥X)) (hVc : IsCompact (V : Set ↥X))
    (hU : ∀ SS : Finset A, ∃ (T : Subalgebra A₀ A), T.FG ∧ (↑SS : Set A) ⊆ T ∧ Set.range
      (algebraMap R A) ⊆ T ∧
        ∃ (X₀ : Scheme.{u}) (f₀ : X₀ ⟶ Spec (CommRingCat.of ↥T)) (π : (U : Scheme.{u}) ⟶ X₀),
          LocallyOfFinitePresentation f₀ ∧ QuasiCompact f₀ ∧ QuasiSeparated f₀ ∧
          IsPullback π (U.ι ≫ g) f₀ (Spec.map (CommRingCat.ofHom (algebraMap ↥T A))))
    (hV : ∀ SS : Finset A, ∃ (T : Subalgebra A₀ A), T.FG ∧ (↑SS : Set A) ⊆ T ∧ Set.range
      (algebraMap R A) ⊆ T ∧
        ∃ (X₀ : Scheme.{u}) (f₀ : X₀ ⟶ Spec (CommRingCat.of ↥T)) (π : (V : Scheme.{u}) ⟶ X₀),
          LocallyOfFinitePresentation f₀ ∧ QuasiCompact f₀ ∧ QuasiSeparated f₀ ∧
          IsPullback π (V.ι ≫ g) f₀ (Spec.map (CommRingCat.ofHom (algebraMap ↥T A))))
    (SS : Finset A) :
    ∃ (T : Subalgebra A₀ A), T.FG ∧ (↑SS : Set A) ⊆ T ∧ Set.range (algebraMap R A) ⊆ T ∧
        ∃ (X₀ : Scheme.{u}) (f₀ : X₀ ⟶ Spec (CommRingCat.of ↥T)) (π : X ⟶ X₀),
          LocallyOfFinitePresentation f₀ ∧ QuasiCompact f₀ ∧ QuasiSeparated f₀ ∧
          IsPullback π g f₀ (Spec.map (CommRingCat.ofHom (algebraMap ↥T A))) := by
  classical
  have : QuasiSeparatedSpace ↥X := quasiSeparatedSpace_of_quasiSeparated g
  obtain ⟨T₁, hT₁, hSS₁, hR₁, X₁, f₁, π₁, l₁, c₁, s₁, sq₁⟩ := hU SS
  obtain ⟨t₁, ht₁⟩ := hT₁
  obtain ⟨T₂, hT₂, hSS₂, hR₂, X₂, f₂, π₂, l₂, c₂, s₂, sq₂⟩ := hV (SS ∪ t₁)
  have h12 : T₁ ≤ T₂ := by
    rw [← ht₁]
    exact Algebra.adjoin_le fun a ha => hSS₂ (Finset.mem_coe.mpr (Finset.mem_union_right _
      (Finset.mem_coe.mp ha)))
  have hSS : (↑SS : Set A) ⊆ T₂ := fun a ha => hSS₂ (Finset.mem_coe.mpr (Finset.mem_union_left _
    (Finset.mem_coe.mp ha)))
  let MU₁ : Model ↥T₁ (U.ι ≫ g) := ⟨X₁, f₁, π₁, l₁, c₁, s₁, sq₁⟩
  let MV₂ : Model ↥T₂ (V.ι ≫ g) := ⟨X₂, f₂, π₂, l₂, c₂, s₂, sq₂⟩
  let MU₂ : Model ↥T₂ (U.ι ≫ g) := MU₁.map ↥T₂ (Subalgebra.inclusion h12).toRingHom (RingHom.ext
    fun x => rfl)
  have hUV' : IsCompact ((U : Set ↥X) ∩ (V : Set ↥X)) := IsCompact.inter_of_isOpen hUc hVc U.2 V.2
  have hWU : IsCompact ((U.ι ⁻¹ᵁ V : (U : Scheme.{u}).Opens) : Set ↥(U : Scheme.{u})) := by
    have h2 := Topology.IsInducing.isCompact_preimage' U.ι.isOpenEmbedding.isInducing hUV'
      (by rw [Scheme.Opens.range_ι]; exact Set.inter_subset_left)
    convert h2 using 1
    ext x
    exact ⟨fun h => ⟨Scheme.Opens.range_ι U ▸ Set.mem_range_self x, h⟩, fun h => h.2⟩
  have hWV : IsCompact ((V.ι ⁻¹ᵁ U : (V : Scheme.{u}).Opens) : Set ↥(V : Scheme.{u})) := by
    have h2 := Topology.IsInducing.isCompact_preimage' V.ι.isOpenEmbedding.isInducing hUV'
      (by rw [Scheme.Opens.range_ι]; exact Set.inter_subset_right)
    convert h2 using 1
    ext x
    exact ⟨fun h => ⟨h, Scheme.Opens.range_ι V ▸ Set.mem_range_self x⟩, fun h => h.1⟩
  obtain ⟨T₃', hT₃', -, W₀U, hW₀U, hpreU⟩ := MU₂.exists_open (U.ι ⁻¹ᵁ V) hWU ∅
  obtain ⟨hT₃, h23⟩ := Subalgebra.fg_restrictScalars_and_le_of_fg T₂ hT₂ T₃' hT₃'
  let T₃ : Subalgebra A₀ A := T₃'.restrictScalars A₀
  let MU₃ : Model ↥T₃ (U.ι ≫ g) := MU₂.toStage T₃'
  let MV₃ : Model ↥T₃ (V.ι ≫ g) := MV₂.toStage T₃'
  obtain ⟨T₄', hT₄', -, W₀V, hW₀V, hpreV⟩ := MV₃.exists_open (V.ι ⁻¹ᵁ U) hWV ∅
  obtain ⟨hT₄, h34⟩ := Subalgebra.fg_restrictScalars_and_le_of_fg T₃ hT₃ T₄' hT₄'
  let T₄ : Subalgebra A₀ A := T₄'.restrictScalars A₀
  let MU₄ : Model ↥T₄ (U.ι ≫ g) := MU₃.toStage T₄'
  let MV₄ : Model ↥T₄ (V.ι ≫ g) := MV₃.toStage T₄'
  let W₀U₄ : MU₄.X₀.Opens := (pullback.fst MU₃.f₀ (Spec.map (CommRingCat.ofHom (algebraMap ↥T₃
    ↥T₄')))) ⁻¹ᵁ W₀U
  have hW₀U₄ : IsCompact (W₀U₄ : Set ↥MU₄.X₀) := MU₃.isCompact_fst_preimage _ _ _ W₀U hW₀U
  have hpreU₄ : MU₄.π ⁻¹ᵁ W₀U₄ = U.ι ⁻¹ᵁ V := by rw [← hpreU]; exact MU₃.map_π_preimage _ _ _ W₀U
  let kU := pullback.fst U.ι V.ι
  let kV := pullback.snd U.ι V.ι
  let gW : pullback U.ι V.ι ⟶ Spec (CommRingCat.of A) := kU ≫ U.ι ≫ g
  have hkU : MU₄.π ⁻¹ᵁ W₀U₄ = (pullback.fst U.ι V.ι).opensRange := by
    rw [hpreU₄, Scheme.Hom.opensRange_pullbackFst, Scheme.Opens.opensRange_ι]
  have hkV : MV₄.π ⁻¹ᵁ W₀V = (pullback.snd U.ι V.ι).opensRange := by
    rw [hpreV, Scheme.Hom.opensRange_pullbackSnd, Scheme.Opens.opensRange_ι]
  have hgW : gW = kV ≫ V.ι ≫ g := by
    change pullback.fst U.ι V.ι ≫ U.ι ≫ g = pullback.snd U.ι V.ι ≫ V.ι ≫ g
    rw [← Category.assoc, pullback.condition, Category.assoc]
  let MWU : Model ↥T₄ gW := MU₄.restrictOpen W₀U₄ hW₀U₄ kU hkU gW rfl
  let MWV : Model ↥T₄ gW := MV₄.restrictOpen W₀V hW₀V kV hkV gW hgW
  obtain ⟨T₅', hT₅', -, e₀, he₀f, he₀π⟩ := Model.exists_iso MWU MWV ∅
  obtain ⟨hT₅, h45⟩ := Subalgebra.fg_restrictScalars_and_le_of_fg T₄ hT₄ T₅' hT₅'
  let T₅ : Subalgebra A₀ A := T₅'.restrictScalars A₀
  let MU₅ : Model ↥T₅ (U.ι ≫ g) := MU₄.toStage T₅'
  let MV₅ : Model ↥T₅ (V.ι ≫ g) := MV₄.toStage T₅'
  let MWU₅ : Model ↥T₅ gW := MWU.toStage T₅'
  let MWV₅ : Model ↥T₅ gW := MWV.toStage T₅'
  let incU := MU₄.inc W₀U₄ hW₀U₄ kU hkU gW rfl ↥T₅' (algebraMap ↥T₄ ↥T₅')
    (IsScalarTower.algebraMap_eq ↥T₄ ↥T₅' A).symm
  let incV := MV₄.inc W₀V hW₀V kV hkV gW hgW ↥T₅' (algebraMap ↥T₄ ↥T₅')
    (IsScalarTower.algebraMap_eq ↥T₄ ↥T₅' A).symm
  have e1 : incU ≫ MU₅.f₀ = MWU₅.f₀ := MU₄.inc_f₀ W₀U₄ hW₀U₄ kU hkU gW rfl ↥T₅' _ _
  have e2 : incV ≫ MV₅.f₀ = MWV₅.f₀ := MV₄.inc_f₀ W₀V hW₀V kV hkV gW hgW ↥T₅' _ _
  have hab : incU ≫ MU₅.f₀ = (e₀.hom ≫ incV) ≫ MV₅.f₀ := by
    rw [Category.assoc, e1, e2]
    exact he₀f.symm
  have : QuasiCompact (incU ≫ MU₅.f₀) := by rw [e1]; exact MWU₅.qc
  have hcov : Set.range U.ι.base ∪ Set.range V.ι.base = Set.univ := by
    rw [Scheme.Opens.range_ι, Scheme.Opens.range_ι, ← TopologicalSpace.Opens.coe_sup, hUV]; rfl
  have hWU₅ : IsPullback kU MWU₅.π MU₅.π incU := MU₄.sq_inc W₀U₄ hW₀U₄ kU hkU gW rfl ↥T₅' _ _
  have hWV₅' : IsPullback kV MWV₅.π MV₅.π incV := MV₄.sq_inc W₀V hW₀V kV hkV gW hgW ↥T₅' _ _
  have hWV₅ : IsPullback kV MWU₅.π MV₅.π (e₀.hom ≫ incV) := by
    refine IsPullback.of_iso hWV₅' (Iso.refl _) (Iso.refl _) e₀.symm (Iso.refl _)
      (by simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]) ?_
      (by simp only [Iso.refl_hom, Category.comp_id, Category.id_comp])
      (by
        exact (Category.comp_id incV).trans
          ((Category.id_comp incV).symm.trans
            ((congrArg (fun t => t ≫ incV) e₀.inv_hom_id.symm).trans
              (Category.assoc _ _ _))))
    rw [Iso.refl_hom, Category.id_comp, Iso.symm_hom, ← he₀π, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  obtain ⟨X₀, f₀, π, iU, iV, -, -, -, -, -, -, -, -, -, hqc, hqs, hlfp, hsq⟩ :=
    AlgebraicGeometry.exists_isPullback_glue_of_isPullback_of_isOpenImmersion (R := ↥T₅) (A := A)
      MU₅.f₀ MV₅.f₀ incU (e₀.hom ≫ incV) hab g U.ι V.ι hcov kU kV (IsPullback.of_hasPullback U.ι
        V.ι)
      MU₅.π MU₅.sq MV₅.π MV₅.sq MWU₅.π hWU₅ hWV₅
  refine ⟨T₅, hT₅, fun a ha => h45 (h34 (h23 (hSS ha))), fun a ha => h45 (h34 (h23 (hR₂ ha))),
    X₀, f₀, π, hlfp, hqc, hqs, hsq⟩

end AlgebraicGeometry
end ProofImplementation
