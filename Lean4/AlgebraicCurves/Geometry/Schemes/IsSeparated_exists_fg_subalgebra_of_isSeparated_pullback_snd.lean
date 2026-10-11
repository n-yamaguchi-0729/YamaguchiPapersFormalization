/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_IsSeparated_exists_fg_subalgebra_of_isSeparated_pullback_snd.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Geometry.Schemes.IsClosedImmersion_exists_fg_subalgebra_of_isClosedImmersion_pullback_map

/-!
# Is Separated exists fg subalgebra of is Separated pullback snd
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs
namespace IsSeparated_exists_fg_subalgebra_of_isSeparated_pullback_snd
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

namespace SepDescAux

section bridge

variable {U U' X S Y : Scheme.{u}} (a : U ⟶ X) (b : U' ⟶ X) (f : X ⟶ S) (g : Y ⟶ S)

/-- The comparison isomorphism between the target pullbacks of the base-changed chart. -/
noncomputable def eT :
    pullback (pullback.snd a (pullback.fst f g) ≫ pullback.snd f g) (pullback.snd b (pullback.fst f
      g) ≫ pullback.snd f g) ≅ pullback (pullback.fst (a ≫ f) (b ≫ f) ≫ a ≫ f) g where
  hom := pullback.lift
    (pullback.lift (pullback.fst _ _ ≫ pullback.fst a (pullback.fst f g)) (pullback.snd _ _ ≫
      pullback.fst b (pullback.fst f g))
      (by
        have hT := pullback.condition_assoc (f := pullback.snd a (pullback.fst f g) ≫ pullback.snd
          f g) (g := pullback.snd b (pullback.fst f g) ≫ pullback.snd f g) g
        simp only [Category.assoc] at hT
        simp only [Category.assoc]
        rw [pullback.condition_assoc (f := a) (g := pullback.fst f g), pullback.condition (f := f)
          (g := g), hT,
          ← pullback.condition (f := f) (g := g), ← pullback.condition_assoc (f := b) (g :=
            pullback.fst f g)]))
    (pullback.fst _ _ ≫ pullback.snd a (pullback.fst f g) ≫ pullback.snd f g)
    (by
      simp only [Category.assoc, pullback.lift_fst_assoc]
      rw [pullback.condition_assoc (f := a) (g := pullback.fst f g), pullback.condition (f := f) (g
        := g)])
  inv := pullback.lift
    (pullback.lift (pullback.fst _ _ ≫ pullback.fst (a ≫ f) (b ≫ f))
      (pullback.lift (pullback.fst _ _ ≫ pullback.fst (a ≫ f) (b ≫ f) ≫ a) (pullback.snd _ _)
        (by simpa only [Category.assoc] using
          pullback.condition (f := (pullback.fst (a ≫ f) (b ≫ f) ≫ a ≫ f)) (g := g)))
      (by simp))
    (pullback.lift (pullback.fst _ _ ≫ pullback.snd (a ≫ f) (b ≫ f))
      (pullback.lift (pullback.fst _ _ ≫ pullback.snd (a ≫ f) (b ≫ f) ≫ b) (pullback.snd _ _)
        (by
          simp only [Category.assoc]
          rw [← pullback.condition (f := a ≫ f) (g := b ≫ f)]
          simpa only [Category.assoc] using pullback.condition (f := (pullback.fst (a ≫ f) (b ≫ f)
            ≫ a ≫ f)) (g := g)))
      (by simp))
    (by simp)
  hom_inv_id := by
    ext <;> simp [pullback.condition]
  inv_hom_id := by
    ext <;> simp

/-- The comparison isomorphism between the source pullbacks of the base-changed chart. -/
noncomputable def eS :
    pullback (pullback.snd a (pullback.fst f g)) (pullback.snd b (pullback.fst f g)) ≅ pullback
      (pullback.mapDesc a b f ≫ pullback.fst (a ≫ f) (b ≫ f) ≫ a ≫ f) g where
  hom := pullback.lift
    (pullback.lift (pullback.fst _ _ ≫ pullback.fst a (pullback.fst f g)) (pullback.snd _ _ ≫
      pullback.fst b (pullback.fst f g))
      (by
        have hS := pullback.condition_assoc (f := pullback.snd a (pullback.fst f g)) (g :=
          pullback.snd b (pullback.fst f g)) (pullback.fst f g)
        simp only [Category.assoc]
        rw [pullback.condition (f := a) (g := pullback.fst f g), hS, ← pullback.condition (f := b)
          (g := pullback.fst f g)]))
    (pullback.fst _ _ ≫ pullback.snd a (pullback.fst f g) ≫ pullback.snd f g)
    (by
      simp only [Category.assoc, pullback.lift_fst_assoc, Category.comp_id]
      rw [pullback.condition_assoc (f := a) (g := pullback.fst f g), pullback.condition (f := f) (g
        := g)])
  inv := pullback.lift
    (pullback.lift (pullback.fst _ _ ≫ pullback.fst a b)
      (pullback.lift (pullback.fst _ _ ≫ pullback.fst a b ≫ a) (pullback.snd _ _)
        (by
          have := pullback.condition (f := (pullback.mapDesc a b f ≫ pullback.fst (a ≫ f) (b ≫ f) ≫
            a ≫ f)) (g := g)
          simp only [pullback.lift_fst_assoc, Category.comp_id] at this
          simpa only [Category.assoc] using this))
      (by simp))
    (pullback.lift (pullback.fst _ _ ≫ pullback.snd a b)
      (pullback.lift (pullback.fst _ _ ≫ pullback.fst a b ≫ a) (pullback.snd _ _)
        (by
          have := pullback.condition (f := (pullback.mapDesc a b f ≫ pullback.fst (a ≫ f) (b ≫ f) ≫
            a ≫ f)) (g := g)
          simp only [pullback.lift_fst_assoc, Category.comp_id] at this
          simpa only [Category.assoc] using this))
      (by simp [pullback.condition]))
    (by simp)
  hom_inv_id := by
    have hS2 := pullback.condition_assoc (f := pullback.snd a (pullback.fst f g)) (g :=
      pullback.snd b (pullback.fst f g)) (pullback.snd f g)
    ext <;> simp [pullback.condition, hS2]
  inv_hom_id := by
    ext <;> simp

lemma eS_hom_mY :
    (eS a b f g).hom ≫ pullback.map (pullback.mapDesc a b f ≫ pullback.fst (a ≫ f) (b ≫ f) ≫ a ≫ f)
      g (pullback.fst (a ≫ f) (b ≫ f) ≫ a ≫ f) g (pullback.mapDesc a b f) (𝟙 Y) (𝟙 S)
      (by simp) (by simp) =
      pullback.mapDesc (pullback.snd a (pullback.fst f g)) (pullback.snd b (pullback.fst f g))
        (pullback.snd f g) ≫ (eT a b f g).hom := by
  have hS2 := pullback.condition_assoc (f := pullback.snd a (pullback.fst f g)) (g := pullback.snd
    b (pullback.fst f g)) (pullback.snd f g)
  ext <;> simp [eS, eT, pullback.condition, hS2]

theorem isClosedImmersion_iff :
    IsClosedImmersion (pullback.mapDesc (pullback.snd a (pullback.fst f g)) (pullback.snd b
      (pullback.fst f g)) (pullback.snd f g)) ↔
      IsClosedImmersion (pullback.map (pullback.mapDesc a b f ≫ pullback.fst (a ≫ f) (b ≫ f) ≫ a ≫
        f) g (pullback.fst (a ≫ f) (b ≫ f) ≫ a ≫ f) g (pullback.mapDesc a b f) (𝟙 Y) (𝟙 S)
        (by simp) (by simp)) := by
  rw [← MorphismProperty.cancel_right_of_respectsIso @IsClosedImmersion
    (pullback.mapDesc (pullback.snd a (pullback.fst f g)) (pullback.snd b (pullback.fst f g))
      (pullback.snd f g)) (eT a b f g).hom, ← eS_hom_mY,
    MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion (eS a b f g).hom]

end bridge

section charts

variable {U U' X S : Scheme.{u}} (a : U ⟶ X) (b : U' ⟶ X) (f : X ⟶ S)

/-- The map between pairwise chart intersections induced by the structure morphism. -/
noncomputable abbrev chart := pullback.mapDesc a b f

/-- The structure map of the pairwise chart pullback to the base scheme. -/
noncomputable abbrev chartBase : pullback (a ≫ f) (b ≫ f) ⟶ S := pullback.fst (a ≫ f) (b ≫ f) ≫ a ≫
  f

/-- The base change of the pairwise chart comparison map. -/
noncomputable abbrev chartBC {Y : Scheme.{u}} (g : Y ⟶ S) :
    pullback (chart a b f ≫ chartBase a b f) g ⟶ pullback (chartBase a b f) g :=
  pullback.map (chart a b f ≫ chartBase a b f) g (chartBase a b f) g (chart a b f) (𝟙 Y) (𝟙 S)
    (by simp) (by simp)

lemma chartBC_fst {Y : Scheme.{u}} (g : Y ⟶ S) :
    chartBC a b f g ≫ pullback.fst _ _ = pullback.fst _ _ ≫ chart a b f := by simp [chartBC]

lemma chartBC_snd {Y : Scheme.{u}} (g : Y ⟶ S) :
    chartBC a b f g ≫ pullback.snd _ _ = pullback.snd _ _ := by simp [chartBC]

lemma eq_chartBC {Y : Scheme.{u}} (g : Y ⟶ S)
    (m' : pullback (chart a b f ≫ chartBase a b f) g ⟶ pullback (chartBase a b f) g)
    (h₁ : m' ≫ pullback.fst _ _ = pullback.fst _ _ ≫ chart a b f) (h₂ : m' ≫ pullback.snd _ _ =
      pullback.snd _ _) :
    m' = chartBC a b f g := by
  apply pullback.hom_ext
  · rw [h₁, chartBC_fst]
  · rw [h₂, chartBC_snd]

lemma isPullback_stage {Z Y₁ Y₂ : Scheme.{u}} (h : Z ⟶ S) (g₁ : Y₁ ⟶ S) (g₂ : Y₂ ⟶ S) (κ : Y₂ ⟶ Y₁)
    (hκ : κ ≫ g₁ = g₂) :
    IsPullback (pullback.snd h g₂) (pullback.map h g₂ h g₁ (𝟙 Z) κ (𝟙 S) (by simp) (by simp [hκ])) κ
      (pullback.snd h g₁) := by
  apply IsPullback.flip
  refine IsPullback.of_right (h₁₂ := pullback.fst h g₁) (v₁₃ := h) (h₂₂ := g₁) ?_ (by simp)
    (IsPullback.of_hasPullback h g₁)
  simp only [pullback.lift_fst, Category.comp_id, hκ]
  exact IsPullback.of_hasPullback h g₂

lemma isClosedImmersion_chartBC_of_fac {Y₁ Y₂ : Scheme.{u}} (g₁ : Y₁ ⟶ S) (g₂ : Y₂ ⟶ S) (κ : Y₂ ⟶
  Y₁)
    (hκ : κ ≫ g₁ = g₂) (H : IsClosedImmersion (chartBC a b f g₁)) : IsClosedImmersion (chartBC a b
      f g₂) := by
  have sqV := isPullback_stage (chartBase a b f) g₁ g₂ κ hκ
  have sqW := isPullback_stage (chart a b f ≫ chartBase a b f) g₁ g₂ κ hκ
  rw [← chartBC_snd a b f g₂, ← chartBC_snd a b f g₁] at sqW
  have sq : IsPullback (chartBC a b f g₂)
      (pullback.map _ g₂ _ g₁ (𝟙 _) κ (𝟙 S) (by simp) (by simp [hκ]))
      (pullback.map _ g₂ _ g₁ (𝟙 _) κ (𝟙 S) (by simp) (by simp [hκ]))
      (chartBC a b f g₁) :=
    IsPullback.of_right sqW (by ext <;> simp [chartBC]) sqV
  exact MorphismProperty.of_isPullback (P := @IsClosedImmersion) sq.flip H

end charts

section key

variable {X S : Scheme.{u}} (f : X ⟶ S) (𝒰 : X.OpenCover) [∀ i, IsAffine (𝒰.X i)] [IsAffine S]
  {Y : Scheme.{u}} [IsAffine Y] (g : Y ⟶ S)

include 𝒰 in
theorem isSeparated_snd_iff :
    IsSeparated (pullback.snd f g) ↔ ∀ i j : 𝒰.I₀, IsClosedImmersion (chartBC (𝒰.f i) (𝒰.f j) f g)
      := by
  let Q : AffineTargetMorphismProperty.{u} := fun X _ f =>
    IsAffine X ∧ Function.Surjective f.appTop
  have : HasAffineProperty (@IsClosedImmersion : MorphismProperty Scheme.{u}) Q :=
    IsClosedImmersion.hasAffineProperty
  have hQ := HasAffineProperty.isLocal_affineProperty
    (@IsClosedImmersion : MorphismProperty Scheme.{u}) (Q := Q)
  let 𝒱 := 𝒰.pullback₂ (pullback.fst f g)
  have hUA : ∀ i : 𝒰.I₀, IsAffine (pullback (𝒰.f i) (pullback.fst f g)) := fun i =>
    IsAffine.of_isIso (pullbackRightPullbackFstIso f g (𝒰.f i)).hom
  have : ∀ i, IsAffine (𝒱.X i) := hUA
  constructor
  · intro hsep i j
    have hd : (MorphismProperty.diagonal @IsClosedImmersion) (pullback.snd f g) :=
      hsep.isClosedImmersion_diagonal
    rw [← HasAffineProperty.diagonal_iff (@IsClosedImmersion : MorphismProperty Scheme.{u}) (Q :=
      Q)] at hd
    have hij := hd (pullback.snd (𝒰.f i) (pullback.fst f g)) (pullback.snd (𝒰.f j) (pullback.fst f
      g))
    exact (isClosedImmersion_iff (𝒰.f i) (𝒰.f j) f g).mp
      ((HasAffineProperty.iff_of_isAffine (P := (@IsClosedImmersion : MorphismProperty Scheme.{u}))
        (Q := Q)).mpr hij)
  · intro h
    have hd : (MorphismProperty.diagonal @IsClosedImmersion) (pullback.snd f g) := by
      rw [← HasAffineProperty.diagonal_iff (@IsClosedImmersion : MorphismProperty Scheme.{u}) (Q :=
        Q)]
      exact AffineTargetMorphismProperty.diagonal_of_openCover_source (pullback.snd f g) 𝒱 fun i j
        =>
        (HasAffineProperty.iff_of_isAffine (P := (@IsClosedImmersion : MorphismProperty
          Scheme.{u})) (Q := Q)).mp
          ((isClosedImmersion_iff (𝒰.f i) (𝒰.f j) f g).mpr (h i j))
    exact ⟨hd⟩

end key

end SepDescAux

open SepDescAux in
theorem _root_.AlgebraicGeometry.IsSeparated.exists_fg_subalgebra_of_isSeparated_pullback_snd
    {A₀ : Type u} [CommRing A₀] {A : Type u} [CommRing A] [Algebra A₀ A]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A₀)) [QuasiCompact f] [QuasiSeparated f]
    [IsSeparated (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))))] (s : Finset A) :
    ∃ (T : Subalgebra A₀ A), T.FG ∧ (↑s : Set A) ⊆ T ∧
      IsSeparated (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥T)))) := by
  classical
  let ι : ∀ (B : Type u) [CommRing B] [Algebra A₀ B], Spec (CommRingCat.of B) ⟶ Spec
    (CommRingCat.of A₀) :=
    fun B _ _ => Spec.map (CommRingCat.ofHom (algebraMap A₀ B))
  have : CompactSpace ↥X :=
    @QuasiCompact.compactSpace_of_compactSpace _ _ f inferInstance (inferInstance : CompactSpace
      (PrimeSpectrum A₀))
  have : QuasiSeparatedSpace ↥X := quasiSeparatedSpace_of_quasiSeparated f
  let 𝒰 := X.affineCover.finiteSubcover
  have : Fintype 𝒰.I₀ := Fintype.ofFinite _
  have inst : ∀ i j : 𝒰.I₀,
      QuasiCompact (chart (𝒰.f i) (𝒰.f j) f) ∧ QuasiSeparated (chart (𝒰.f i) (𝒰.f j) f) ∧
        LocallyOfFiniteType (chart (𝒰.f i) (𝒰.f j) f) := by
    intro i j
    have e : chart (𝒰.f i) (𝒰.f j) f ≫ pullback.fst _ _ = pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝟙 _ :=
      pullback.lift_fst _ _ _
    have : QuasiCompact (chart (𝒰.f i) (𝒰.f j) f ≫ pullback.fst _ _) := by rw [e]; infer_instance
    have : QuasiSeparated (chart (𝒰.f i) (𝒰.f j) f ≫ pullback.fst _ _) := by rw [e]; infer_instance
    have : LocallyOfFiniteType (chart (𝒰.f i) (𝒰.f j) f ≫ pullback.fst _ _) :=
      by rw [e]; infer_instance
    have hbc : MorphismProperty.IsStableUnderBaseChange (@IsAffineHom : MorphismProperty
      Scheme.{u}) :=
      isAffineHom_isStableUnderBaseChange
    have : IsAffineHom (pullback.fst (𝒰.f i ≫ f) (𝒰.f j ≫ f)) :=
      hbc.of_isPullback (IsPullback.of_hasPullback (𝒰.f i ≫ f) (𝒰.f j ≫ f)).flip
        (isAffineHom_of_isAffine (𝒰.f j ≫ f))
    exact ⟨QuasiCompact.of_comp _ (pullback.fst _ _), QuasiSeparated.of_comp _ (pullback.fst _ _),
      locallyOfFiniteType_of_comp _ (pullback.fst _ _)⟩
  have hA : ∀ i j : 𝒰.I₀, IsClosedImmersion (chartBC (𝒰.f i) (𝒰.f j) f (ι A)) :=
    (isSeparated_snd_iff f 𝒰 (ι A)).mp inferInstance
  have step : ∀ (i j : 𝒰.I₀) (t : Finset A), ∃ (T : Subalgebra A₀ A), T.FG ∧ (↑t : Set A) ⊆ T ∧
      IsClosedImmersion (chartBC (𝒰.f i) (𝒰.f j) f (ι ↥T)) := by
    intro i j t
    obtain ⟨hqc, hqs, hlft⟩ := inst i j
    obtain ⟨T, hT, htT, hci⟩ :=
      AlgebraicGeometry.IsClosedImmersion.exists_fg_subalgebra_of_isClosedImmersion_pullback_map
        (A := A) (chart (𝒰.f i) (𝒰.f j) f) (chartBase (𝒰.f i) (𝒰.f j) f)
        (fun mA h₁ h₂ => by rw [eq_chartBC _ _ _ _ mA h₁ h₂]; exact hA i j) t
    exact ⟨T, hT, htT, hci _ (chartBC_fst _ _ _ _) (chartBC_snd _ _ _ _)⟩
  have fold : ∀ (L : List (𝒰.I₀ × 𝒰.I₀)) (t : Finset A), ∃ (T : Subalgebra A₀ A), T.FG ∧ (↑t : Set
    A) ⊆ T ∧
      ∀ p ∈ L, IsClosedImmersion (chartBC (𝒰.f p.1) (𝒰.f p.2) f (ι ↥T)) := by
    intro L
    induction L with
    | nil =>
      intro t
      exact ⟨Algebra.adjoin A₀ ↑t, Subalgebra.fg_adjoin_finset t, Algebra.subset_adjoin, fun p hp
        => by simp at hp⟩
    | cons p L ih =>
      intro t
      obtain ⟨T₁, ⟨t₁, ht₁⟩, htT₁, hL⟩ := ih t
      obtain ⟨T, hT, ht₁T, hp⟩ := step p.1 p.2 t₁
      have h₁ : T₁ ≤ T := by rw [← ht₁]; exact Algebra.adjoin_le ht₁T
      refine ⟨T, hT, htT₁.trans h₁, ?_⟩
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq'
      · exact hp
      · refine isClosedImmersion_chartBC_of_fac (𝒰.f q.1) (𝒰.f q.2) f (ι ↥T₁) (ι ↥T)
          (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion h₁).toRingHom)) ?_ (hL q hq')
        change Spec.map _ ≫ Spec.map _ = Spec.map _
        rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
        rfl
  obtain ⟨T, hT, hsT, hall⟩ := fold (Finset.univ : Finset (𝒰.I₀ × 𝒰.I₀)).toList s
  exact ⟨T, hT, hsT, (isSeparated_snd_iff f 𝒰 (ι ↥T)).mpr fun i j => hall (i, j) (by simp)⟩
end IsSeparated_exists_fg_subalgebra_of_isSeparated_pullback_snd
end AlgebraicCurves.Geometry.Schemes.Proofs
end ProofImplementation
