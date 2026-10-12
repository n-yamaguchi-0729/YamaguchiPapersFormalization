/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_nonempty_normModule_curveChange_dualNumber_iso_unit_of_finrank_eq_char_of_forall_isClosed_eq.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Algebra.DualNumber
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Spec
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.RingTheory.Trace.Defs
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.Topology.Sets.Opens
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.AlgebraicCurves.Geometry.Picard.Pullback
import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesNormModule
import Nyll.AlgebraicCurves.Geometry.Deformation.RigKerDualNumber
import Nyll.SchemeTheory.Cohomology.Cech.TwoAffineOpenCover
import Nyll.AlgebraicCurves.Geometry.Schemes.TwoAffineOpenCoverH1BaseChange
import Nyll.JacobianVarieties.Picard.PicDualNumberDeformationClassSpec
import Nyll.SchemeTheory.Modules.Monoidal
import Nyll.AlgebraicCurves.Geometry.Schemes.Scheme_Hom_finrank_pullbackMap_of_comp_eq
import Nyll.AlgebraicCurves.Geometry.Schemes.Scheme_TwoAffineOpenCover_exists_basicOpen_refinement_basis_pushforward
import Nyll.JacobianVarieties.Picard.exists_isFrameOn_and_map_eq_oneAddEpsMul_smul_of_nonempty_pullback_iso_unit
import Nyll.JacobianVarieties.Picard.exists_forall_basis_pushforward_dualNumberThickening_of_forall_basis
import Nyll.JacobianVarieties.Picard.exists_isFrameOn_normModule_and_map_eq_oneAddEpsMul_trace_smul
import Nyll.AlgebraicCurves.Geometry.Schemes.trace_eq_zero_of_finrank_eq_char_of_forall_isClosed_eq
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsFrameOn_nonempty_iso_tensorUnit_of_map_eq_mul

import Nyll.JacobianVarieties.Picard.RepresentsRelSubPicPullback
import Nyll.JacobianVarieties.Picard.RepresentsRelSubPicKerPoints

/-!
Norms of infinitesimally trivial line bundles are trivial when rank equals the characteristic.
-/

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.DualNormRankCharacteristic
attribute [-instance]
  AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField
  AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd
  AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst
  AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one
  AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field
  AlgebraicGeometry.IsProper.fiberToSpecResidueField
  SheafOfModules.isIso_ihomModelToIhom
attribute [-simp]
  AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe
  AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe
  AlgebraicGeometry.RelPicard.BaseChange.restrict_P
  AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd
  AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst
  PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom
  SheafOfModules.ihomSectionsEquivFamily_unit
  AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply
  SheafOfModules.ihomEval_unit_app
  AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right
  AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left
  AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply
  SheafOfModules.unit_ihomSectionsEquivFamily
  AlgebraicGeometry.Scheme.Modules.familyOfHom_app
  AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add
  AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.RelPicard
open _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian

universe u

namespace NormDefTriv

variable {κ : Type u} [Field κ] {C C' : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of κ)) (c' : C' ⟶ Spec (CommRingCat.of κ)) (f : C' ⟶ C) (hf : f ≫ c =
    c')

scoped instance isIso_specMap_self : IsIso (specMap κ κ) := by
  rw [show specMap κ κ = 𝟙 _ by
    simp only [Scheme.TwoAffineOpenCover.specMap, Algebra.algebraMap_self, CommRingCat.ofHom_id,
      Spec.map_id]]
  infer_instance

scoped instance isIso_fst_specMap_self : IsIso (pullback.fst c (specMap κ κ)) :=
  (IsPullback.of_hasPullback c (specMap κ κ)).isIso_fst_of_isIso

theorem isIntegral_pullback_specMap_self [IsIntegral C] : IsIntegral (pullback c (specMap κ κ)) :=
  IsIntegral.of_isIso (inv (pullback.fst c (specMap κ κ)))

theorem curveHyp_pullback_specMap_self (hC : ∀ Z : Set C, IsClosed Z → Z ≠ Set.univ → Z.Finite) :
    ∀ Z : Set ↥(pullback c (specMap κ κ)), IsClosed Z → Z ≠ Set.univ → Z.Finite := by
  intro Z hZ hZne
  let φ := Scheme.homeoOfIso (asIso (pullback.fst c (specMap κ κ)))
  have himg : (φ '' Z).Finite := by
    refine hC _ (φ.isClosedMap _ hZ) ?_
    intro h
    apply hZne
    rw [← Set.image_univ_of_surjective φ.surjective] at h
    exact φ.injective.image_injective h
  exact himg.of_finite_image φ.injective.injOn

variable {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of κ))

theorem isPullback_curveChange :
    IsPullback (curveChange f hf t) (pullback.fst c' t) (pullback.fst c t) f := by
  refine IsPullback.of_right ?_ ?_ (IsPullback.of_hasPullback c t).flip
  · rw [curveChange_snd]
    subst hf
    exact (IsPullback.of_hasPullback (f ≫ c) t).flip
  · simp only [curveChange, pullback.lift_fst]

scoped instance isFinite_curveChange [IsFinite f] : IsFinite (curveChange f hf t) :=
  MorphismProperty.of_isPullback (P := @IsFinite) (isPullback_curveChange c c' f hf t).flip ‹_›
scoped instance flat_curveChange [Flat f] : Flat (curveChange f hf t) :=
  MorphismProperty.of_isPullback (P := @Flat) (isPullback_curveChange c c' f hf t).flip ‹_›
scoped instance locallyOfFinitePresentation_curveChange [LocallyOfFinitePresentation f] :
    LocallyOfFinitePresentation (curveChange f hf t) :=
  MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) (isPullback_curveChange c c' f
    hf t).flip ‹_›
scoped instance isAffineHom_curveChange [IsAffineHom f] : IsAffineHom (curveChange f hf t) :=
  MorphismProperty.of_isPullback (P := @IsAffineHom) (isPullback_curveChange c c' f hf t).flip ‹_›

theorem finrank_curveChange [IsFinite f] [Flat f] {p : ℕ} (hrk : ∀ y, f.finrank y = p) (y) :
    (curveChange f hf t).finrank y = p := by
  have h := AlgebraicGeometry.Scheme.Hom.finrank_pullbackMap_of_comp_eq c c' t f hf y
  simp only [curveChange]
  exact h.trans (hrk _)

theorem hinj_curveChange_specMap_self
    (hinj : ∀ x₁ x₂ : C', IsClosed ({x₁} : Set C') → IsClosed ({x₂} : Set C') → f.base x₁ = f.base
      x₂ → x₁ = x₂)
    (x₁ x₂ : ↥(pullback c' (specMap κ κ))) (h₁ : IsClosed ({x₁} : Set _)) (h₂ : IsClosed ({x₂} :
      Set _))
    (h : (curveChange f hf (specMap κ κ)).base x₁ = (curveChange f hf (specMap κ κ)).base x₂) : x₁
      = x₂ := by
  let φ' := Scheme.homeoOfIso (asIso (pullback.fst c' (specMap κ κ)))
  have hcomm : ∀ x, f.base ((pullback.fst c' (specMap κ κ)).base x) =
      (pullback.fst c (specMap κ κ)).base ((curveChange f hf (specMap κ κ)).base x) := fun x => by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply]
    congr 2
    simp only [curveChange, pullback.lift_fst]
  apply φ'.injective
  refine hinj _ _ ?_ ?_ ?_
  · simpa only [Set.image_singleton] using φ'.isClosedMap _ h₁
  · simpa only [Set.image_singleton] using φ'.isClosedMap _ h₂
  · change f.base ((pullback.fst c' (specMap κ κ)).base x₁) = f.base ((pullback.fst c' (specMap κ
      κ)).base x₂)
    rw [hcomm, hcomm, h]

theorem basisOn_congr {X : Scheme.{u}} (M : X.Modules) {p : ℕ} {U U' : X.Opens} (h : U' = U)
    (H : ∃ e : Fin p → Γ(M, U), ∀ (W : X.Opens) (hW : W ≤ U),
      ∃ b : Module.Basis (Fin p) Γ(X, W) Γ(M, W), ∀ i, b i = M.presheaf.map (homOfLE hW).op (e i)) :
    ∃ e : Fin p → Γ(M, U'), ∀ (W : X.Opens) (hW : W ≤ U'),
      ∃ b : Module.Basis (Fin p) Γ(X, W) Γ(M, W), ∀ i, b i = M.presheaf.map (homOfLE hW).op (e i)
        := by
  subst h; exact H

theorem exists_twoAffineOpenCover_forall_basis [IsIntegral C]
    (hC : ∀ Z : Set C, IsClosed Z → Z ≠ Set.univ → Z.Finite) (𝒱 : C.TwoAffineOpenCover)
    [IsFinite f] [Flat f] [LocallyOfFinitePresentation f] {p : ℕ} (hrk : ∀ y, f.finrank y = p) :
    ∃ 𝒱' : C.TwoAffineOpenCover,
      (∃ e : Fin p → Γ((Scheme.Modules.pushforward (curveChange f hf (specMap κ κ))).obj (𝟙_ _),
        (𝒱'.pullback c κ).U0),
        ∀ (W : (pullback c (specMap κ κ)).Opens) (hW : W ≤ (𝒱'.pullback c κ).U0),
          ∃ b : Module.Basis (Fin p) Γ(pullback c (specMap κ κ), W)
              Γ((Scheme.Modules.pushforward (curveChange f hf (specMap κ κ))).obj (𝟙_ _), W),
            ∀ i, b i = ((Scheme.Modules.pushforward (curveChange f hf (specMap κ κ))).obj (𝟙_
              _)).presheaf.map
              (homOfLE hW).op (e i)) ∧
      (∃ e : Fin p → Γ((Scheme.Modules.pushforward (curveChange f hf (specMap κ κ))).obj (𝟙_ _),
        (𝒱'.pullback c κ).U1),
        ∀ (W : (pullback c (specMap κ κ)).Opens) (hW : W ≤ (𝒱'.pullback c κ).U1),
          ∃ b : Module.Basis (Fin p) Γ(pullback c (specMap κ κ), W)
              Γ((Scheme.Modules.pushforward (curveChange f hf (specMap κ κ))).obj (𝟙_ _), W),
            ∀ i, b i = ((Scheme.Modules.pushforward (curveChange f hf (specMap κ κ))).obj (𝟙_
              _)).presheaf.map
              (homOfLE hW).op (e i)) := by
  classical
  have : IsIntegral (pullback c (specMap κ κ)) := isIntegral_pullback_specMap_self c
  have hX := curveHyp_pullback_specMap_self c hC
  have hd : ∀ x, (curveChange f hf (specMap κ κ)).finrank x = p := finrank_curveChange c c' f hf _
    hrk
  let φh := Scheme.homeoOfIso (asIso (pullback.fst c (specMap κ κ)))
  obtain ⟨𝒱n, hn0, hn1⟩ : ∃ 𝒱n : C.TwoAffineOpenCover, (𝒱n.U0 : Set C).Nonempty ∧ (𝒱n.U1 : Set
    C).Nonempty := by
    by_cases h0 : (𝒱.U0 : Set C).Nonempty <;> by_cases h1 : (𝒱.U1 : Set C).Nonempty
    · exact ⟨𝒱, h0, h1⟩
    · have hU1 : 𝒱.U1 = ⊥ :=
        TopologicalSpace.Opens.ext
          (by rw [TopologicalSpace.Opens.coe_bot]; exact Set.not_nonempty_iff_eq_empty.mp h1)
      have hU0 : 𝒱.U0 = ⊤ := by simpa only [hU1, sup_bot_eq] using 𝒱.sup_eq_top
      refine ⟨⟨𝒱.U0, 𝒱.U0, 𝒱.isAffineOpen_U0, 𝒱.isAffineOpen_U0, by rw [hU0, sup_idem], by
        rw [inf_idem]; exact 𝒱.isAffineOpen_U0⟩, h0, h0⟩
    · have hU0 : 𝒱.U0 = ⊥ :=
        TopologicalSpace.Opens.ext
          (by rw [TopologicalSpace.Opens.coe_bot]; exact Set.not_nonempty_iff_eq_empty.mp h0)
      have hU1 : 𝒱.U1 = ⊤ := by simpa only [hU0, bot_sup_eq] using 𝒱.sup_eq_top
      refine ⟨⟨𝒱.U1, 𝒱.U1, 𝒱.isAffineOpen_U1, 𝒱.isAffineOpen_U1, by rw [hU1, sup_idem], by
        rw [inf_idem]; exact 𝒱.isAffineOpen_U1⟩, h1, h1⟩
    · exfalso
      have hU0 : 𝒱.U0 = ⊥ :=
        TopologicalSpace.Opens.ext
          (by rw [TopologicalSpace.Opens.coe_bot]; exact Set.not_nonempty_iff_eq_empty.mp h0)
      have hU1 : 𝒱.U1 = ⊥ :=
        TopologicalSpace.Opens.ext
          (by rw [TopologicalSpace.Opens.coe_bot]; exact Set.not_nonempty_iff_eq_empty.mp h1)
      have htop : (⊤ : C.Opens) = ⊥ := by rw [← 𝒱.sup_eq_top, hU0, hU1, sup_idem]
      have hne : ((⊤ : C.Opens) : Set C).Nonempty := by
        rw [TopologicalSpace.Opens.coe_top]; exact Set.univ_nonempty
      rw [htop, TopologicalSpace.Opens.coe_bot] at hne
      exact Set.not_nonempty_empty hne
  have h₀ : ((𝒱n.pullback c κ).U0 : Set ↥(pullback c (specMap κ κ))).Nonempty := hn0.preimage
    φh.surjective
  have h₁ : ((𝒱n.pullback c κ).U1 : Set ↥(pullback c (specMap κ κ))).Nonempty := hn1.preimage
    φh.surjective
  obtain ⟨-, -, 𝒱'', -, -, hb0, hb1⟩ :=
    AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_basicOpen_refinement_basis_pushforward
      (curveChange f hf (specMap κ κ)) p hd hX (𝒱n.pullback c κ) h₀ h₁
  let ψ := inv (pullback.fst c (specMap κ κ))
  let 𝒱' : C.TwoAffineOpenCover :=
    { U0 := ψ ⁻¹ᵁ 𝒱''.U0
      U1 := ψ ⁻¹ᵁ 𝒱''.U1
      isAffineOpen_U0 := 𝒱''.isAffineOpen_U0.preimage ψ
      isAffineOpen_U1 := 𝒱''.isAffineOpen_U1.preimage ψ
      sup_eq_top := by rw [← Scheme.Hom.preimage_sup, 𝒱''.sup_eq_top]; rfl
      isAffineOpen_inf := by rw [← Scheme.Hom.preimage_inf]; exact 𝒱''.isAffineOpen_inf.preimage ψ }
  have hU0 : (𝒱'.pullback c κ).U0 = 𝒱''.U0 := by
    change (pullback.fst c (specMap κ κ) ≫ ψ) ⁻¹ᵁ 𝒱''.U0 = 𝒱''.U0
    rw [IsIso.hom_inv_id]; rfl
  have hU1 : (𝒱'.pullback c κ).U1 = 𝒱''.U1 := by
    change (pullback.fst c (specMap κ κ) ≫ ψ) ⁻¹ᵁ 𝒱''.U1 = 𝒱''.U1
    rw [IsIso.hom_inv_id]; rfl
  exact ⟨𝒱', basisOn_congr _ hU0 hb0, basisOn_congr _ hU1 hb1⟩

section U3
variable {κ : Type u} [Field κ] {C C' : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of κ)) (c' : C' ⟶ Spec (CommRingCat.of κ)) (f : C' ⟶ C) (hf : f ≫ c =
    c')

theorem curveChange_fst {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of κ)) :
    curveChange f hf t ≫ pullback.fst c t = pullback.fst c' t ≫ f := by
  simp only [curveChange, pullback.lift_fst]

/-- The two affine charts pulled back along an affine morphism. -/
def preimageCover [IsAffineHom f] (𝒱 : C.TwoAffineOpenCover) : C'.TwoAffineOpenCover where
  U0 := f ⁻¹ᵁ 𝒱.U0
  U1 := f ⁻¹ᵁ 𝒱.U1
  isAffineOpen_U0 := 𝒱.isAffineOpen_U0.preimage f
  isAffineOpen_U1 := 𝒱.isAffineOpen_U1.preimage f
  sup_eq_top := by rw [← Scheme.Hom.preimage_sup, 𝒱.sup_eq_top]; rfl
  isAffineOpen_inf := by rw [← Scheme.Hom.preimage_inf]; exact 𝒱.isAffineOpen_inf.preimage f

variable (A : Type u) [CommRing A] [Algebra κ A]

theorem preimageCover_pullback_U0 [IsAffineHom f] (𝒱 : C.TwoAffineOpenCover) :
    ((preimageCover f 𝒱).pullback c' A).U0 = curveChange f hf (specMap κ A) ⁻¹ᵁ (𝒱.pullback c A).U0
      := by
  simp only [pullback_U0, preimageCover, ← Scheme.Hom.comp_preimage, curveChange_fst]

theorem preimageCover_pullback_U1 [IsAffineHom f] (𝒱 : C.TwoAffineOpenCover) :
    ((preimageCover f 𝒱).pullback c' A).U1 = curveChange f hf (specMap κ A) ⁻¹ᵁ (𝒱.pullback c A).U1
      := by
  simp only [pullback_U1, preimageCover, ← Scheme.Hom.comp_preimage, curveChange_fst]

/-- The morphism between the base-changed two-chart covers. -/
noncomputable def homOver [IsAffineHom f] (𝒱 : C.TwoAffineOpenCover) :
    HomOver (RingHom.id A) (𝒱.pullback c A) (pullback.snd c (specMap κ A))
      ((preimageCover f 𝒱).pullback c' A) (pullback.snd c' (specMap κ A)) where
  hom := curveChange f hf (specMap κ A)
  comm := by
    rw [curveChange_snd]
    change _ = _ ≫ Spec.map (𝟙 _)
    rw [Spec.map_id, Category.comp_id]
  U0_le := (preimageCover_pullback_U0 c c' f hf A 𝒱).le
  U1_le := (preimageCover_pullback_U1 c c' f hf A 𝒱).le

@[scoped simp] theorem homOver_hom [IsAffineHom f] (𝒱 : C.TwoAffineOpenCover) :
    (homOver c c' f hf A 𝒱).hom = curveChange f hf (specMap κ A) := rfl

theorem isPullback_thickening [IsAffineHom f] (𝒱 : C.TwoAffineOpenCover) :
    IsPullback (homOver c c' f hf (DualNumber A) 𝒱).hom (dualNumberThickening A (preimageCover f 𝒱)
      c').hom
      (dualNumberThickening A 𝒱 c).hom (homOver c c' f hf A 𝒱).hom := by
  have outer := isPullback_curveChange c c' f hf (specMap κ (DualNumber A))
  have bot := isPullback_curveChange c c' f hf (specMap κ A)
  refine IsPullback.of_bot ?_ ?_ bot
  · have h1 : (dualNumberThickening A (preimageCover f 𝒱) c').hom ≫ pullback.fst c' (specMap κ A) =
        pullback.fst c' (specMap κ (DualNumber A)) := by
      dsimp only [dualNumberThickening, HomOver.stage]
      exact (pullback.lift_fst _ _ _).trans (Category.comp_id _)
    have h2 : (dualNumberThickening A 𝒱 c).hom ≫ pullback.fst c (specMap κ A) =
        pullback.fst c (specMap κ (DualNumber A)) := by
      dsimp only [dualNumberThickening, HomOver.stage]
      exact (pullback.lift_fst _ _ _).trans (Category.comp_id _)
    rw [h1, h2]
    exact outer
  · dsimp only [dualNumberThickening, HomOver.stage, homOver]
    exact curveChange_baseChangeSnd f hf _

theorem free_finite_trace_of_basis {X Y : Scheme.{u}} (g : X ⟶ Y) (U : Y.Opens) (V : X.Opens)
    (hV : V = g ⁻¹ᵁ U)
    {d : ℕ} (b : Module.Basis (Fin d) Γ(Y, U) Γ((Scheme.Modules.pushforward g).obj (𝟙_ X.Modules),
      U))
    (htz : let : Algebra Γ(Y, U) Γ(X, g ⁻¹ᵁ U) := (g.app U).hom.toAlgebra
      ∀ [Module.Free Γ(Y, U) Γ(X, g ⁻¹ᵁ U)] [Module.Finite Γ(Y, U) Γ(X, g ⁻¹ᵁ U)],
        Algebra.trace Γ(Y, U) Γ(X, g ⁻¹ᵁ U) = 0) :
    let : Algebra Γ(Y, U) Γ(X, V) := (g.appLE U V hV.le).hom.toAlgebra
    ∃ (_ : Module.Free Γ(Y, U) Γ(X, V)) (_ : Module.Finite Γ(Y, U) Γ(X, V)), Algebra.trace Γ(Y, U)
      Γ(X, V) = 0 := by
  generalize hφ : g.appLE U V hV.le = φ
  subst hV
  obtain rfl : φ = g.app U := by rw [← hφ]; exact (Scheme.Hom.app_eq_appLE g).symm
  intro algSections
  have hF : Module.Free Γ(Y, U) Γ(X, g ⁻¹ᵁ U) := Module.Free.of_basis b
  have hFin : Module.Finite Γ(Y, U) Γ(X, g ⁻¹ᵁ U) := Module.Finite.of_basis b
  exact ⟨hF, hFin, htz⟩

end U3
end NormDefTriv

attribute [local instance]
  _root_.JacobianVarieties.Picard.Proofs.DualNormRankCharacteristic.NormDefTriv.isIso_specMap_self
open _root_.JacobianVarieties.Picard.Proofs.DualNormRankCharacteristic.NormDefTriv in
attribute [local instance] isIso_fst_specMap_self
attribute [local instance]
  _root_.JacobianVarieties.Picard.Proofs.DualNormRankCharacteristic.NormDefTriv.isFinite_curveChange
attribute [local instance]
  _root_.JacobianVarieties.Picard.Proofs.DualNormRankCharacteristic.NormDefTriv.flat_curveChange
open _root_.JacobianVarieties.Picard.Proofs.DualNormRankCharacteristic.NormDefTriv in
attribute [local instance] locallyOfFinitePresentation_curveChange
open _root_.JacobianVarieties.Picard.Proofs.DualNormRankCharacteristic.NormDefTriv in
attribute [local instance] isAffineHom_curveChange
attribute [local simp]
  _root_.JacobianVarieties.Picard.Proofs.DualNormRankCharacteristic.NormDefTriv.homOver_hom

open NormDefTriv
end JacobianVarieties.Picard.Proofs.DualNormRankCharacteristic

namespace AlgebraicGeometry.RelPicard

open _root_.JacobianVarieties.Picard.Proofs.DualNormRankCharacteristic
open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.RelPicard
open _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian
universe u
attribute [local instance]
  _root_.JacobianVarieties.Picard.Proofs.DualNormRankCharacteristic.NormDefTriv.isIso_specMap_self
open _root_.JacobianVarieties.Picard.Proofs.DualNormRankCharacteristic.NormDefTriv in
attribute [local instance] isIso_fst_specMap_self
attribute [local instance]
  _root_.JacobianVarieties.Picard.Proofs.DualNormRankCharacteristic.NormDefTriv.isFinite_curveChange
attribute [local instance]
  _root_.JacobianVarieties.Picard.Proofs.DualNormRankCharacteristic.NormDefTriv.flat_curveChange
open _root_.JacobianVarieties.Picard.Proofs.DualNormRankCharacteristic.NormDefTriv in
attribute [local instance] locallyOfFinitePresentation_curveChange
open _root_.JacobianVarieties.Picard.Proofs.DualNormRankCharacteristic.NormDefTriv in
attribute [local instance] isAffineHom_curveChange
attribute [local simp]
  _root_.JacobianVarieties.Picard.Proofs.DualNormRankCharacteristic.NormDefTriv.homOver_hom
open _root_.JacobianVarieties.Picard.Proofs.DualNormRankCharacteristic.NormDefTriv

/-- Norms of infinitesimally trivial line bundles are trivial
when rank equals the characteristic. -/
theorem nonempty_normModule_curveChange_dualNumber_iso_unit_of_finrank_eq_char_of_forall_isClosed_eq
    {κ : Type u} [Field κ] [IsAlgClosed κ] {p : ℕ} [Fact p.Prime] [CharP κ p]
    {C C' : Scheme.{u}} [IsIntegral C] [IsIntegral C']
    (c : C ⟶ Spec (CommRingCat.of κ)) (c' : C' ⟶ Spec (CommRingCat.of κ))
    [LocallyOfFiniteType c] (𝒱 : C.TwoAffineOpenCover)
    (hC : ∀ Z : Set C, IsClosed Z → Z ≠ Set.univ → Z.Finite)
    (f : C' ⟶ C) (hf : f ≫ c = c')
    [IsFinite f] [Flat f] [LocallyOfFinitePresentation f] (hrk : ∀ y, f.finrank y = p)
    (hinj : ∀ x₁ x₂ : C', IsClosed ({x₁} : Set C') → IsClosed ({x₂} : Set C') → f.base x₁ = f.base
      x₂ → x₁ = x₂)
    (L : (pullback c' (Scheme.TwoAffineOpenCover.specMap κ (DualNumber κ))).Modules)
    (hL : Scheme.Modules.IsInvertible L)
    (h0 : Nonempty ((Scheme.Modules.pullback (RelPicard.baseChangeSnd c' (dualNumberReductionOver κ
      κ))).obj L ≅
      SheafOfModules.unit.{u} (pullback c' (Scheme.TwoAffineOpenCover.specMap κ κ)).ringCatSheaf)) :
    Nonempty (Scheme.Modules.normModule (curveChange f hf (Scheme.TwoAffineOpenCover.specMap κ
      (DualNumber κ))) p L ≅
      SheafOfModules.unit.{u} (pullback c (Scheme.TwoAffineOpenCover.specMap κ (DualNumber
        κ))).ringCatSheaf) := by
  classical
  have : IsAffineHom f := inferInstance
  obtain ⟨𝒱', ⟨e₀, he₀⟩, ⟨e₁, he₁⟩⟩ := NormDefTriv.exists_twoAffineOpenCover_forall_basis c c' f hf
    hC 𝒱 hrk
  let 𝒲' := preimageCover f 𝒱'
  let f₀ := homOver c c' f hf κ 𝒱'
  let fε := homOver c c' f hf (DualNumber κ) 𝒱'
  have hsq := isPullback_thickening c c' f hf κ 𝒱'
  have : IsAffineHom f₀.hom := by rw [homOver_hom]; infer_instance
  have : IsFinite fε.hom := by rw [homOver_hom]; infer_instance
  have : Flat fε.hom := by rw [homOver_hom]; infer_instance
  have : LocallyOfFinitePresentation fε.hom := by rw [homOver_hom]; infer_instance
  have hW0 := preimageCover_pullback_U0 c c' f hf κ 𝒱'
  have hW1 := preimageCover_pullback_U1 c c' f hf κ 𝒱'
  have hW0ε := preimageCover_pullback_U0 c c' f hf (DualNumber κ) 𝒱'
  have hW1ε := preimageCover_pullback_U1 c c' f hf (DualNumber κ) 𝒱'
  obtain ⟨s₀, s₁, g, hs₀, hs₁, hs⟩ :=
    exists_isFrameOn_and_map_eq_oneAddEpsMul_smul_of_nonempty_pullback_iso_unit c' κ 𝒲' L hL h0
  obtain ⟨eε₀, heε₀⟩ :=
    exists_forall_basis_pushforward_dualNumberThickening_of_forall_basis
      c c' κ 𝒱' 𝒲' f₀ fε
      hsq p (𝒱'.pullback c κ).U0 ((𝒱'.pullback c (DualNumber κ)).U0)
      (baseChangeSnd_preimage_U0 𝒱' c _).symm e₀ he₀
  obtain ⟨eε₁, heε₁⟩ :=
    exists_forall_basis_pushforward_dualNumberThickening_of_forall_basis
      c c' κ 𝒱' 𝒲' f₀ fε
      hsq p (𝒱'.pullback c κ).U1 ((𝒱'.pullback c (DualNumber κ)).U1)
      (baseChangeSnd_preimage_U1 𝒱' c _).symm e₁ he₁
  let instA01 : Algebra ((𝒱'.pullback c κ).cover (pullback.snd c (specMap κ κ))).A01
      ((𝒲'.pullback c' κ).cover (pullback.snd c' (specMap κ κ))).A01 :=
    (f₀.hom.appLE ((𝒱'.pullback c κ).U0 ⊓ (𝒱'.pullback c κ).U1) ((𝒲'.pullback c' κ).U0 ⊓
      (𝒲'.pullback c' κ).U1)
      f₀.inf_le).hom.toAlgebra
  have hV : (𝒲'.pullback c' κ).U0 ⊓ (𝒲'.pullback c' κ).U1 =
      f₀.hom ⁻¹ᵁ ((𝒱'.pullback c κ).U0 ⊓ (𝒱'.pullback c κ).U1) := by
    rw [Scheme.Hom.preimage_inf, hW0, hW1]; rfl
  obtain ⟨b, -⟩ := he₀ ((𝒱'.pullback c κ).U0 ⊓ (𝒱'.pullback c κ).U1) inf_le_left
  have : IsIntegral (pullback c (specMap κ κ)) := NormDefTriv.isIntegral_pullback_specMap_self c
  have : IsIntegral (pullback c' (specMap κ κ)) := NormDefTriv.isIntegral_pullback_specMap_self c'
  have : IsFinite f₀.hom := by rw [homOver_hom]; infer_instance
  have : Flat f₀.hom := by rw [homOver_hom]; infer_instance
  have : LocallyOfFinitePresentation f₀.hom := by rw [homOver_hom]; infer_instance
  have hbr := free_finite_trace_of_basis f₀.hom ((𝒱'.pullback c κ).U0 ⊓ (𝒱'.pullback c κ).U1)
    ((𝒲'.pullback c' κ).U0 ⊓ (𝒲'.pullback c' κ).U1) hV b
    (AlgebraicGeometry.trace_eq_zero_of_finrank_eq_char_of_forall_isClosed_eq (p := p)
      (pullback.snd c (specMap κ κ)) f₀.hom (fun y => NormDefTriv.finrank_curveChange c c' f hf _
        hrk y)
      (NormDefTriv.hinj_curveChange_specMap_self c c' f hf hinj)
      ((𝒱'.pullback c κ).U0 ⊓ (𝒱'.pullback c κ).U1) (𝒱'.pullback c κ).isAffineOpen_inf)
  obtain ⟨hfree, hfin, htr⟩ := hbr
  have : Module.Free ((𝒱'.pullback c κ).cover (pullback.snd c (specMap κ κ))).A01
      ((𝒲'.pullback c' κ).cover (pullback.snd c' (specMap κ κ))).A01 := hfree
  have : Module.Finite ((𝒱'.pullback c κ).cover (pullback.snd c (specMap κ κ))).A01
      ((𝒲'.pullback c' κ).cover (pullback.snd c' (specMap κ κ))).A01 := hfin
  have key :=
    AlgebraicGeometry.RelPicard.exists_isFrameOn_normModule_and_map_eq_oneAddEpsMul_trace_smul c c'
    κ 𝒱' 𝒲'
    f₀ fε hsq hW0ε hW1ε p eε₀ heε₀ eε₁ heε₁ L s₀ s₁ hs₀ hs₁ g hs
  obtain ⟨Ω₀, Ω₁, hΩ₀, hΩ₁, hΩ⟩ := key
  have htrg : Algebra.trace ((𝒱'.pullback c κ).cover (pullback.snd c (specMap κ κ))).A01
      ((𝒲'.pullback c' κ).cover (pullback.snd c' (specMap κ κ))).A01 g = 0 := by
    have htrA01 : Algebra.trace
        ((𝒱'.pullback c κ).cover (pullback.snd c (specMap κ κ))).A01
        ((𝒲'.pullback c' κ).cover (pullback.snd c' (specMap κ κ))).A01 = 0 := htr
    exact LinearMap.congr_fun htrA01 g
  have hone : oneAddEpsMul κ 𝒱' c
      (Algebra.trace ((𝒱'.pullback c κ).cover (pullback.snd c (specMap κ κ))).A01
        ((𝒲'.pullback c' κ).cover (pullback.snd c' (specMap κ κ))).A01 g) = 1 := by
    rw [htrg]; simp only [oneAddEpsMul, map_zero, mul_zero, add_zero]
  dsimp only at hΩ
  rw [hone] at hΩ
  change _ = (1 : Γ(pullback c (specMap κ (DualNumber κ)),
      (𝒱'.pullback c (DualNumber κ)).U0 ⊓ (𝒱'.pullback c (DualNumber κ)).U1)) • _ at hΩ
  rw [one_smul] at hΩ
  exact AlgebraicGeometry.Scheme.Modules.IsFrameOn.nonempty_iso_tensorUnit_of_map_eq_mul
    (L := Scheme.Modules.normModule fε.hom p L)
    (𝒱'.pullback c (DualNumber κ)).sup_eq_top hΩ₀ hΩ₁ 1 (by
      rw [one_smul]
      exact hΩ.symm) 1 1 isUnit_one isUnit_one
    (by simp only [map_one, one_mul])
end AlgebraicGeometry.RelPicard
end ProofImplementation

attribute [-simp]
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.HomOver.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.HomOver.mk.injEq
  AlgebraicGeometry.RelPicard.LFP.stageHom_val
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right
  AlgebraicGeometry.Scheme.Modules.map_unitSection
  AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply
  AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left
  AlgebraicGeometry.Scheme.Modules.tensorPow_zero
  AlgebraicGeometry.Scheme.Modules.tensorPow_succ
  AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe
  AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe
  AlgebraicGeometry.RelPicard.BaseChange.restrict_P
  AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd
  AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst
  PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom
  SheafOfModules.ihomSectionsEquivFamily_unit
  AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply
  SheafOfModules.ihomEval_unit_app
  AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right
  AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left
  AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply
  SheafOfModules.unit_ihomSectionsEquivFamily
  AlgebraicGeometry.Scheme.Modules.familyOfHom_app
  AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add
  AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app
