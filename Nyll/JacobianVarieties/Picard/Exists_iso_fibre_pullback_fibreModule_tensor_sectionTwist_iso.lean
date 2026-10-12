/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_exists_iso_fibre_pullback_fibreModule_tensor_sectionTwist_iso.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroCut
import Nyll.SchemeTheory.Modules.Monoidal
import Nyll.AlgebraicCurves.Geometry.Sheaves.IdealSheafModule
import Nyll.JacobianVarieties.Picard.ThetaBundle
import Nyll.AlgebraicCurves.RelativeDivisors.Cartier
import Nyll.SchemeTheory.Modules.PullbackMonoidal
import Nyll.AlgebraicCurves.Geometry.Schemes.Scheme_Hom_isInvertible_ker_of_comp_eq_id
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_pow
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_comap_mul
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_nonempty_pullback_invModule_iso

/-!
Compare the pullback of a fibre module tensored with a section twist along the specified fibre
isomorphism.
-/

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs
namespace Exists_iso_fibre_pullback_fibreModule_tensor_sectionTwist_iso

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.RelPicard
open _root_.NeronModelInfra

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry

theorem fibreIdE9_comap_pow {X Y : Scheme.{u}} (I : Y.IdealSheafData) (f : X ⟶ Y) (n : ℕ) :
    (I ^ n).comap f = (I.comap f) ^ n := by
  induction n with
  | zero =>
      rw [pow_zero, pow_zero, Scheme.IdealSheafData.one_eq_top,
        Scheme.IdealSheafData.comap_top, Scheme.IdealSheafData.one_eq_top]
  | succ n ih => rw [pow_succ, pow_succ, Scheme.IdealSheafData.comap_mul, ih]

variable {k : Type u} [Field k] {C T : Scheme.{u}}

theorem fibreIdE9_isInvertible_sectionIdeal (c : C ⟶ Spec (CommRingCat.of k))
    [IsSeparated c] [SmoothOfRelativeDimension 1 c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c) (t : T ⟶ Spec (CommRingCat.of k)) :
    (RelPicard.sectionIdeal c ε t).IsInvertible := by
  have : SmoothOfRelativeDimension 1 (pullback.snd c t) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)).of_isPullback
      (IsPullback.of_hasPullback c t) inferInstance
  have hσq : RelPicard.rigSection c t ε ≫ pullback.snd c t = 𝟙 T := by
    simp only [RelPicard.rigSection, pullback.lift_snd]
  exact Scheme.Hom.isInvertible_ker_of_comp_eq_id (RelPicard.rigSection c t ε) hσq

theorem fibreIdE9_sectionIdeal_comap_section (c : C ⟶ Spec (CommRingCat.of k)) [IsSeparated c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c) (t : T ⟶ Spec (CommRingCat.of k))
    (x : Spec (CommRingCat.of k) ⟶ T) (hx : x ≫ t = 𝟙 _)
    (ix : C ⟶ pullback c t) (hix_fst : ix ≫ pullback.fst c t = 𝟙 C)
    (hix_snd : ix ≫ pullback.snd c t = c ≫ x) :
    (RelPicard.sectionIdeal c ε t).comap ix = ε.1.ker := by
  have hrig_snd : RelPicard.rigSection c t ε ≫ pullback.snd c t = 𝟙 T := by
    simp only [RelPicard.rigSection, pullback.lift_snd]
  have hrig_fst : RelPicard.rigSection c t ε ≫ pullback.fst c t = t ≫ ε.1 := by
    simp only [RelPicard.rigSection, pullback.lift_fst]
  have : IsClosedImmersion (RelPicard.rigSection c t ε) := by
    have : IsClosedImmersion (RelPicard.rigSection c t ε ≫ pullback.snd c t) := by
      rw [hrig_snd]; infer_instance
    exact IsClosedImmersion.of_comp (RelPicard.rigSection c t ε) (pullback.snd c t)
  have hsq : ε.1 ≫ ix = x ≫ RelPicard.rigSection c t ε := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, hix_fst, hrig_fst, Category.comp_id, ← Category.assoc, hx,
        Category.id_comp]
    · rw [Category.assoc, Category.assoc, hix_snd, hrig_snd, Category.comp_id, ← Category.assoc,
        ε.2,
        Category.id_comp]
  let q : Spec (CommRingCat.of k) ⟶ pullback ix (RelPicard.rigSection c t ε) := pullback.lift
    ε.1 x hsq
  have hq_fst : q ≫ pullback.fst ix (RelPicard.rigSection c t ε) = ε.1 := pullback.lift_fst _ _ _
  have hq_snd : q ≫ pullback.snd ix (RelPicard.rigSection c t ε) = x := pullback.lift_snd _ _ _
  have hB1 : pullback.fst ix (RelPicard.rigSection c t ε) =
      pullback.snd ix (RelPicard.rigSection c t ε) ≫ t ≫ ε.1 := by
    have h := congrArg (· ≫ pullback.fst c t)
      (pullback.condition (f := ix) (g := RelPicard.rigSection c t ε))
    simp only [Category.assoc, hix_fst, hrig_fst, Category.comp_id] at h
    exact h
  have hB2 : pullback.fst ix (RelPicard.rigSection c t ε) ≫ c ≫ x =
      pullback.snd ix (RelPicard.rigSection c t ε) := by
    have h := congrArg (· ≫ pullback.snd c t)
      (pullback.condition (f := ix) (g := RelPicard.rigSection c t ε))
    simp only [Category.assoc, hix_snd, hrig_snd, Category.comp_id] at h
    exact h
  have hB3 : pullback.fst ix (RelPicard.rigSection c t ε) ≫ c =
      pullback.snd ix (RelPicard.rigSection c t ε) ≫ t := by
    rw [hB1, Category.assoc, Category.assoc, ε.2, Category.comp_id]
  have : IsIso q := by
    refine ⟨⟨pullback.fst ix (RelPicard.rigSection c t ε) ≫ c, ?_, ?_⟩⟩
    · rw [← Category.assoc, hq_fst, ε.2]
    · apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, hq_fst, Category.id_comp, ← Category.assoc, hB3,
          Category.assoc, ← hB1]
      · rw [Category.assoc, Category.assoc, hq_snd, Category.id_comp, hB2]
  calc (RelPicard.sectionIdeal c ε t).comap ix
      = (RelPicard.rigSection c t ε).ker.comap ix := rfl
    _ = (pullback.fst ix (RelPicard.rigSection c t ε)).ker :=
        (Scheme.IdealSheafData.ker_fst_of_isClosedImmersion (RelPicard.rigSection c t ε) ix).symm
    _ = (q ≫ pullback.fst ix (RelPicard.rigSection c t ε)).ker :=
        (Scheme.Hom.ker_comp_of_isIso q _).symm
    _ = ε.1.ker := by rw [hq_fst]

theorem fibreIdE9_nonempty_pullback_sectionTwist_iso (c : C ⟶ Spec (CommRingCat.of k))
    [IsSeparated c] [SmoothOfRelativeDimension 1 c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c) (t : T ⟶ Spec (CommRingCat.of k))
    (x : Spec (CommRingCat.of k) ⟶ T) (hx : x ≫ t = 𝟙 _)
    (ix : C ⟶ pullback c t) (hix_fst : ix ≫ pullback.fst c t = 𝟙 C)
    (hix_snd : ix ≫ pullback.snd c t = c ≫ x) (d : ℕ) :
    Nonempty ((Scheme.Modules.pullback ix).obj (RelPicard.sectionTwist c ε t d) ≅
      ((ε.1.ker) ^ d).invModule) := by
  have hJ : (RelPicard.sectionIdeal c ε t).IsInvertible := fibreIdE9_isInvertible_sectionIdeal c ε t
  have hε : (ε.1.ker).IsInvertible := Scheme.Hom.isInvertible_ker_of_comp_eq_id ε.1 ε.2
  have hcomap : ((RelPicard.sectionIdeal c ε t) ^ d).comap ix = (ε.1.ker) ^ d := by
    rw [fibreIdE9_comap_pow]
    exact congrArg (· ^ d) (fibreIdE9_sectionIdeal_comap_section c ε t x hx ix hix_fst hix_snd)
  have hI' : (((RelPicard.sectionIdeal c ε t) ^ d).comap ix).IsInvertible := by
    rw [hcomap]; exact hε.pow d
  obtain ⟨e⟩ := Scheme.IdealSheafData.IsInvertible.nonempty_pullback_invModule_iso ix (hJ.pow d) hI'
  unfold RelPicard.sectionTwist
  exact ⟨e ≪≫ eqToIso (by rw [hcomap])⟩

end AlgebraicGeometry

theorem
    _root_.AlgebraicGeometry.RelPicard.exists_iso_fibre_pullback_fibreModule_tensor_sectionTwist_iso
    {k : Type u} [Field k] {C T : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
    [IsProper c] [SmoothOfRelativeDimension 1 c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c) (t : T ⟶ Spec (CommRingCat.of k))
    (x : Spec (CommRingCat.of k) ⟶ T) (hx : x ≫ t = 𝟙 _) :
    ∃ φ : C ≅ pullback (pullback.snd c t) x,
      φ.hom ≫ fibreAt c t x = c ∧
      φ.hom ≫ pullback.fst (pullback.snd c t) x =
        pullback.lift (𝟙 C) (c ≫ x) (by rw [Category.id_comp, Category.assoc, hx,
          Category.comp_id]) ∧
      ∀ (F : (pullback c t).Modules) (d : ℕ),
        Nonempty ((Scheme.Modules.pullback φ.hom).obj (fibreModule c t x (F ⊗ sectionTwist c ε t
          d)) ≅
          (Scheme.Modules.pullback
              (pullback.lift (𝟙 C) (c ≫ x) (by rw [Category.id_comp, Category.assoc, hx,
                Category.comp_id]))).obj F ⊗
            ((ε.1.ker) ^ d).invModule) := by
  have hix : 𝟙 C ≫ c = (c ≫ x) ≫ t := by rw [Category.id_comp, Category.assoc, hx, Category.comp_id]
  let ix : C ⟶ pullback c t := pullback.lift (𝟙 C) (c ≫ x) hix
  have hix_fst : ix ≫ pullback.fst c t = 𝟙 C := pullback.lift_fst _ _ _
  have hix_snd : ix ≫ pullback.snd c t = c ≫ x := pullback.lift_snd _ _ _
  have hA : pullback.fst (pullback.snd c t) x ≫ pullback.fst c t ≫ c =
      pullback.snd (pullback.snd c t) x := by
    rw [pullback.condition (f := c) (g := t), ← Category.assoc,
      pullback.condition (f := pullback.snd c t) (g := x), Category.assoc, hx, Category.comp_id]
  let φhom : C ⟶ pullback (pullback.snd c t) x := pullback.lift ix c (by rw [hix_snd])
  have hφ_fst : φhom ≫ pullback.fst (pullback.snd c t) x = ix := pullback.lift_fst _ _ _
  have hφ_snd : φhom ≫ pullback.snd (pullback.snd c t) x = c := pullback.lift_snd _ _ _
  let φ : C ≅ pullback (pullback.snd c t) x :=
    { hom := φhom
      inv := pullback.fst (pullback.snd c t) x ≫ pullback.fst c t
      hom_inv_id := by rw [← Category.assoc, hφ_fst, hix_fst]
      inv_hom_id := by
        apply pullback.hom_ext
        · rw [Category.assoc, Category.assoc, hφ_fst, Category.id_comp]
          apply pullback.hom_ext
          · rw [Category.assoc, Category.assoc, hix_fst, Category.comp_id]
          · rw [Category.assoc, Category.assoc, hix_snd,
              pullback.condition (f := pullback.snd c t) (g := x), ← hA]
            simp only [Category.assoc]
        · rw [Category.assoc, Category.assoc, hφ_snd, Category.id_comp, hA] }
  refine ⟨φ, ?_, hφ_fst, fun F d => ?_⟩
  · change φhom ≫ pullback.snd (pullback.snd c t) x = c
    exact hφ_snd
  · obtain ⟨e4⟩ :=
      AlgebraicGeometry.fibreIdE9_nonempty_pullback_sectionTwist_iso c ε t x hx ix hix_fst hix_snd d
    exact ⟨(Scheme.Modules.pullbackComp φhom (pullback.fst (pullback.snd c t) x)).app
        (F ⊗ sectionTwist c ε t d) ≪≫
      (Scheme.Modules.pullbackCongr hφ_fst).app (F ⊗ sectionTwist c ε t d) ≪≫
      Scheme.Modules.pullbackTensorObjIso ix F (sectionTwist c ε t d) ≪≫
      whiskerLeftIso ((Scheme.Modules.pullback ix).obj F) e4⟩
end JacobianVarieties.Picard.Proofs.Exists_iso_fibre_pullback_fibreModule_tensor_sectionTwist_iso
end ProofImplementation

attribute [-instance]
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub
open _root_.AlgebraicGeometry.Scheme.IdealSheafData.IdealHom in
attribute [-instance]
  instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop
open _root_.AlgebraicGeometry.Scheme.IdealSheafData.IdealHom in
attribute [-instance]
  instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop
attribute [-instance]
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero
  AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap
  AlgebraicGeometry.Scheme.Modules.pullback_monoidal
  AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization'
  AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap
  AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal
  AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap
  AlgebraicGeometry.Scheme.Modules.sheafifyPullback_lifting
  PresheafOfModules.PullbackMonoidal.pullback_monoidal
  PresheafOfModules.PullbackMonoidal.isIso_δ
  PresheafOfModules.pushforward_laxMonoidal
  PresheafOfModules.PullbackMonoidal.isIso_η
  PresheafOfModules.free_monoidal
  PresheafOfModules.restrictScalars_laxMonoidal
  PresheafOfModules.PullbackMonoidal.isIso_δ_gS
  PresheafOfModules.pullback_oplaxMonoidal
open _root_.PresheafOfModules.PullbackMonoidal in
attribute [-instance]
  instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb
attribute [-instance]
  PresheafOfModules.pullback_monoidal'
attribute [-simp]
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app
  AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app
  AlgebraicGeometry.Scheme.IdealSheafData.sres_sres
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app
  PresheafOfModules.freeεIso_hom_app
  PresheafOfModules.freeμIso_hom_app
