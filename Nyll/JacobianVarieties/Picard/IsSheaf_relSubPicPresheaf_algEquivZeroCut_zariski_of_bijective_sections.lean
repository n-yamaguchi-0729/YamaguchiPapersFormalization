/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_isSheaf_relSubPicPresheaf_algEquivZeroCut_zariski_of_bijective_sections.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Util.WithWeakNamespace
import Mathlib.AlgebraicGeometry.Sites.BigZariski
import Mathlib.AlgebraicGeometry.Sites.Small
import Mathlib.CategoryTheory.Sites.Coverage
import Mathlib.CategoryTheory.Sites.Hypercover.Zero
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.JacobianVarieties.Picard.Representation
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroCut
import Nyll.AlgebraicCurves.Geometry.Picard.RelSubPic.Presheaf
import Nyll.SchemeTheory.Cohomology.Cech.TwoAffineOpenCover
import Nyll.JacobianVarieties.Picard.RigidifiedLineBundle_exists_gluing_openCover_of_bijective_sections
import Nyll.AlgebraicCurves.Geometry.Picard.RigidifiedLineBundle_nonempty_iso_of_pullbackAlong_openCover_of_bijective_sections
import Nyll.JacobianVarieties.Picard.RigidifiedLineBundle_fibrewiseAlgEquivZero_of_pullbackAlong_openCover

import Nyll.JacobianVarieties.Picard.RepresentsRelSubPicPresheaf
/-!
The algebraically trivial relative Picard presheaf satisfies Zariski descent
when scalar extension induces bijections on global sections.
-/

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.ZariskiSheaf
attribute [-instance]
  AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory
  SheafOfModules.instFaithfulRingSheafPModToPMod SheafOfModules.symmetricCategory
  AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory
  AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed
  SheafOfModules.instFullRingSheafPModToPMod SheafOfModules.monoidalCategory
  AlgebraicGeometry.Scheme.Modules.symmetricCategory SheafOfModules.monoidalClosed
  SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW
  SheafOfModules.sheafifyFunctor_monoidal AlgebraicGeometry.Scheme.Modules.monoidalClosed
  AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify
  AlgebraicGeometry.Scheme.Modules.monoidalCategory PresheafOfModules.instMonoidalClosed
open _root_.PresheafOfModules.InternalHom in
attribute [-instance]
  instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies
open _root_.PresheafOfModules.InternalHom in
attribute [-instance]
  instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf
open _root_.PresheafOfModules.InternalHom in
attribute [-instance]
  instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies
attribute [-instance]
  AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap
  AlgebraicGeometry.Scheme.Modules.pullback_monoidal
  AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization'
  AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap
  AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal
  AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap
  AlgebraicGeometry.Scheme.Modules.sheafifyPullback_lifting
  PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ
  PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η
  PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal
  PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal
open _root_.PresheafOfModules.PullbackMonoidal in
attribute [-instance]
  instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb
attribute [-instance]
  PresheafOfModules.pullback_monoidal'
attribute [-simp]
  AlgebraicGeometry.RelPicard.rigSection_snd
  AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L
  AlgebraicGeometry.RelPicard.rigSection_snd_assoc
  AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.injEq
  AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.sizeOf_spec
  GoodReductionJacobian.relativeGroupLawOfGrpObj_inv
  GoodReductionJacobian.relativeGroupLawOfGrpObj_mul
  GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe
  GoodReductionJacobian.relativeGroupLawOfGrpObj_one
  GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left SheafOfModules.tensorUnit_eq
  AlgebraicGeometry.Scheme.Modules.tensorUnit_eq PresheafOfModules.InternalHom.presheaf_map_apply
  PresheafOfModules.InternalHom.curryFamily_app PresheafOfModules.InternalHom.add_app
  PresheafOfModules.InternalHom.smul_app PresheafOfModules.InternalHom.zero_app
  PresheafOfModules.ihomObj_map_val PresheafOfModules.ihomFunctor_map
  PresheafOfModules.InternalHom.restrict_app PresheafOfModules.InternalHom.postcomp_app
  PresheafOfModules.InternalHom.neg_app PresheafOfModules.curry'_app_val
  PresheafOfModules.InternalHom.presheaf_obj PresheafOfModules.ihomFunctor_obj
  PresheafOfModules.ihomObj_obj PresheafOfModules.InternalHom.sub_app
  PresheafOfModules.ihomMap_app_val PresheafOfModules.freeεIso_hom_app
  PresheafOfModules.freeμIso_hom_app

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.RelPicard NeronModelInfra Opposite

with_weak_namespace _root_.AlgebraicGeometry.RelPicard
theorem isSheaf_relSubPicPresheaf_algEquivZeroCut_zariski_of_bijective_sections
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (hH0 : ∀ (A : Type u) [CommRing A] [Algebra R A],
      let : Algebra A
          Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A), ⊤) :=
        Scheme.TwoAffineOpenCover.algebraOfHom
          (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A)) ⊤
      Function.Bijective (algebraMap A
        Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A), ⊤))) :
    Presieve.IsSheaf (Scheme.zariskiTopology.over (Spec (CommRingCat.of R)))
      (relSubPicPresheaf c ε (algEquivZeroCut c ε)) := by
  classical
  have hJ : Scheme.zariskiTopology.over (Spec (CommRingCat.of R)) =
      (Scheme.overPretopology @IsOpenImmersion (Spec (CommRingCat.of R))).toGrothendieck :=
    Scheme.overGrothendieckTopology_eq_toGrothendieck_overPretopology _ _
  rw [hJ, Precoverage.toGrothendieck_toPretopology_eq_toGrothendieck,
    Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange_of_small.{u}]
  intro Y E
  let 𝒰 : Scheme.Cover.{u} (Scheme.precoverage @IsOpenImmersion) Y.left :=
    E.map (Over.forget (Spec (CommRingCat.of R))) le_rfl
  change Presieve.IsSheafFor (relSubPicPresheaf c ε (algEquivZeroCut c ε))
    (Presieve.ofArrows E.X E.f)
  rw [Presieve.isSheafFor_arrows_iff]
  intro x hx
  let u : ∀ i : E.I₀, (E.X i).left ⟶ Spec (CommRingCat.of R) := fun i =>
    (E.X i).hom
  let f : ∀ i, SchemeHomOver (u i) Y.hom := fun i =>
    ⟨(E.f i).left, Over.w (E.f i)⟩
  have hfo : ∀ i, IsOpenImmersion (f i).1 := fun i => 𝒰.map_prop i
  have hf : ∀ y : Y.left, ∃ i, y ∈ Set.range (f i).1.base := fun y => by
    obtain ⟨i, z, hz⟩ := 𝒰.exists_eq y
    exact ⟨i, z, hz⟩
  let M : ∀ i, RigidifiedLineBundle c ε (u i) := fun i => (x i).1.out
  have hM : ∀ i, Quotient.mk _ (M i) = (x i).1 := fun i => Quotient.out_eq _
  have hMP : ∀ i, FibrewiseAlgEquivZero (M i) := fun i => by
    have h : (algEquivZeroCut c ε).onClasses _ (x i).1 := (x i).2
    rw [← hM i] at h
    exact h
  have hcompat : ∀ (i j : E.I₀) (Z : Scheme.{u}) (z : Z ⟶ Spec (CommRingCat.of R))
      (p₁ : SchemeHomOver z (u i)) (p₂ : SchemeHomOver z (u j)),
      p₁.1 ≫ (f i).1 = p₂.1 ≫ (f j).1 →
        Nonempty (((M i).pullbackAlong p₁).L ≅ ((M j).pullbackAlong p₂).L) := by
    intro i j Z z p₁ p₂ hp
    let P₁ : Over.mk z ⟶ E.X i := Over.homMk p₁.1 p₁.2
    let P₂ : Over.mk z ⟶ E.X j := Over.homMk p₂.1 p₂.2
    have hP : P₁ ≫ E.f i = P₂ ≫ E.f j := by
      ext
      exact hp
    have h := congrArg Subtype.val (hx i j (Over.mk z) P₁ P₂ hP)
    rw [relSubPicPresheaf_map_coe, relSubPicPresheaf_map_coe] at h
    change RigidifiedLineBundle.classesMap p₁ (x i).1
      = RigidifiedLineBundle.classesMap p₂ (x j).1 at h
    rw [← hM i, ← hM j] at h
    exact Quotient.exact h
  obtain ⟨N, hN⟩ :=
    RigidifiedLineBundle.exists_gluing_openCover_of_bijective_sections
      R c ε hH0 Y.hom u f hf M hcompat
  have hNP : FibrewiseAlgEquivZero N :=
    RigidifiedLineBundle.fibrewiseAlgEquivZero_of_pullbackAlong_openCover
      R c ε Y.hom u f hf N (fun i =>
        (algEquivZeroCut c ε).congr _ (M i) (N.pullbackAlong (f i)) ⟨(hN i).some.symm⟩ (hMP i))
  have hmap : ∀ (i : E.I₀) (y : (relSubPicPresheaf c ε (algEquivZeroCut c ε)).obj (op Y))
      (N' : RigidifiedLineBundle c ε Y.hom), y.1 = Quotient.mk _ N' →
      ((relSubPicPresheaf c ε (algEquivZeroCut c ε)).map
        (E.f i).op y).1 = Quotient.mk _ (N'.pullbackAlong (f i)) := by
    intro i y N' hy
    rw [relSubPicPresheaf_map_coe, hy]
    rfl
  let y₀ : (relSubPicPresheaf c ε (algEquivZeroCut c ε)).obj (op Y) :=
    ⟨Quotient.mk _ N, (SubPicCondition.onClasses_mk (algEquivZeroCut c ε) Y.hom N).2 hNP⟩
  refine ⟨y₀, ?_, ?_⟩
  · intro i
    apply Subtype.ext
    rw [← hM i]
    exact (hmap i y₀ N rfl).trans (Quotient.sound (hN i))
  · intro y hy
    apply Subtype.ext
    obtain ⟨N', hN'⟩ := Quotient.exists_rep y.1
    have hiso : ∀ i, Nonempty ((N'.pullbackAlong (f i)).L ≅ (N.pullbackAlong (f i)).L) := by
      intro i
      have h₁ : (Quotient.mk _ (N'.pullbackAlong (f i)) : RigidifiedLineBundle.Classes c ε (u i)) =
          Quotient.mk _ (M i) :=
        (hmap i y N' hN'.symm).symm.trans ((congrArg Subtype.val (hy i)).trans (hM i).symm)
      exact ⟨(Quotient.exact h₁).some ≪≫ (hN i).some.symm⟩
    rw [← hN']
    exact Quotient.sound
      (RigidifiedLineBundle.nonempty_iso_of_pullbackAlong_openCover_of_bijective_sections
        R c ε hH0 Y.hom u f hf N' N hiso)
end JacobianVarieties.Picard.Proofs.ZariskiSheaf
end ProofImplementation
