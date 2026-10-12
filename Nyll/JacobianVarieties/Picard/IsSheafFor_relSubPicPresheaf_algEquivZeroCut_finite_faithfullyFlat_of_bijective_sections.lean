/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_isSheafFor_relSubPicPresheaf_algEquivZeroCut_finite_faithfullyFlat_of_bijective_sections.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Util.WithWeakNamespace
import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.CategoryTheory.Sites.IsSheafFor
import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.JacobianVarieties.Picard.Representation
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroCut
import Nyll.AlgebraicCurves.Geometry.Picard.RelSubPic.Presheaf
import Nyll.SchemeTheory.Cohomology.Cech.TwoAffineOpenCover
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurveBase
import Nyll.JacobianVarieties.Picard.RigidifiedLineBundle_exists_descent_finite_faithfullyFlat_of_bijective_sections
import Nyll.JacobianVarieties.Picard.RigidifiedLineBundle_nonempty_iso_of_pullback_finite_faithfullyFlat_of_bijective_sections
import Nyll.JacobianVarieties.Picard.RigidifiedLineBundle_fibrewiseAlgEquivZero_of_pullback_finite_faithfullyFlat

import Nyll.JacobianVarieties.Picard.RepresentsRelSubPicPresheaf
/-!
# Faithfully flat descent for algebraically trivial Picard classes

Prove the singleton sheaf condition by descending line bundles and their isomorphisms.
-/

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.FaithfulPicardSheaf
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
  PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app
  Algebra.DescentCofaces.i₁_apply Algebra.DescentCofaces.i₂_apply Algebra.DescentCofaces.c₁₂_tmul
  Algebra.DescentCofaces.c₂₃_tmul Algebra.DescentCofaces.c₁₃_tmul

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve NeronModelInfra Opposite

open _root_.AlgebraicGeometry.RelPicard.RigidifiedLineBundle in
with_weak_namespace _root_.AlgebraicGeometry.RelPicard
theorem isSheafFor_relSubPicPresheaf_algEquivZeroCut_finite_faithfullyFlat_of_bijective_sections
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (hH0 : ∀ (A : Type u) [CommRing A] [Algebra R A],
      let : Algebra A
          Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A), ⊤) :=
        Scheme.TwoAffineOpenCover.algebraOfHom
          (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A)) ⊤
      Function.Bijective (algebraMap A
        Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A), ⊤)))
    (R' : Type u) [CommRing R'] [Algebra R R'] [Module.Finite R R'] [Module.FaithfullyFlat R R']
    (T : Over (Spec (CommRingCat.of R))) :
    Presieve.IsSheafFor (relSubPicPresheaf c ε (algEquivZeroCut c ε))
      (Presieve.singleton
        ((Over.mapPullbackAdj (SmoothProperCurve.specMap R R')).counit.app T)) := by
  classical
  rw [Presieve.isSheafFor_singleton]
  intro x hx
  let ξ : RigidifiedLineBundle.Classes c ε
      (pullback.snd T.hom (specMap R R') ≫ specMap R R') := x.val
  have hξ : (algEquivZeroCut c ε).onClasses
      (pullback.snd T.hom (specMap R R') ≫ specMap R R') ξ := x.property
  have hπ : ((Over.mapPullbackAdj (specMap R R')).counit.app T).left =
      pullback.fst T.hom (specMap R R') := by
    simp only [Over.mapPullbackAdj_counit_app, Over.homMk_left]
  let πS : SchemeHomOver (pullback.snd T.hom (specMap R R') ≫ specMap R R') T.hom :=
    ⟨pullback.fst T.hom (specMap R R'), pullback.condition⟩
  let counitOver : SchemeHomOver
      (pullback.snd T.hom (specMap R R') ≫ specMap R R') T.hom :=
    ⟨((Over.mapPullbackAdj (specMap R R')).counit.app T).left,
      Over.w ((Over.mapPullbackAdj (specMap R R')).counit.app T)⟩
  set M' : RigidifiedLineBundle c ε (pullback.snd T.hom (specMap R R') ≫ specMap R R') := ξ.out
  have hM' : Quotient.mk _ M' = ξ := Quotient.out_eq ξ
  have hξP : FibrewiseAlgEquivZero M' := by
    have h : (algEquivZeroCut c ε).onClasses _ ξ := hξ
    rw [← hM'] at h
    exact h
  have hcompat : ∀ (Z : Scheme.{u}) (z : Z ⟶ Spec (CommRingCat.of R))
      (p₁ p₂ : SchemeHomOver z (pullback.snd T.hom (specMap R R') ≫ specMap R R')),
      p₁.1 ≫ pullback.fst T.hom (specMap R R') = p₂.1 ≫ pullback.fst T.hom (specMap R R') →
        Nonempty ((M'.pullbackAlong p₁).L ≅ (M'.pullbackAlong p₂).L) := by
    intro Z z p₁ p₂ hp
    let P₁ : Over.mk z ⟶ (Over.map (specMap R R')).obj ((Over.pullback (specMap R R')).obj T) :=
      Over.homMk p₁.1 p₁.2
    let P₂ : Over.mk z ⟶ (Over.map (specMap R R')).obj ((Over.pullback (specMap R R')).obj T) :=
      Over.homMk p₂.1 p₂.2
    have hP : P₁ ≫ (Over.mapPullbackAdj (specMap R R')).counit.app T =
        P₂ ≫ (Over.mapPullbackAdj (specMap R R')).counit.app T := by
      ext
      change p₁.1 ≫ ((Over.mapPullbackAdj (specMap R R')).counit.app T).left =
        p₂.1 ≫ ((Over.mapPullbackAdj (specMap R R')).counit.app T).left
      rw [hπ]
      exact hp
    have h : RigidifiedLineBundle.classesMap p₁ ξ =
        RigidifiedLineBundle.classesMap p₂ ξ :=
      (relSubPicPresheaf_map_coe (c := c) (ε := ε)
        (P := algEquivZeroCut c ε) P₁.op x).symm.trans
        ((congrArg Subtype.val (hx P₁ P₂ hP)).trans
          (relSubPicPresheaf_map_coe (c := c) (ε := ε)
            (P := algEquivZeroCut c ε) P₂.op x))
    rw [← hM'] at h
    exact Quotient.exact h
  obtain ⟨M, ⟨e⟩⟩ :=
    exists_descent_finite_faithfullyFlat_of_bijective_sections
      R c ε hH0 R' T.hom M' hcompat
  have hM : FibrewiseAlgEquivZero M :=
    fibrewiseAlgEquivZero_of_pullback_finite_faithfullyFlat
      R c ε R' T.hom M ((algEquivZeroCut c ε).congr _ M' (M.pullbackAlong πS) ⟨e.symm⟩ hξP)
  have hmap : ∀ (ψ : SchemeHomOver (pullback.snd T.hom (specMap R R') ≫ specMap R R') T.hom),
      ψ.1 = pullback.fst T.hom (specMap R R') → ∀ N : RigidifiedLineBundle c ε T.hom,
        RigidifiedLineBundle.classesMap ψ (Quotient.mk _ N) =
          Quotient.mk _ (N.pullbackAlong πS) := by
    intro ψ h N
    have hψ : ψ = πS := Subtype.ext h
    subst ψ
    rfl
  let η : (relPicardPresheaf c ε).obj (op T) := Quotient.mk _ M
  let y : (relSubPicPresheaf c ε (algEquivZeroCut c ε)).obj (op T) :=
    ⟨η, show (algEquivZeroCut c ε).onClasses T.hom η from
      (SubPicCondition.onClasses_mk (algEquivZeroCut c ε) T.hom M).2 hM⟩
  refine ⟨y, ?_, ?_⟩
  · apply Subtype.ext
    have he : (Quotient.mk _ (M.pullbackAlong πS) : RigidifiedLineBundle.Classes c ε
        (pullback.snd T.hom (specMap R R') ≫ specMap R R')) = Quotient.mk _ M' :=
      Quotient.sound ⟨e⟩
    have hy : RigidifiedLineBundle.classesMap counitOver (Quotient.mk _ M) = ξ :=
      (hmap counitOver hπ M).trans (he.trans hM')
    exact (relSubPicPresheaf_map_coe (c := c) (ε := ε)
      (P := algEquivZeroCut c ε)
      ((Over.mapPullbackAdj (specMap R R')).counit.app T).op y).trans hy
  · intro ξ₁ hy
    apply Subtype.ext
    let ζ₁ : RigidifiedLineBundle.Classes c ε T.hom := ξ₁.val
    obtain ⟨N, hN⟩ := Quotient.exists_rep ζ₁
    have h₁ : RigidifiedLineBundle.classesMap counitOver ζ₁ = ξ :=
      (relSubPicPresheaf_map_coe (c := c) (ε := ε)
        (P := algEquivZeroCut c ε)
        ((Over.mapPullbackAdj (specMap R R')).counit.app T).op ξ₁).symm.trans
        (congrArg Subtype.val hy)
    rw [← hN] at h₁
    have h₃ : Quotient.mk _ (N.pullbackAlong πS) = Quotient.mk _ M' :=
      ((hmap counitOver hπ N).symm.trans h₁).trans hM'.symm
    have h₂ : Nonempty ((N.pullbackAlong πS).L ≅ (M.pullbackAlong πS).L) :=
      ⟨(Quotient.exact h₃).some ≪≫ e.symm⟩
    exact hN.symm.trans (Quotient.sound
      (nonempty_iso_of_pullback_finite_faithfullyFlat_of_bijective_sections
        R c ε hH0 R' T.hom N M h₂))
end JacobianVarieties.Picard.Proofs.FaithfulPicardSheaf
end ProofImplementation
