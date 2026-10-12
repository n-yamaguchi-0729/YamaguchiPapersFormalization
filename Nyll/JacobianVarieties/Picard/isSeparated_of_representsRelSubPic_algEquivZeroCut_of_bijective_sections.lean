/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_isSeparated_of_representsRelSubPic_algEquivZeroCut_of_bijective_sections.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.JacobianVarieties.Picard.Representation
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroCut
import Nyll.AlgebraicCurves.Geometry.Picard.RelSubPic.Presheaf
import Nyll.JacobianVarieties.Picard.ThetaBundle
import Nyll.SchemeTheory.Modules.Monoidal
import Nyll.AlgebraicCurves.Geometry.Picard.RelSubPic.Group
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroGroupCut
import Nyll.SchemeTheory.Modules.PullbackMonoidal
import Nyll.JacobianVarieties.Picard.isClosed_setOf_exists_fibreModule_iso_unit_of_flat
import Nyll.SchemeTheory.Cohomology.Cech.TwoAffineOpenCover
import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver

import Nyll.JacobianVarieties.Picard.RepresentsRelSubPicPresheaf
import Nyll.JacobianVarieties.Picard.RepresentsRelSubPicGroup

/-! Separatedness of the representing scheme from the closed fibrewise triviality locus. -/

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.SectionPicardSeparated
attribute [-instance]
  AlgebraicGeometry.OModulePresheaf.isScalarTower
  AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder
  AlgebraicGeometry.OModulePresheaf.module
  AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype
  AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx
  AlgebraicGeometry.OModulePresheaf.addCommGroup
  AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx
  AlgebraicGeometry.OModulePresheaf.moduleSections
  AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero
  AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower
  AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ
  AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ
  AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp
  AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ
  AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul
  AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower
  AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul
  AlgebraicGeometry.OModulePresheaf.Leray.biC_module
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx
  DoubleComplex.instModuleE₂I
  DoubleComplex.Bounded.modR
  DoubleComplex.instModuleE₂II
  DoubleComplex.instAddCommGroupE₂II
  DoubleComplex.Bounded.abGrp
  DoubleComplex.instAddCommGroupE₂I
  AlgebraicGeometry.ChowDatum.hι_closed
  AlgebraicGeometry.ChowDatumProj.hιN_closed
  AlgebraicGeometry.ChowDatumProj.hp_proper
  AlgebraicGeometry.ChowDatum.hp_isoU
  AlgebraicGeometry.ChowDatum.hp_proper
  AlgebraicGeometry.ProjSpace.algebraAway
  AlgebraicGeometry.ProjSpace.instIsProperProdOverπ
  AlgebraicGeometry.ChowDatumProj.hp_isoU
  AlgebraicGeometry.ProjSpace.isProper_π
  AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial
  ProjSpaceCech.GradedModule.H.module
  ProjSpaceCech.GradedModule.H.addCommGroup
attribute [-instance]
  ProjSpaceCech.GradedModule.sec.instAdd
  ProjSpaceCech.GradedModule.sec.instNeg
  ProjSpaceCech.GradedModule.acg
  ProjSpaceCech.GradedModule.Frac.setoid
  ProjSpaceCech.GradedModule.modR
  ProjSpaceCech.GradedModule.sec.instModule
  ProjSpaceCech.GradedModule.sec.instAddCommGroup
  ProjSpaceCech.GradedModule.sec.instZero
  ProjSpaceCech.GradedModule.Presentation.fJ
  ProjSpaceCech.GradedModule.sec.instSMul
  ProjSpaceCech.Twist.H.module
  ProjSpaceCech.Idx.instFintype
  ProjSpaceCech.Twist.H.addCommGroup
  ProjSpaceCech.Idx.instDecidableEq
  ProjSpaceCech.Twist.Mon.instDecidableEq
  ProjSpaceCech.Twist.cochain.instAddCommGroup
  ProjSpaceCech.Twist.cochain.instModule
attribute [-simp]
  AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq
  AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.mk.injEq
  AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app
  CoherentBaseChange.FibreH0Family.mk.sizeOf_spec
  CoherentBaseChange.FibreH0Family.mk.injEq
  AlgebraicGeometry.OModulePresheaf.prod_obj
  AlgebraicGeometry.OModulePresheaf.restrOpen_obj
  AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq
  AlgebraicGeometry.OModulePresheaf.pushforward_obj
  AlgebraicGeometry.OModulePresheaf.im_obj
  AlgebraicGeometry.OModulePresheaf.pow_obj
  AlgebraicGeometry.OModulePresheaf.fstHom_app
  AlgebraicGeometry.OModulePresheaf.ker_obj
  AlgebraicGeometry.OModulePresheaf.coker_obj
  AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U
  AlgebraicGeometry.OModulePresheaf.sndHom_app
  AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq
  AlgebraicGeometry.OModulePresheaf.Hom.id_app
  AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply
  AlgebraicGeometry.OModulePresheaf.AffHom.comp_app
  AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe
  AlgebraicGeometry.OModulePresheaf.AffHom.id_app
  AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app
  AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.Hom.comp_app
  AlgebraicGeometry.OModulePresheaf.SES.mk.injEq
  AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq
  AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply
  AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq
  AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U
  AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq
  AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U
attribute [-simp]
  DoubleComplex.Bounded.mk.injEq
  DoubleComplex.Bounded.mk.sizeOf_spec
  DoubleComplex.Convergence.mk.injEq
  DoubleComplex.Convergence.mk.sizeOf_spec
  DoubleComplex.SubQuot.mk.sizeOf_spec
  DoubleComplex.SubQuot.mk.injEq
  AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec
  AlgebraicGeometry.ChowDatum.mk.sizeOf_spec
  AlgebraicGeometry.ChowDatumProj.mk.injEq
  AlgebraicGeometry.ChowDatum.mk.injEq
  ProjSpaceCech.GradedModule.mk.injEq
  ProjSpaceCech.GradedModule.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Presentation.mk.injEq
  ProjSpaceCech.GradedModule.Frac.mk.injEq
  ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Hom.shift_toLinearMap
  ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Hom.mk.injEq

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.RelPicard
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian
open _root_.CategoryTheory.MonoidalCategory
open _root_.Opposite

namespace AlgebraicGeometry

export _root_.AlgebraicGeometry (
  IsClosedImmersion.of_isPreimmersion
  IsProper
  Scheme.Modules.pullback
  Scheme.Hom
  LocallyOfFiniteType
  Spec
  Scheme
  Flat
  IsClosedImmersion
  IsSeparated
  Scheme.Modules.pullbackCongr
  Scheme.fromSpecResidueField_apply
  Scheme.Modules.pullbackId
  Scheme.Modules
  Scheme.Hom.comp_apply
  Scheme.Modules.pullbackComp
  Scheme.Modules.IsInvertible
  Scheme.Modules.pullbackUnitIso
  Scheme.Modules.pullbackTensorObjIso
  Scheme.Modules.pullbackTensorUnitObjIso
  Scheme.TwoAffineOpenCover
  Scheme.TwoAffineOpenCover.specMap
  Scheme.TwoAffineOpenCover.algebraOfHom)

namespace RelPicard

export _root_.AlgebraicGeometry.RelPicard (
  baseChangeSnd
  RigidifiedLineBundle
  RigidifiedLineBundle.unit
  RepresentsRelSubPic
  IsAlgEquivZero
  FibrewiseAlgEquivZero
  FibrewiseAlgEquivZero.pullback
  algEquivZeroCut
  fibreModule
  FibrewiseAlgEquivZero.of_tensor_iso_unit
  isClosed_setOf_exists_fibreModule_iso_unit_of_flat)

namespace Sep

open _root_.AlgebraicGeometry.RelPicard
open _root_.AlgebraicGeometry

variable {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}

/-- Cancel a common tensor factor using two specified trivializations. -/
noncomputable def isoOfTensorIsoUnit {V : Scheme.{u}} (X Y Y' : V.Modules) (i : X ⊗ Y ≅ 𝟙_ _)
    (i' : X ⊗ Y' ≅ 𝟙_ _) : Y ≅ Y' :=
  (λ_ Y).symm ≪≫ (i'.symm ⊗ᵢ Iso.refl Y) ≪≫ ((β_ X Y') ⊗ᵢ Iso.refl Y) ≪≫ α_ Y' X Y ≪≫
    (Iso.refl Y' ⊗ᵢ i) ≪≫ ρ_ Y'

/-- Transport a pullback trivialization along a scheme isomorphism. -/
noncomputable def isoUnitOfPullbackIso {X Y : Scheme.{u}} (φ : X ≅ Y) (M : Y.Modules)
    (e : (Scheme.Modules.pullback φ.hom).obj M ≅ 𝟙_ X.Modules) : M ≅ 𝟙_ Y.Modules :=
  ((Scheme.Modules.pullbackId Y).app M).symm ≪≫
    (Scheme.Modules.pullbackCongr φ.inv_hom_id.symm).app M ≪≫
    (Scheme.Modules.pullbackComp φ.inv φ.hom).symm.app M ≪≫
    (Scheme.Modules.pullback φ.inv).mapIso e ≪≫ Scheme.Modules.pullbackTensorUnitObjIso φ.inv

theorem nonempty_fibreModule_iso_unit_iff {D : RelativePic0Designation R c}
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (Q : RigidifiedLineBundle c ε (pullback.fst D.toBase D.toBase ≫ D.toBase))
    (hQ : Nonempty ((((h.poincare.pullbackAlong ⟨pullback.snd D.toBase D.toBase,
      pullback.condition.symm⟩).tensor Q).L ≅
      (RigidifiedLineBundle.unit (c := c) (ε := ε) (pullback.fst D.toBase D.toBase ≫ D.toBase)).L)))
    {k : Type u} [Field k] (s : Spec (CommRingCat.of k) ⟶ pullback D.toBase D.toBase) :
    Nonempty (fibreModule c (pullback.fst D.toBase D.toBase ≫ D.toBase) s
        ((h.poincare.pullbackAlong ⟨pullback.fst D.toBase D.toBase, rfl⟩).tensor Q).L ≅ 𝟙_ _) ↔
      s ≫ pullback.fst D.toBase D.toBase = s ≫ pullback.snd D.toBase D.toBase := by
  let T : Scheme.{u} := pullback D.toBase D.toBase
  let t : T ⟶ Spec (CommRingCat.of R) := pullback.fst D.toBase D.toBase ≫ D.toBase
  let P₁ : RigidifiedLineBundle c ε t := h.poincare.pullbackAlong ⟨pullback.fst D.toBase D.toBase,
    rfl⟩
  let P₂ : RigidifiedLineBundle c ε t :=
    h.poincare.pullbackAlong ⟨pullback.snd D.toBase D.toBase, pullback.condition.symm⟩
  let ψ : SchemeHomOver (s ≫ t) t := ⟨s, rfl⟩
  let g₁ : SchemeHomOver (s ≫ t) D.toBase := ⟨s ≫ pullback.fst D.toBase D.toBase,
    by rw [Category.assoc]⟩
  let g₂ : SchemeHomOver (s ≫ t) D.toBase := ⟨s ≫ pullback.snd D.toBase D.toBase, by
    rw [Category.assoc, ← pullback.condition]⟩
  have hbc : IsPullback (baseChangeSnd c ψ) (pullback.snd c (s ≫ t)) (pullback.snd c t) s := by
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback c t)
    rw [show baseChangeSnd c ψ ≫ pullback.fst c t = pullback.fst c (s ≫ t) from
      (pullback.lift_fst _ _ _).trans (Category.comp_id _)]
    exact IsPullback.of_hasPullback c (s ≫ t)
  let φ : pullback c (s ≫ t) ≅ pullback (pullback.snd c t) s := hbc.isoPullback
  have hφ : φ.hom ≫ pullback.fst (pullback.snd c t) s = baseChangeSnd c ψ := hbc.isoPullback_hom_fst
  have Φ : ∀ (N : RigidifiedLineBundle c ε t),
      (Scheme.Modules.pullback φ.hom).obj (fibreModule c t s N.L) ≅ (N.pullbackAlong ψ).L := fun N
        =>
    (Scheme.Modules.pullbackComp _ _).app N.L ≪≫ (Scheme.Modules.pullbackCongr hφ).app N.L
  have e₁ : (P₁.pullbackAlong ψ).L ≅ (h.poincare.pullbackAlong g₁).L :=
    h.poincare.pullbackAlongPullbackAlongIso ⟨pullback.fst D.toBase D.toBase, rfl⟩ ψ
  have e₂ : (P₂.pullbackAlong ψ).L ≅ (h.poincare.pullbackAlong g₂).L :=
    h.poincare.pullbackAlongPullbackAlongIso ⟨pullback.snd D.toBase D.toBase,
      pullback.condition.symm⟩ ψ
  have iQ : (P₂.pullbackAlong ψ).L ⊗ (Q.pullbackAlong ψ).L ≅ 𝟙_ _ :=
    (Scheme.Modules.pullbackTensorObjIso _ _ _).symm ≪≫ (Scheme.Modules.pullback _).mapIso hQ.some
      ≪≫
      Scheme.Modules.pullbackUnitIso _
  constructor
  · rintro ⟨e⟩
    have e' : (P₁.pullbackAlong ψ).L ⊗ (Q.pullbackAlong ψ).L ≅ 𝟙_ _ :=
      (Scheme.Modules.pullbackTensorObjIso _ _ _).symm ≪≫ (Φ (P₁.tensor Q)).symm ≪≫
        (Scheme.Modules.pullback φ.hom).mapIso e ≪≫ Scheme.Modules.pullbackTensorUnitObjIso _
    have i12 : (P₁.pullbackAlong ψ).L ≅ (P₂.pullbackAlong ψ).L :=
      isoOfTensorIsoUnit _ _ _ ((β_ _ _) ≪≫ e') ((β_ _ _) ≪≫ iQ)
    have hg : g₁ = g₂ := h.ext_of_iso (s ≫ t) g₁ g₂ ⟨e₁.symm ≪≫ i12 ≪≫ e₂⟩
    exact congrArg Subtype.val hg
  · intro hs
    have hg : g₁ = g₂ := Subtype.ext hs
    have i12 : (P₁.pullbackAlong ψ).L ≅ (P₂.pullbackAlong ψ).L :=
      e₁ ≪≫ eqToIso (by rw [hg]) ≪≫ e₂.symm
    have e' : (P₁.pullbackAlong ψ).L ⊗ (Q.pullbackAlong ψ).L ≅ 𝟙_ _ := (i12 ⊗ᵢ Iso.refl _) ≪≫ iQ
    exact ⟨isoUnitOfPullbackIso φ _ ((Φ (P₁.tensor Q)) ≪≫ Scheme.Modules.pullbackTensorObjIso _ _ _
      ≪≫ e')⟩

end AlgebraicGeometry.RelPicard.Sep
end JacobianVarieties.Picard.Proofs.SectionPicardSeparated

namespace AlgebraicGeometry.RelPicard

open _root_.JacobianVarieties.Picard.Proofs
open _root_.JacobianVarieties.Picard.Proofs.SectionPicardSeparated
universe u
open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.RelPicard
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian
open _root_.CategoryTheory.MonoidalCategory
open _root_.Opposite

/-- Separatedness of the representing scheme from the closed fibrewise triviality locus. -/
theorem isSeparated_of_representsRelSubPic_algEquivZeroCut_of_bijective_sections
    (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of
      R))
    [IsProper c] [Flat c] (𝒱 : C.TwoAffineOpenCover)
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (hH0 : ∀ (A : Type u) [CommRing A] [Algebra R A],
      let : Algebra A Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A), ⊤) :=
        Scheme.TwoAffineOpenCover.algebraOfHom
          (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A)) ⊤
      Function.Bijective (algebraMap A Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A),
        ⊤)))
    (hfib : ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
      (L : (pullback c x).Modules), Scheme.Modules.IsInvertible L →
      IsAlgEquivZero (pullback.snd c x) L →
      ∀ s : 𝟙_ (pullback c x).Modules ⟶ L, s ≠ 0 → Nonempty (L ≅ 𝟙_ (pullback c x).Modules))
    (D : RelativePic0Designation R c) (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    [LocallyOfFiniteType D.toBase] :
    IsSeparated D.toBase := by
  let T : Scheme.{u} := pullback D.toBase D.toBase
  let t : T ⟶ Spec (CommRingCat.of R) := pullback.fst D.toBase D.toBase ≫ D.toBase
  let P₁ : RigidifiedLineBundle c ε t := h.poincare.pullbackAlong ⟨pullback.fst D.toBase D.toBase,
    rfl⟩
  let P₂ : RigidifiedLineBundle c ε t := h.poincare.pullbackAlong ⟨pullback.snd D.toBase D.toBase,
    pullback.condition.symm⟩
  obtain ⟨Q, hQ⟩ := P₂.exists_tensor_iso_unit
  have hP₁ : FibrewiseAlgEquivZero P₁ := FibrewiseAlgEquivZero.pullback _ h.poincare_mem
  have hP₂ : FibrewiseAlgEquivZero P₂ := FibrewiseAlgEquivZero.pullback _ h.poincare_mem
  have hL : FibrewiseAlgEquivZero (P₁.tensor Q) := hP₁.tensor
    (FibrewiseAlgEquivZero.of_tensor_iso_unit hQ hP₂)
  have : LocallyOfFiniteType t := inferInstance
  have hZ := isClosed_setOf_exists_fibreModule_iso_unit_of_flat R c 𝒱 ε hH0 hfib t (P₁.tensor Q) hL
  have hrange : Set.range ⇑(pullback.diagonal D.toBase) = {x : T | ∃ (k : Type u) (_ : Field k)
      (s : Spec (CommRingCat.of k) ⟶ T), s.base (IsLocalRing.closedPoint k) = x ∧
        Nonempty (fibreModule c t s (P₁.tensor Q).L ≅ 𝟙_ (pullback (pullback.snd c t) s).Modules)}
          := by
    ext x
    constructor
    · rintro ⟨q, rfl⟩
      refine ⟨D.P.residueField q, inferInstance, D.P.fromSpecResidueField q ≫ pullback.diagonal
        D.toBase, ?_, ?_⟩
      · exact congrArg (pullback.diagonal D.toBase).base (Scheme.fromSpecResidueField_apply q
          (IsLocalRing.closedPoint (D.P.residueField q)))
      · exact
          (SectionPicardSeparated.AlgebraicGeometry.RelPicard.Sep.nonempty_fibreModule_iso_unit_iff
          h Q hQ _).mpr (by
          rw [Category.assoc, Category.assoc, pullback.diagonal_fst, pullback.diagonal_snd])
    · rintro ⟨k, _, s, rfl, hs⟩
      have heq :=
        (SectionPicardSeparated.AlgebraicGeometry.RelPicard.Sep.nonempty_fibreModule_iso_unit_iff h
        Q hQ s).mp hs
      have hfac : (s ≫ pullback.fst D.toBase D.toBase) ≫ pullback.diagonal D.toBase = s := by
        apply pullback.hom_ext
        · rw [Category.assoc, pullback.diagonal_fst, Category.comp_id]
        · rw [Category.assoc, pullback.diagonal_snd, Category.comp_id, heq]
      exact ⟨(s ≫ pullback.fst D.toBase D.toBase) (IsLocalRing.closedPoint k), by
        exact congrArg (fun f : Spec (CommRingCat.of k) ⟶ T =>
          f.base (IsLocalRing.closedPoint k)) hfac⟩
  rw [← hrange] at hZ
  exact ⟨IsClosedImmersion.of_isPreimmersion _ hZ⟩
end AlgebraicGeometry.RelPicard
end ProofImplementation

attribute [-instance]
  PresheafOfModules.ExteriorPower.instModulePresheafAb
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
  AlgebraicGeometry.OModulePresheaf.isScalarTower
  AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder
  AlgebraicGeometry.OModulePresheaf.module
  AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype
  AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx
  AlgebraicGeometry.OModulePresheaf.addCommGroup
  AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx
  AlgebraicGeometry.OModulePresheaf.moduleSections
  AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero
  AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower
  AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ
  AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ
  AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp
  AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ
  AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul
  AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower
  AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul
  AlgebraicGeometry.OModulePresheaf.Leray.biC_module
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx
attribute [-instance]
  DoubleComplex.instModuleE₂I
  DoubleComplex.Bounded.modR
  DoubleComplex.instModuleE₂II
  DoubleComplex.instAddCommGroupE₂II
  DoubleComplex.Bounded.abGrp
  DoubleComplex.instAddCommGroupE₂I
  AlgebraicGeometry.ChowDatum.hι_closed
  AlgebraicGeometry.ChowDatumProj.hιN_closed
  AlgebraicGeometry.ChowDatumProj.hp_proper
  AlgebraicGeometry.ChowDatum.hp_isoU
  AlgebraicGeometry.ChowDatum.hp_proper
  AlgebraicGeometry.ProjSpace.algebraAway
  AlgebraicGeometry.ProjSpace.instIsProperProdOverπ
  AlgebraicGeometry.ChowDatumProj.hp_isoU
  AlgebraicGeometry.ProjSpace.isProper_π
  AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial
  ProjSpaceCech.GradedModule.H.module
  ProjSpaceCech.GradedModule.H.addCommGroup
  ProjSpaceCech.GradedModule.sec.instAdd
  ProjSpaceCech.GradedModule.sec.instNeg
  ProjSpaceCech.GradedModule.acg
  ProjSpaceCech.GradedModule.Frac.setoid
  ProjSpaceCech.GradedModule.modR
  ProjSpaceCech.GradedModule.sec.instModule
  ProjSpaceCech.GradedModule.sec.instAddCommGroup
  ProjSpaceCech.GradedModule.sec.instZero
  ProjSpaceCech.GradedModule.Presentation.fJ
  ProjSpaceCech.GradedModule.sec.instSMul
  ProjSpaceCech.Twist.H.module
  ProjSpaceCech.Idx.instFintype
  ProjSpaceCech.Twist.H.addCommGroup
  ProjSpaceCech.Idx.instDecidableEq
  ProjSpaceCech.Twist.Mon.instDecidableEq
  ProjSpaceCech.Twist.cochain.instAddCommGroup
  ProjSpaceCech.Twist.cochain.instModule
attribute [-simp]
  AlgebraicGeometry.RelPicard.SubPicCondition.onClasses_mk
  AlgebraicGeometry.RelPicard.relSubPicPresheaf_map_coe
  AlgebraicGeometry.RelPicard.thetaBundle_def
  AlgebraicGeometry.RelPicard.picardBundle_def
  AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor
  AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_I
  AlgebraicGeometry.mapOnProdOver_fst_assoc
  AlgebraicGeometry.RelEffCartierDiv.mk.sizeOf_spec
  AlgebraicGeometry.RelEffCartierDiv.mk.injEq
  AlgebraicGeometry.mapOnProdOver_snd
  AlgebraicGeometry.mapOnProdOver_fst
  AlgebraicGeometry.mapOnProdOver_snd_assoc
  AlgebraicGeometry.mapOnProdOver_id
  AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec
  AlgebraicCurve.mapOnProd_fst
  AlgebraicCurve.mapOnProd_fst_assoc
  AlgebraicCurve.mapOnProd_snd
  AlgebraicCurve.UnivDivisorPack.mk.injEq
  AlgebraicCurve.RelEffDivisor.mk.injEq
  AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec
  AlgebraicCurve.mapOnProd_snd_assoc
  AlgebraicGeometry.Scheme.Modules.exteriorPower_obj
  PresheafOfModules.exteriorPower_map_ιMulti
  PresheafOfModules.ExteriorPower.appₗ_apply
  AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.injEq
  AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.sizeOf_spec
  GoodReductionJacobian.relativeGroupLawOfGrpObj_inv
  GoodReductionJacobian.relativeGroupLawOfGrpObj_mul
  GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe
  GoodReductionJacobian.relativeGroupLawOfGrpObj_one
  GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left
  PresheafOfModules.freeεIso_hom_app
  PresheafOfModules.freeμIso_hom_app
  AlgebraicGeometry.RelPicard.algEquivZeroGroupCut_toSubPicCondition
  AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq
  AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.mk.injEq
  AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app
  CoherentBaseChange.FibreH0Family.mk.sizeOf_spec
attribute [-simp]
  CoherentBaseChange.FibreH0Family.mk.injEq
  AlgebraicGeometry.OModulePresheaf.prod_obj
  AlgebraicGeometry.OModulePresheaf.restrOpen_obj
  AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq
  AlgebraicGeometry.OModulePresheaf.pushforward_obj
  AlgebraicGeometry.OModulePresheaf.im_obj
  AlgebraicGeometry.OModulePresheaf.pow_obj
  AlgebraicGeometry.OModulePresheaf.fstHom_app
  AlgebraicGeometry.OModulePresheaf.ker_obj
  AlgebraicGeometry.OModulePresheaf.coker_obj
  AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U
  AlgebraicGeometry.OModulePresheaf.sndHom_app
  AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq
  AlgebraicGeometry.OModulePresheaf.Hom.id_app
  AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply
  AlgebraicGeometry.OModulePresheaf.AffHom.comp_app
  AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe
  AlgebraicGeometry.OModulePresheaf.AffHom.id_app
  AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app
  AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.Hom.comp_app
  AlgebraicGeometry.OModulePresheaf.SES.mk.injEq
  AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq
  AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply
  AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq
  AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U
  AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq
  AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U
  DoubleComplex.Bounded.mk.injEq
  DoubleComplex.Bounded.mk.sizeOf_spec
  DoubleComplex.Convergence.mk.injEq
  DoubleComplex.Convergence.mk.sizeOf_spec
  DoubleComplex.SubQuot.mk.sizeOf_spec
  DoubleComplex.SubQuot.mk.injEq
attribute [-simp]
  AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec
  AlgebraicGeometry.ChowDatum.mk.sizeOf_spec
  AlgebraicGeometry.ChowDatumProj.mk.injEq
  AlgebraicGeometry.ChowDatum.mk.injEq
  ProjSpaceCech.GradedModule.mk.injEq
  ProjSpaceCech.GradedModule.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Presentation.mk.injEq
  ProjSpaceCech.GradedModule.Frac.mk.injEq
  ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Hom.shift_toLinearMap
  ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Hom.mk.injEq
