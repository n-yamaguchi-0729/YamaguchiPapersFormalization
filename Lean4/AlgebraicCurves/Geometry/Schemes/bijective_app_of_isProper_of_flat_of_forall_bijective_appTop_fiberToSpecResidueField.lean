/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_bijective_app_of_isProper_of_flat_of_forall_bijective_appTop_fiberToSpecResidueField.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Spec
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.CategoryTheory.ConcreteCategory.Basic
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.AlgebraicGeometry.Fiber
import AlgebraicCurves.Geometry.Schemes.bijective_appTop_of_isProper_of_flat_of_locallyOfFinitePresentation_of_isLocalRing
import AlgebraicCurves.Geometry.Schemes.bijective_appTop_pullback_snd_of_bijective_appTop_fiberToSpecResidueField
import AlgebraicCurves.Geometry.Schemes.bijective_appTop_of_forall_isMaximal
import AlgebraicCurves.Geometry.Schemes.bijective_app_of_forall_isAffineOpen
import AlgebraicCurves.Geometry.Schemes.bijective_app_of_bijective_appTop_morphismRestrict

/-!
# bijective app of is Proper of flat of forall bijective app Top fiber To Spec Residue Field
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs
namespace bijective_app_of_isProper_of_flat_of_forall_bijective_appTop_fiberToSpecResidueField
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
  IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty
  AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed
  AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU
  AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway
  AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU
  AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial
  AdicCompletion.instIsLocalRingMaximalIdeal
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
  AlgebraicGeometry.SubalgebraStages.leg_trans IsDirectLimit.Module.linearEquiv_symm_apply
  IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply
  IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply
  AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec
  AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq

open AlgebraicGeometry CategoryTheory

universe u

open CategoryTheory.Limits TopologicalSpace

namespace H0AuxGen

theorem bijective_appTop_of_iso {P P' Y : Scheme.{u}} (e : P ≅ P') (s : P ⟶ Y) (s' : P' ⟶ Y) (w :
  e.hom ≫ s' = s)
    (h : Function.Bijective s'.appTop) : Function.Bijective s.appTop := by
  rw [← w, Scheme.Hom.comp_appTop]
  have : IsIso e.hom.appTop := ⟨⟨e.inv.appTop, by rw [← Scheme.Hom.comp_appTop, e.inv_hom_id]; simp,
    by rw [← Scheme.Hom.comp_appTop, e.hom_inv_id]; simp⟩⟩
  have he : Function.Bijective e.hom.appTop := (ConcreteCategory.isIso_iff_bijective _).mp
    inferInstance
  change Function.Bijective (e.hom.appTop.hom ∘ s'.appTop.hom)
  exact he.comp h

open _root_.AlgebraicGeometry in
theorem bijective_appTop_of_affine {X : Scheme.{u}} {R : CommRingCat.{u}}
    (q : X ⟶ Spec R) [IsProper q] [Flat q] [LocallyOfFinitePresentation q]
    (h : ∀ {K : Type u} [Field K] (k : Spec (CommRingCat.of K) ⟶ Spec R), Function.Bijective
      (pullback.snd q k).appTop) :
    Function.Bijective q.appTop := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace q
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated q
  apply AlgebraicGeometry.bijective_appTop_of_forall_isMaximal q
  intro P _
  let A : Type u := Localization.AtPrime P
  let ιA : Spec (CommRingCat.of A) ⟶ Spec R := Spec.map (CommRingCat.ofHom (algebraMap (↑R) A))
  let qA : pullback q ιA ⟶ Spec (CommRingCat.of A) := pullback.snd q ιA
  have : IsProper qA := by
    have : MorphismProperty.IsStableUnderBaseChange
        (@IsProper : MorphismProperty Scheme.{u}) :=
          AlgebraicGeometry.IsProper.isStableUnderBaseChange
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := (@IsProper : MorphismProperty Scheme.{u}))
      (IsPullback.of_hasPullback q ιA) inferInstance
  have : Flat qA := by
    have : MorphismProperty.IsStableUnderBaseChange
        (@Flat : MorphismProperty Scheme.{u}) := AlgebraicGeometry.Flat.isStableUnderBaseChange
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := (@Flat : MorphismProperty Scheme.{u}))
      (IsPullback.of_hasPullback q ιA) inferInstance
  have : LocallyOfFinitePresentation qA := by
    have : MorphismProperty.IsStableUnderBaseChange
        (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) :=
          AlgebraicGeometry.locallyOfFinitePresentation_isStableUnderBaseChange
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u}))
      (IsPullback.of_hasPullback q ιA) inferInstance
  have : IsLocalRing (CommRingCat.of A) := (inferInstance : IsLocalRing A)
  apply bijective_appTop_of_isProper_of_flat_of_locallyOfFinitePresentation_of_isLocalRing qA
  let mk : Spec (CommRingCat.of (A ⧸ IsLocalRing.maximalIdeal A)) ⟶ Spec (CommRingCat.of A) :=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)))
  let : Field (A ⧸ IsLocalRing.maximalIdeal A) := Ideal.Quotient.field _
  have hk := h (mk ≫ ιA)
  exact bijective_appTop_of_iso (pullbackLeftPullbackSndIso q ιA mk) _ _
    (pullbackLeftPullbackSndIso_hom_snd q ιA mk) hk

end H0AuxGen

end bijective_app_of_isProper_of_flat_of_forall_bijective_appTop_fiberToSpecResidueField
end AlgebraicCurves.Geometry.Schemes.Proofs

namespace AlgebraicGeometry

universe u

open _root_.AlgebraicCurves.Geometry.Schemes.Proofs in
open bijective_app_of_isProper_of_flat_of_forall_bijective_appTop_fiberToSpecResidueField in
open AlgebraicGeometry CategoryTheory in
open CategoryTheory.Limits TopologicalSpace in
theorem bijective_app_of_isProper_of_flat_of_forall_bijective_appTop_fiberToSpecResidueField
    {X B : Scheme.{u}} (p : X ⟶ B) [IsProper p] [Flat p] [LocallyOfFinitePresentation p]
    (h : ∀ b : B, Function.Bijective (p.fiberToSpecResidueField b).appTop) (U : B.Opens) :
    Function.Bijective (p.app U) := by
  apply AlgebraicGeometry.bijective_app_of_forall_isAffineOpen p ?_ U
  intro V hV
  apply AlgebraicGeometry.bijective_app_of_bijective_appTop_morphismRestrict p V
  have : IsAffine (↑V : Scheme.{u}) := hV
  let e : (↑V : Scheme.{u}) ≅ Spec Γ(B, V) := hV.isoSpec
  let q : (↑(p ⁻¹ᵁ V) : Scheme.{u}) ⟶ Spec Γ(B, V) := (p ∣_ V) ≫ e.hom
  have hq : Function.Bijective q.appTop := by
    apply H0AuxGen.bijective_appTop_of_affine q
    intro K _ k
    let k' : Spec (CommRingCat.of K) ⟶ B := (k ≫ e.inv) ≫ V.ι
    have hP1 :=
      AlgebraicGeometry.bijective_appTop_pullback_snd_of_bijective_appTop_fiberToSpecResidueField p
      k'
      (h (k'.base (IsLocalRing.closedPoint K)))
    have sq1 : IsPullback (pullback.fst q k) (pullback.snd q k) (p ∣_ V) (k ≫ e.inv) := by
      refine (IsPullback.of_hasPullback q k).of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) e.symm
        ?_ ?_ ?_ ?_
      · simp
      · simp
      · simp [q]
      · simp
    have sq2 : IsPullback (p ⁻¹ᵁ V).ι (p ∣_ V) p V.ι := (isPullback_morphismRestrict p V).flip
    have big := sq1.paste_horiz sq2
    exact H0AuxGen.bijective_appTop_of_iso big.isoPullback _ _ (big.isoPullback_hom_snd) hP1
  rw [show q = (p ∣_ V) ≫ e.hom from rfl, Scheme.Hom.comp_appTop] at hq
  have : IsIso e.hom.appTop := ⟨⟨e.inv.appTop, by rw [← Scheme.Hom.comp_appTop, e.inv_hom_id]; simp,
    by rw [← Scheme.Hom.comp_appTop, e.hom_inv_id]; simp⟩⟩
  have he : Function.Bijective e.hom.appTop := (ConcreteCategory.isIso_iff_bijective _).mp
    inferInstance
  have : Function.Bijective ((p ∣_ V).appTop.hom ∘ e.hom.appTop.hom) := hq
  exact (Function.Bijective.of_comp_iff _ he).mp this
end AlgebraicGeometry
end ProofImplementation
