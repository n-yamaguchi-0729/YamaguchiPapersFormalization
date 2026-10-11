/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Anthropic FLT source material is identified by code comparison;
the exact source-file correspondence remains unresolved.
Upstream repository: https://github.com/anthropics/fermats-last-theorem
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Pullbacks
import Nyll.AlgebraicCurves.Geometry.Curves.bijective_appTop_of_universallyClosed_of_geometricallyReduced_of_geometricallyConnected
import Nyll.AlgebraicCurves.Geometry.Schemes.bijective_app_of_isProper_of_flat_of_forall_bijective_appTop_fiberToSpecResidueField

/-!
# bijective app of is Proper of flat of geometrically Reduced of geometrically Connected
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Curves.Proofs
namespace bijective_app_of_isProper_of_flat_of_geometricallyReduced_of_geometricallyConnected
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

end bijective_app_of_isProper_of_flat_of_geometricallyReduced_of_geometricallyConnected
end AlgebraicCurves.Geometry.Curves.Proofs

namespace AlgebraicGeometry

universe u

open _root_.AlgebraicCurves.Geometry.Curves.Proofs in
open bijective_app_of_isProper_of_flat_of_geometricallyReduced_of_geometricallyConnected in
open AlgebraicGeometry CategoryTheory in
theorem bijective_app_of_isProper_of_flat_of_geometricallyReduced_of_geometricallyConnected
    {X B : Scheme.{u}} (p : X ⟶ B) [IsProper p] [Flat p] [LocallyOfFinitePresentation p]
    [GeometricallyReduced p] [GeometricallyConnected p] (U : B.Opens) :
    Function.Bijective (p.app U) := by
  refine bijective_app_of_isProper_of_flat_of_forall_bijective_appTop_fiberToSpecResidueField p
    (fun b ↦ ?_) U
  have : IsProper (p.fiberToSpecResidueField b) := by
    have : MorphismProperty.IsStableUnderBaseChange
        (@IsProper : MorphismProperty Scheme.{u}) :=
          AlgebraicGeometry.IsProper.isStableUnderBaseChange
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := (@IsProper : MorphismProperty Scheme.{u}))
      (CategoryTheory.IsPullback.of_hasPullback p (B.fromSpecResidueField b)) inferInstance
  exact bijective_appTop_of_universallyClosed_of_geometricallyReduced_of_geometricallyConnected
    (K := B.residueField b) (p.fiberToSpecResidueField b)
end AlgebraicGeometry
end ProofImplementation
