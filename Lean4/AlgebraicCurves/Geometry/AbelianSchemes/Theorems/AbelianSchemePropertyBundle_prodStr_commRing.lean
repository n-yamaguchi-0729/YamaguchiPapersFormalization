/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_GoodReductionJacobian_AbelianSchemePropertyBundle_prodStr_commRing.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.AlgebraicGeometry.Fiber
import AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.Product
import AlgebraicCurves.Geometry.AbelianSchemes.Theorems.AbelianSchemePropertyBundle_of_isPullback
import AlgebraicCurves.Geometry.AbelianSchemes.Theorems.abelianSchemePropertyBundle_prodStr

/-!
# Abelian Scheme Property Bundle prod Str comm Ring
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.AbelianSchemes.Theorems.Proofs
namespace AbelianSchemePropertyBundle_prodStr_commRing
attribute [-simp] GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase
  GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe
  GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe
  GoodReductionJacobian.RelativeGroupLaw.baseChange_inv
  GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase
  GoodReductionJacobian.RelativeGroupLaw.baseChange_mul
  GoodReductionJacobian.RelativeGroupLaw.baseChange_one
  GoodReductionJacobian.RelativeGroupLaw.nsmul_zero
  GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset
  GoodReductionJacobian.RelativeGroupLaw.nsmul_succ NeronModelInfra.fibreRestrictAlong_coe_comp_snd
  NeronModelInfra.fibreRestrictAlong_coe_comp_fst GoodReductionJacobian.RelativeGroupLaw.fibre_inv
  GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe
  GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase
  GoodReductionJacobian.RelativeGroupLaw.fibre_mul
  GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase
  GoodReductionJacobian.RelativeGroupLaw.fibre_one
  GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd
  AlgebraicGeometry.schemeFibreEndo_fst


open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian


universe u

noncomputable section

namespace GoodReductionJacobian

export _root_.GoodReductionJacobian (AbelianSchemePropertyBundle RelativeGroupLaw prodStr
  RelativeGroupLaw.prod AbelianSchemePropertyBundle.of_isPullback
  abelianSchemePropertyBundle_prodStr)

namespace ProdCommRingAux

open _root_.GoodReductionJacobian


theorem isPullback_map {T T' X X' Y Y' : Scheme.{u}} {fX : X ⟶ T} {fY : Y ⟶ T} {fX' : X' ⟶ T'} {fY'
  : Y' ⟶ T'}
    {pX : X' ⟶ X} {pY : Y' ⟶ Y} {t : T' ⟶ T} (hX : IsPullback pX fX' fX t) (hY : IsPullback pY fY'
      fY t) :
    IsPullback (pullback.map fX' fY' fX fY pX pY t hX.w.symm hY.w.symm)
      (pullback.fst fX' fY' ≫ fX') (pullback.fst fX fY ≫ fX) t := by
  have S1 : IsPullback (pullback.snd fX' fY') (pullback.fst fX' fY' ≫ pX) (fY' ≫ t) fX :=
    (IsPullback.of_hasPullback fX' fY').flip.paste_vert hX.flip
  have S1' : IsPullback (pullback.map fX' fY' fX fY pX pY t hX.w.symm hY.w.symm ≫ pullback.fst fX
    fY)
      (pullback.snd fX' fY') fX (pY ≫ fY) := by
    convert S1.flip using 1
    · simp only [pullback.lift_fst]
    · exact hY.w
  have S2 : IsPullback (pullback.map fX' fY' fX fY pX pY t hX.w.symm hY.w.symm) (pullback.snd fX'
    fY')
      (pullback.snd fX fY) pY :=
    S1'.of_right (by simp only [pullback.lift_snd]) (IsPullback.of_hasPullback fX fY)
  have S3 := S2.paste_vert hY
  convert S3 using 1
  · exact pullback.condition
  · exact pullback.condition

variable {R : Type u} [CommRing R] {B C : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)}
  {h : C ⟶ Spec (CommRingCat.of R)}

theorem isConnected_fibre (hB : AbelianSchemePropertyBundle R g) (hC : AbelianSchemePropertyBundle
  R h)
    (s : Spec (CommRingCat.of R)) : _root_.IsConnected ((prodStr g h).base ⁻¹' {s}) := by
  let ι : Spec ((Spec (CommRingCat.of R)).residueField s) ⟶ Spec (CommRingCat.of R) :=
    (Spec (CommRingCat.of R)).fromSpecResidueField s
  have hBs : AbelianSchemePropertyBundle ((Spec (CommRingCat.of R)).residueField s) (pullback.snd g
    ι) :=
    hB.of_isPullback (R' := (Spec (CommRingCat.of R)).residueField s) (ι := ι)
      (IsPullback.of_hasPullback _ _)
  have hCs : AbelianSchemePropertyBundle ((Spec (CommRingCat.of R)).residueField s) (pullback.snd h
    ι) :=
    hC.of_isPullback (R' := (Spec (CommRingCat.of R)).residueField s) (ι := ι)
      (IsPullback.of_hasPullback _ _)
  have hP := abelianSchemePropertyBundle_prodStr hBs hCs
  have hconn : ConnectedSpace ↑(pullback (pullback.snd g ι) (pullback.snd h ι)) := by
    rw [connectedSpace_iff_univ]
    convert hP.connectedFibres (IsLocalRing.closedPoint _) using 1
    refine (Set.eq_univ_of_forall fun x => ?_).symm
    change _ = _
    exact Subsingleton.elim (α := PrimeSpectrum ((Spec (CommRingCat.of R)).residueField s)) _ _
  have hsq := isPullback_map (IsPullback.of_hasPullback g ι) (IsPullback.of_hasPullback h ι)
  let e : pullback (pullback.snd g ι) (pullback.snd h ι) ≅ (prodStr g h).fiber s := hsq.isoPullback
  have : ConnectedSpace ↑((prodStr g h).fiber s) := by
    rw [connectedSpace_iff_univ]
    have himg := (isConnected_range (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso e)).continuous)
    rwa [(TopCat.homeoOfIso (Scheme.forgetToTop.mapIso e)).surjective.range_eq] at himg
  rw [← Scheme.Hom.range_fiberι]
  exact isConnected_range (Scheme.Hom.continuous _)

theorem main (hB : AbelianSchemePropertyBundle R g) (hC : AbelianSchemePropertyBundle R h) :
    AbelianSchemePropertyBundle R (prodStr g h) := by
  have := hB.smooth
  have := hC.smooth
  have := hB.proper
  have := hC.proper
  obtain ⟨LB⟩ := hB.hasGroupLaw
  obtain ⟨LC⟩ := hC.hasGroupLaw
  exact
    { smooth := inferInstance
      proper := inferInstance
      connectedFibres := isConnected_fibre hB hC
      hasGroupLaw := ⟨LB.prod LC⟩ }

end GoodReductionJacobian.ProdCommRingAux

end

theorem _root_.GoodReductionJacobian.AbelianSchemePropertyBundle.prodStr_commRing
    {R : Type u} [CommRing R] {B C : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)}
    {h : C ⟶ Spec (CommRingCat.of R)} (hB : AbelianSchemePropertyBundle R g)
    (hC : AbelianSchemePropertyBundle R h) :
    AbelianSchemePropertyBundle R (prodStr g h) :=
  GoodReductionJacobian.ProdCommRingAux.main hB hC
end AbelianSchemePropertyBundle_prodStr_commRing
end AlgebraicCurves.Geometry.AbelianSchemes.Theorems.Proofs
end ProofImplementation
