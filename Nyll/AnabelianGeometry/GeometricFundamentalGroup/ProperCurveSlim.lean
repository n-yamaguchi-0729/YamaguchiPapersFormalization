/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.GeometricFundamentalGroup.ProperDeckFaithfulness
import Nyll.EtaleFundamentalGroups.Cohomology.DeckH1Centralizer
import Nyll.EtaleFundamentalGroups.GaloisCovers.OpenSubgroupFundamentalGroup
import Nyll.EtaleFundamentalGroups.GaloisCovers.ConnectedCurveModel
import Nyll.EtaleFundamentalGroups.GeometricFiber.PullbackEquivalence
import Nyll.ProCGroups.FiniteStepSolvableQuotients.SlimnessAndTorsion

/-! # Slimness of actual fundamental groups of proper hyperbolic curves

Every actual open subgroup is realized by an actual connected finite étale
cover. Its smooth proper model remains hyperbolic by Riemann--Hurwitz.
Geometric deck H¹ faithfulness proves its center trivial, and the existing
open-subgroup criterion gives the full centralizer quantification of IsSlim.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicCurve
open CategoryTheory.PreGaloisCategory EtaleFundamentalGroups
open ProCGroups.FiniteStepSolvableQuotients

namespace AnabelianGeometry

/-- The actual étale fundamental group of a proper hyperbolic curve over an
algebraically closed field of characteristic zero is slim, with the actual
open-subgroup quantification of the library's IsSlim definition. -/
theorem isSlim_fundamentalGroup_proper_hyperbolic
    {K F : Type} [Field K] [IsAlgClosed K] [CharZero K]
    [Field F] [Algebra K F] [IsCurveOver K F]
    (M : CurveModel K F) (hg : 2 ≤ genusFF K F)
    {Ω : Type} [Field Ω] [IsSepClosed Ω]
    (geom : Spec (.of Ω) ⟶ M.C) :
    IsSlim (Aut (FiniteEtale.fiber geom)) := by
  apply isSlim_iff_openSubgroups_center_eq_bot.mpr
  intro H
  rw [Subgroup.eq_bot_iff_forall]
  intro z hz
  obtain ⟨A, hA, geomA, _, eA, _⟩ :=
    FiniteEtale.exists_connectedCover_lift_fundamentalGroup_equiv_openSubgroup geom H
  have : IsConnected A := FiniteEtale.isConnected_of_connectedSpace_left A
  have : Smooth M.toBase := SmoothOfRelativeDimension.smooth 1 M.toBase
  have : IsIntegrallyClosed Γ(Spec (.of K), ⊤) :=
    IsIntegrallyClosed.of_equiv (Scheme.ΓSpecIso (.of K)).symm.commRingCatIsoToRingEquiv
  have : IsNormalIntegral M.C := IsNormalIntegral.of_stalks M.C
    (fun x => (Smooth.isDomain_and_isIntegrallyClosed_stalk M.toBase x).2)
  have : IsIntegral A.left := isIntegral_left_of_isConnected_finiteEtale A
  let : Algebra K A.left.functionField :=
    (baseToFunctionField (show A.left ⟶ Spec (.of K) from A.hom ≫ M.toBase)).toAlgebra
  obtain ⟨hC, hFT, N, i, _, hgenus⟩ :=
    exists_curveModel_of_connected_finiteEtale M A
  let E : FiniteEtale N.C ≌ FiniteEtale A.left :=
    MorphismProperty.Over.pullbackIso
      (@IsFiniteEtale : MorphismProperty Scheme) ⊤ i
  have : (FiniteEtale.pullback i.inv).IsEquivalence := E.isEquivalence_functor
  let e : H ≃ₜ* Aut (FiniteEtale.fiber (geomA ≫ i.inv)) :=
    eA.symm.trans (FiniteEtale.fundamentalGroupEquivOfPullbackEquivalence i.inv geomA)
  have he : e z = 1 :=
    Cohomology.fundamentalGroup_eq_one_of_finiteH1_deck_faithful (geomA ≫ i.inv)
      (fun B _ xi σ hσ => deck_eq_one_of_all_finiteH1_trivial N (hgenus hg) B xi σ hσ)
      (e z) (by
      intro a
      have hcomm : z * e.symm a = e.symm a * z :=
        (Subgroup.mem_center_iff.mp hz (e.symm a)).symm
      have hmap := congrArg e hcomm
      change e z * a = a * e z
      simpa only [map_mul, e.apply_symm_apply] using hmap)
  exact e.injective (he.trans (map_one e).symm)

end AnabelianGeometry
