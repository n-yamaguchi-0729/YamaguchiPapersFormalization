/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.GeometricFundamentalGroup.OpenDeckFaithfulness
import Nyll.EtaleFundamentalGroups.Cohomology.DeckH1Centralizer
import Nyll.EtaleFundamentalGroups.GaloisCovers.OpenSubgroupFundamentalGroup
import Nyll.ProCGroups.FiniteStepSolvableQuotients.SlimnessAndTorsion

/-! # Slimness of actual hyperbolic open-curve fundamental groups

Arbitrary open subgroups, including nonnormal ones, are realized by actual
connected finite étale covers. Their actual compactifications and boundary
Riemann--Hurwitz prove hyperbolicity. The geometric H¹ argument then kills
their centers, giving the existing full IsSlim predicate.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicCurve
open CategoryTheory.PreGaloisCategory EtaleFundamentalGroups
open ProCGroups.FiniteStepSolvableQuotients

namespace AnabelianGeometry

/-- The actual fundamental group of a hyperbolic open curve is slim. -/
theorem isSlim_fundamentalGroup_open_hyperbolic
    {K F : Type} [Field K] [IsAlgClosed K] [CharZero K]
    [Field F] [Algebra K F]
    (M : CurveModel K F) {X : Scheme}
    [IsIntegral X] [IsNormalIntegral X] [IsLocallyNoetherian X] [CompactSpace X]
    (j : X ⟶ M.C) [IsOpenImmersion j] [QuasiCompact j] [QuasiSeparated j]
    (hboundary : (M.openBoundaryPlaces j).Nonempty)
    (hhyperbolic : 0 <
      2 * (genusFF K F : ℤ) + (M.openBoundaryPlaces_finite j).toFinset.card - 2)
    {Ω : Type} [Field Ω] [IsSepClosed Ω]
    (geom : Spec (.of Ω) ⟶ X) :
    IsSlim (Aut (FiniteEtale.fiber geom)) := by
  apply isSlim_iff_openSubgroups_center_eq_bot.mpr
  intro H
  rw [Subgroup.eq_bot_iff_forall]
  intro z hz
  obtain ⟨A, hA, geomA, _, eA, _⟩ :=
    FiniteEtale.exists_connectedCover_lift_fundamentalGroup_equiv_openSubgroup geom H
  have : IsConnected A := FiniteEtale.isConnected_of_connectedSpace_left A
  have : IsIntegral A.left := isIntegral_left_of_isConnected_finiteEtale A
  have : IsNormalIntegral A.left := isNormalIntegral_left_of_isConnected_finiteEtale A
  have : IsLocallyNoetherian A.left := isLocallyNoetherian_left_finiteEtale A
  have : IsIntegral ((Functor.id Scheme).obj A.left) :=
    inferInstanceAs (IsIntegral A.left)
  have : IsIntegral ((Functor.fromPUnit X).obj A.right) :=
    inferInstanceAs (IsIntegral X)
  have : IsFiniteEtale A.hom := A.prop
  have : CompactSpace A.left :=
    QuasiCompact.compactSpace_of_compactSpace (X := A.left) (Y := X) A.hom
  have : Surjective A.hom := IsFiniteEtale.surjective A.hom
  let cA : A.left ⟶ Spec (.of K) := A.hom ≫ j ≫ M.toBase
  let : Algebra K A.left.functionField := (baseToFunctionField cA).toAlgebra
  obtain ⟨N, d, k, hk, hd, hfinite, hsquare, hb, hn⟩ :=
    exists_hyperbolic_open_cover_model M j A hhyperbolic
  have : IsOpenImmersion k := hk
  have : IsFinite d := hfinite
  have : IsProper N.toBase := N.isProper
  have : QuasiSeparatedSpace N.C :=
    quasiSeparatedSpace_of_quasiSeparated N.toBase
  have : QuasiCompact k := inferInstance
  have : QuasiSeparated k := inferInstance
  have hsurj : Function.Surjective d :=
    surjective_finite_extension_of_open_square j A.hom A.hom.surjective k d hsquare
  have hNboundary :=
    openBoundary_nonempty_of_finite_square M N d hd hsurj j k hb hboundary
  have he : eA.symm z = 1 :=
    Cohomology.fundamentalGroup_eq_one_of_finiteH1_deck_faithful geomA
      (fun B _ xi σ hσ =>
        open_deck_eq_one_of_all_finiteH1_trivial N k hNboundary hn B xi σ hσ)
      (eA.symm z) (by
        intro a
        have hcomm : z * eA a = eA a * z :=
          (Subgroup.mem_center_iff.mp hz (eA a)).symm
        have hmap := congrArg eA.symm hcomm
        change eA.symm z * a = a * eA.symm z
        simpa only [map_mul, eA.symm_apply_apply] using hmap)
  exact eA.symm.injective (he.trans (map_one eA.symm).symm)

end AnabelianGeometry
