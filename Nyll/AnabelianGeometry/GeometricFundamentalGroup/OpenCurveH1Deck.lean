/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Cohomology.SchemePullback
import Nyll.EtaleFundamentalGroups.GaloisCovers.OpenCoverSquareBoundary
import Nyll.EtaleFundamentalGroups.GaloisCovers.OpenCoverInvariants
import Nyll.AlgebraicCurves.Models.OpenCoverRiemannHurwitz
import Nyll.AlgebraicCurves.Models.RationalPointExistence
import Nyll.JacobianVarieties.Kummer.OpenFiniteH1Cardinality

/-!
# Non-surjective actual H¹ pullback on hyperbolic open covers

Actual compactification, interior unramifiedness and boundary
Riemann--Hurwitz force a strict increase in actual finite H¹ cardinality.
No Euler characteristic or cohomological comparison is an input assumption.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicCurve TopologicalSpace NeronModelInfra
open CategoryTheory.PreGaloisCategory EtaleFundamentalGroups
open EtaleFundamentalGroups.Cohomology

namespace AnabelianGeometry

attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

theorem not_surjective_open_finiteH1Pullback
    {K F : Type} [Field K] [IsAlgClosed K] [CharZero K]
    [Field F] [Algebra K F]
    (M : CurveModel K F) {X : Scheme}
    [IsIntegral X] [IsNormalIntegral X] [IsLocallyNoetherian X] [CompactSpace X]
    (j : X ⟶ M.C) [IsOpenImmersion j] [QuasiCompact j] [QuasiSeparated j]
    (hboundary : (M.openBoundaryPlaces j).Nonempty)
    (hhyperbolic : 0 <
      2 * (genusFF K F : ℤ) + (M.openBoundaryPlaces_finite j).toFinset.card - 2)
    (W : FiniteEtale X) [IsGalois W] (σ : Aut W) (hσ : σ ≠ 1)
    (n : ℕ+) (hn : 1 < (n : ℕ))
    {Ω : Type} [Field Ω] [IsSepClosed Ω] (geom : Spec (.of Ω) ⟶ W.left) :
    ¬ Function.Surjective (constantCohomologyPullback (X := W.left) (Y := X) W.hom
      (AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))) 1) := by
  classical
  have : IsIntegral W.left := isIntegral_left_of_isConnected_finiteEtale W
  have : IsIntegral ((Functor.id Scheme).obj W.left) :=
    inferInstanceAs (IsIntegral W.left)
  have : IsIntegral ((Functor.fromPUnit X).obj W.right) :=
    inferInstanceAs (IsIntegral X)
  have : IsFiniteEtale W.hom := W.prop
  have : CompactSpace W.left :=
    QuasiCompact.compactSpace_of_compactSpace (X := W.left) (Y := X) W.hom
  have : Surjective W.hom := IsFiniteEtale.surjective W.hom
  let cW : W.left ⟶ Spec (.of K) := W.hom ≫ j ≫ M.toBase
  let : Algebra K W.left.functionField := (baseToFunctionField cW).toAlgebra
  obtain ⟨N, d, k, hd, hfinite, hk, hsquare, hb⟩ :=
    exists_open_cover_curveModel_square_boundary M j W
  have : IsFinite d := hfinite
  have : IsOpenImmersion k := hk
  have hsurj : Function.Surjective d :=
    surjective_finite_extension_of_open_square j W.hom W.hom.surjective k d hsquare
  have : Etale (k ≫ d) := by rw [hsquare]; infer_instance
  have hNboundary := openBoundary_nonempty_of_finite_square M N d hd hsurj j k hb hboundary
  let : Fintype (M.openBoundaryPlaces j) := (M.openBoundaryPlaces_finite j).fintype
  let : Fintype (N.openBoundaryPlaces k) := (N.openBoundaryPlaces_finite k).fintype
  obtain ⟨v, hv⟩ := hboundary
  obtain ⟨w, hw⟩ := hNboundary
  have hSpos : 0 < Fintype.card (M.openBoundaryPlaces j) :=
    Fintype.card_pos_iff.mpr ⟨⟨v, hv⟩⟩
  have hTpos : 0 < Fintype.card (N.openBoundaryPlaces k) :=
    Fintype.card_pos_iff.mpr ⟨⟨w, hw⟩⟩
  have hRH := M.two_mul_genus_add_openBoundary_sub_two_eq N d hd hsurj j k hb
  rw [Set.Finite.card_toFinset, Set.Finite.card_toFinset] at hRH
  have hH := hhyperbolic
  rw [Set.Finite.card_toFinset] at hH
  have hdegree : 1 < finrankAlong K (M.finiteCurveFieldMap N d hd hsurj) := by
    rw [finrankAlong_openCover_eq_actual M N j W d hd hsurj k hsquare]
    exact one_lt_functionField_degree_of_nontrivial_galois_deck W σ hσ
  have hdZ : (1 : ℤ) < finrankAlong K (M.finiteCurveFieldMap N d hd hsurj) := by
    exact_mod_cast hdegree
  have hstrict :
      2 * (genusFF K F : ℤ) + Fintype.card (M.openBoundaryPlaces j) - 2 <
        2 * (genusFF K W.left.functionField : ℤ) +
          Fintype.card (N.openBoundaryPlaces k) - 2 := by
    nlinarith [hRH, hH, hdZ]
  have hdim :
      2 * genusFF K F + Fintype.card (M.openBoundaryPlaces j) - 1 <
        2 * genusFF K W.left.functionField + Fintype.card (N.openBoundaryPlaces k) - 1 := by
    omega
  have : IsCurveOver K F :=
    isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one M.toBase
      M.ffEquiv M.ffEquiv_algebraMap
  have : IsCurveOver K W.left.functionField :=
    isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one N.toBase
      N.ffEquiv N.ffEquiv_algebraMap
  obtain ⟨εM⟩ := M.nonempty_rationalPoint
  obtain ⟨εN⟩ := N.nonempty_rationalPoint
  have hj : DenseRange j :=
    j.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace j
  have hkdense : DenseRange k :=
    k.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace k
  have hM := M.natCard_open_finiteH1_eq_pow_genus_boundary εM j hj ⟨v, hv⟩ n
    (geom ≫ W.hom)
  have hN := N.natCard_open_finiteH1_eq_pow_genus_boundary εN k hkdense ⟨w, hw⟩ n geom
  let C := AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))
  have : Finite (Sheaf.H.{0} ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{0}).obj C) 1) :=
    Nat.finite_of_card_ne_zero (by rw [hM]; exact pow_ne_zero _ n.ne_zero)
  intro h
  have hle := Nat.card_le_card_of_surjective
    (constantCohomologyPullback (X := W.left) (Y := X) W.hom C 1) h
  dsimp only [C] at hle
  rw [hM, hN] at hle
  exact (not_lt_of_ge hle) (Nat.pow_lt_pow_right hn hdim)

end AnabelianGeometry
