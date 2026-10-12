/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.GeometricFundamentalGroup.OpenCurveH1Deck
import Nyll.EtaleFundamentalGroups.GaloisCovers.OpenCoverHyperbolicity

/-! # Actual intermediate covers of a hyperbolic open curve -/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicCurve TopologicalSpace
open CategoryTheory.PreGaloisCategory EtaleFundamentalGroups
open EtaleFundamentalGroups.Cohomology

namespace AnabelianGeometry

attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

/-- The intermediate curve inherits its geometry from the original open
curve. A nonidentity deck transformation over it forces strict H¹ growth. -/
theorem not_surjective_open_finiteH1Pullback_intermediate
    {K F : Type} [Field K] [IsAlgClosed K] [CharZero K]
    [Field F] [Algebra K F]
    (M : CurveModel K F) {X : Scheme}
    [IsIntegral X] [IsNormalIntegral X] [IsLocallyNoetherian X] [CompactSpace X]
    (j : X ⟶ M.C) [IsOpenImmersion j] [QuasiCompact j] [QuasiSeparated j]
    (hboundary : (M.openBoundaryPlaces j).Nonempty)
    (hhyperbolic : 0 <
      2 * (genusFF K F : ℤ) + (M.openBoundaryPlaces_finite j).toFinset.card - 2)
    (A B : FiniteEtale X) [IsConnected A] [IsConnected B] [ConnectedSpace B.left]
    (f : A ⟶ B) [CategoryTheory.PreGaloisCategory.IsGalois (FiniteEtale.mk f.left)]
    (σ : Aut (FiniteEtale.mk f.left)) (hσ : σ ≠ 1)
    (n : ℕ+) (hn : 1 < (n : ℕ))
    {Ω : Type} [Field Ω] [IsSepClosed Ω] (geom : Spec (.of Ω) ⟶ A.left) :
    ¬ Function.Surjective (constantCohomologyPullback f.left
      (AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))) 1) := by
  have : IsIntegral B.left := isIntegral_left_of_isConnected_finiteEtale B
  have : IsNormalIntegral B.left := isNormalIntegral_left_of_isConnected_finiteEtale B
  have : IsLocallyNoetherian B.left := isLocallyNoetherian_left_finiteEtale B
  have : IsIntegral ((Functor.id Scheme).obj B.left) :=
    inferInstanceAs (IsIntegral B.left)
  have : IsIntegral ((Functor.fromPUnit X).obj B.right) :=
    inferInstanceAs (IsIntegral X)
  have : IsFiniteEtale B.hom := B.prop
  have : CompactSpace B.left :=
    QuasiCompact.compactSpace_of_compactSpace (X := B.left) (Y := X) B.hom
  have : Surjective B.hom := IsFiniteEtale.surjective B.hom
  let cB : B.left ⟶ Spec (.of K) := B.hom ≫ j ≫ M.toBase
  let : Algebra K B.left.functionField := (baseToFunctionField cB).toAlgebra
  obtain ⟨P, d, k, hk, hd, hfinite, hsquare, hb, hp⟩ :=
    exists_hyperbolic_open_cover_model M j B hhyperbolic
  have : IsOpenImmersion k := hk
  have : IsFinite d := hfinite
  have hsurj : Function.Surjective d :=
    surjective_finite_extension_of_open_square j B.hom B.hom.surjective k d hsquare
  have hPboundary :=
    openBoundary_nonempty_of_finite_square M P d hd hsurj j k hb hboundary
  have : IsProper P.toBase := P.isProper
  have : QuasiSeparatedSpace P.C :=
    quasiSeparatedSpace_of_quasiSeparated P.toBase
  have : QuasiCompact k := inferInstance
  have : QuasiSeparated k := inferInstance
  exact not_surjective_open_finiteH1Pullback P k hPboundary hp
    (FiniteEtale.mk f.left) σ hσ n hn geom

end AnabelianGeometry
