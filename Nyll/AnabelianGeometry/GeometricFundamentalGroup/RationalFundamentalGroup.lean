/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.GeometricFundamentalGroup.RationalConnectedEtale
import Nyll.EtaleFundamentalGroups.FiniteEtale.Connected
import Nyll.EtaleFundamentalGroups.Pi1.FiniteEtale.GaloisCategory
import Mathlib.CategoryTheory.Galois.Prorepresentability

/-!
# The fundamental group of a proper rational curve

The actual etale fundamental group of a proper rational curve model over an
algebraically closed field of characteristic zero is trivial at every geometric
point. Connected finite etale covers are isomorphisms by the geometric argument.
Their geometric fibres are therefore singletons. The proved reconstruction of
fibre-functor endomorphisms from pointed Galois objects then forces every
automorphism of the actual fibre functor to agree with every other one.
-/

noncomputable section

open CategoryTheory CategoryTheory.PreGaloisCategory
open AlgebraicGeometry AlgebraicGeometry.FiniteEtale AlgebraicCurve

namespace AnabelianGeometry.GeometricFundamentalGroup

/-- A connected finite etale cover of a proper rational curve has singleton
geometric fibre in characteristic zero. -/
theorem subsingleton_fiber_of_connected_rational
    {K : Type} [Field K] [IsAlgClosed K] [CharZero K]
    (M : CurveModel K (RatFunc K)) {Ω : Type} [Field Ω]
    (ξ : Spec (CommRingCat.of Ω) ⟶ M.C)
    (Y : FiniteEtale M.C) [ConnectedSpace Y.left] :
    Subsingleton ((fiber ξ).obj Y) := by
  have finiteEtale : IsFiniteEtale Y.hom := Y.prop
  have finite : IsFinite Y.hom := finiteEtale.toIsFinite
  have etale : Etale Y.hom := finiteEtale.toEtale
  have connectedSource : ConnectedSpace ((𝟭 Scheme).obj Y.left) := by
    change ConnectedSpace Y.left
    infer_instance
  have iso : IsIso Y.hom := isIso_of_connected_finite_etale_rational M Y.hom
  let e : (Limits.pullback Y.hom ξ : Scheme) ≃ₜ Spec (CommRingCat.of Ω) :=
    (asIso (Limits.pullback.snd Y.hom ξ)).schemeIsoToHomeo
  change Subsingleton (Limits.pullback Y.hom ξ : Scheme)
  exact ⟨fun x y => e.injective (Subsingleton.elim (e x) (e y))⟩

/-- The actual geometric etale fundamental group of a proper rational curve
over an algebraically closed field of characteristic zero is trivial. -/
theorem subsingleton_fundamentalGroup_rational
    {K : Type} [Field K] [IsAlgClosed K] [CharZero K]
    (M : CurveModel K (RatFunc K)) {Ω : Type} [Field Ω] [IsSepClosed Ω]
    (ξ : Spec (CommRingCat.of Ω) ⟶ M.C) : Subsingleton π₁ᵉᵗ(ξ) := by
  constructor
  intro σ τ
  apply Iso.ext
  apply (endEquivAutGalois (fiber ξ)).injective
  apply AutGalois.ext
  intro A
  have connected : ConnectedSpace A.obj.left := connectedSpace_left_of_isConnected A.obj
  have singleton : Subsingleton ((fiber ξ).obj A.obj) :=
    subsingleton_fiber_of_connected_rational M ξ A.obj
  apply evaluation_aut_injective_of_isConnected (fiber ξ) A.obj A.pt
  exact Subsingleton.elim _ _

end AnabelianGeometry.GeometricFundamentalGroup
