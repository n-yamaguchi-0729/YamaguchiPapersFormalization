/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Cohomology.AbelianH1Duality
import EtaleFundamentalGroups.Cohomology.PointedH1Pullback
import EtaleFundamentalGroups.GeometricFiber.DeckFundamentalGroup

/-!
# Equivariance of actual abelian H¹ duality for pointed deck actions

The existing duality is reused. Its scheme naturality and base-point
naturality give equivariance for any specified pointed geometric pullback.
For a deck transformation, the actual comparison with conjugation is the
one constructed by the geometric fiber functor.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.PreGaloisCategory
open EtaleCohomology.Classical

namespace EtaleFundamentalGroups.Cohomology

local instance torsionTopology (X : Scheme.{u}) :
    TopologicalSpace (Multiplicative (finiteTorsionCohomology X 1)) := ⊥

/-- The existing duality intertwines actual inverse image with the
abelianization map from any pointed geometric fiber comparison. -/
theorem abelianizationFiniteTorsionH1DualEquiv_pointedPullback
    {X Y : Scheme.{u}} [ConnectedSpace X] [ConnectedSpace Y]
    (f : X ⟶ Y)
    {Ω Ω' : Type u} [Field Ω] [IsSepClosed Ω] [Field Ω'] [IsSepClosed Ω']
    (ξ : Spec (.of Ω) ⟶ X) (η : Spec (.of Ω') ⟶ Y)
    (t : FiniteEtale.pullback f ⋙ FiniteEtale.fiber ξ ≅ FiniteEtale.fiber η)
    (g : TopologicalAbelianization (Aut (FiniteEtale.fiber ξ))) :
    abelianizationFiniteTorsionH1DualEquiv η
      (ProCGroups.Abelian.TopologicalAbelianization.map
        (autHomOfCompIso (FiniteEtale.pullback f) t) g) =
      (abelianizationFiniteTorsionH1DualEquiv ξ g).comp
        (finiteTorsionH1PullbackHom f) := by
  let c := FiniteEtale.pullbackFiberIso f ξ
  let τ := c.symm ≪≫ t
  have ht : c ≪≫ τ = t := by
    change c ≪≫ (c.symm ≪≫ t) = t
    rw [← Iso.trans_assoc, Iso.self_symm_id, Iso.refl_trans]
  have hg : autHomOfCompIso (FiniteEtale.pullback f) t =
      (ContinuousMonoidHom.toContinuousMonoidHom (continuousConjAut τ)).comp
        (FiniteEtale.fundamentalGroupHom f ξ) := by
    apply ContinuousMonoidHom.ext
    intro a
    let b := ((Functor.whiskeringLeft _ _ FintypeCat).obj
      (FiniteEtale.pullback f)).mapAut (FiniteEtale.fiber ξ) a
    change t.conjAut b = τ.conjAut (c.conjAut b)
    exact (congrArg (fun e => e.conjAut b) ht.symm).trans
      (Iso.trans_conjAut c τ b)
  rw [hg, ProCGroups.Abelian.TopologicalAbelianization.map_comp]
  change abelianizationFiniteTorsionH1DualEquiv η
    (ProCGroups.Abelian.TopologicalAbelianization.map
      (ContinuousMonoidHom.toContinuousMonoidHom (continuousConjAut τ))
      (ProCGroups.Abelian.TopologicalAbelianization.map
        (FiniteEtale.fundamentalGroupHom f ξ) g)) = _
  rw [abelianizationFiniteTorsionH1DualEquiv_basePoint (ξ ≫ f) η τ]
  exact abelianizationFiniteTorsionH1DualEquiv_schemePullback ξ f g

/-- Equivariance for the actual pointed deck action, with no assumed
compatibility between the deck action and cohomological duality. -/
theorem abelianizationFiniteTorsionH1DualEquiv_deck
    {S : Scheme.{u}} [ConnectedSpace S]
    (A : FiniteEtale S) [ConnectedSpace A.left]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (ξ : Spec (.of Ω) ⟶ A.left)
    (σ : Aut A) (g : Aut (FiniteEtale.fiber (ξ ≫ A.hom)))
    (h : (FiniteEtale.fiber (ξ ≫ A.hom)).map σ.hom
      (FiniteEtale.liftedFiberPoint A ξ) =
        g • FiniteEtale.liftedFiberPoint A ξ)
    (a : TopologicalAbelianization (Aut (FiniteEtale.fiber ξ))) :
    abelianizationFiniteTorsionH1DualEquiv ξ
      (ProCGroups.Abelian.TopologicalAbelianization.map
        (autHomOfCompIso (FiniteEtale.pullback σ.hom.left)
          (FiniteEtale.deckPointedGeometricFiberIso A ξ σ g h)) a) =
      (abelianizationFiniteTorsionH1DualEquiv ξ a).comp
        (finiteTorsionH1PullbackHom σ.hom.left) :=
  abelianizationFiniteTorsionH1DualEquiv_pointedPullback σ.hom.left ξ ξ
    (FiniteEtale.deckPointedGeometricFiberIso A ξ σ g h) a

end EtaleFundamentalGroups.Cohomology
