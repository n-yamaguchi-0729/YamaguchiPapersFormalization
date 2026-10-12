/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Albanese.GenusOneAlbanese
import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import Nyll.AlgebraicCurves.Geometry.Picard.RelativeGroupLaw
import Nyll.EtaleFundamentalGroups.GeometricFiber.AbelianTateComparison
import Nyll.EtaleFundamentalGroups.GeometricFiber.PullbackEquivalence
import Nyll.ProCGroups.Abelian.FullTateModule
import Nyll.SchemeTheory.Pi1.Affine.Over
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.Topology.JacobsonSpace

/-!
# The full Tate module comparison for an arbitrary proper genus-one curve

A closed point supplies a rational basepoint internally. The actual coherent
genus comparison and Abel--Jacobi isomorphism then identify the original curve
with its constructed Albanese variety. Pullback of finite etale covers transports
the fundamental group to the actual full Tate module of its algebraic points.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry.FiniteEtale

namespace JacobianVarieties.Albanese

/-- A proper smooth integral curve of coherent genus one has fundamental group
isomorphic to the actual full Tate module of its constructed Albanese variety.
No rational basepoint, curve model, group law, or comparison is assumed. -/
theorem exists_fullTate_equiv_of_finrank_H1_eq_one
    {K : Type} [Field K] [IsAlgClosed K] [CharZero K]
    (X : Scheme) [IsIntegral X] (c : X ⟶ Spec (.of K))
    [IsProper c] [SmoothOfRelativeDimension 1 c] (V : X.TwoAffineOpenCover)
    (hg : Module.finrank K (V.structureSheafSections c).H1 = 1) :
    ∃ (A : Scheme) (f : A ⟶ Spec (.of K)) (G : RelativeGroupLaw K f)
      (hc : G.IsCommutative), Smooth f ∧ IsProper f ∧ GeometricallyConnected f ∧
      Nonempty (X ≅ A) ∧
      ∀ (Ω : Type) [Field Ω] [IsSepClosed Ω] (xi : Spec (.of Ω) ⟶ X),
        Nonempty (π₁ᵉᵗ(xi) ≃ₜ* Multiplicative (ProCGroups.FullTateModule (G.AlgPoints hc K))) := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace c
  obtain ⟨x, _, hx⟩ := nonempty_inter_closedPoints
    (Set.univ_nonempty : (Set.univ : Set X).Nonempty) isOpen_univ.isLocallyClosed
  let ε : SchemeHomOver (𝟙 (Spec (.of K))) c := (pointEquivClosedPoint c).symm ⟨x, hx⟩
  obtain ⟨A, f, G, hc, aj, hsm, hpr, hgc, hiso, _, _⟩ :=
    exists_albanese_isIso_of_finrank_H1_eq_one X c V hg ε
  have : Smooth f := hsm
  have : IsProper f := hpr
  have : GeometricallyConnected f := hgc
  have : ConnectedSpace A := GeometricallyConnected.connectedSpace f f.isOpenMap
  have : IsIso aj.1 := hiso
  refine ⟨A, f, G, hc, hsm, hpr, hgc, ⟨asIso aj.1⟩, ?_⟩
  intro Ω _ _ xi
  let E : FiniteEtale A ≌ FiniteEtale X :=
    MorphismProperty.Over.pullbackIso (@IsFiniteEtale : MorphismProperty Scheme) ⊤
      (asIso aj.1).symm
  have : (pullback aj.1).IsEquivalence := E.isEquivalence_functor
  exact ⟨(fundamentalGroupEquivOfPullbackEquivalence aj.1 xi).trans
    (G.fundamentalGroupEquivFullTateAt hc (xi ≫ aj.1))⟩

end JacobianVarieties.Albanese
