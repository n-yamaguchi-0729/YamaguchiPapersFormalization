/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Cohomology.TorsionH1Comparison
import EtaleFundamentalGroups.GaloisCategories.FiberIso
import ProCGroups.Abelian.TopologicalAbelianization
import ProCGroups.Abelian.ProfiniteBidual
import ProCGroups.ProC.Quotients.ClosedNormal
import ProCGroups.Topologies.ContinuousMulEquiv
import Mathlib.Algebra.Group.Equiv.TypeTags

/-!
# The abelian étale fundamental group as a cohomological dual

For a connected scheme and a geometric point, the actual topological
abelianization is the Pontryagin dual of the discrete direct limit of its
ordinary finite-coefficient étale H¹ groups. Both maps and both continuity
statements are proved, and the isomorphism is the monodromy evaluation pairing.

This retains finite torsion. No smoothness, properness, noetherianity or
characteristic hypothesis is needed. Identifying the displayed direct limit
with derived cohomology of an infinite constant sheaf is a separate issue.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory EtaleCohomology.Classical

universe u

namespace EtaleFundamentalGroups.Cohomology

local instance torsionH1Topology (X : Scheme.{u}) :
    TopologicalSpace (Multiplicative (finiteTorsionCohomology X 1)) := ⊥
local instance torsionH1Discrete (X : Scheme.{u}) :
    DiscreteTopology (Multiplicative (finiteTorsionCohomology X 1)) := ⟨rfl⟩

variable {X : Scheme.{u}} [ConnectedSpace X]
  {Ω : Type u} [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ X)

private abbrev P := TopologicalAbelianization (Aut (FiniteEtale.fiber ξ))

private instance : TotallyDisconnectedSpace (P ξ) :=
  ProCGroups.totallyDisconnectedSpace_quotient_closedNormal
    (Subgroup.closedCommutator (Aut (FiniteEtale.fiber ξ)))
    (Subgroup.isClosed_closedCommutator _)

/-- The finite-coefficient H¹ character comparison respects the actual discrete
topology on cohomology and the compact-open topology on the character group. -/
def finiteTorsionH1ContinuousCharacterEquiv :
    Multiplicative (finiteTorsionCohomology X 1) ≃ₜ* PontryaginDual (P ξ) where
  toMulEquiv := AddEquiv.toMultiplicativeLeft (finiteTorsionH1CharacterEquiv ξ)
  continuous_toFun := continuous_of_discreteTopology
  continuous_invFun := continuous_of_discreteTopology

/-- The full topological abelianization of the étale fundamental group is the
actual Pontryagin dual of the finite-coefficient direct-limit étale H¹ group. -/
def abelianizationFiniteTorsionH1DualEquiv :
    TopologicalAbelianization (Aut (FiniteEtale.fiber ξ)) ≃ₜ*
      PontryaginDual (Multiplicative (finiteTorsionCohomology X 1)) := by
  let e := finiteTorsionH1ContinuousCharacterEquiv ξ
  let f := PontryaginDual.map (ContinuousMonoidHom.toContinuousMonoidHom e)
  let g := PontryaginDual.map (ContinuousMonoidHom.toContinuousMonoidHom e.symm)
  let d := ProCGroups.ContinuousMulEquiv.ofHomInv f g
    (fun χ => PontryaginDual.ext fun a => congrArg χ (e.apply_symm_apply a))
    (fun χ => PontryaginDual.ext fun a => congrArg χ (e.symm_apply_apply a))
  exact ProCGroups.Duality.profiniteBidualEquiv.trans d

/-- The duality isomorphism evaluates a cohomology class by its actual
finite-coefficient monodromy character on the abelianized fundamental group. -/
theorem abelianizationFiniteTorsionH1DualEquiv_apply
    (g : TopologicalAbelianization (Aut (FiniteEtale.fiber ξ)))
    (a : finiteTorsionCohomology X 1) :
    abelianizationFiniteTorsionH1DualEquiv ξ g (Multiplicative.ofAdd a) =
      (finiteTorsionH1Character ξ a).toMul g := rfl


/-- The actual Pontryagin duality is independent of the geometric base point,
with transport on the topological abelianization induced by the given
isomorphism of fiber functors. Scheme-pullback equivariance is a separate
comparison; it is not an assumption of this theorem. -/
theorem abelianizationFiniteTorsionH1DualEquiv_basePoint
    {Ω' : Type u} [Field Ω'] [IsSepClosed Ω'] (η : Spec (.of Ω') ⟶ X)
    (τ : FiniteEtale.fiber ξ ≅ FiniteEtale.fiber η)
    (g : TopologicalAbelianization (Aut (FiniteEtale.fiber ξ))) :
    abelianizationFiniteTorsionH1DualEquiv η
        (ProCGroups.Abelian.TopologicalAbelianization.map
          (ContinuousMonoidHom.toContinuousMonoidHom
            (PreGaloisCategory.continuousConjAut τ)) g) =
      abelianizationFiniteTorsionH1DualEquiv ξ g := by
  apply PontryaginDual.ext
  intro a
  change (finiteTorsionH1Character η a.toAdd).toMul
      (ProCGroups.Abelian.TopologicalAbelianization.map
        (ContinuousMonoidHom.toContinuousMonoidHom
          (PreGaloisCategory.continuousConjAut τ)) g) =
    (finiteTorsionH1Character ξ a.toAdd).toMul g
  exact congrArg (fun χ : PontryaginDual
    (TopologicalAbelianization (Aut (FiniteEtale.fiber ξ))) => χ g)
    (finiteTorsionH1Character_basePoint ξ η τ a.toAdd)


/-- Actual derived inverse image on finite-torsion H¹, with its discrete topology. -/
def finiteTorsionH1PullbackHom {Y : Scheme.{u}} (f : X ⟶ Y) :
    Multiplicative (finiteTorsionCohomology Y 1) →ₜ*
      Multiplicative (finiteTorsionCohomology X 1) where
  toMonoidHom := (finiteTorsionCohomologyPullback f 1).toMultiplicative
  continuous_toFun := continuous_of_discreteTopology

/-- The established Pontryagin duality intertwines actual geometric inverse
image and the induced map of actual topological abelianizations. In particular,
the comparison applies to actual deck automorphisms and is not an assumed
equivariance field. -/
theorem abelianizationFiniteTorsionH1DualEquiv_schemePullback
    {Y : Scheme.{u}} [ConnectedSpace Y] (f : X ⟶ Y)
    (g : TopologicalAbelianization (Aut (FiniteEtale.fiber ξ))) :
    abelianizationFiniteTorsionH1DualEquiv (ξ ≫ f)
        (ProCGroups.Abelian.TopologicalAbelianization.map
          (FiniteEtale.fundamentalGroupHom f ξ) g) =
      (abelianizationFiniteTorsionH1DualEquiv ξ g).comp
        (finiteTorsionH1PullbackHom f) := by
  apply PontryaginDual.ext
  intro a
  change (finiteTorsionH1Character (ξ ≫ f) a.toAdd).toMul
      (ProCGroups.Abelian.TopologicalAbelianization.map
        (FiniteEtale.fundamentalGroupHom f ξ) g) =
    (finiteTorsionH1Character ξ (finiteTorsionCohomologyPullback f 1 a.toAdd)).toMul g
  exact (congrArg
    (fun χ : PontryaginDual (TopologicalAbelianization (Aut (FiniteEtale.fiber ξ))) => χ g)
    (finiteTorsionH1Character_schemePullback ξ f a.toAdd)).symm

end EtaleFundamentalGroups.Cohomology
