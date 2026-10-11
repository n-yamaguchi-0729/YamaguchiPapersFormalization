/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.FiniteEtale.HenselianPair
import EtaleFundamentalGroups.GeometricFiber.BasePoint
import EtaleFundamentalGroups.GeometricFiber.FieldFunctoriality
import EtaleFundamentalGroups.GeometricFiber.PullbackEquivalence
import EtaleFundamentalGroups.StrictHenselian.GeometricStalkHenselian
import EtaleFundamentalGroups.StrictHenselian.GeometricStalkResidue

/-!
# The fundamental group of an actual strictly Henselian spectrum

Henselian reduction identifies finite etale covers with those of the residue
field. When this field is separably closed its Galois group is trivial.
Base-point comparison gives the result at every geometric point, including
points over the fraction field. The geometric etale stalk constructed as a
colimit satisfies all these hypotheses internally.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory AlgebraicGeometry.FiniteEtale

namespace EtaleFundamentalGroups.StrictHenselian

universe u

/-- Every geometric fundamental group of a strictly Henselian local ring is
trivial. No finiteness or Noetherian hypothesis on the ring is needed. -/
theorem subsingleton_fundamentalGroup_of_strictHenselian
    (R : Type u) [CommRing R] [HenselianLocalRing R]
    [IsSepClosed (IsLocalRing.ResidueField R)]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (s : Spec (.of Ω) ⟶ Spec (.of R)) : Subsingleton π₁ᵉᵗ(s) := by
  let : PreconnectedSpace (Spec (.of R)) := by
    refine ⟨?_⟩
    intro U V hU hV hcover hneU hneV
    rcases hcover (Set.mem_univ (IsLocalRing.closedPoint R)) with h | h
    · obtain ⟨v, _, hv⟩ := hneV
      exact ⟨v, trivial, (IsLocalRing.specializes_closedPoint v).mem_open hU h, hv⟩
    · obtain ⟨u, _, hu⟩ := hneU
      exact ⟨u, trivial, hu, (IsLocalRing.specializes_closedPoint u).mem_open hV h⟩
  let : ConnectedSpace (Spec (.of R)) := ⟨⟨IsLocalRing.closedPoint R⟩⟩
  let k := IsLocalRing.ResidueField R
  let r : Spec (.of k) ⟶ Spec (.of R) :=
    Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))
  let : MorphismProperty.IsStableUnderBaseChange
      ((@IsFinite : MorphismProperty Scheme.{u}) ⊓ (@Etale : MorphismProperty Scheme.{u})) :=
    MorphismProperty.IsStableUnderBaseChange.inf
  let : (pullback r).IsEquivalence := by
    have htransport (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
        (hP : P = (@IsFiniteEtale : MorphismProperty Scheme.{u}))
        (h : (MorphismProperty.Over.pullback P ⊤ r).IsEquivalence) :
        (pullback r).IsEquivalence := by
      subst P
      exact h
    exact htransport _ IsFiniteEtale.eq_inf.symm
      (pullback_isEquivalence_of_henselian (IsLocalRing.maximalIdeal R))
  let e : π₁ᵉᵗ(ξ k k) ≃ₜ* π₁ᵉᵗ(ξ k k ≫ r) :=
    fundamentalGroupEquivOfPullbackEquivalence r (ξ k k)
  let : Subsingleton π₁ᵉᵗ(ξ k k) :=
    (absoluteGaloisToFiberAutMulEquiv k k inferInstance).symm.injective.subsingleton
  let : Subsingleton π₁ᵉᵗ(ξ k k ≫ r) := e.symm.injective.subsingleton
  obtain ⟨t⟩ := nonempty_fiber_iso s (ξ k k ≫ r)
  exact (fundamentalGroupIsoOfFiberIso s (ξ k k ≫ r) t).injective.subsingleton

/-- The actual geometric etale stalk has trivial fundamental group at every
geometric point of its spectrum. -/
theorem subsingleton_fundamentalGroup_geometricStalk
    {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (s : Spec (.of Ω) ⟶ X)
    {Ω' : Type u} [Field Ω'] [IsSepClosed Ω']
    (t : Spec (.of Ω') ⟶ Spec (geometricStalk s)) : Subsingleton π₁ᵉᵗ(t) := by
  exact @subsingleton_fundamentalGroup_of_strictHenselian
    (geometricStalk s) inferInstance (geometricStalk_henselianLocalRing s)
    (geometricStalk_residueField_isSepClosed s) Ω' inferInstance inferInstance t

end EtaleFundamentalGroups.StrictHenselian
