/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.FiniteEtale.Connected
import Nyll.EtaleFundamentalGroups.GaloisCovers.Basic
import Mathlib.CategoryTheory.Galois.Prorepresentability
import Mathlib.CategoryTheory.Galois.Topology
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.IndexNormal
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Instances.ZMod

/-!
# The cyclic quotient supplied by a connected double cover

The action of the fundamental group on a connected two-element fiber is
transitive. A point stabilizer therefore has index two and is normal. The
stabilizer is open for the actual fiber-functor topology, so its quotient
is discrete. Identifying this two-element quotient with the cyclic group
constructs a continuous surjection; Galoisness or a quotient map is not
an additional input.
-/

noncomputable section

open CategoryTheory

namespace CategoryTheory.PreGaloisCategory

universe u v w

/-- A connected object with two-element fiber gives a continuous cyclic
quotient of order two of the automorphism group of the fiber functor. -/
theorem exists_surjective_cyclicTwo_of_connected_fiber_card_two
    {C : Type u} [Category.{v} C] [GaloisCategory C]
    (F : C ⥤ FintypeCat.{w}) [FiberFunctor F]
    (X : C) [IsConnected X] (hcard : Nat.card (F.obj X) = 2) :
    ∃ φ : Aut F →ₜ* Multiplicative (ZMod 2), Function.Surjective φ := by
  let x : F.obj X := Classical.choice inferInstance
  let H : Subgroup (Aut F) := MulAction.stabilizer (Aut F) x
  have hindex : H.index = 2 :=
    (MulAction.index_stabilizer_of_transitive (Aut F) x).trans hcard
  have : H.Normal := Subgroup.normal_of_index_eq_two hindex
  have : DiscreteTopology (Aut F ⧸ H) :=
    QuotientGroup.discreteTopology (stabilizer_isOpen (Aut F) x)
  have hquotient : Nat.card (Aut F ⧸ H) = 2 := hindex
  have hcyclic : Nat.card (Multiplicative (ZMod 2)) = 2 := by
    change Nat.card (ZMod 2) = 2
    exact Nat.card_zmod 2
  let e : (Aut F ⧸ H) ≃* Multiplicative (ZMod 2) :=
    mulEquivOfPrimeCardEq hquotient hcyclic
  let q : Aut F →ₜ* Aut F ⧸ H :=
    { toMonoidHom := QuotientGroup.mk' H
      continuous_toFun := QuotientGroup.continuous_mk }
  let e' : (Aut F ⧸ H) →ₜ* Multiplicative (ZMod 2) :=
    { toMonoidHom := e.toMonoidHom
      continuous_toFun := continuous_of_discreteTopology }
  exact ⟨e'.comp q, e.surjective.comp (QuotientGroup.mk'_surjective H)⟩

end CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.FiniteEtale

universe u

/-- A connected finite etale cover of degree two constructs a continuous
surjection from the actual etale fundamental group to the cyclic group of
order two. Its degree is measured at the given geometric point. -/
theorem exists_surjective_cyclicTwo_of_connected_doubleCover
    {S : Scheme.{u}} [ConnectedSpace S]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (ξ : Spec (.of Ω) ⟶ S) (Y : FiniteEtale S) [ConnectedSpace Y.left]
    (hdegree : Y.hom.finrank (ξ (IsLocalRing.closedPoint Ω)) = 2) :
    ∃ φ : π₁ᵉᵗ(ξ) →ₜ* Multiplicative (ZMod 2), Function.Surjective φ := by
  have : PreGaloisCategory.IsConnected Y := isConnected_of_connectedSpace_left Y
  exact PreGaloisCategory.exists_surjective_cyclicTwo_of_connected_fiber_card_two
    (fiber ξ) Y ((natCard_fiber_eq_finrank ξ Y).trans hdegree)

end AlgebraicGeometry.FiniteEtale
