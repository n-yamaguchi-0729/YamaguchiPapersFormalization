/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import EtaleFundamentalGroups.ContinuousActions.TopCatCompat
public import Mathlib.CategoryTheory.Action.Concrete
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.Category.FinTopCat

/-!
# Finite orbits of a discrete continuous action

This file supplies the finite-orbit construction used internally for Stacks
Project, Tag `03QR`.  Every orbit of a discrete continuous action of a compact
topological group is finite.
-/

@[expose] public section

universe u v

noncomputable section

open CategoryTheory
open scoped FintypeCatDiscrete

namespace CategoryTheory.DiscreteContAction

variable {G : Type v} [Group G] [TopologicalSpace G]

/-- A single orbit of a discrete continuous action, regarded as a finite
continuous `G`-action. -/
noncomputable def orbitContAction
    [IsTopologicalGroup G] [CompactSpace G]
    (S : DiscreteContAction TopCat.{u} G)
    (ω : MulAction.orbitRel.Quotient G
      ((forget₂ (DiscreteContAction TopCat.{u} G) TopCat).obj S)) :
    ContAction FintypeCat.{u} G := by
  letI : DiscreteTopology
      ((forget₂ (DiscreteContAction TopCat.{u} G) TopCat).obj S) := S.property
  letI : ContinuousSMul G
      ((forget₂ (DiscreteContAction TopCat.{u} G) TopCat).obj S) :=
    S.obj.property
  letI : Finite ω.orbit := by
    let U :=
      MulAction.stabilizer G
        (ω.out :
          (forget₂ (DiscreteContAction TopCat.{u} G) TopCat).obj S)
    let : Finite (G ⧸ U) :=
      Subgroup.quotient_finite_of_isOpen U
        (stabilizer_isOpen G
          (ω.out :
            (forget₂ (DiscreteContAction TopCat.{u} G) TopCat).obj S))
    let e : ω.orbit ≃ G ⧸ U :=
      (Set.equivOfEq
        (ω.orbit_eq_orbit_out Quotient.out_eq')).trans
          (MulAction.orbitEquivQuotientStabilizer G
            (ω.out :
              (forget₂ (DiscreteContAction TopCat.{u} G) TopCat).obj S))
    exact Finite.of_equiv (G ⧸ U) e.symm
  letI : Fintype ω.orbit := Fintype.ofFinite ω.orbit
  letI : TopologicalSpace ω.orbit := ⊥
  letI : DiscreteTopology ω.orbit := ⟨rfl⟩
  refine
    ⟨Action.FintypeCat.ofMulAction G (FintypeCat.of ω.orbit), ?_⟩
  change ContinuousSMul G ω.orbit
  rw [continuousSMul_iff_stabilizer_isOpen]
  intro x
  have hstabilizer :
      MulAction.stabilizer G x =
        MulAction.stabilizer G
          (x :
            (forget₂ (DiscreteContAction TopCat.{u} G) TopCat).obj S) := by
    ext g
    simp only [MulAction.mem_stabilizer_iff, Subtype.ext_iff,
      MulAction.orbitRel.Quotient.orbit.coe_smul]
  rw [hstabilizer]
  exact stabilizer_isOpen G
    (x : (forget₂ (DiscreteContAction TopCat.{u} G) TopCat).obj S)

end CategoryTheory.DiscreteContAction
