/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.GeometricFiber.AbelianMultiplicationMonodromy
import Nyll.EtaleFundamentalGroups.GeometricFiber.AbelianMultiplicationCover
import Nyll.EtaleFundamentalGroups.GeometricFiber.AbelianMultiplicationTransitions
import Nyll.EtaleFundamentalGroups.GeometricFiber.FundamentalGroup
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.CategoryTheory.Galois.Topology
import Nyll.ProCGroups.Abelian.FullTateModule

/-!
# Actual compatible torsion families from the fundamental group

The maps of multiplication covers give compatibility of monodromy at every
positive torsion level. Compactness then realizes every compatible family:
finitely many prescribed coordinates are realized at the product of their
indices. Separation by multiplication covers gives injectivity.
-/

noncomputable section

open CategoryTheory CategoryTheory.PreGaloisCategory
open AlgebraicGeometry AlgebraicGeometry.FiniteEtale
open scoped FintypeCatDiscrete BigOperators

namespace GoodReductionJacobian.RelativeGroupLaw

variable {K : Type} [Field K] [IsAlgClosed K] [CharZero K]
  {A : Scheme} {f : A ⟶ Spec (.of K)}
  [IsProper f] [Smooth f]
  (G : RelativeGroupLaw K f) (hc : G.IsCommutative)

/-- The actual multiplication transition preserves the distinguished unit fibre point. -/
theorem multiplicationCoverTransition_unit (n m : ℕ+) :
    (fiber (G.one (𝟙 (Spec (.of K)))).1).map (G.multiplicationCoverTransition hc n m)
      (G.multiplicationCoverUnit hc (n * m)) = G.multiplicationCoverUnit hc n := by
  apply (G.multiplicationCoverFiberEquivTorsion hc n).injective
  rw [G.multiplicationCoverFiberEquivTorsion_transition]
  simp only [multiplicationCoverUnit, Equiv.apply_symm_apply, map_zero]

/-- Monodromy is compatible with the actual full Tate transition, without
choosing independent identifications of the torsion levels. -/
theorem multiplicationMonodromy_compatible (n m : ℕ+)
    (g : π₁ᵉᵗ((G.one (𝟙 (Spec (.of K)))).1)) :
    ProCGroups.torsionTransition (G.AlgPoints hc K) n m
      (G.multiplicationMonodromy hc (n * m) g) = G.multiplicationMonodromy hc n g := by
  change ProCGroups.torsionTransition (G.AlgPoints hc K) n m
    (G.multiplicationCoverFiberEquivTorsion hc (n * m)
      (g • G.multiplicationCoverUnit hc (n * m))) =
    G.multiplicationCoverFiberEquivTorsion hc n (g • G.multiplicationCoverUnit hc n)
  rw [← G.multiplicationCoverFiberEquivTorsion_transition, ← mulAction_naturality,
    G.multiplicationCoverTransition_unit]

/-- The actual compatible family of torsion points obtained by unit monodromy. -/
def fundamentalGroupToFullTate
    (g : π₁ᵉᵗ((G.one (𝟙 (Spec (.of K)))).1)) :
    ProCGroups.FullTateModule (G.AlgPoints hc K) :=
  ⟨fun n => G.multiplicationMonodromy hc n g,
    fun n m => G.multiplicationMonodromy_compatible hc n m g⟩

/-- The constructed compatible-family map separates fundamental-group elements. -/
theorem fundamentalGroupToFullTate_injective [GeometricallyConnected f] :
    Function.Injective (G.fundamentalGroupToFullTate hc) := by
  intro g h heq
  apply G.fundamentalGroup_ext_of_multiplicationMonodromy hc g h
  intro n
  exact congrArg (ProCGroups.FullTateModule.projection (G.AlgPoints hc K) n) heq

local instance (n : ℕ+) : TopologicalSpace (ProCGroups.torsionLevel (G.AlgPoints hc K) n) :=
  ProCGroups.FullTateModule.torsionLevelTopology (G.AlgPoints hc K) n

local instance (n : ℕ+) : DiscreteTopology (ProCGroups.torsionLevel (G.AlgPoints hc K) n) :=
  ⟨rfl⟩

/-- The compatible-family map is continuous in the actual full Tate topology. -/
theorem fundamentalGroupToFullTate_continuous :
    Continuous (G.fundamentalGroupToFullTate hc) := by
  exact (continuous_pi (fun n => G.multiplicationMonodromy_continuous hc n)).subtype_mk
    (fun g n m => G.multiplicationMonodromy_compatible hc n m g)

/-- Compactness realizes every actual compatible torsion family simultaneously. -/
theorem fundamentalGroupToFullTate_surjective [GeometricallyConnected f] :
    Function.Surjective (G.fundamentalGroupToFullTate hc) := by
  classical
  have : ConnectedSpace A := GeometricallyConnected.connectedSpace f f.isOpenMap
  intro x
  let P := π₁ᵉᵗ((G.one (𝟙 (Spec (.of K)))).1)
  let Z : ℕ+ → Set P := fun n =>
    {g | G.multiplicationMonodromy hc n g = x.1 n}
  have hclosed : ∀ n, IsClosed (Z n) := fun n =>
    isClosed_eq (G.multiplicationMonodromy_continuous hc n) continuous_const
  have hfinite : ∀ s : Finset ℕ+, (⋂ n ∈ s, Z n).Nonempty := by
    intro s
    let N : ℕ+ := ∏ n ∈ s, n
    obtain ⟨g, hg⟩ := G.multiplicationMonodromy_surjective hc N (x.1 N)
    refine ⟨g, Set.mem_iInter.mpr fun n => Set.mem_iInter.mpr fun hn => ?_⟩
    obtain ⟨m, hm⟩ := Finset.dvd_prod_of_mem (fun i : ℕ+ => i) hn
    change G.multiplicationMonodromy hc n g = x.1 n
    have hN : N = n * m := hm
    calc
      G.multiplicationMonodromy hc n g =
          ProCGroups.torsionTransition (G.AlgPoints hc K) n m
            (G.multiplicationMonodromy hc (n * m) g) :=
        (G.multiplicationMonodromy_compatible hc n m g).symm
      _ = ProCGroups.torsionTransition (G.AlgPoints hc K) n m (x.1 (n * m)) := by
        have hi : G.multiplicationMonodromy hc (n * m) g = x.1 (n * m) := by
          rw [← hN]
          exact hg
        exact congrArg (ProCGroups.torsionTransition (G.AlgPoints hc K) n m) hi
      _ = x.1 n := x.2 n m
  obtain ⟨g, hg⟩ := CompactSpace.iInter_nonempty hclosed hfinite
  refine ⟨g, ?_⟩
  apply Subtype.ext
  funext n
  exact Set.mem_iInter.mp hg n

end GoodReductionJacobian.RelativeGroupLaw
