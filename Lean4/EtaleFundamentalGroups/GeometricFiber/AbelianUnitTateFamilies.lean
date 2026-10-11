/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.GeometricFiber.AbelianUnitMonodromy
import ProCGroups.Abelian.RestrictedTateModule
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.CategoryTheory.Galois.Topology

import EtaleFundamentalGroups.GeometricFiber.AbelianUnitTorsionFiber

/-!
# Actual compatible torsion families at invertible indices

Unit monodromy gives actual compatible torsion points. Every such family is
realized by compactness: any finite set of its coordinates is realized at the
product of their indices, which remains invertible in the ground field.
-/

noncomputable section

open CategoryTheory CategoryTheory.PreGaloisCategory AlgebraicGeometry
open AlgebraicGeometry.FiniteEtale
open scoped FintypeCatDiscrete BigOperators

namespace GoodReductionJacobian.RelativeGroupLaw.UnitMultiplication

variable {K : Type} [Field K] [IsSepClosed K]
  {A : Scheme} {f : A ⟶ Spec (.of K)} [IsProper f] [Smooth f]
  (G : RelativeGroupLaw K f) (hc : G.IsCommutative)

/-- The actual multiplication transition preserves the distinguished unit fibre point. -/
theorem transition_unit (n m : unitIndices K) :
    (fiber (G.one (𝟙 (Spec (.of K)))).1).map (transition G hc n m)
      (unit G hc (n * m)) = unit G hc n := by
  apply (fiberEquivTorsion G hc n).injective
  rw [fiberEquivTorsion_transition G]
  simp only [unit, Equiv.apply_symm_apply, map_zero]

/-- Monodromy is compatible with the actual full Tate transition, without
choosing independent identifications of the torsion levels. -/
theorem monodromy_compatible (n m : unitIndices K)
    (g : π₁ᵉᵗ((G.one (𝟙 (Spec (.of K)))).1)) :
    ProCGroups.torsionTransition (G.AlgPoints hc K) n.1 m.1
      (monodromy G hc (n * m) g) = monodromy G hc n g := by
  change ProCGroups.torsionTransition (G.AlgPoints hc K) n.1 m.1
    (fiberEquivTorsion G hc (n * m)
      (g • unit G hc (n * m))) =
    fiberEquivTorsion G hc n (g • unit G hc n)
  rw [← fiberEquivTorsion_transition G, ← mulAction_naturality,
    transition_unit G]

/-- The actual compatible family of torsion points obtained by unit monodromy. -/
def toTate
    (g : π₁ᵉᵗ((G.one (𝟙 (Spec (.of K)))).1)) :
    ProCGroups.RestrictedTateModule (G.AlgPoints hc K) (unitIndices K) :=
  ⟨fun n => monodromy G hc n g,
    fun n m => monodromy_compatible G hc n m g⟩

local instance (n : ℕ+) : TopologicalSpace (ProCGroups.torsionLevel (G.AlgPoints hc K) n) :=
  ProCGroups.FullTateModule.torsionLevelTopology (G.AlgPoints hc K) n

local instance (n : ℕ+) : DiscreteTopology (ProCGroups.torsionLevel (G.AlgPoints hc K) n) :=
  ⟨rfl⟩

/-- The compatible-family map is continuous in the actual full Tate topology. -/
theorem toTate_continuous :
    Continuous (toTate G hc) := by
  exact (continuous_pi (fun n => monodromy_continuous G hc n)).subtype_mk
    (fun g n m => monodromy_compatible G hc n m g)

/-- Compactness realizes every actual compatible torsion family simultaneously. -/
theorem toTate_surjective [GeometricallyConnected f] :
    Function.Surjective (toTate G hc) := by
  classical
  have : ConnectedSpace A := GeometricallyConnected.connectedSpace f f.isOpenMap
  intro x
  let P := π₁ᵉᵗ((G.one (𝟙 (Spec (.of K)))).1)
  let Z : unitIndices K → Set P := fun n =>
    {g | monodromy G hc n g = x.1 n}
  have hclosed : ∀ n, IsClosed (Z n) := fun n =>
    isClosed_eq (monodromy_continuous G hc n) continuous_const
  have hfinite : ∀ s : Finset (unitIndices K), (⋂ n ∈ s, Z n).Nonempty := by
    intro s
    let N : unitIndices K := ∏ n ∈ s, n
    obtain ⟨g, hg⟩ := monodromy_surjective G hc N (x.1 N)
    refine ⟨g, Set.mem_iInter.mpr fun n => Set.mem_iInter.mpr fun hn => ?_⟩
    obtain ⟨m, hm⟩ := Finset.dvd_prod_of_mem (fun i : unitIndices K => i) hn
    change monodromy G hc n g = x.1 n
    have hN : N = n * m := hm
    calc
      monodromy G hc n g =
          ProCGroups.torsionTransition (G.AlgPoints hc K) n.1 m.1
            (monodromy G hc (n * m) g) :=
        (monodromy_compatible G hc n m g).symm
      _ = ProCGroups.torsionTransition (G.AlgPoints hc K) n.1 m.1 (x.1 (n * m)) := by
        have hi : monodromy G hc (n * m) g = x.1 (n * m) := by
          rw [← hN]
          exact hg
        exact congrArg (ProCGroups.torsionTransition (G.AlgPoints hc K) n.1 m.1) hi
      _ = x.1 n := x.2 n m
  obtain ⟨g, hg⟩ := CompactSpace.iInter_nonempty hclosed hfinite
  refine ⟨g, ?_⟩
  apply Subtype.ext
  funext n
  exact Set.mem_iInter.mp hg n

/-- Actual unit monodromy as a continuous homomorphism to compatible torsion families. -/
def toTateHom :
    π₁ᵉᵗ((G.one (𝟙 (Spec (.of K)))).1) →ₜ*
      Multiplicative (ProCGroups.RestrictedTateModule (G.AlgPoints hc K) (unitIndices K)) where
  toFun g := Multiplicative.ofAdd (toTate G hc g)
  map_one' := by
    apply congrArg Multiplicative.ofAdd
    apply Subtype.ext
    funext n
    exact monodromy_one G hc n
  map_mul' g h := by
    apply congrArg Multiplicative.ofAdd
    apply Subtype.ext
    funext n
    exact monodromy_mul G hc n g h
  continuous_toFun := toTate_continuous G hc

end GoodReductionJacobian.RelativeGroupLaw.UnitMultiplication
