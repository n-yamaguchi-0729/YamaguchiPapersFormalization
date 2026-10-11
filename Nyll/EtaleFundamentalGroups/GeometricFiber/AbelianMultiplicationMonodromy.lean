/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.GeometricFiber.AbelianMultiplicationCofinality
import Nyll.EtaleFundamentalGroups.GeometricFiber.AbelianMultiplicationCover
import Nyll.EtaleFundamentalGroups.GeometricFiber.FundamentalGroup
import Nyll.EtaleFundamentalGroups.GeometricFiber.ProperGroupScheme
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.CategoryTheory.Galois.Decomposition
import Mathlib.CategoryTheory.Galois.Prorepresentability
import Mathlib.CategoryTheory.Galois.Topology
import Nyll.ProCGroups.Abelian.FullTateModule

/-!
# Separation by actual multiplication monodromy

Evaluation at the unit of each multiplication cover gives a surjective
continuous map to its actual torsion fibre. The collection of these maps
separates the actual fundamental group: commutativity and transitivity
recover the whole fibre action from its value at the unit, and cofinality
then detects every Galois fibre.
-/

noncomputable section

open CategoryTheory CategoryTheory.PreGaloisCategory
open AlgebraicGeometry AlgebraicGeometry.FiniteEtale
open scoped FintypeCatDiscrete

namespace GoodReductionJacobian.RelativeGroupLaw

variable {K : Type} [Field K] [IsAlgClosed K] [CharZero K]
  {A : Scheme} {f : A ⟶ Spec (.of K)}
  [IsProper f] [Smooth f] [GeometricallyConnected f]
  (G : RelativeGroupLaw K f) (hc : G.IsCommutative)

/-- The unit in the actual geometric fibre of the multiplication cover. -/
def multiplicationCoverUnit (n : ℕ+) :
    (fiber (G.one (𝟙 (Spec (.of K)))).1).obj (G.multiplicationCover hc n) :=
  (G.multiplicationCoverFiberEquivTorsion hc n).symm 0

/-- Evaluation of actual monodromy at the unit, expressed in actual torsion points. -/
def multiplicationMonodromy (n : ℕ+)
    (g : π₁ᵉᵗ((G.one (𝟙 (Spec (.of K)))).1)) :
    ProCGroups.torsionLevel (G.AlgPoints hc K) n :=
  G.multiplicationCoverFiberEquivTorsion hc n (g • G.multiplicationCoverUnit hc n)

/-- Connectedness of the multiplication cover makes unit evaluation surjective. -/
theorem multiplicationMonodromy_surjective (n : ℕ+) :
    Function.Surjective (G.multiplicationMonodromy hc n) := by
  have : ConnectedSpace A := GeometricallyConnected.connectedSpace f f.isOpenMap
  have : IsConnected (G.multiplicationCover hc n) := G.isConnected_multiplicationCover hc n
  intro x
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq
    π₁ᵉᵗ((G.one (𝟙 (Spec (.of K)))).1) (G.multiplicationCoverUnit hc n)
      ((G.multiplicationCoverFiberEquivTorsion hc n).symm x)
  refine ⟨g, ?_⟩
  exact (congrArg (G.multiplicationCoverFiberEquivTorsion hc n) hg).trans
    ((G.multiplicationCoverFiberEquivTorsion hc n).apply_symm_apply x)

local instance (n : ℕ+) : TopologicalSpace (ProCGroups.torsionLevel (G.AlgPoints hc K) n) :=
  ProCGroups.FullTateModule.torsionLevelTopology (G.AlgPoints hc K) n

omit [GeometricallyConnected f] in
/-- Unit evaluation is continuous for the discrete topology on actual torsion points. -/
theorem multiplicationMonodromy_continuous (n : ℕ+) :
    Continuous (G.multiplicationMonodromy hc n) := by
  exact (continuous_of_discreteTopology :
    Continuous (G.multiplicationCoverFiberEquivTorsion hc n)).comp
      (continuous_id.smul continuous_const)

/-- All actual multiplication fibres together detect the fundamental group. -/
theorem fundamentalGroup_ext_of_multiplicationMonodromy
    (g h : π₁ᵉᵗ((G.one (𝟙 (Spec (.of K)))).1))
    (hgh : ∀ n : ℕ+, G.multiplicationMonodromy hc n g = G.multiplicationMonodromy hc n h) :
    g = h := by
  have : ConnectedSpace A := GeometricallyConnected.connectedSpace f f.isOpenMap
  let e : Spec (.of K) ⟶ A := (G.one (𝟙 (Spec (.of K)))).1
  let F := fiber e
  have heq (n : ℕ+) (x : F.obj (G.multiplicationCover hc n)) : g • x = h • x := by
    have : IsConnected (G.multiplicationCover hc n) := G.isConnected_multiplicationCover hc n
    have hunit : g • G.multiplicationCoverUnit hc n = h • G.multiplicationCoverUnit hc n :=
      (G.multiplicationCoverFiberEquivTorsion hc n).injective (hgh n)
    obtain ⟨a, rfl⟩ := MulAction.exists_smul_eq (Aut F) (G.multiplicationCoverUnit hc n) x
    rw [← mul_smul, G.fundamentalGroup_mul_comm g a, mul_smul, hunit,
      ← mul_smul, G.fundamentalGroup_mul_comm a h, mul_smul]
  apply Aut.ext
  apply natTrans_ext_of_isGalois F
  intro W hW
  obtain ⟨n, ⟨q⟩⟩ := G.exists_multiplicationCover_hom hc W
  have : IsConnected (G.multiplicationCover hc n) := G.isConnected_multiplicationCover hc n
  apply ConcreteCategory.hom_ext
  intro w
  obtain ⟨x, rfl⟩ := surjective_of_nonempty_fiber_of_isConnected F q w
  change g • F.map q x = h • F.map q x
  rw [mulAction_naturality, mulAction_naturality, heq n x]

end GoodReductionJacobian.RelativeGroupLaw
