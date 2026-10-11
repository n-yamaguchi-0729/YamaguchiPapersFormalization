/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.GeometricFiber.AbelianTateFamilies
import Nyll.EtaleFundamentalGroups.GeometricFiber.AbelianMultiplicationMonodromyGroup
import Nyll.EtaleFundamentalGroups.GeometricFiber.BasePoint
import Nyll.EtaleFundamentalGroups.GeometricFiber.FundamentalGroup
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.CategoryTheory.Galois.Topology
import Nyll.ProCGroups.Abelian.FullTateModule
import Nyll.ProCGroups.Topologies.ContinuousMulEquiv

/-!
# The actual full Tate module and the fundamental group of an abelian variety

Unit monodromy on the actual multiplication covers identifies the fundamental
group with compatible families of actual torsion points. The group law is
proved using deck translations, and the bijection and topology come from
cofinality of the multiplication covers and compactness.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FiniteEtale

namespace GoodReductionJacobian.RelativeGroupLaw

variable {K : Type} [Field K] [IsAlgClosed K] [CharZero K]
  {A : Scheme} {f : A ⟶ Spec (.of K)}
  [IsProper f] [Smooth f]
  (G : RelativeGroupLaw K f) (hc : G.IsCommutative)

/-- The actual compatible torsion family of unit monodromy, as a continuous
group homomorphism. -/
def fundamentalGroupToFullTateHom :
    π₁ᵉᵗ((G.one (𝟙 (Spec (.of K)))).1) →ₜ*
      Multiplicative (ProCGroups.FullTateModule (G.AlgPoints hc K)) where
  toFun g := Multiplicative.ofAdd (G.fundamentalGroupToFullTate hc g)
  map_one' := by
    apply congrArg Multiplicative.ofAdd
    apply Subtype.ext
    funext n
    exact G.multiplicationMonodromy_one hc n
  map_mul' g h := by
    apply congrArg Multiplicative.ofAdd
    apply Subtype.ext
    funext n
    exact G.multiplicationMonodromy_mul hc n g h
  continuous_toFun := G.fundamentalGroupToFullTate_continuous hc

/-- The etale fundamental group of a proper smooth geometrically connected
commutative group over an algebraically closed field of characteristic zero
is its actual full Tate module, with the inverse-limit topology. -/
def fundamentalGroupEquivFullTate [GeometricallyConnected f] :
    π₁ᵉᵗ((G.one (𝟙 (Spec (.of K)))).1) ≃ₜ*
      Multiplicative (ProCGroups.FullTateModule (G.AlgPoints hc K)) :=
  ProCGroups.ContinuousMulEquiv.ofBijectiveCompactToT2
    (G.fundamentalGroupToFullTateHom hc).toMonoidHom
    (G.fundamentalGroupToFullTateHom hc).continuous_toFun
    ⟨G.fundamentalGroupToFullTate_injective hc,
      G.fundamentalGroupToFullTate_surjective hc⟩

/-- At every positive integer, the comparison is the actual action on the
unit of the multiplication-cover fibre, identified with its torsion point. -/
theorem fundamentalGroupEquivFullTate_projection [GeometricallyConnected f]
    (g : π₁ᵉᵗ((G.one (𝟙 (Spec (.of K)))).1)) (n : ℕ+) :
    ProCGroups.FullTateModule.projection (G.AlgPoints hc K) n
        (Multiplicative.toAdd (G.fundamentalGroupEquivFullTate hc g)) =
      G.multiplicationMonodromy hc n g := by
  rfl

/-- At any separably closed geometric basepoint, the fundamental group is
topologically isomorphic to the actual full Tate module of the original
group of algebraic points. The basepoint comparison is chosen internally. -/
def fundamentalGroupEquivFullTateAt [GeometricallyConnected f]
    {Ω : Type} [Field Ω] [IsSepClosed Ω] (xi : Spec (.of Ω) ⟶ A) :
    π₁ᵉᵗ(xi) ≃ₜ* Multiplicative (ProCGroups.FullTateModule (G.AlgPoints hc K)) := by
  have : ConnectedSpace A := GeometricallyConnected.connectedSpace f f.isOpenMap
  let e : Spec (.of K) ⟶ A := (G.one (𝟙 (Spec (.of K)))).1
  let t : fiber xi ≅ fiber e := Classical.choice (nonempty_fiber_iso xi e)
  exact (fundamentalGroupIsoOfFiberIso xi e t).trans (G.fundamentalGroupEquivFullTate hc)

end GoodReductionJacobian.RelativeGroupLaw
