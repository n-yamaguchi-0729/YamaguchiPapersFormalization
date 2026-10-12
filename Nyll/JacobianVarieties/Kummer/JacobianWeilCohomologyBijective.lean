/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Kummer.JacobianWeilCohomologyInjective
import Nyll.JacobianVarieties.Pic0.Pic0_torsion_bijective_of_injective
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Nyll.EtaleFundamentalGroups.GeometricFiber.AbelianMultiplicationCharacters
import Nyll.JacobianVarieties.WeilPairing.Divisorial
import Nyll.JacobianVarieties.Autoduality.Cohomology
import Nyll.EtaleFundamentalGroups.GeometricFiber.AbelianMultiplicationMonodromy
import Nyll.EtaleFundamentalGroups.Cohomology.FiniteH1Comparison
import Mathlib.RingTheory.RootsOfUnity.Basic

/-!
# Every actual finite H¹ class on the Jacobian is a Weil class

Finite-exponent characters of the actual fundamental group factor through
the corresponding multiplication cover. Geometric nondegeneracy and finite
torsion duality then give all characters, not only an injective family.
The separate Abel--Jacobi pullback comparison is not asserted here.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicCurve NeronModelInfra GoodReductionJacobian
open EtaleFundamentalGroups.Cohomology

namespace JacobianVarieties.Kummer

/-- The actual Weil cohomology classes exhaust finite-coefficient derived H¹,
using their constructed character formula and actual multiplication covers. -/
theorem jacobian_weil_cohomology_bijective
    {K F : Type} [Field K] [IsAlgClosed K] [CharZero K]
    [Field F] [Algebra K F] [HasPrincipalDivisors K F]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    {J : Scheme} {b : J ⟶ Spec (.of K)}
    [Smooth b] [IsProper b] [GeometricallyConnected b]
    (G : RelativeGroupLaw K b) (hc : G.IsCommutative) (n : ℕ+)
    (τ : Pic0.torsion K F (n : ℕ) ≃+ ProCGroups.torsionLevel (G.AlgPoints hc K) n)
    (w : DivisorialWeilPairingData K F (n : ℕ)) :
    let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
    let : DiscreteTopology (rootsOfUnity (n : ℕ) K) := ⟨rfl⟩
    let A := AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))
    let : TopologicalSpace (Multiplicative A) := ⊥
    let : DiscreteTopology (Multiplicative A) := ⟨rfl⟩
    let : ConnectedSpace J := GeometricallyConnected.connectedSpace b b.isOpenMap
    ∀ ν : Pic0.torsion K F (n : ℕ) →+
        Sheaf.H.{0} ((constantSheaf J.smallEtaleTopology AddCommGrpCat.{0}).obj A) 1,
      (∀ (x : Pic0.torsion K F (n : ℕ))
        (g : π₁ᵉᵗ((G.one (𝟙 (Spec (.of K)))).1)),
        ((finiteH1CharacterEquiv A (G.one (𝟙 (Spec (.of K)))).1 (ν x)).toMul g :
          rootsOfUnity (n : ℕ) K).val.val =
            w.pair x (τ.symm (G.multiplicationMonodromy hc n g))) →
      Function.Bijective ν := by
  intro htop hdiscrete A hAtop hAdiscrete hconnected ν hν
  refine ⟨jacobian_weil_cohomology_injective hfg G hc n τ w ν hν, ?_⟩
  have : Finite (ProCGroups.torsionLevel (G.AlgPoints hc K) n) :=
    Finite.of_equiv
      ((AlgebraicGeometry.FiniteEtale.fiber (G.one (𝟙 (Spec (.of K)))).1).obj
        (G.multiplicationCover hc n))
      (G.multiplicationCoverFiberEquivTorsion hc n)
  have : Finite (Pic0.torsion K F (n : ℕ)) :=
    Finite.of_injective τ τ.injective
  have : NeZero ((n : ℕ) : K) := ⟨Nat.cast_ne_zero.mpr n.ne_zero⟩
  have hw : Function.Bijective w.toHom :=
    Pic0.torsion.bijective_of_injective w.toHom (w.toHom_injective_charZero hfg)
  intro a
  let χ := (finiteH1CharacterEquiv A (G.one (𝟙 (Spec (.of K)))).1 a).toMul
  have hA : ∀ u : A, (n : ℕ) • u = 0 := by
    intro u
    apply (Additive.ofMul : rootsOfUnity (n : ℕ) K ≃
      Additive (rootsOfUnity (n : ℕ) K)).symm.injective
    apply Subtype.ext
    apply Units.ext
    change (u.toMul.val.val) ^ (n : ℕ) = 1
    exact (mem_rootsOfUnity' (n : ℕ) _).mp u.toMul.property
  obtain ⟨ψ, hψ⟩ := G.character_factors_multiplicationMonodromy hc n χ.toMonoidHom hA
  let η : HomPic0Gm K F (n : ℕ) :=
    { toFun := fun z => (ψ (τ z)).toMul.val.val
      map_zero_eq_one' := by
        rw [map_zero, map_zero]
        rfl
      map_add_eq_mul' := by
        intro z z'
        rw [map_add, map_add]
        rfl }
  obtain ⟨x, hx⟩ := hw.2 (Additive.ofMul η)
  have hp (z : Pic0.torsion K F (n : ℕ)) :
      w.pair x z = (ψ (τ z)).toMul.val.val :=
    congrArg (fun c : Additive (HomPic0Gm K F (n : ℕ)) => c.toMul z) hx
  refine ⟨x, ?_⟩
  apply (finiteH1CharacterEquiv A (G.one (𝟙 (Spec (.of K)))).1).injective
  apply ContinuousMonoidHom.ext
  intro g
  apply Subtype.ext
  apply Units.ext
  change ((finiteH1CharacterEquiv A (G.one (𝟙 (Spec (.of K)))).1 (ν x)).toMul g :
    rootsOfUnity (n : ℕ) K).val.val = (χ g : rootsOfUnity (n : ℕ) K).val.val
  rw [hν x g, hp, τ.apply_symm_apply]
  exact congrArg (fun u : A => u.toMul.val.val) (hψ g)

end JacobianVarieties.Kummer
