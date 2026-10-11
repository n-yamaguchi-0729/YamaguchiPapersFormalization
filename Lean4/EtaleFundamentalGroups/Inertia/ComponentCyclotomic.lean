/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.FiniteEtale.Boundary.ComponentGenericResidue
import EtaleFundamentalGroups.LocalGeometry.HeightOne.CartierComponentStalkDVR
import SchemeTheory.AbhyankarLemma.Geometry.CyclicInertia.DVRCyclotomicInversion

/-!
# Cyclotomic inversion at a component of a locally regular boundary

Only the ambient local rings along the Cartier divisor are required to be
regular.  In particular the ambient scheme is allowed to be reducible and
nonnormal elsewhere.  At the selected component's generic point we construct
the DVR and use its own fraction field; no global function field of the
ambient scheme is used.

For a component dominant over an integral base with rational generic residue
field, geometric integrality of its generic fibre supplies the residue-field
hypothesis for cyclotomic inversion in every finite Galois normalization of
this local fraction field.  Comparing these local normalization groups with
the deck stabilizers of a finite cover remains a separate geometric step.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open RamificationTheory.HilbertRamification

namespace EtaleFundamentalGroups.Inertia

universe u

/-- Every inertia element in a finite Galois extension of the local fraction
field at a horizontal Cartier component is conjugate to its inverse when
the component's generic fibre is geometrically integral over a rational
field. All regularity and residue-field data are constructed from the
component, without global integrality or normality of `X`. -/
theorem componentNormalizationInertia_isConj_inv
    {X S : Scheme.{u}} [IsLocallyNoetherian X] [IsIntegral S]
    (D : X.EffectiveCartierDivisor) (hreg : D.IsAmbientRegularAlongSupport)
    (p : X ⟶ S) (ek : S.residueField (genericPoint S) ≃+* ℚ)
    (Z : Set D.1.subscheme) (hZ : Z ∈ irreducibleComponents D.1.subscheme)
    (hdominant : DenseRange (D.1.componentToBase p Z hZ))
    (hgeo : GeometricallyIntegral
      ((D.1.componentToBase p Z hZ).fiberToSpecResidueField (genericPoint S))) :
    let A := X.presheaf.stalk (D.1.componentGenericPoint Z hZ)
    letI : IsDomain A := isDomain_stalk_componentGenericPoint D hreg Z hZ
    ∀ (L : Type u) [Field L] [Algebra (FractionRing A) L]
      [FiniteDimensional (FractionRing A) L] [IsGalois (FractionRing A) L],
      letI : Algebra A L :=
        ((algebraMap (FractionRing A) L).comp
          (algebraMap A (FractionRing A))).toAlgebra
      letI : IsScalarTower A (FractionRing A) L :=
        IsScalarTower.of_algebraMap_eq' rfl
      ∀ (Q : Ideal (integralClosure A L)) [Q.IsPrime]
        [Q.LiesOver (IsLocalRing.maximalIdeal A)],
        letI : MulSemiringAction Gal(L/FractionRing A) (integralClosure A L) :=
          IsIntegralClosure.MulSemiringAction A (FractionRing A) L
            (integralClosure A L)
        ∀ sigma : Q.toAddSubgroup.inertia Gal(L/FractionRing A),
          IsConj (sigma : Gal(L/FractionRing A))
            ((sigma⁻¹ : Q.toAddSubgroup.inertia Gal(L/FractionRing A)) :
              Gal(L/FractionRing A)) := by
  let x := D.1.componentGenericPoint Z hZ
  let A := X.presheaf.stalk x
  let : IsDomain A := isDomain_stalk_componentGenericPoint D hreg Z hZ
  let : IsDiscreteValuationRing A :=
    isDiscreteValuationRing_stalk_componentGenericPoint D hreg Z hZ
  let k := S.residueField (genericPoint S)
  obtain ⟨hAlg, hfield⟩ :=
    D.1.componentGenericPoint_exists_geometricallyIntegralResidueAlgebra
      p Z hZ hdominant hgeo
  let : Algebra k (X.residueField x) := hAlg
  let : Algebra k (IsLocalRing.ResidueField A) := by
    change Algebra k (X.residueField x)
    infer_instance
  dsimp only
  intro L instField instAlgebra instFinite instGalois
  let : Algebra A L :=
    ((algebraMap (FractionRing A) L).comp
      (algebraMap A (FractionRing A))).toAlgebra
  let : IsScalarTower A (FractionRing A) L :=
    IsScalarTower.of_algebraMap_eq' rfl
  intro Q instPrime instLiesOver
  exact
    (open _root_.TameAbhyankar.SGA1 in
      idealInertia_isConj_inv_of_geometricallyIntegral_dvrNormalizationResidue_of_ratEquiv
        k ek (A := A) (K := FractionRing A) (L := L) Q hfield)

end EtaleFundamentalGroups.Inertia
