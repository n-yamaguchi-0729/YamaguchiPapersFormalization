/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SchemeTheory.Divisors.ReducedIrreducibleComponentGeometry
import SchemeTheory.Divisors.ComponentStalkBranch
import EtaleFundamentalGroups.LocalGeometry.HeightOne.GenericFiberResidue

/-!
# Geometrically integral residue fields of horizontal components

The ambient scheme need not be integral or normal.  Only the selected reduced
component is integral.  Its dominance over the integral arithmetic base and
the geometric integrality of its generic fibre supply the base-field algebra
on the ambient residue field.  The second result transports this algebra to
the literal branch prime in the stalk at any point of the component.

These are the residue-field inputs to the cyclotomic argument in Lemma 2.1 of
Yamaguchi's solvable-coverings paper.  No condition on finite covers, inertia,
or an abelian quotient is assumed here.
-/

noncomputable section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme.IdealSheafData

universe u

variable {X S : Scheme.{u}} [IsIntegral S]

/-- A dominant component with geometrically integral generic fibre has a
geometrically integral generic residue field, even when the ambient scheme
is reducible or nonnormal away from the component. -/
theorem componentGenericPoint_exists_geometricallyIntegralResidueAlgebra
    (I : X.IdealSheafData) (p : X ⟶ S)
    (Z : Set I.subscheme) (hZ : Z ∈ irreducibleComponents I.subscheme)
    (hdominant : DenseRange (I.componentToBase p Z hZ))
    (hgeo : GeometricallyIntegral
      ((I.componentToBase p Z hZ).fiberToSpecResidueField (genericPoint S))) :
    ∃ hAlg : Algebra (S.residueField (genericPoint S))
        (X.residueField (I.componentGenericPoint Z hZ)),
      letI : Algebra (S.residueField (genericPoint S))
          (X.residueField (I.componentGenericPoint Z hZ)) := hAlg
      GeometricallyIntegral
        (Spec.map (CommRingCat.ofHom
          (algebraMap (S.residueField (genericPoint S))
            (X.residueField (I.componentGenericPoint Z hZ))))) := by
  let C := I.subscheme.reducedIrreducibleComponent Z hZ
  let i : C ⟶ X :=
    I.subscheme.reducedIrreducibleComponentι Z hZ ≫ I.subschemeι
  let f : C ⟶ S := I.componentToBase p Z hZ
  have hη : f (genericPoint C) = genericPoint S :=
    I.componentToBase_genericPoint p Z hZ hdominant
  exact i.exists_algebra_geometricallyIntegral_genericSourceResidue_of_genericFiber
    f hη hgeo

/-- At any specialization on the selected component, the residue field of
its canonical stalk prime is the same geometrically integral field. -/
theorem componentBranchPrime_exists_geometricallyIntegralResidueAlgebra
    (I : X.IdealSheafData) (p : X ⟶ S)
    (Z : Set I.subscheme) (hZ : Z ∈ irreducibleComponents I.subscheme)
    (hdominant : DenseRange (I.componentToBase p Z hZ))
    (hgeo : GeometricallyIntegral
      ((I.componentToBase p Z hZ).fiberToSpecResidueField (genericPoint S)))
    (z : I.subscheme) (hz : z ∈ Z) :
    letI : (I.componentBranchPrimeAt Z hZ z hz).asIdeal.IsPrime :=
      (I.componentBranchPrimeAt Z hZ z hz).isPrime
    ∃ hAlg : Algebra (S.residueField (genericPoint S))
        (I.componentBranchPrimeAt Z hZ z hz).asIdeal.ResidueField,
      letI : Algebra (S.residueField (genericPoint S))
          (I.componentBranchPrimeAt Z hZ z hz).asIdeal.ResidueField := hAlg
      GeometricallyIntegral
        (Spec.map (CommRingCat.ofHom
          (algebraMap (S.residueField (genericPoint S))
            (I.componentBranchPrimeAt Z hZ z hz).asIdeal.ResidueField))) := by
  let k := S.residueField (genericPoint S)
  let x := I.componentGenericPoint Z hZ
  let b := I.componentBranchPrimeAt Z hZ z hz
  let : b.asIdeal.IsPrime := b.isPrime
  obtain ⟨hAlg, hfield⟩ :=
    I.componentGenericPoint_exists_geometricallyIntegralResidueAlgebra
      p Z hZ hdominant hgeo
  let : Algebra k (X.residueField x) := hAlg
  have hb : X.fromSpecStalk (I.subschemeι z) b = x :=
    I.fromSpecStalk_componentBranchPrimeAt Z hZ z hz
  let e : X.residueField x ≃+* b.asIdeal.ResidueField :=
    (X.residueFieldCongr hb.symm).commRingCatIsoToRingEquiv.trans
      (X.residueFieldFromSpecStalkEquiv (I.subschemeι z) b)
  let hBranchAlg : Algebra k b.asIdeal.ResidueField :=
    (e.toRingHom.comp (algebraMap k (X.residueField x))).toAlgebra
  refine ⟨hBranchAlg, ?_⟩
  exact GeometricallyIntegral.specMap_transport_ringEquiv e hfield

end AlgebraicGeometry.Scheme.IdealSheafData
