/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.FiniteEtale.Boundary.ArithmeticComponentChart
import Nyll.EtaleFundamentalGroups.LocalGeometry.HeightOne.GenericFiberResidue

/-!
# Residue fields of arithmetic boundary components

The geometrically integral generic fibre supplied by the arithmetic boundary
condition determines a geometrically integral residue field at the canonical
generic point of every pulled-back boundary component.
-/

noncomputable section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme.EffectiveCartierDivisor

universe u

variable {X S : Scheme.{u}}

/-- The residue field at the canonical generic point of a boundary component
after a Galois finite-etale pullback is geometrically integral over the
generic residue field of the arithmetic base.  The required algebra structure
is the canonical one transported through the generic fibre. -/
theorem
    galoisPullback_componentGenericPoint_exists_geometricallyIntegralResidueAlgebra
    [IsIntegral X] [IsNormalIntegral X] [IsLocallyNoetherian X] [IsIntegral S]
    (D : EffectiveCartierDivisor X) (p : X ⟶ S)
    (hD : D.SatisfiesResidueCharacteristicTwoBoundaryCondition p)
    (Y : FiniteEtale X) (hY : CategoryTheory.PreGaloisCategory.IsGalois Y)
    (Z : Set (D.1.comap Y.hom).subscheme)
    (hZ : Z ∈ irreducibleComponents (D.1.comap Y.hom).subscheme) :
    let I : Y.left.IdealSheafData := D.1.comap Y.hom
    let x := I.componentGenericPoint Z hZ
    let k := S.residueField (genericPoint S)
    ∃ hAlg : Algebra k (Y.left.residueField x),
      letI : Algebra k (Y.left.residueField x) := hAlg
      GeometricallyIntegral
        (Spec.map (CommRingCat.ofHom
          (algebraMap k (Y.left.residueField x)))) := by
  let : CategoryTheory.PreGaloisCategory.IsGalois Y := hY
  let : IsIntegral Y.left :=
    EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale Y
  let I : Y.left.IdealSheafData := D.1.comap Y.hom
  let C := I.subscheme.reducedIrreducibleComponent Z hZ
  let x := I.componentGenericPoint Z hZ
  let f : C ⟶ S := I.componentToBase (Y.hom ≫ p) Z hZ
  let i : C ⟶ Y.left :=
    I.subscheme.reducedIrreducibleComponentι Z hZ ≫ I.subschemeι
  have hchart :=
    D.galoisPullback_componentGenericPoint_chart p hD Y hY Z hZ
  dsimp only at hchart
  rcases hchart with ⟨_hregular, _hheight, hη, hgeo, _hchart⟩
  change ∃ hAlg : Algebra (S.residueField (genericPoint S))
      (Y.left.residueField x),
    letI : Algebra (S.residueField (genericPoint S))
      (Y.left.residueField x) := hAlg
    GeometricallyIntegral
      (Spec.map (CommRingCat.ofHom
        (algebraMap (S.residueField (genericPoint S))
          (Y.left.residueField x))))
  have hex :=
    i.exists_algebra_geometricallyIntegral_genericSourceResidue_of_genericFiber
      f hη hgeo
  have hix : i (genericPoint C) = x := by
    rfl
  rw [← hix]
  exact hex

/-- Complete height-one residue data at the canonical generic point of a
pulled-back arithmetic boundary component: ambient regularity, codimension
one, and geometric integrality of the residue field over the generic base
field. -/
theorem galoisPullback_componentGenericPoint_localResidueData
    [IsIntegral X] [IsNormalIntegral X] [IsLocallyNoetherian X] [IsIntegral S]
    (D : EffectiveCartierDivisor X) (p : X ⟶ S)
    (hD : D.SatisfiesResidueCharacteristicTwoBoundaryCondition p)
    (Y : FiniteEtale X) (hY : CategoryTheory.PreGaloisCategory.IsGalois Y)
    (Z : Set (D.1.comap Y.hom).subscheme)
    (hZ : Z ∈ irreducibleComponents (D.1.comap Y.hom).subscheme) :
    let I : Y.left.IdealSheafData := D.1.comap Y.hom
    let x := I.componentGenericPoint Z hZ
    let k := S.residueField (genericPoint S)
    Y.left.IsRegularAt x ∧
      Order.coheight x = 1 ∧
        ∃ hAlg : Algebra k (Y.left.residueField x),
          letI : Algebra k (Y.left.residueField x) := hAlg
          GeometricallyIntegral
            (Spec.map (CommRingCat.ofHom
              (algebraMap k (Y.left.residueField x)))) := by
  let : CategoryTheory.PreGaloisCategory.IsGalois Y := hY
  let : IsIntegral Y.left :=
    EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale Y
  let I : Y.left.IdealSheafData := D.1.comap Y.hom
  let x := I.componentGenericPoint Z hZ
  let k := S.residueField (genericPoint S)
  have hchart :=
    D.galoisPullback_componentGenericPoint_chart p hD Y hY Z hZ
  dsimp only at hchart
  have hres :=
    D.galoisPullback_componentGenericPoint_exists_geometricallyIntegralResidueAlgebra
      p hD Y hY Z hZ
  dsimp only at hres
  exact ⟨hchart.1, hchart.2.1, hres⟩

end AlgebraicGeometry.Scheme.EffectiveCartierDivisor

end
