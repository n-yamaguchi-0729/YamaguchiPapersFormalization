/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import SchemeTheory.Affine.StalkLocalization
import SchemeTheory.FunctionFields.GeometricIntegrality

/-!
# Function fields of closed integral components

At the generic point of an integral closed subscheme, the ambient residue
field is the function field of the subscheme.  The comparison below also
transports geometric integrality across this canonical field equivalence.
-/

noncomputable section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

universe u

namespace Scheme

/-- A closed immersion induces an isomorphism on residue fields at every
point of its source. -/
theorem Hom.residueFieldMap_bijective_of_isClosedImmersion
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (z : Z) :
    Function.Bijective (i.residueFieldMap z) := by
  constructor
  · exact (i.residueFieldMap z).hom.injective
  · intro y
    obtain ⟨b, hb⟩ := IsLocalRing.residue_surjective y
    obtain ⟨a, ha⟩ := i.stalkMap_surjective z b
    refine ⟨X.residue (i z) a, ?_⟩
    calc
      i.residueFieldMap z (X.residue (i z) a) =
          Z.residue z (i.stalkMap z a) := by
        simpa only [ConcreteCategory.comp_apply] using
          congrArg (fun g ↦ g a) (residue_residueFieldMap i z)
      _ = Z.residue z b := congrArg (Z.residue z) ha
      _ = y := hb

/-- The residue-field equivalence induced by a closed immersion. -/
noncomputable def Hom.residueFieldRingEquivOfIsClosedImmersion
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (z : Z) :
    X.residueField (i z) ≃+* Z.residueField z :=
  RingEquiv.ofBijective (i.residueFieldMap z).hom
    (i.residueFieldMap_bijective_of_isClosedImmersion z)

/-- The function field of an integral scheme is canonically its residue
field at the generic point. -/
noncomputable def functionFieldResidueFieldRingEquiv
    (Z : Scheme.{u}) [IsIntegral Z] :
    Z.functionField ≃+* Z.residueField (genericPoint Z) :=
  RingEquiv.ofBijective (Z.residue (genericPoint Z)).hom
    ⟨(Z.residue (genericPoint Z)).hom.injective,
      Z.residue_surjective (genericPoint Z)⟩

/-- The residue field of a prime ideal is canonically the function field of
the integral affine scheme cut out by that prime. -/
noncomputable def primeResidueFieldEquivQuotientFunctionField
    {A : Type u} [CommRing A] (P : Ideal A) [P.IsPrime] :
    P.ResidueField ≃+*
      (Spec (CommRingCat.of (A ⧸ P))).functionField := by
  let Z := Spec (CommRingCat.of (A ⧸ P))
  letI : Algebra (A ⧸ P) Z.functionField :=
    (StructureSheaf.toStalk (A ⧸ P) (genericPoint Z)).hom.toAlgebra
  letI : IsFractionRing (A ⧸ P) Z.functionField := by
    change IsFractionRing (A ⧸ P)
      (Spec (CommRingCat.of (A ⧸ P))).functionField
    exact functionField_isFractionRing_of_affine
      (CommRingCat.of (A ⧸ P))
  exact
    ((FractionRing.algEquiv (A ⧸ P) P.ResidueField).symm.trans
      (FractionRing.algEquiv (A ⧸ P) Z.functionField)).toRingEquiv

/-- At the generic point of an integral closed subscheme, the ambient
residue field is canonically the function field of the subscheme. -/
noncomputable def Hom.genericSourceResidueEquivFunctionField
    {Z X : Scheme.{u}} [IsIntegral Z]
    (i : Z ⟶ X) [IsClosedImmersion i] :
    X.residueField (i (genericPoint Z)) ≃+* Z.functionField :=
  (i.residueFieldRingEquivOfIsClosedImmersion (genericPoint Z)).trans
    (functionFieldResidueFieldRingEquiv Z).symm

end Scheme

private theorem geometricallyIntegral_specMap_transport_ringEquiv
    {k R S : Type u} [Field k] [Field R] [Field S]
    [Algebra k R] (e : R ≃+* S)
    (h : GeometricallyIntegral
      (Spec.map (CommRingCat.ofHom (algebraMap k R)))) :
    letI : Algebra k S :=
      (e.toRingHom.comp (algebraMap k R)).toAlgebra
    GeometricallyIntegral
      (Spec.map (CommRingCat.ofHom (algebraMap k S))) := by
  let : Algebra k S :=
    (e.toRingHom.comp (algebraMap k R)).toAlgebra
  let j : Spec (CommRingCat.of S) ≅ Spec (CommRingCat.of R) :=
    Scheme.Spec.mapIso e.toCommRingCatIso.op
  let : MorphismProperty.RespectsIso
      (@GeometricallyIntegral : MorphismProperty Scheme.{u}) := by
    rw [GeometricallyIntegral.eq_geometrically, geometrically_eq_universally]
    exact MorphismProperty.universally_respectsIso _
  have hj : GeometricallyIntegral
      (j.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap k R))) :=
    (MorphismProperty.cancel_left_of_respectsIso
      (P := @GeometricallyIntegral) j.hom _).mpr h
  have hmap : CommRingCat.ofHom (algebraMap k R) ≫
      e.toCommRingCatIso.hom.op.unop =
      CommRingCat.ofHom (algebraMap k S) := by
    ext x
    rfl
  simpa only [j, Functor.mapIso_hom, Iso.op_hom,
    Scheme.Spec_map, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hmap]
    using hj

/-- Geometric integrality of a field over the base is invariant under a
ring equivalence, with the target algebra structure transported along that
equivalence. -/
theorem geometricallyIntegral_specMap_transport_ringEquiv'
    {k R S : Type u} [Field k] [Field R] [Field S]
    [Algebra k R] (e : R ≃+* S)
    (h : GeometricallyIntegral
      (Spec.map (CommRingCat.ofHom (algebraMap k R)))) :
    letI : Algebra k S :=
      (e.toRingHom.comp (algebraMap k R)).toAlgebra
    GeometricallyIntegral
      (Spec.map (CommRingCat.ofHom (algebraMap k S))) :=
  geometricallyIntegral_specMap_transport_ringEquiv e h

/-- Geometric integrality of the residue field at a point represented in a
stalk transports to the residue field of the corresponding stalk prime. -/
theorem Scheme.geometricallyIntegral_residueFieldFromSpecStalk
    {k : Type u} [Field k] (X : Scheme.{u}) (x : X)
    (p : Spec (X.presheaf.stalk x))
    [Algebra k (X.residueField (X.fromSpecStalk x p))]
    (h : GeometricallyIntegral
      (Spec.map (CommRingCat.ofHom
        (algebraMap k (X.residueField (X.fromSpecStalk x p)))))) :
    letI : p.asIdeal.IsPrime := p.isPrime
    let e := X.residueFieldFromSpecStalkEquiv x p
    letI : Algebra k p.asIdeal.ResidueField :=
      (e.toRingHom.comp
        (algebraMap k (X.residueField (X.fromSpecStalk x p)))).toAlgebra
    GeometricallyIntegral
      (Spec.map (CommRingCat.ofHom
        (algebraMap k p.asIdeal.ResidueField))) := by
  let : p.asIdeal.IsPrime := p.isPrime
  exact geometricallyIntegral_specMap_transport_ringEquiv'
    (X.residueFieldFromSpecStalkEquiv x p) h

/-- Geometric integrality of the affine divisor cut out by a prime gives
geometric integrality of the prime's residue field.  The algebra structure is
transported through the canonical quotient-function-field equivalence. -/
theorem geometricallyIntegral_primeResidueField_of_specQuotient
    {k A : Type u} [Field k] [CommRing A]
    (P : Ideal A) [P.IsPrime] [Algebra k (A ⧸ P)]
    (hgeo : GeometricallyIntegral
      (Spec.map (CommRingCat.ofHom (algebraMap k (A ⧸ P))))) :
    let Z := Spec (CommRingCat.of (A ⧸ P))
    let f : Z ⟶ Spec (CommRingCat.of k) :=
      Spec.map (CommRingCat.ofHom (algebraMap k (A ⧸ P)))
    letI : Algebra k Z.functionField := f.functionFieldAlgebra
    let e := Scheme.primeResidueFieldEquivQuotientFunctionField P
    letI : Algebra k P.ResidueField :=
      (e.symm.toRingHom.comp (algebraMap k Z.functionField)).toAlgebra
    GeometricallyIntegral
      (Spec.map (CommRingCat.ofHom
        (algebraMap k P.ResidueField))) := by
  let Z := Spec (CommRingCat.of (A ⧸ P))
  let f : Z ⟶ Spec (CommRingCat.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k (A ⧸ P)))
  let : GeometricallyIntegral f := hgeo
  let : Algebra k Z.functionField := f.functionFieldAlgebra
  let e := Scheme.primeResidueFieldEquivQuotientFunctionField P
  let : Algebra k P.ResidueField :=
    (e.symm.toRingHom.comp (algebraMap k Z.functionField)).toAlgebra
  exact geometricallyIntegral_specMap_transport_ringEquiv e.symm
    (GeometricallyIntegral.spec_functionField f)

/-- Geometric integrality of an integral closed component over a field gives
geometric integrality of the ambient residue field at the component's
generic point, with the algebra structure transported by the canonical
residue/function-field equivalence. -/
theorem Scheme.Hom.geometricallyIntegral_genericSourceResidue
    {k : Type u} [Field k] {Z X : Scheme.{u}} [IsIntegral Z]
    (i : Z ⟶ X) [IsClosedImmersion i]
    (f : Z ⟶ Spec (.of k)) (hgeo : GeometricallyIntegral f) :
    letI : Algebra k Z.functionField := f.functionFieldAlgebra
    let e := i.genericSourceResidueEquivFunctionField
    letI : Algebra k (X.residueField (i (genericPoint Z))) :=
      (e.symm.toRingHom.comp (algebraMap k Z.functionField)).toAlgebra
    GeometricallyIntegral
      (Spec.map (CommRingCat.ofHom
        (algebraMap k (X.residueField (i (genericPoint Z)))))) := by
  let : GeometricallyIntegral f := hgeo
  let : Algebra k Z.functionField := f.functionFieldAlgebra
  let e := i.genericSourceResidueEquivFunctionField
  let : Algebra k (X.residueField (i (genericPoint Z))) :=
    (e.symm.toRingHom.comp (algebraMap k Z.functionField)).toAlgebra
  exact geometricallyIntegral_specMap_transport_ringEquiv e.symm
    (GeometricallyIntegral.spec_functionField f)

end AlgebraicGeometry

end
