/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SchemeTheory.Fibers.ResidueField
import EtaleFundamentalGroups.LocalGeometry.HeightOne.ComponentFunctionField

/-!
# Generic-fibre residue fields

For a morphism of integral schemes whose generic point lies over the generic
point of the base, geometric integrality of the generic fibre makes the
residue field at the source generic point geometrically integral over the
base generic residue field.
-/

noncomputable section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

universe u

/-- Geometric integrality of a field extension is invariant under a ring
equivalence, with the algebra structure transported along that equivalence. -/
theorem GeometricallyIntegral.specMap_transport_ringEquiv
    {k R T : Type u} [Field k] [Field R] [Field T]
    [Algebra k R] (e : R ≃+* T)
    (h : GeometricallyIntegral
      (Spec.map (CommRingCat.ofHom (algebraMap k R)))) :
    letI : Algebra k T :=
      (e.toRingHom.comp (algebraMap k R)).toAlgebra
    GeometricallyIntegral
      (Spec.map (CommRingCat.ofHom (algebraMap k T))) := by
  let : Algebra k T :=
    (e.toRingHom.comp (algebraMap k R)).toAlgebra
  let j : Spec (CommRingCat.of T) ≅ Spec (CommRingCat.of R) :=
    Scheme.Spec.mapIso e.toCommRingCatIso.op
  let : MorphismProperty.RespectsIso
      (@GeometricallyIntegral : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hj : GeometricallyIntegral
      (j.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap k R))) :=
    (MorphismProperty.cancel_left_of_respectsIso
      (P := @GeometricallyIntegral) j.hom _).mpr h
  have hmap : CommRingCat.ofHom (algebraMap k R) ≫
      e.toCommRingCatIso.hom.op.unop =
      CommRingCat.ofHom (algebraMap k T) := by
    ext x
    rfl
  simpa only [j, Functor.mapIso_hom, Iso.op_hom,
    Scheme.Spec_map, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hmap]
    using hj

namespace Scheme.Hom

variable {X S : Scheme.{u}}

/-- Geometric integrality of the generic fibre gives geometric integrality
of the source residue field at its generic point.  The algebra structure is
transported through the canonical generic-fibre residue/function-field
equivalence. -/
theorem geometricallyIntegral_spec_genericPointResidue_of_genericFiber
    [IsIntegral X] [IsIntegral S]
    (f : X ⟶ S) (hη : f (genericPoint X) = genericPoint S)
    (hgeo : GeometricallyIntegral
      (f.fiberToSpecResidueField (genericPoint S))) :
    let k := S.residueField (genericPoint S)
    let F := f.fiber (genericPoint S)
    let q := f.fiberToSpecResidueField (genericPoint S)
    letI : GeometricallyIntegral q := hgeo
    letI : IsIntegral F :=
      GeometricallyIntegral.isIntegral_of_subsingleton q
    letI : Algebra k F.functionField := q.functionFieldAlgebra
    let e : X.residueField (genericPoint X) ≃+* F.functionField :=
      (f.genericFiberResidueFieldRingEquiv hη).trans
        (Scheme.functionFieldResidueFieldRingEquiv F).symm
    letI : Algebra k (X.residueField (genericPoint X)) :=
      (e.symm.toRingHom.comp (algebraMap k F.functionField)).toAlgebra
    GeometricallyIntegral
      (Spec.map (CommRingCat.ofHom
        (algebraMap k (X.residueField (genericPoint X))))) := by
  let k := S.residueField (genericPoint S)
  let F := f.fiber (genericPoint S)
  let q := f.fiberToSpecResidueField (genericPoint S)
  let : GeometricallyIntegral q := hgeo
  let : IsIntegral F :=
    GeometricallyIntegral.isIntegral_of_subsingleton q
  let : Algebra k F.functionField := q.functionFieldAlgebra
  let e : X.residueField (genericPoint X) ≃+* F.functionField :=
    (f.genericFiberResidueFieldRingEquiv hη).trans
      (Scheme.functionFieldResidueFieldRingEquiv F).symm
  let : Algebra k (X.residueField (genericPoint X)) :=
    (e.symm.toRingHom.comp (algebraMap k F.functionField)).toAlgebra
  have hq : GeometricallyIntegral q := inferInstance
  have hff : GeometricallyIntegral
      (Spec.map (CommRingCat.ofHom (algebraMap k F.functionField))) :=
    @GeometricallyIntegral.spec_functionField k _ F inferInstance q hq
  exact GeometricallyIntegral.specMap_transport_ringEquiv e.symm hff

/-- Geometric integrality of a generic fibre gives geometric integrality of
the ambient residue field at the generic point of an integral closed
component. -/
theorem geometricallyIntegral_genericSourceResidue_of_genericFiber
    {C A S : Scheme.{u}} [IsIntegral C] [IsIntegral S]
    (i : C ⟶ A) [IsClosedImmersion i]
    (f : C ⟶ S) (hη : f (genericPoint C) = genericPoint S)
    (hgeo : GeometricallyIntegral
      (f.fiberToSpecResidueField (genericPoint S))) :
    let k := S.residueField (genericPoint S)
    let F := f.fiber (genericPoint S)
    let q := f.fiberToSpecResidueField (genericPoint S)
    letI : GeometricallyIntegral q := hgeo
    letI : IsIntegral F :=
      GeometricallyIntegral.isIntegral_of_subsingleton q
    letI : Algebra k F.functionField := q.functionFieldAlgebra
    let eF : C.residueField (genericPoint C) ≃+* F.functionField :=
      (f.genericFiberResidueFieldRingEquiv hη).trans
        (Scheme.functionFieldResidueFieldRingEquiv F).symm
    let e : A.residueField (i (genericPoint C)) ≃+* F.functionField :=
      (i.residueFieldRingEquivOfIsClosedImmersion
        (genericPoint C)).trans eF
    letI : Algebra k (A.residueField (i (genericPoint C))) :=
      (e.symm.toRingHom.comp (algebraMap k F.functionField)).toAlgebra
    GeometricallyIntegral
      (Spec.map (CommRingCat.ofHom
        (algebraMap k (A.residueField (i (genericPoint C)))))) := by
  let k := S.residueField (genericPoint S)
  let F := f.fiber (genericPoint S)
  let q := f.fiberToSpecResidueField (genericPoint S)
  let : GeometricallyIntegral q := hgeo
  let : IsIntegral F :=
    GeometricallyIntegral.isIntegral_of_subsingleton q
  let : Algebra k F.functionField := q.functionFieldAlgebra
  let eF : C.residueField (genericPoint C) ≃+* F.functionField :=
    (f.genericFiberResidueFieldRingEquiv hη).trans
      (Scheme.functionFieldResidueFieldRingEquiv F).symm
  let e : A.residueField (i (genericPoint C)) ≃+* F.functionField :=
    (i.residueFieldRingEquivOfIsClosedImmersion
      (genericPoint C)).trans eF
  let : Algebra k (A.residueField (i (genericPoint C))) :=
    (e.symm.toRingHom.comp (algebraMap k F.functionField)).toAlgebra
  have hq : GeometricallyIntegral q := inferInstance
  have hff : GeometricallyIntegral
      (Spec.map (CommRingCat.ofHom (algebraMap k F.functionField))) :=
    @GeometricallyIntegral.spec_functionField k _ F inferInstance q hq
  exact GeometricallyIntegral.specMap_transport_ringEquiv e.symm hff

/-- Existence form of
`geometricallyIntegral_genericSourceResidue_of_genericFiber`, convenient
when only the canonical transported field structure and its geometric
integrality are needed downstream. -/
theorem exists_algebra_geometricallyIntegral_genericSourceResidue_of_genericFiber
    {C A S : Scheme.{u}} [IsIntegral C] [IsIntegral S]
    (i : C ⟶ A) [IsClosedImmersion i]
    (f : C ⟶ S) (hη : f (genericPoint C) = genericPoint S)
    (hgeo : GeometricallyIntegral
      (f.fiberToSpecResidueField (genericPoint S))) :
    let k := S.residueField (genericPoint S)
    ∃ hAlg : Algebra k (A.residueField (i (genericPoint C))),
      letI : Algebra k (A.residueField (i (genericPoint C))) := hAlg
      GeometricallyIntegral
        (Spec.map (CommRingCat.ofHom
          (algebraMap k (A.residueField (i (genericPoint C)))))) := by
  let k := S.residueField (genericPoint S)
  let F := f.fiber (genericPoint S)
  let q := f.fiberToSpecResidueField (genericPoint S)
  let : GeometricallyIntegral q := hgeo
  let : IsIntegral F :=
    GeometricallyIntegral.isIntegral_of_subsingleton q
  let : Algebra k F.functionField := q.functionFieldAlgebra
  let eF : C.residueField (genericPoint C) ≃+* F.functionField :=
    (f.genericFiberResidueFieldRingEquiv hη).trans
      (Scheme.functionFieldResidueFieldRingEquiv F).symm
  let e : A.residueField (i (genericPoint C)) ≃+* F.functionField :=
    (i.residueFieldRingEquivOfIsClosedImmersion
      (genericPoint C)).trans eF
  let hAlg : Algebra k (A.residueField (i (genericPoint C))) :=
    (e.symm.toRingHom.comp (algebraMap k F.functionField)).toAlgebra
  refine ⟨hAlg, ?_⟩
  let : Algebra k (A.residueField (i (genericPoint C))) := hAlg
  exact i.geometricallyIntegral_genericSourceResidue_of_genericFiber
    f hη hgeo

end Scheme.Hom

end AlgebraicGeometry

end
