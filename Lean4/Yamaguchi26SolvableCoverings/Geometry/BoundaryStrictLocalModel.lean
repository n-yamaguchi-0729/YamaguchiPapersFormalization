/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Yamaguchi26SolvableCoverings.Geometry.Boundary
import EtaleFundamentalGroups.LocalGeometry.HeightOne.CartierComponentStalkDVR
import EtaleFundamentalGroups.StrictHenselian.CartierGenericPoint
import EtaleFundamentalGroups.StrictHenselian.GeometricStalkHenselian
import EtaleFundamentalGroups.StrictHenselian.GeometricStalkResidue
import Mathlib.AlgebraicGeometry.ResidueField

/-!
# The canonical strict local model at a boundary component

The shared component generic point and the manuscript component point agree
by the proved generic-point equation. Transporting the actual local-ring
results along that equation gives the domain and DVR structures used here.
All strict-local maps use the manuscript's original component point and
its original residue-field algebraic closure.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open EtaleFundamentalGroups EtaleFundamentalGroups.StrictHenselian

namespace Yamaguchi26SolvableCoverings

variable {X : Scheme.{0}} [IsLocallyNoetherian X]

/-- The original component point has a domain stalk. -/
theorem isDomain_stalk_componentPoint
    (D : X.EffectiveCartierDivisor) (hreg : D.IsAmbientRegularAlongSupport) (E : Component D) :
    IsDomain (X.presheaf.stalk (componentPoint D E)) :=
  Eq.mp (congrArg (fun x : X => IsDomain (X.presheaf.stalk x))
    (D.1.componentGenericPoint_eq E.val E.property))
    (isDomain_stalk_componentGenericPoint D hreg E.val E.property)

/-- The original component point has a DVR stalk. -/
theorem isDiscreteValuationRing_stalk_componentPoint
    (D : X.EffectiveCartierDivisor) (hreg : D.IsAmbientRegularAlongSupport) (E : Component D) :
    let : IsDomain (X.presheaf.stalk (componentPoint D E)) :=
      isDomain_stalk_componentPoint D hreg E
    IsDiscreteValuationRing (X.presheaf.stalk (componentPoint D E)) := by
  intro hDomain
  have hlocal : ∃ h : IsDomain (X.presheaf.stalk (componentPoint D E)),
      let : IsDomain (X.presheaf.stalk (componentPoint D E)) := h
      IsDiscreteValuationRing (X.presheaf.stalk (componentPoint D E)) := by
    apply Eq.mp (congrArg (fun x : X => ∃ h : IsDomain (X.presheaf.stalk x),
      let : IsDomain (X.presheaf.stalk x) := h
      IsDiscreteValuationRing (X.presheaf.stalk x))
        (D.1.componentGenericPoint_eq E.val E.property))
    exact ⟨isDomain_stalk_componentGenericPoint D hreg E.val E.property,
      isDiscreteValuationRing_stalk_componentGenericPoint D hreg E.val E.property⟩
  obtain ⟨_, h⟩ := hlocal
  exact h

/-- The actual closed geometric point map into the prescribed algebraic closure. -/
def boundaryComponentResidueMap (D : X.EffectiveCartierDivisor) (E : Component D) :
    X.presheaf.stalk (componentPoint D E) →+*
      AlgebraicClosure (X.residueField (componentPoint D E)) :=
  (algebraMap (X.residueField (componentPoint D E))
    (AlgebraicClosure (X.residueField (componentPoint D E)))).comp
      (X.residue (componentPoint D E)).hom

instance boundaryComponentResidueMap_isLocalHom
    (D : X.EffectiveCartierDivisor) (E : Component D) :
    IsLocalHom (boundaryComponentResidueMap D E) := by
  refine ⟨fun a ha => ?_⟩
  apply isUnit_of_map_unit (IsLocalRing.residue (X.presheaf.stalk (componentPoint D E))) a
  apply isUnit_iff_ne_zero.mpr
  intro hzero
  have hz : boundaryComponentResidueMap D E a = 0 := by
    change algebraMap (X.residueField (componentPoint D E))
      (AlgebraicClosure (X.residueField (componentPoint D E)))
        (IsLocalRing.residue (X.presheaf.stalk (componentPoint D E)) a) = 0
    exact (congrArg (algebraMap (X.residueField (componentPoint D E))
      (AlgebraicClosure (X.residueField (componentPoint D E)))) hzero).trans (map_zero _)
  exact (isUnit_iff_ne_zero.mp ha) hz

/-- The fraction ring of the actual geometric etale stalk at the component. -/
abbrev boundaryStrictFractionField (D : X.EffectiveCartierDivisor) (E : Component D) :=
  FractionRing (geometricStalk (Spec.map (CommRingCat.ofHom (boundaryComponentResidueMap D E))))

/-- Its canonical field structure is supplied by the actual DVR stalk theorem. -/
@[instance_reducible] def boundaryStrictFractionFieldField
    (D : X.EffectiveCartierDivisor) (hreg : D.IsAmbientRegularAlongSupport) (E : Component D) :
    Field (boundaryStrictFractionField D E) := by
  let : IsDomain (X.presheaf.stalk (componentPoint D E)) :=
    isDomain_stalk_componentPoint D hreg E
  let : IsDiscreteValuationRing (X.presheaf.stalk (componentPoint D E)) :=
    isDiscreteValuationRing_stalk_componentPoint D hreg E
  infer_instance

/-- The canonical strict generic morphism into the original complement. -/
def boundaryStrictGenericMorphism
    (D : X.EffectiveCartierDivisor) (hreg : D.IsAmbientRegularAlongSupport) (E : Component D) :
    let : Field (boundaryStrictFractionField D E) := boundaryStrictFractionFieldField D hreg E
    Spec (.of (boundaryStrictFractionField D E)) ⟶ D.1.supportComplement := by
  intro hField
  let : IsDomain (X.presheaf.stalk (componentPoint D E)) :=
    isDomain_stalk_componentPoint D hreg E
  let : IsDiscreteValuationRing (X.presheaf.stalk (componentPoint D E)) :=
    isDiscreteValuationRing_stalk_componentPoint D hreg E
  exact geometricStalkFractionFieldToComplement D (componentPoint D E)
    (boundaryComponentResidueMap D E)

/-- The canonical geometric point of the strict fraction field. -/
def boundaryStrictGenericPoint
    (D : X.EffectiveCartierDivisor) (hreg : D.IsAmbientRegularAlongSupport) (E : Component D) :
    let : Field (boundaryStrictFractionField D E) := boundaryStrictFractionFieldField D hreg E
    Spec (.of (AlgebraicClosure (boundaryStrictFractionField D E))) ⟶
      Spec (.of (boundaryStrictFractionField D E)) := by
  intro hField
  exact Spec.map (CommRingCat.ofHom (algebraMap (boundaryStrictFractionField D E)
    (AlgebraicClosure (boundaryStrictFractionField D E))))

end Yamaguchi26SolvableCoverings
