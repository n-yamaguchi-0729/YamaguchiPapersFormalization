/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.StrictHenselian.OrdinaryHenselizationUniversal
import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkHenselian
import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkHenselianMap
import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkStructure
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# The actual ordinary-to-pointed-stalk comparison

The ordinary universal lift gives the map into the existing pointed étale
stalk. Uniqueness proves the literal triangle with its existing Henselian
target map. This also applies to the original strict stalk inside a
normalization-prime localization.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace EtaleFundamentalGroups.StrictHenselian

universe u

section Point

variable {A Ω : Type u} [CommRing A] [IsLocalRing A] [Field Ω]
  (φ : A →+* Ω) [IsLocalHom φ]

/-- The actual ordinary universal lift into the existing pointed étale stalk. -/
def ordinaryHenselizationToGeometricStalk :
    ordinaryHenselization A →+* geometricStalk (Spec.map (CommRingCat.ofHom φ)) :=
  ordinaryHenselizationLift (geometricStalkStructureMap φ)

instance ordinaryHenselizationToGeometricStalk_isLocalHom :
    IsLocalHom (ordinaryHenselizationToGeometricStalk φ) :=
  ordinaryHenselizationLift_isLocalHom (geometricStalkStructureMap φ)

/-- The comparison preserves the original map from the base ring. -/
theorem ordinaryHenselizationToGeometricStalk_comp_map :
    (ordinaryHenselizationToGeometricStalk φ).comp (ordinaryHenselizationMap A) =
      geometricStalkStructureMap φ :=
  ordinaryHenselizationLift_comp_map (geometricStalkStructureMap φ)

end Point

variable {A S : Type u} [CommRing A] [IsLocalRing A]
  [CommRing S] [HenselianLocalRing S] (f : A →+* S) [IsLocalHom f]

/-- The ordinary-to-pointed comparison and the existing actual Henselian
target map compose to the original ordinary universal lift. -/
theorem ordinaryHenselizationToGeometricStalk_comp_toHenselian :
    (geometricStalkToHenselian f).comp
        (ordinaryHenselizationToGeometricStalk ((IsLocalRing.residue S).comp f)) =
      ordinaryHenselizationLift f := by
  let G := geometricStalk (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue S).comp f)))
  let i : ordinaryHenselization A →+* G :=
    ordinaryHenselizationToGeometricStalk ((IsLocalRing.residue S).comp f)
  let j : G →+* S := geometricStalkToHenselian f
  have : IsLocalHom i :=
    ordinaryHenselizationToGeometricStalk_isLocalHom ((IsLocalRing.residue S).comp f)
  have : IsLocalHom j := geometricStalkToHenselian_isLocalHom f
  apply ordinaryHenselizationLift_unique f (j.comp i)
  exact (RingHom.comp_assoc (ordinaryHenselizationMap A) i j).trans
    ((congrArg (fun k : A →+* G => j.comp k)
      (ordinaryHenselizationToGeometricStalk_comp_map ((IsLocalRing.residue S).comp f))).trans
        (geometricStalkToHenselian_comp_structure f))

end EtaleFundamentalGroups.StrictHenselian
