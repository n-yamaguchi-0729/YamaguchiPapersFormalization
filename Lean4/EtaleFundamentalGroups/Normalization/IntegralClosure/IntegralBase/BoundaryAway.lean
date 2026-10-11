/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SchemeTheory.Normalization.IntegralClosure.IntegralBase.Equiv
import EtaleFundamentalGroups.Normalization.IntegralClosure.BoundaryAwayFieldEquiv

/-!
# Boundary-away transport through a finite integral base

For a finite base enlargement inside one field, the two integral closures
are canonically equivalent.  Localizing that equivalence at a primitive
element transports etaleness of the literal away map to the normalization
over the enlarged base.
-/

noncomputable section

namespace EtaleFundamentalGroups

universe uA uB uL

/-- The primitive away property of a normalization is unchanged after a
finite integral enlargement of the base inside the same ambient field. -/
theorem integralClosure_integralBase_boundaryAway
    {A : Type uA} {B : Type uB} {L : Type uL}
    [CommRing A] [CommRing B] [Field L]
    [Algebra A B] [Module.Finite A B]
    [Algebra A L] [Algebra B L] [IsScalarTower A B L]
    (f : A)
    (hAway :
      (Localization.awayMap
        (algebraMap A (integralClosure A L)) f).Etale) :
    (Localization.awayMap
      (algebraMap A (integralClosure B L)) f).Etale := by
  let C := integralClosure A L
  let E := integralClosure B L
  let S := Localization.Away f
  let T := Localization.Away (algebraMap A C f)
  let U := Localization.Away (algebraMap A E f)
  let : Algebra B C := integralClosureIntegralBaseAlgebra
  let : IsScalarTower A B C :=
    integralClosureIntegralBase_isScalarTower
  let eB : E ≃ₐ[B] C := integralClosureIntegralBaseAlgEquiv
  let eA : E ≃ₐ[A] C := eB.restrictScalars A
  have hPowers :
      Submonoid.map eA
          (Submonoid.powers (algebraMap A E f)) =
        Submonoid.powers (algebraMap A C f) := by
    rw [Submonoid.map_powers]
    congr 1
    exact eA.commutes f
  let eLocA : U ≃ₐ[A] T :=
    IsLocalization.algEquivOfAlgEquiv U T eA hPowers
  let mapST : S →+* T := Localization.awayMap (algebraMap A C) f
  let mapSU : S →+* U := Localization.awayMap (algebraMap A E) f
  let : Algebra S T := mapST.toAlgebra
  let : Algebra S U := mapSU.toAlgebra
  let eLocS : U ≃ₐ[S] T :=
    { toRingEquiv := eLocA.toRingEquiv
      commutes' := fun z ↦ by
        apply DFunLike.congr_fun (f :=
            eLocA.toRingHom.comp (algebraMap S U))
          (g := algebraMap S T) ?_ z
        apply IsLocalization.ringHom_ext (Submonoid.powers f)
        ext a
        simp only [RingHom.comp_apply]
        change eLocA (mapSU (algebraMap A S a)) =
          mapST (algebraMap A S a)
        rw [show mapSU (algebraMap A S a) =
            algebraMap E U (algebraMap A E a) by
          exact IsLocalization.map_eq _ a]
        rw [IsLocalization.algEquivOfAlgEquiv_eq]
        rw [show mapST (algebraMap A S a) =
            algebraMap C T (algebraMap A C a) by
          exact IsLocalization.map_eq _ a]
        rw [eA.commutes] }
  let : Algebra.Etale S T := hAway.toAlgebra
  exact (show Algebra.Etale S U from Algebra.Etale.of_equiv eLocS.symm)

/-- Map-explicit form of integral-base boundary-away transport: the target
map is the literal composite through the enlarged base. -/
theorem integralClosure_integralBase_boundaryAway_comp
    {A : Type uA} {B : Type uB} {L : Type uL}
    [CommRing A] [CommRing B] [Field L]
    [Algebra A B] [Module.Finite A B]
    [Algebra A L] [Algebra B L] [IsScalarTower A B L]
    (f : A)
    (hAway :
      (Localization.awayMap
        (algebraMap A (integralClosure A L)) f).Etale) :
    (Localization.awayMap
      ((algebraMap B (integralClosure B L)).comp (algebraMap A B))
      f).Etale := by
  have h := integralClosure_integralBase_boundaryAway
    (A := A) (B := B) (L := L) f hAway
  have hmap :
      (algebraMap B (integralClosure B L)).comp (algebraMap A B) =
        algebraMap A (integralClosure B L) := by
    ext a
    exact (IsScalarTower.algebraMap_apply A B L a).symm
  rw [hmap]
  exact h

/-- A sourced comparison of ambient fields followed by a finite integral
base enlargement preserves the primitive boundary-away map. -/
theorem
    integralClosure_integralBase_boundaryAway_of_bijective_fieldTower_algebraMap
    {A : Type uA} {B : Type uB}
    {Omega : Type uL} {P : Type*}
    [CommRing A] [CommRing B] [Field Omega] [Field P]
    [Algebra A Omega]
    [Algebra Omega P] [Algebra A P] [IsScalarTower A Omega P]
    [Algebra A B] [Module.Finite A B]
    [Algebra B P] [IsScalarTower A B P]
    (hbij : Function.Bijective (algebraMap Omega P))
    (f : A)
    (hAway :
      (Localization.awayMap
        (algebraMap A (integralClosure A Omega)) f).Etale) :
    (Localization.awayMap
      (algebraMap A (integralClosure B P)) f).Etale := by
  have hAwayP :
      (Localization.awayMap
        (algebraMap A (integralClosure A P)) f).Etale :=
    integralClosure_boundaryAway_of_bijective_fieldTower_algebraMap
      (A := A) hbij f hAway
  exact integralClosure_integralBase_boundaryAway
    (A := A) (B := B) (L := P) f hAwayP

/-- Map-explicit form of the preceding transport: the target map is written
as the literal composite through the finite integral base. -/
theorem
    integralClosure_integralBase_boundaryAway_comp_of_bijective_fieldTower_algebraMap
    {A : Type uA} {B : Type uB}
    {Omega : Type uL} {P : Type*}
    [CommRing A] [CommRing B] [Field Omega] [Field P]
    [Algebra A Omega]
    [Algebra Omega P] [Algebra A P] [IsScalarTower A Omega P]
    [Algebra A B] [Module.Finite A B]
    [Algebra B P] [IsScalarTower A B P]
    (hbij : Function.Bijective (algebraMap Omega P))
    (f : A)
    (hAway :
      (Localization.awayMap
        (algebraMap A (integralClosure A Omega)) f).Etale) :
    (Localization.awayMap
      ((algebraMap B (integralClosure B P)).comp (algebraMap A B))
      f).Etale := by
  have h :=
    integralClosure_integralBase_boundaryAway_of_bijective_fieldTower_algebraMap
      (A := A) (B := B) (Omega := Omega) (P := P)
      hbij f hAway
  have hmap :
      (algebraMap B (integralClosure B P)).comp (algebraMap A B) =
        algebraMap A (integralClosure B P) := by
    ext a
    exact (IsScalarTower.algebraMap_apply A B P a).symm
  rw [hmap]
  exact h

end EtaleFundamentalGroups

end
