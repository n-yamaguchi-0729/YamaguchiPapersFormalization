/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.GaloisCovers.FiberQuotient
import EtaleFundamentalGroups.GeometricFiber.Functoriality

/-!
# Fundamental-group images from geometric local models

For a morphism `j : T ⟶ U`, functoriality of the geometric fiber gives the
canonical homomorphism from the fundamental group of `T` to that of `U`.
This file records its image and its finite monodromy on a pointed finite-etale
Galois cover of `U`.

The intended divisorial application takes `T` to be the generic point of a
strictly Henselian discrete valuation ring.  The definitions below do not
postulate a strict henselization or an inertia comparison: they apply to the
actual local model once it has been constructed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open CategoryTheory.PreGaloisCategory

namespace EtaleFundamentalGroups.Inertia

universe u

/-- The subgroup of the target fundamental group contributed by a geometric
source.  For the generic point of a strict-Henselian DVR this is the
corresponding divisorial inertia subgroup. -/
noncomputable def fundamentalGroupImageOfMorphism
    {T U : Scheme.{u}} {Omega : Type u}
    [Field Omega] [IsSepClosed Omega]
    (j : T ⟶ U) (xi : Spec (.of Omega) ⟶ T) :
    Subgroup π₁ᵉᵗ(xi ≫ j) :=
  (AlgebraicGeometry.FiniteEtale.fundamentalGroupHom j xi).toMonoidHom.range

/-- The finite monodromy of a pointed Galois cover after restriction to a
geometric source. -/
noncomputable def finiteEtaleGaloisCoverQuotientOfMorphism
    {T U : Scheme.{u}} [ConnectedSpace U]
    {Omega : Type u} [Field Omega] [IsSepClosed Omega]
    (j : T ⟶ U) (xi : Spec (.of Omega) ⟶ T)
    (Y : AlgebraicGeometry.FiniteEtale U) (hY : IsGalois Y)
    (y : (AlgebraicGeometry.FiniteEtale.fiber (xi ≫ j)).obj Y) :
    letI : IsGalois Y := hY
    π₁ᵉᵗ(xi) →* (Aut Y)ᵐᵒᵖ := by
  letI : IsGalois Y := hY
  exact
    (finiteEtaleGaloisCoverQuotientMonoidHom (xi ≫ j) Y hY y).comp
      (AlgebraicGeometry.FiniteEtale.fundamentalGroupHom j xi).toMonoidHom

/-- Restricting a pointed finite-cover quotient to the geometric-source
image is exactly the range of the local monodromy homomorphism. -/
theorem finiteEtaleGaloisCoverQuotient_map_fundamentalGroupImage
    {T U : Scheme.{u}} [ConnectedSpace U]
    {Omega : Type u} [Field Omega] [IsSepClosed Omega]
    (j : T ⟶ U) (xi : Spec (.of Omega) ⟶ T)
    (Y : AlgebraicGeometry.FiniteEtale U) (hY : IsGalois Y)
    (y : (AlgebraicGeometry.FiniteEtale.fiber (xi ≫ j)).obj Y) :
    letI : IsGalois Y := hY
    Subgroup.map
        (finiteEtaleGaloisCoverQuotientMonoidHom (xi ≫ j) Y hY y)
        (fundamentalGroupImageOfMorphism j xi) =
      (finiteEtaleGaloisCoverQuotientOfMorphism j xi Y hY y).range := by
  let : IsGalois Y := hY
  exact MonoidHom.map_range
    (finiteEtaleGaloisCoverQuotientMonoidHom (xi ≫ j) Y hY y)
    (AlgebraicGeometry.FiniteEtale.fundamentalGroupHom j xi).toMonoidHom

/-- The kernel of local monodromy on a pointed Galois cover is the stabilizer
of the point transported to the pulled-back cover. -/
theorem finiteEtaleGaloisCoverQuotientOfMorphism_ker
    {T U : Scheme.{u}} [ConnectedSpace U]
    {Omega : Type u} [Field Omega] [IsSepClosed Omega]
    (j : T ⟶ U) (xi : Spec (.of Omega) ⟶ T)
    (Y : AlgebraicGeometry.FiniteEtale U) (hY : IsGalois Y)
    (y : (AlgebraicGeometry.FiniteEtale.fiber (xi ≫ j)).obj Y) :
    letI : IsGalois Y := hY
    (finiteEtaleGaloisCoverQuotientOfMorphism j xi Y hY y).ker =
      MulAction.stabilizer π₁ᵉᵗ(xi)
        (transportedPointOfCompIso
          (AlgebraicGeometry.FiniteEtale.pullback j)
          (AlgebraicGeometry.FiniteEtale.pullbackFiberIso j xi) Y y) := by
  let : IsGalois Y := hY
  let h :=
    (AlgebraicGeometry.FiniteEtale.fundamentalGroupHom j xi).toMonoidHom
  let q := finiteEtaleGaloisCoverQuotientMonoidHom (xi ≫ j) Y hY y
  calc
    (finiteEtaleGaloisCoverQuotientOfMorphism j xi Y hY y).ker =
        Subgroup.comap h q.ker := rfl
    _ = Subgroup.comap h (MulAction.stabilizer π₁ᵉᵗ(xi ≫ j) y) := by
      rw [finiteEtaleGaloisCoverQuotientMonoidHom_ker]
    _ = MulAction.stabilizer π₁ᵉᵗ(xi)
        (transportedPointOfCompIso
          (AlgebraicGeometry.FiniteEtale.pullback j)
          (AlgebraicGeometry.FiniteEtale.pullbackFiberIso j xi) Y y) := by
      exact (stabilizer_transportedPointOfCompIso
        (AlgebraicGeometry.FiniteEtale.pullback j)
        (AlgebraicGeometry.FiniteEtale.pullbackFiberIso j xi) Y y).symm

end EtaleFundamentalGroups.Inertia
