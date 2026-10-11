/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.DivisorialStrictHenselian
import Mathlib.GroupTheory.Coset.Card

/-!
# Coprimality transfer for divisorial finite images

The image of a geometric local fundamental group in a pointed finite Galois
quotient is a finite subgroup of the deck group.  Its order therefore divides
the deck-group order, and more sharply divides the order of every subgroup
which contains that image.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open CategoryTheory.PreGaloisCategory

namespace EtaleFundamentalGroups.Inertia

universe u

/-- The finite monodromy image contributed by a geometric source has order
dividing the automorphism-group order of the pointed Galois cover. -/
theorem finiteEtaleGaloisCoverQuotient_map_fundamentalGroupImage_natCard_dvd_aut
    {T U : Scheme.{u}} [ConnectedSpace U]
    {Omega : Type u} [Field Omega] [IsSepClosed Omega]
    (j : T ⟶ U) (xi : Spec (.of Omega) ⟶ T)
    (Y : FiniteEtale U) (hY : IsGalois Y)
    (y : (FiniteEtale.fiber (xi ≫ j)).obj Y) :
    letI : IsGalois Y := hY
    Nat.card
        (Subgroup.map
          (finiteEtaleGaloisCoverQuotientMonoidHom
            (xi ≫ j) Y hY y)
          (fundamentalGroupImageOfMorphism j xi)) ∣
      Nat.card (Aut Y) := by
  let : IsGalois Y := hY
  rw [finiteEtaleGaloisCoverQuotient_map_fundamentalGroupImage]
  calc
    Nat.card
          (finiteEtaleGaloisCoverQuotientOfMorphism
            j xi Y hY y).range ∣
        Nat.card ((Aut Y)ᵐᵒᵖ) :=
      Subgroup.card_subgroup_dvd_card
        (finiteEtaleGaloisCoverQuotientOfMorphism j xi Y hY y).range
    _ = Nat.card (Aut Y) :=
      Nat.card_congr MulOpposite.opEquiv.symm

/-- If the geometric-source finite image lies in a specified subgroup of the
deck group, its order divides the order of that subgroup. -/
theorem finiteEtaleGaloisCoverQuotient_map_fundamentalGroupImage_natCard_dvd_of_le
    {T U : Scheme.{u}} [ConnectedSpace U]
    {Omega : Type u} [Field Omega] [IsSepClosed Omega]
    (j : T ⟶ U) (xi : Spec (.of Omega) ⟶ T)
    (Y : FiniteEtale U) (hY : IsGalois Y)
    (y : (FiniteEtale.fiber (xi ≫ j)).obj Y)
    (H : Subgroup (Aut Y)ᵐᵒᵖ)
    (himage :
      Subgroup.map
          (finiteEtaleGaloisCoverQuotientMonoidHom
            (xi ≫ j) Y hY y)
          (fundamentalGroupImageOfMorphism j xi) ≤ H) :
    letI : IsGalois Y := hY
    Nat.card
        (Subgroup.map
          (finiteEtaleGaloisCoverQuotientMonoidHom
            (xi ≫ j) Y hY y)
          (fundamentalGroupImageOfMorphism j xi)) ∣
      Nat.card H := by
  let : IsGalois Y := hY
  exact Subgroup.card_dvd_of_le himage

/-- Coprimality of a containing finite subgroup descends to the geometric
local monodromy image. -/
theorem finiteEtaleGaloisCoverQuotient_map_fundamentalGroupImage_coprime_of_le
    {T U : Scheme.{u}} [ConnectedSpace U]
    {Omega : Type u} [Field Omega] [IsSepClosed Omega]
    (j : T ⟶ U) (xi : Spec (.of Omega) ⟶ T)
    (Y : FiniteEtale U) (hY : IsGalois Y)
    (y : (FiniteEtale.fiber (xi ≫ j)).obj Y)
    (H : Subgroup (Aut Y)ᵐᵒᵖ)
    (himage :
      Subgroup.map
          (finiteEtaleGaloisCoverQuotientMonoidHom
            (xi ≫ j) Y hY y)
          (fundamentalGroupImageOfMorphism j xi) ≤ H)
    (p : ℕ) (hcoprime : Nat.Coprime (Nat.card H) p) :
    letI : IsGalois Y := hY
    Nat.Coprime
      (Nat.card
        (Subgroup.map
          (finiteEtaleGaloisCoverQuotientMonoidHom
            (xi ≫ j) Y hY y)
          (fundamentalGroupImageOfMorphism j xi))) p := by
  let : IsGalois Y := hY
  exact hcoprime.of_dvd_left
    (finiteEtaleGaloisCoverQuotient_map_fundamentalGroupImage_natCard_dvd_of_le
      j xi Y hY y H himage)

/-- In particular, coprimality of the whole component deck group descends to
the geometric local monodromy image. -/
theorem finiteEtaleGaloisCoverQuotient_map_fundamentalGroupImage_coprime_of_aut
    {T U : Scheme.{u}} [ConnectedSpace U]
    {Omega : Type u} [Field Omega] [IsSepClosed Omega]
    (j : T ⟶ U) (xi : Spec (.of Omega) ⟶ T)
    (Y : FiniteEtale U) (hY : IsGalois Y)
    (y : (FiniteEtale.fiber (xi ≫ j)).obj Y)
    (p : ℕ) (hcoprime : Nat.Coprime (Nat.card (Aut Y)) p) :
    letI : IsGalois Y := hY
    Nat.Coprime
      (Nat.card
        (Subgroup.map
          (finiteEtaleGaloisCoverQuotientMonoidHom
            (xi ≫ j) Y hY y)
          (fundamentalGroupImageOfMorphism j xi))) p := by
  let : IsGalois Y := hY
  exact hcoprime.of_dvd_left
    (finiteEtaleGaloisCoverQuotient_map_fundamentalGroupImage_natCard_dvd_aut
      j xi Y hY y)

end EtaleFundamentalGroups.Inertia

end
