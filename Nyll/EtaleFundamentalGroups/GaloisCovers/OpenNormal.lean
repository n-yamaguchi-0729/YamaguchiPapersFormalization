/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.GaloisCovers.Basic
import Nyll.EtaleFundamentalGroups.GaloisCategories.ConnectedActions
import Mathlib.CategoryTheory.Galois.Equivalence
import Nyll.ProCGroups.ProC.OpenNormalSubgroups.Basic

/-!
# Galois objects attached to open normal subgroups

This file packages the normal-subgroup part of the fundamental equivalence
between a Galois category and finite continuous actions of its fundamental
group.
-/

noncomputable section

open CategoryTheory

namespace CategoryTheory.PreGaloisCategory

universe u₁ u₂

variable {C : Type u₁} [Category.{u₂} C] [GaloisCategory C]
variable (F : C ⥤ FintypeCat.{u₁}) [FiberFunctor F]

private def quotientRightIso
    (N : Subgroup (Aut F)) [N.Normal]
    [Fintype (Aut F ⧸ N)] (g : Aut F) :
    (Aut F ⧸ₐ N) ≅ (Aut F ⧸ₐ N) where
  hom := Action.FintypeCat.toEndHom N g
  inv := Action.FintypeCat.toEndHom N g⁻¹
  hom_inv_id := by
    apply Action.hom_ext
    ext q
    induction q using Quotient.inductionOn with
    | _ q =>
        change (⟦q * g⁻¹ * (g⁻¹)⁻¹⟧ : Aut F ⧸ N) = ⟦q⟧
        rw [mul_inv_cancel_right]
  inv_hom_id := by
    apply Action.hom_ext
    ext q
    induction q using Quotient.inductionOn with
    | _ q =>
        change (⟦q * g * g⁻¹⟧ : Aut F ⧸ N) = ⟦q⟧
        rw [mul_inv_cancel_right]

/-- An object whose canonical fundamental-group action is an open-normal
quotient is a Galois object. -/
theorem isGalois_of_fiber_iso_quotient_openNormal
    (U : OpenNormalSubgroup (Aut F)) (X : C)
    (e : (functorToAction F).obj X ≅
      Aut F ⧸ₐ (U : Subgroup (Aut F))) :
    IsGalois X := by
  let : Fintype (Aut F ⧸ (U : Subgroup (Aut F))) :=
    Fintype.ofFinite _
  let ef : F.obj X ≅
      FintypeCat.of (Aut F ⧸ (U : Subgroup (Aut F))) :=
    (forget₂ (Action FintypeCat (Aut F)) FintypeCat).mapIso e
  let : Nonempty (F.obj X) := by
    let q : Aut F ⧸ (U : Subgroup (Aut F)) := 1
    exact ⟨ef.inv q⟩
  let : MulAction.IsPretransitive (Aut F) (F.obj X) := by
    constructor
    intro x y
    let qx : Aut F ⧸ (U : Subgroup (Aut F)) := ef.hom x
    let qy : Aut F ⧸ (U : Subgroup (Aut F)) := ef.hom y
    obtain ⟨a, ha⟩ := Quotient.exists_rep qx
    obtain ⟨b, hb⟩ := Quotient.exists_rep qy
    refine ⟨b * a⁻¹, ?_⟩
    apply (ConcreteCategory.bijective_of_isIso ef.hom).injective
    have hx : ef.hom ((b * a⁻¹) • x) =
        (b * a⁻¹) • ef.hom x := by
      exact ConcreteCategory.congr_hom (e.hom.comm (b * a⁻¹)) x
    rw [hx]
    change (b * a⁻¹) • qx = qy
    rw [← ha, ← hb]
    change (⟦(b * a⁻¹) * a⟧ : Aut F ⧸ (U : Subgroup (Aut F))) = ⟦b⟧
    rw [inv_mul_cancel_right]
  let : IsConnected X :=
    FiberFunctor.isConnected_of_isPretransitive F X
  apply (isGalois_iff_pretransitive F X).mpr
  constructor
  intro x y
  let qx : Aut F ⧸ (U : Subgroup (Aut F)) := ef.hom x
  let qy : Aut F ⧸ (U : Subgroup (Aut F)) := ef.hom y
  obtain ⟨a, ha⟩ := Quotient.exists_rep qx
  obtain ⟨b, hb⟩ := Quotient.exists_rep qy
  let r := quotientRightIso F (U : Subgroup (Aut F)) (b⁻¹ * a)
  let s : (functorToAction F).obj X ≅ (functorToAction F).obj X :=
    e ≪≫ r ≪≫ e.symm
  let φ : X ≅ X := (functorToAction F).preimageIso s
  refine ⟨φ, ?_⟩
  apply (ConcreteCategory.bijective_of_isIso ef.hom).injective
  change ef.hom (F.map φ.hom x) = ef.hom y
  have hmap : (functorToAction F).map φ.hom = s.hom := by
    exact (functorToAction F).map_preimage s.hom
  have happ : F.map φ.hom x = s.hom.hom x := by
    exact ConcreteCategory.congr_hom
      (congrArg Action.Hom.hom hmap) x
  rw [happ]
  have hs : ef.hom (s.hom.hom x) = r.hom.hom (ef.hom x) := by
    change ef.hom (ef.inv (r.hom.hom (ef.hom x))) =
      r.hom.hom (ef.hom x)
    exact FintypeCat.inv_hom_id_apply ef _
  rw [hs]
  change r.hom.hom qx = qy
  rw [← ha, ← hb]
  change (⟦a * (b⁻¹ * a)⁻¹⟧ :
    Aut F ⧸ (U : Subgroup (Aut F))) = ⟦b⟧
  rw [mul_inv_rev, inv_inv, mul_inv_cancel_left]

/-- Every open normal subgroup of the fundamental group of a Galois category
is represented by a Galois object whose fiber is the corresponding quotient
action. -/
theorem exists_galois_object_fiber_iso_quotient
    (U : OpenNormalSubgroup (Aut F)) :
    ∃ (X : C) (hX : IsGalois X),
      letI := hX
      Nonempty ((functorToAction F).obj X ≅
        Aut F ⧸ₐ (U : Subgroup (Aut F))) := by
  let : Fintype (Aut F ⧸ (U : Subgroup (Aut F))) :=
    Fintype.ofFinite _
  let V : OpenSubgroup (Aut F) := U.toOpenSubgroup
  obtain ⟨X, ⟨e⟩⟩ :=
    exists_lift_of_quotient_openSubgroup (F := F) V
  have hX : IsGalois X :=
    isGalois_of_fiber_iso_quotient_openNormal F U X e
  exact ⟨X, hX, ⟨e⟩⟩

/-- Every open normal subgroup is the stabilizer of a point on the fiber of
a Galois object.  The point is the inverse image of the identity coset under
the quotient-action presentation of the fiber. -/
theorem exists_galois_object_point_stabilizer_eq
    (U : OpenNormalSubgroup (Aut F)) :
    ∃ (X : C) (_ : IsGalois X) (x : F.obj X),
      MulAction.stabilizer (Aut F) x = (U : Subgroup (Aut F)) := by
  obtain ⟨X, hX, he⟩ := exists_galois_object_fiber_iso_quotient F U
  let : IsGalois X := hX
  obtain ⟨e⟩ := he
  let ef : F.obj X ≅ FintypeCat.of (Aut F ⧸ (U : Subgroup (Aut F))) :=
    (forget₂ (Action FintypeCat (Aut F)) FintypeCat).mapIso e
  let q := QuotientGroup.mk' (U : Subgroup (Aut F)) (1 : Aut F)
  let x : F.obj X := ef.inv q
  refine ⟨X, hX, x, ?_⟩
  ext g
  change g • x = x ↔ g ∈ (U : Subgroup (Aut F))
  rw [← MulAction.mem_stabilizer_iff]
  rw [← MulAction.stabilizer_quotient (U : Subgroup (Aut F))]
  change g • x = x ↔ g • q = q
  constructor
  · intro hg
    calc
      g • q = g • ef.hom x := by
        rw [FintypeCat.inv_hom_id_apply]
      _ = ef.hom (g • x) :=
        (ConcreteCategory.congr_hom (e.hom.comm g) x).symm
      _ = ef.hom x := congrArg ef.hom.hom hg
      _ = q := FintypeCat.inv_hom_id_apply ef q
  · intro hg
    apply (ConcreteCategory.bijective_of_isIso ef.hom).injective
    calc
      ef.hom (g • x) = g • ef.hom x :=
        ConcreteCategory.congr_hom (e.hom.comm g) x
      _ = g • q := by rw [FintypeCat.inv_hom_id_apply]
      _ = q := hg
      _ = ef.hom x := (FintypeCat.inv_hom_id_apply ef q).symm

end CategoryTheory.PreGaloisCategory
