/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_CurveModel_ffEquiv_symm_germToFunctionField_mem_and_sub_algebraMap_appLE_mem_nonunits_pointEquivPlace.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Models.Basic

/-!
# Curve Model ff Equiv symm germ To Function Field mem and sub algebra Map app LE mem
nonunits point Equiv Place
-/

section ProofImplementation

namespace AlgebraicCurves.Models.Proofs.GermsAtPointPlace

open CategoryTheory AlgebraicGeometry

universe u v

namespace P2mValueAtPoint

open AlgebraicCurve IsLocalRing

variable {K : Type u} [Field K] [IsAlgClosed K] {L : Type v} [Field L] [Algebra K L]

theorem base_closedPoint_eq (M : CurveModel K L)
    (z : {q : Spec (CommRingCat.of K) ⟶ M.C // q ≫ M.toBase = 𝟙 _}) :
    z.1.base (closedPoint K) = (pointEquivClosedPoint M.toBase z).1 :=
  (pointEquivClosedPoint_apply_coe M.toBase z).symm

/--
Map the local ring at a point into the modelled function field using the inverse field
equivalence.
-/
noncomputable def theta (M : CurveModel K L) (x : M.C) : M.C.presheaf.stalk x →+* L :=
  (M.ffEquiv.symm : M.C.functionField ≃+* L).toRingHom.comp
    (algebraMap (M.C.presheaf.stalk x) M.C.functionField)
omit [IsAlgClosed K] in
theorem theta_germ (M : CurveModel K L) (U : M.C.Opens) [Nonempty (Scheme.Opens.toScheme U)]
    (x : M.C) (hx : x ∈ U) (s : Γ(M.C, U)) :
    theta M x ((M.C.presheaf.germ U x hx).hom s) = M.ffEquiv.symm ((M.C.germToFunctionField U).hom
      s) := by
  unfold theta
  simp only [RingHom.coe_comp, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, Function.comp_apply]
  congr 1
  rw [RingHom.algebraMap_toAlgebra]
  exact TopCat.Presheaf.germ_stalkSpecializes_apply _ _ _ _
omit [IsAlgClosed K] in
theorem range_theta (M : CurveModel K L) (x : closedPoints M.C) :
    (theta M x.1).range = (M.placeOfPoint x).toValuationSubring.toSubring :=
  M.range_stalk_eq x
omit [IsAlgClosed K] in
theorem theta_mem_nonunits (M : CurveModel K L) (x : closedPoints M.C)
    (g : M.C.presheaf.stalk x.1) (hg : ¬ IsUnit g) :
    theta M x.1 g ∈ (M.placeOfPoint x).toValuationSubring.nonunits := by
  set P := M.placeOfPoint x
  have hrange := range_theta M x
  have hmem : ∀ t, theta M x.1 t ∈ P.toValuationSubring := fun t => by
    have : theta M x.1 t ∈ (theta M x.1).range := ⟨t, rfl⟩
    rw [hrange] at this
    exact this
  let θ' : M.C.presheaf.stalk x.1 →+* P.toValuationSubring :=
    (theta M x.1).codRestrict P.toValuationSubring.toSubring hmem
  have hsurj : Function.Surjective θ' := by
    intro a
    have ha : (a : L) ∈ (theta M x.1).range := by rw [hrange]; exact a.2
    obtain ⟨t, ht⟩ := ha
    exact ⟨t, Subtype.ext ht⟩
  have : IsLocalHom θ' := IsLocalHom.of_surjective θ' hsurj
  have hnu : ¬ IsUnit (θ' g) := fun h => hg (isUnit_of_map_unit θ' g h)
  rw [ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal]
  exact ⟨hmem g, (IsLocalRing.mem_maximalIdeal _).mpr hnu⟩

/-- The section obtained by pulling back a base-field constant to the chosen open set. -/
noncomputable def constSec (M : CurveModel K L) (c : K) (U : M.C.Opens) : Γ(M.C, U) :=
  (M.toBase.appLE ⊤ U le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv c)
omit [IsAlgClosed K] in
theorem germToFunctionField_constSec (M : CurveModel K L) (c : K) (U : M.C.Opens)
    [Nonempty (Scheme.Opens.toScheme U)] :
    (M.C.germToFunctionField U).hom (constSec M c U) = M.ffEquiv (algebraMap K L c) := by
  let A : CommRingCat.{u} := Γ(Spec (CommRingCat.of K), ⊤)
  let B : CommRingCat.{u} := Γ(M.C, U)
  let α : A ⟶ B := M.toBase.appLE ⊤ U le_top
  let β : B ⟶ M.C.functionField := M.C.germToFunctionField U
  have happ : α = M.toBase.appTop ≫ M.C.presheaf.map
      (homOfLE (le_top : U ≤ ⊤)).op := rfl
  have hres : M.C.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op ≫ β =
      M.C.presheaf.germ ⊤ (genericPoint M.C) trivial :=
    TopCat.Presheaf.germ_res M.C.presheaf (homOfLE le_top) (genericPoint M.C) _
  have hmap : α ≫ β = M.toBase.appTop ≫
      M.C.presheaf.germ ⊤ (genericPoint M.C) trivial :=
    (eq_whisker happ β).trans ((Category.assoc _ _ _).trans
      (whisker_eq M.toBase.appTop hres))
  rw [M.ffEquiv_algebraMap]
  exact congrArg (fun f : A ⟶ M.C.functionField =>
    f.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom c)) hmap
omit [IsAlgClosed K] in
theorem appLE_constSec (M : CurveModel K L) (c : K) (U : M.C.Opens)
    (z : {q : Spec (CommRingCat.of K) ⟶ M.C // q ≫ M.toBase = 𝟙 _}) (hz : ⊤ ≤ z.1 ⁻¹ᵁ U) :
    (z.1.appLE U ⊤ hz).hom (constSec M c U) = (Scheme.ΓSpecIso (CommRingCat.of K)).inv c := by
  let S : Scheme.{u} := Spec (CommRingCat.of K)
  let A : CommRingCat.{u} := Γ(S, ⊤)
  let B : CommRingCat.{u} := Γ(M.C, U)
  let α : A ⟶ B := M.toBase.appLE ⊤ U le_top
  let β : B ⟶ A := z.1.appLE U ⊤ hz
  have hcomp : α ≫ β = (z.1 ≫ M.toBase).appLE ⊤ ⊤ le_top :=
    Scheme.Hom.appLE_comp_appLE z.1 M.toBase ⊤ U ⊤ le_top hz
  have htop : (z.1 ≫ M.toBase).appLE ⊤ ⊤ le_top = 𝟙 A := by
    have heq := congrArg (fun f : S ⟶ S => f.appLE ⊤ ⊤ le_top) z.2
    exact heq.trans ((Scheme.Hom.appLE_eq_app (𝟙 S)).trans
      (Scheme.Hom.id_app (X := S) ⊤))
  exact congrArg (fun f : A ⟶ A =>
    f.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom c)) (hcomp.trans htop)

theorem main (M : CurveModel K L) (U : M.C.Opens) [Nonempty (Scheme.Opens.toScheme U)] (s : Γ(M.C,
  U))
    (z : {q : Spec (CommRingCat.of K) ⟶ M.C // q ≫ M.toBase = 𝟙 _}) (hz : ⊤ ≤ z.1 ⁻¹ᵁ U) :
    M.ffEquiv.symm ((M.C.germToFunctionField U).hom s) ∈ (M.pointEquivPlace z).toValuationSubring ∧
    M.ffEquiv.symm ((M.C.germToFunctionField U).hom s) -
        algebraMap K L ((Scheme.ΓSpecIso (CommRingCat.of K)).hom ((z.1.appLE U ⊤ hz).hom s)) ∈
      (M.pointEquivPlace z).toValuationSubring.nonunits := by
  set x : closedPoints M.C := pointEquivClosedPoint M.toBase z with hxdef
  have hxz : z.1.base (closedPoint K) = x.1 := base_closedPoint_eq M z
  have hxU : x.1 ∈ U := by
    rw [← hxz]
    exact hz (Set.mem_univ (closedPoint K))
  have hP : M.pointEquivPlace z = M.placeOfPoint x := M.pointEquivPlace_apply z
  rw [hP]
  refine ⟨?_, ?_⟩
  · have h1 : M.ffEquiv.symm ((M.C.germToFunctionField U).hom s) = theta M x.1 ((M.C.presheaf.germ
      U x.1 hxU).hom s) :=
      (theta_germ M U x.1 hxU s).symm
    rw [h1]
    have : theta M x.1 ((M.C.presheaf.germ U x.1 hxU).hom s) ∈ (theta M x.1).range := ⟨_, rfl⟩
    rw [range_theta M x] at this
    exact this
  · set c : K := (Scheme.ΓSpecIso (CommRingCat.of K)).hom ((z.1.appLE U ⊤ hz).hom s) with hc
    have hconst : algebraMap K L c = M.ffEquiv.symm ((M.C.germToFunctionField U).hom (constSec M c
      U)) := by
      rw [germToFunctionField_constSec, RingEquiv.symm_apply_apply]
    rw [hconst, ← map_sub, ← map_sub, ← theta_germ M U x.1 hxU]
    refine theta_mem_nonunits M x _ ?_
    intro hunit
    have hmem : x.1 ∈ M.C.basicOpen (s - constSec M c U) := (M.C.mem_basicOpen _ _ hxU).mpr hunit
    have hz0 : (z.1.appLE U ⊤ hz).hom (s - constSec M c U) = 0 := by
      rw [map_sub, appLE_constSec, hc, Iso.hom_inv_id_apply, sub_self]
    have hbo : (Spec (CommRingCat.of K)).basicOpen ((z.1.appLE U ⊤ hz).hom (s - constSec M c U)) =
        ⊤ ⊓ z.1 ⁻¹ᵁ M.C.basicOpen (s - constSec M c U) := Scheme.basicOpen_appLE _ _ _ _ _
    rw [hz0, Scheme.basicOpen_zero] at hbo
    have hpt : closedPoint K ∈ (⊤ ⊓ z.1 ⁻¹ᵁ M.C.basicOpen (s - constSec M c U) : (Spec
      (CommRingCat.of K)).Opens) := by
      refine ⟨Set.mem_univ _, ?_⟩
      change z.1.base (closedPoint K) ∈ M.C.basicOpen (s - constSec M c U)
      rw [hxz]
      exact hmem
    rw [← hbo] at hpt
    exact hpt

end P2mValueAtPoint
end AlgebraicCurves.Models.Proofs.GermsAtPointPlace

namespace AlgebraicCurve.CurveModel

open _root_.AlgebraicCurves.Models.Proofs.GermsAtPointPlace
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u v


open _root_.AlgebraicCurve in
theorem ffEquiv_symm_germToFunctionField_mem_and_sub_algebraMap_appLE_mem_nonunits_pointEquivPlace
    {K : Type u} [Field K] [IsAlgClosed K] {L : Type v} [Field L] [Algebra K L]
    (M : CurveModel K L) (U : M.C.Opens) [Nonempty (Scheme.Opens.toScheme U)] (s : Γ(M.C, U))
    (z : {q : Spec (CommRingCat.of K) ⟶ M.C // q ≫ M.toBase = 𝟙 _}) (hz : ⊤ ≤ z.1 ⁻¹ᵁ U) :
    M.ffEquiv.symm (M.C.germToFunctionField U s) ∈ (M.pointEquivPlace z).toValuationSubring ∧
    M.ffEquiv.symm (M.C.germToFunctionField U s) -
        algebraMap K L ((Scheme.ΓSpecIso (CommRingCat.of K)).hom (z.1.appLE U ⊤ hz s)) ∈
      (M.pointEquivPlace z).toValuationSubring.nonunits :=
  P2mValueAtPoint.main M U s z hz
end AlgebraicCurve.CurveModel
end ProofImplementation
