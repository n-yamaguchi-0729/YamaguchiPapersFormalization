/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_eq_of_section_of_base_closedPoint_eq_of_ker_stalkMap_le.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Stalk

/-!
# eq of section of base closed Point eq of ker stalk Map le
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs
namespace eq_of_section_of_base_closedPoint_eq_of_ker_stalkMap_le

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Topology

namespace B12C5

theorem presheaf_map_eqToHom_op_apply {X : Scheme.{u}} {U V : X.Opens} (h : U = V)
    (t : Γ(X, V)) : (X.presheaf.map (eqToHom h).op).hom t = cast (by rw [h]) t := by
  subst h; simp

variable {A : Type u} [CommRing A] [IsLocalRing A] {X : Scheme.{u}} (c : X ⟶ Spec (CommRingCat.of
  A))

/-- The global section obtained by pulling back an element of the base ring. -/
noncomputable def const (a : A) : Γ(X, ⊤) := (c.appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of
  A)).inv.hom a)
omit [IsLocalRing A] in
theorem app_top_const (σ : Spec (CommRingCat.of A) ⟶ X) (hσ : σ ≫ c = 𝟙 _) (a : A) :
    (σ.app ⊤).hom (const c a) = (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a := by
  have h1 := Scheme.Hom.congr_app hσ ⊤
  rw [Scheme.Hom.comp_app, Scheme.Hom.id_app] at h1
  change ((c.app ⊤ ≫ σ.app (c ⁻¹ᵁ ⊤))).hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a) = _
  rw [h1]
  erw [Category.id_comp]
  erw [presheaf_map_eqToHom_op_apply]

theorem stalkClosedPointTo_germ_const (σ : Spec (CommRingCat.of A) ⟶ X) (hσ : σ ≫ c = 𝟙 _) (a : A)
    (U : X.Opens) (hU : σ.base (IsLocalRing.closedPoint A) ∈ U) :
    (Scheme.stalkClosedPointTo σ).hom
      ((X.presheaf.germ U (σ.base (IsLocalRing.closedPoint A)) hU).hom
        ((X.presheaf.map (homOfLE (le_top (a := U))).op).hom (const c a))) = a := by
  rw [← CommRingCat.comp_apply (X.presheaf.map _), TopCat.Presheaf.germ_res]
  let p : Spec (CommRingCat.of A) := IsLocalRing.closedPoint A
  have htop : σ p ∈ (⊤ : X.Opens) := trivial
  have hmap : X.presheaf.germ ⊤ (σ p) htop ≫ σ.stalkMap p =
      σ.appTop ≫ (Spec (CommRingCat.of A)).presheaf.germ ⊤ p trivial :=
    σ.germ_stalkMap ⊤ p htop
  have h : X.presheaf.germ ⊤ (σ p) htop ≫ Scheme.stalkClosedPointTo σ =
      σ.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of A)).hom := by
    calc
      X.presheaf.germ ⊤ (σ p) htop ≫ Scheme.stalkClosedPointTo σ =
          (X.presheaf.germ ⊤ (σ p) htop ≫ σ.stalkMap p) ≫
            (stalkClosedPointIso (CommRingCat.of A)).hom :=
        (Category.assoc _ _ _).symm
      _ = (σ.appTop ≫ (Spec (CommRingCat.of A)).presheaf.germ ⊤ p trivial) ≫
          (stalkClosedPointIso (CommRingCat.of A)).hom :=
        congrArg (fun g : Γ(X, ⊤) ⟶ (Spec (CommRingCat.of A)).presheaf.stalk p =>
          g ≫ (stalkClosedPointIso (CommRingCat.of A)).hom) hmap
      _ = σ.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of A)).hom := by
        rw [Category.assoc]
        exact congrArg (fun g : Γ(Spec (CommRingCat.of A), ⊤) ⟶ CommRingCat.of A =>
          σ.appTop ≫ g) (germ_stalkClosedPointIso_hom (CommRingCat.of A))
  have hsections : c.appTop ≫ σ.appTop = 𝟙 (Γ(Spec (CommRingCat.of A), ⊤)) :=
    (Scheme.Hom.comp_appTop σ c).symm.trans
      ((congrArg (fun f : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of A) => f.appTop) hσ).trans
        Scheme.Hom.id_appTop)
  have hconst := congrArg (fun g : Γ(Spec (CommRingCat.of A), ⊤) ⟶ Γ(Spec (CommRingCat.of A), ⊤) =>
    g.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)) hsections
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_id, RingHom.id_apply]
    at hconst
  have h' := congrArg (fun g : Γ(X, ⊤) ⟶ CommRingCat.of A => g.hom (const c a)) h
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h'
  change (Scheme.stalkClosedPointTo σ).hom
    ((X.presheaf.germ ⊤ (σ p) htop).hom (const c a)) = a
  have hi : (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a) = a :=
    congrArg (fun g : CommRingCat.of A ⟶ CommRingCat.of A => g.hom a)
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv_hom_id
  exact h'.trans ((congrArg ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom) hconst).trans hi)
omit [IsLocalRing A] in
theorem stalkClosedPointTo_apply [IsLocalRing A] (σ : Spec (CommRingCat.of A) ⟶ X) (z :
  X.presheaf.stalk (σ.base (IsLocalRing.closedPoint A))) :
    (Scheme.stalkClosedPointTo σ).hom z = (stalkClosedPointIso (CommRingCat.of A)).hom.hom
      ((σ.stalkMap (IsLocalRing.closedPoint A)).hom z) := rfl

theorem stalkMap_eq_zero_iff (σ : Spec (CommRingCat.of A) ⟶ X) (z : X.presheaf.stalk (σ.base
  (IsLocalRing.closedPoint A))) :
    (σ.stalkMap (IsLocalRing.closedPoint A)).hom z = 0 ↔ (Scheme.stalkClosedPointTo σ).hom z = 0 :=
      by
  rw [stalkClosedPointTo_apply]
  constructor
  · intro h; rw [h, map_zero]
  · intro h
    apply (ConcreteCategory.bijective_of_isIso (stalkClosedPointIso (CommRingCat.of A)).hom).1
    rw [h]; exact (map_zero _).symm

end B12C5

open B12C5 in
theorem _root_.AlgebraicGeometry.eq_of_section_of_base_closedPoint_eq_of_ker_stalkMap_le
    {A : Type u} [CommRing A] [IsLocalRing A] {X : Scheme.{u}} (c : X ⟶ Spec (CommRingCat.of A))
    (σ σ' : Spec (CommRingCat.of A) ⟶ X) (hσ : σ ≫ c = 𝟙 _) (hσ' : σ' ≫ c = 𝟙 _)
    (hx : σ'.base (IsLocalRing.closedPoint A) = σ.base (IsLocalRing.closedPoint A))
    (hker : ∀ (U : X.Opens) (hU : σ.base (IsLocalRing.closedPoint A) ∈ U) (s : X.presheaf.obj
      (Opposite.op U)),
      (σ.stalkMap (IsLocalRing.closedPoint A)).hom (X.presheaf.germ U (σ.base
        (IsLocalRing.closedPoint A)) hU s) = 0 →
      (σ'.stalkMap (IsLocalRing.closedPoint A)).hom
        (X.presheaf.germ U (σ'.base (IsLocalRing.closedPoint A)) (by rw [hx]; exact hU) s) = 0) :
    σ = σ' := by
  let e := SpecToEquivOfLocalRing X (CommRingCat.of A)
  apply e.injective
  rw [SpecToEquivOfLocalRing_eq_iff]
  refine ⟨hx.symm, ?_⟩
  change Scheme.stalkClosedPointTo σ = (X.presheaf.stalkCongr _).hom ≫ Scheme.stalkClosedPointTo σ'
  apply TopCat.Presheaf.stalk_hom_ext
  intro U hxU
  let p : Spec (CommRingCat.of A) := IsLocalRing.closedPoint A
  have hxU' : σ' p ∈ U := by rw [hx]; exact hxU
  have hxIns : Inseparable (σ p) (σ' p) := Inseparable.of_eq hx.symm
  let e' : X.presheaf.stalk (σ p) ≅ X.presheaf.stalk (σ' p) := X.presheaf.stalkCongr hxIns
  have hs : σ' p ⤳ σ p := hxIns.ge
  have hg : X.presheaf.germ U (σ p) hxU ≫ e'.hom = X.presheaf.germ U (σ' p) hxU' :=
    X.presheaf.germ_stalkSpecializes hxU hs
  have hmove : X.presheaf.germ U (σ p) hxU ≫ (e'.hom ≫ Scheme.stalkClosedPointTo σ') =
      X.presheaf.germ U (σ' p) hxU' ≫ Scheme.stalkClosedPointTo σ' :=
    (Category.assoc (X.presheaf.germ U (σ p) hxU) e'.hom (Scheme.stalkClosedPointTo σ')).symm.trans
      (congrArg (fun g : Γ(X, U) ⟶ X.presheaf.stalk (σ' p) => g ≫ Scheme.stalkClosedPointTo σ') hg)
  change X.presheaf.germ U (σ p) hxU ≫ Scheme.stalkClosedPointTo σ =
    X.presheaf.germ U (σ p) hxU ≫ (e'.hom ≫ Scheme.stalkClosedPointTo σ')
  apply Eq.trans (b := X.presheaf.germ U (σ' p) hxU' ≫ Scheme.stalkClosedPointTo σ') _ hmove.symm
  ext s
  simp only [CommRingCat.hom_comp, RingHom.comp_apply]
  set a : A := (Scheme.stalkClosedPointTo σ).hom ((X.presheaf.germ U (σ.base
    (IsLocalRing.closedPoint A)) hxU).hom s) with ha
  let s₁ : X.presheaf.obj (Opposite.op U) := s - (X.presheaf.map (homOfLE (le_top (a :=
    U))).op).hom (const c a)
  have h1 : (Scheme.stalkClosedPointTo σ).hom ((X.presheaf.germ U (σ.base (IsLocalRing.closedPoint
    A)) hxU).hom s₁) = 0 := by
    simp only [s₁, map_sub, stalkClosedPointTo_germ_const c σ hσ a U hxU]
    exact sub_self a
  have h2 := hker U hxU s₁ ((stalkMap_eq_zero_iff σ _).2 h1)
  have h3 : (Scheme.stalkClosedPointTo σ').hom ((X.presheaf.germ U (σ'.base
    (IsLocalRing.closedPoint A)) hxU').hom s₁) = 0 :=
    (stalkMap_eq_zero_iff σ' _).1 h2
  simp only [s₁, map_sub, stalkClosedPointTo_germ_const c σ' hσ' a U hxU'] at h3
  exact (sub_eq_zero.1 h3).symm
end AlgebraicCurves.Geometry.Schemes.Proofs.eq_of_section_of_base_closedPoint_eq_of_ker_stalkMap_le
end ProofImplementation
