/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_CurveModel_ffEquiv_symm_germToFunctionField_sub_algebraMap_mem_nonunits_pointEquivPlace_of_comp_eq_specMap_comp.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Models.Basic

/-!
# Curve Model ff Equiv symm germ To Function Field sub algebra Map mem nonunits point Equiv
Place of comp eq spec Map comp
-/

section ProofImplementation

namespace AlgebraicCurves.Models.Proofs.GermsAfterBaseChange

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve Opposite

namespace ChartValueCongruence

variable {K : Type u} [Field K]

theorem eq_closedPoint (x : Spec (CommRingCat.of K)) : x = IsLocalRing.closedPoint K :=
  Subsingleton.elim _ _

theorem top_le_preimage {X : Scheme.{u}} (z : Spec (CommRingCat.of K) ⟶ X) (U : X.Opens)
    (h : z.base (IsLocalRing.closedPoint K) ∈ U) : (⊤ : (Spec (CommRingCat.of K)).Opens) ≤ z ⁻¹ᵁ U
      := by
  rintro x -
  change z.base x ∈ U
  rwa [eq_closedPoint x]

/-- Evaluate a section at the rational point `z` using its map on sections. -/
noncomputable def ev {X : Scheme.{u}} (z : Spec (CommRingCat.of K) ⟶ X) (U : X.Opens)
    (h : z.base (IsLocalRing.closedPoint K) ∈ U) : Γ(X, U) →+* K :=
  (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom.comp (z.appLE U ⊤ (top_le_preimage z U h)).hom

theorem ev_eq_stalkClosedPointTo {X : Scheme.{u}} (z : Spec (CommRingCat.of K) ⟶ X) (U : X.Opens)
    (h : z.base (IsLocalRing.closedPoint K) ∈ U) (t : Γ(X, U)) :
    ev z U h t = (Scheme.stalkClosedPointTo z).hom ((X.presheaf.germ U _ h).hom t) := by
  have H := Scheme.germ_stalkClosedPointTo z U h
  have h2 := congrArg (fun φ => φ.hom t) H
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h2
  rw [h2]
  simp only [ev, RingHom.comp_apply, Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom,
    CommRingCat.hom_comp,
    Scheme.Hom.appLE]
  congr 3

theorem ev_chart {X : Scheme.{u}} {Y : Scheme.{u}} (f : X ⟶ Y) {B : Type u} [CommRing B]
    (ι : Spec (CommRingCat.of B) ⟶ Y) [IsOpenImmersion ι]
    (z : Spec (CommRingCat.of K) ⟶ X) (β : B →+* K) (hz : z ≫ f = Spec.map (CommRingCat.ofHom β) ≫
      ι)
    (h : z.base (IsLocalRing.closedPoint K) ∈ f ⁻¹ᵁ (ι ''ᵁ ⊤)) (b : B) :
    ev z (f ⁻¹ᵁ (ι ''ᵁ ⊤)) h ((f.app (ι ''ᵁ ⊤)).hom ((ι.appIso ⊤).inv ((Scheme.ΓSpecIso
      (CommRingCat.of B)).inv b))) = β b := by
  simp only [ev, RingHom.comp_apply]
  have h1 : (f.app (ι ''ᵁ ⊤) ≫ z.appLE (f ⁻¹ᵁ (ι ''ᵁ ⊤)) ⊤ (top_le_preimage z _ h)) =
      (z ≫ f).appLE (ι ''ᵁ ⊤) ⊤ (top_le_preimage z _ h) := (Scheme.Hom.comp_appLE z f _ _ _).symm
  have key : ∀ {g g' : Spec (CommRingCat.of K) ⟶ Y} (hg : g = g') (e : (⊤ : (Spec (CommRingCat.of
    K)).Opens) ≤ g ⁻¹ᵁ (ι ''ᵁ ⊤)),
      g.appLE (ι ''ᵁ ⊤) ⊤ e = g'.appLE (ι ''ᵁ ⊤) ⊤ (hg ▸ e) := by
    intro g g' hg e
    subst hg
    rfl
  have h2 : (z ≫ f).appLE (ι ''ᵁ ⊤) ⊤ (top_le_preimage z _ h) =
      ι.appLE (ι ''ᵁ ⊤) ⊤ (by rw [Scheme.Hom.preimage_image_eq]) ≫
        (Spec.map (CommRingCat.ofHom β)).appLE ⊤ ⊤ le_top := by
    exact (key hz _).trans (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
  have h3 : (ι.appIso ⊤).inv ≫ ι.appLE (ι ''ᵁ ⊤) ⊤
    (by rw [Scheme.Hom.preimage_image_eq]) = 𝟙 _ := by
    rw [Scheme.Hom.appIso_inv_appLE]
    exact (Spec (CommRingCat.of B)).presheaf.map_id _
  have h4 : (Spec.map (CommRingCat.ofHom β)).appLE ⊤ ⊤ le_top = (Spec.map (CommRingCat.ofHom
    β)).appTop :=
    Scheme.Hom.appLE_eq_app _
  have h3' : ∀ {W : CommRingCat} (k : Γ(Spec (CommRingCat.of B), ⊤) ⟶ W),
      (ι.appIso ⊤).inv ≫ ι.appLE (ι ''ᵁ ⊤) ⊤ (by rw [Scheme.Hom.preimage_image_eq]) ≫ k = k := by
    intro W k
    rw [← Category.assoc, h3, Category.id_comp]
  have hcomp : (Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫ ((ι.appIso ⊤).inv ≫
      ((f.app (ι ''ᵁ ⊤) ≫ z.appLE (f ⁻¹ᵁ (ι ''ᵁ ⊤)) ⊤ (top_le_preimage z _ h)) ≫
        (Scheme.ΓSpecIso (CommRingCat.of K)).hom)) = CommRingCat.ofHom β := by
    rw [h1, h2, Category.assoc, h3', h4, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality,
      Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have := congrArg (fun φ : CommRingCat.of B ⟶ CommRingCat.of K => φ.hom b) hcomp
  simpa using this

/-- The constant section on `U` obtained from the structure morphism `g`. -/
noncomputable def cst {X : Scheme.{u}} (g : X ⟶ Spec (CommRingCat.of K)) (U : X.Opens) (c : K) :
  Γ(X, U) :=
  (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom
    ((Scheme.Hom.appTop g).hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom c))

theorem ev_cst {X : Scheme.{u}} (g : X ⟶ Spec (CommRingCat.of K)) (z : Spec (CommRingCat.of K) ⟶ X)
    (hz : z ≫ g = 𝟙 _) (U : X.Opens) (h : z.base (IsLocalRing.closedPoint K) ∈ U) (c : K) :
    ev z U h (cst g U c) = c := by
  have hcomp : (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ Scheme.Hom.appTop g ≫
      X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op ≫ z.appLE U ⊤ (top_le_preimage z U h) ≫
        (Scheme.ΓSpecIso (CommRingCat.of K)).hom = 𝟙 _ := by
    rw [Scheme.Hom.map_appLE_assoc]
    have key : ∀ {g₁ g₂ : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of K)} (hg : g₁ = g₂)
        (e : (⊤ : (Spec (CommRingCat.of K)).Opens) ≤ g₁ ⁻¹ᵁ ⊤),
        g₁.appLE ⊤ ⊤ e = g₂.appLE ⊤ ⊤ (hg ▸ e) := by
      intro g₁ g₂ hg e
      subst hg
      rfl
    have : Scheme.Hom.appTop g ≫ z.appLE ⊤ ⊤ ((top_le_preimage z U h).trans
        ((TopologicalSpace.Opens.map z.base).map (homOfLE (le_top : U ≤ ⊤))).le) = 𝟙 _ := by
      change g.appTop ≫ z.appTop = _
      rw [← Scheme.Hom.comp_appTop, hz, Scheme.Hom.id_appTop]
    rw [← Category.assoc (Scheme.Hom.appTop g), this, Category.id_comp, Iso.inv_hom_id]
  have := congrArg (fun φ : CommRingCat.of K ⟶ CommRingCat.of K => φ.hom c) hcomp
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_id, RingHom.id_apply] at this
  exact this

theorem ffEquiv_symm_germToFunctionField_cst {L : Type v} [Field L] [Algebra K L] (N : CurveModel K
  L)
    (U : N.C.Opens) [Nonempty (Scheme.Opens.toScheme U)] (c : K) :
    N.ffEquiv.symm (N.C.germToFunctionField U (cst N.toBase U c)) = algebraMap K L c := by
  rw [RingEquiv.symm_apply_eq, N.ffEquiv_algebraMap]
  simp only [cst]
  rw [← CommRingCat.comp_apply, Scheme.germToFunctionField, TopCat.Presheaf.germ_res]
  rfl

end ChartValueCongruence
end AlgebraicCurves.Models.Proofs.GermsAfterBaseChange

namespace AlgebraicCurve.CurveModel

open _root_.AlgebraicCurves.Models.Proofs.GermsAfterBaseChange
universe u v
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
  _root_.AlgebraicCurve _root_.Opposite


open _root_.AlgebraicCurves.Models.Proofs.GermsAfterBaseChange.ChartValueCongruence in
theorem
ffEquiv_symm_germToFunctionField_sub_algebraMap_mem_nonunits_pointEquivPlace_of_comp_eq_specMap_comp
    {K : Type u} [Field K] [IsAlgClosed K] {L : Type v} [Field L] [Algebra K L] (N : CurveModel K L)
    {Y : Scheme.{u}} (f : N.C ⟶ Y) {B : Type u} [CommRing B] (ι : Spec (CommRingCat.of B) ⟶ Y)
      [IsOpenImmersion ι]
    [Nonempty (Scheme.Opens.toScheme (f ⁻¹ᵁ (ι ''ᵁ ⊤)))]
    (z : {q : Spec (CommRingCat.of K) ⟶ N.C // q ≫ N.toBase = 𝟙 _}) (β : B →+* K)
    (hz : z.1 ≫ f = Spec.map (CommRingCat.ofHom β) ≫ ι) (b : B) :
    N.ffEquiv.symm (N.C.germToFunctionField (f ⁻¹ᵁ (ι ''ᵁ ⊤))
        ((f.app (ι ''ᵁ ⊤)).hom ((ι.appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of B)).inv b)))) -
      algebraMap K L (β b) ∈ (N.pointEquivPlace z).toValuationSubring.nonunits := by
  have hpt : z.1.base (IsLocalRing.closedPoint K) ∈ f ⁻¹ᵁ (ι ''ᵁ ⊤) := by
    change (z.1 ≫ f).base (IsLocalRing.closedPoint K) ∈ ι ''ᵁ ⊤
    rw [hz, Scheme.Hom.image_top_eq_opensRange]
    exact ⟨_, rfl⟩
  let x : closedPoints N.C := pointEquivClosedPoint N.toBase z
  let φ : (N.C.presheaf.stalk (z.1.base (IsLocalRing.closedPoint K))) →+* L :=
    N.ffEquiv.symm.toRingHom.comp
      (algebraMap (N.C.presheaf.stalk (z.1.base (IsLocalRing.closedPoint K))) N.C.functionField)
  have hφinj : Function.Injective φ :=
    N.ffEquiv.symm.injective.comp
      (IsFractionRing.injective (N.C.presheaf.stalk (z.1.base (IsLocalRing.closedPoint K)))
        N.C.functionField)
  have hrange : φ.range = (N.placeOfPoint x).toValuationSubring.toSubring := N.range_stalk_eq x
  have hread : ∀ t : Γ(N.C, f ⁻¹ᵁ (ι ''ᵁ ⊤)),
      N.ffEquiv.symm (N.C.germToFunctionField (f ⁻¹ᵁ (ι ''ᵁ ⊤)) t) =
        φ ((N.C.presheaf.germ (f ⁻¹ᵁ (ι ''ᵁ ⊤)) _ hpt).hom t) := by
    intro t
    change N.ffEquiv.symm _ = N.ffEquiv.symm ((N.C.presheaf.stalkSpecializes _).hom
      ((N.C.presheaf.germ (f ⁻¹ᵁ (ι ''ᵁ ⊤)) _ hpt).hom t))
    rw [← CommRingCat.comp_apply, TopCat.Presheaf.germ_stalkSpecializes]
  have hm : (N.C.presheaf.germ (f ⁻¹ᵁ (ι ''ᵁ ⊤)) _ hpt).hom
      ((f.app (ι ''ᵁ ⊤)).hom ((ι.appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of B)).inv b)) -
        cst N.toBase (f ⁻¹ᵁ (ι ''ᵁ ⊤)) (β b)) ∈ IsLocalRing.maximalIdeal _ := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have h1 := hu.map (Scheme.stalkClosedPointTo z.1).hom
    rw [← ev_eq_stalkClosedPointTo, map_sub, ev_chart f ι z.1 β hz hpt b, ev_cst N.toBase z.1 z.2 _
      hpt,
      sub_self] at h1
    exact not_isUnit_zero h1
  rw [CurveModel.pointEquivPlace_apply, ← ffEquiv_symm_germToFunctionField_cst N (f ⁻¹ᵁ (ι ''ᵁ ⊤))
    (β b),
    ← map_sub, ← map_sub, hread]
  set m := (N.C.presheaf.germ (f ⁻¹ᵁ (ι ''ᵁ ⊤)) _ hpt).hom
      ((f.app (ι ''ᵁ ⊤)).hom ((ι.appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of B)).inv b)) -
        cst N.toBase (f ⁻¹ᵁ (ι ''ᵁ ⊤)) (β b)) with hm_def
  have hmem : φ m ∈ (N.placeOfPoint x).toValuationSubring := by
    have : φ m ∈ φ.range := ⟨m, rfl⟩
    rw [hrange] at this
    exact this
  rw [show φ m = ((⟨φ m, hmem⟩ : (N.placeOfPoint x).toValuationSubring) : L) from rfl,
    ValuationSubring.coe_mem_nonunits_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  obtain ⟨w, hw⟩ := hu.exists_right_inv
  have hw' : (w : L) ∈ φ.range := by
    rw [hrange]
    exact w.2
  obtain ⟨m', hm'⟩ := hw'
  have h1 : φ (m * m') = φ 1 := by
    rw [map_mul, hm', map_one]
    exact congrArg Subtype.val hw
  have hunit : IsUnit m := IsUnit.of_mul_eq_one m' (hφinj h1)
  exact (IsLocalRing.mem_maximalIdeal _).mp hm hunit
end AlgebraicCurve.CurveModel
end ProofImplementation
