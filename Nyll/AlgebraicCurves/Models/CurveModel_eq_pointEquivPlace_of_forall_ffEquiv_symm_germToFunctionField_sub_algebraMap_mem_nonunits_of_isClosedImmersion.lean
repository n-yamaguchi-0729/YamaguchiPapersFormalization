/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_CurveModel_eq_pointEquivPlace_of_forall_ffEquiv_symm_germToFunctionField_sub_algebraMap_mem_nonunits_of_isClosedImmersion.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Models.Basic

/-!
# Curve Model eq point Equiv Place of forall ff Equiv symm germ To Function Field sub
algebra Map mem nonunits of is Closed Immersion
-/

section ProofImplementation

namespace AlgebraicCurves.Models.Proofs.PointPlaceClosedImmersion

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve

open Opposite TensorProduct

namespace ChartValueUnique

theorem place_eq_of_le {K : Type u} [Field K] {L : Type v} [Field L] [Algebra K L] (v w : Place K L)
    (h : v.toValuationSubring ≤ w.toValuationSubring) : v = w := by
  apply Place.ext
  have hw := ValuationSubring.ofPrime_idealOfLE _ _ h
  set P := v.toValuationSubring.idealOfLE w.toValuationSubring h with hP
  by_cases hbot : P = ⊥
  · exfalso
    apply w.ne_top'
    rw [← hw]
    have : ∀ (Q : Ideal v.toValuationSubring) [Q.IsPrime], Q = ⊥ → v.toValuationSubring.ofPrime Q =
      ⊤ := by
      intro Q _ hQ
      subst hQ
      exact ValuationSubring.ofPrime_bot _
    exact this P hbot
  · have hmax : P.IsMaximal := IsPrime.to_maximal_ideal hbot
    have hPm : P = IsLocalRing.maximalIdeal _ := IsLocalRing.eq_maximalIdeal hmax
    have : ∀ (Q : Ideal v.toValuationSubring) [Q.IsPrime], Q = IsLocalRing.maximalIdeal _ →
        v.toValuationSubring.ofPrime Q = v.toValuationSubring := by
      intro Q _ hQ
      subst hQ
      exact ValuationSubring.ofPrime_top _
    rw [← hw, this P hPm]

variable {L : Type v} [Field L]

theorem mem_of_mem_nonunits (O : ValuationSubring L) {x : L} (hx : x ∈ O.nonunits) : x ∈ O :=
  (O.valuation_le_one_iff x).mp ((O.mem_nonunits_iff.mp hx).le)

theorem add_mem_nonunits (O : ValuationSubring L) {x y : L} (hx : x ∈ O.nonunits) (hy : y ∈
  O.nonunits) :
    x + y ∈ O.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff] at hx hy ⊢
  exact lt_of_le_of_lt (O.valuation.map_add x y) (max_lt hx hy)

theorem mul_mem_nonunits_of_mem (O : ValuationSubring L) {x y : L} (hx : x ∈ O) (hy : y ∈
  O.nonunits) :
    x * y ∈ O.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff] at hy ⊢
  rw [map_mul]
  calc
    O.valuation x * O.valuation y ≤ 1 * O.valuation y :=
      mul_le_mul_left ((O.valuation_le_one_iff x).mpr hx) _
    _ = O.valuation y := one_mul _
    _ < 1 := hy

theorem zero_mem_nonunits (O : ValuationSubring L) : (0 : L) ∈ O.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff, map_zero]
  exact zero_lt_one

theorem valuation_eq_one_of_add {O : ValuationSubring L} {n c : L} (hn : n ∈ O.nonunits) (hc :
  O.valuation c = 1) :
    O.valuation (n + c) = 1 := by
  rw [ValuationSubring.mem_nonunits_iff] at hn
  rw [add_comm, Valuation.map_add_eq_of_lt_left]
  · exact hc
  · rw [hc]; exact hn

theorem inv_mem_of_valuation_eq_one {O : ValuationSubring L} {x : L} (hx : O.valuation x = 1) : x⁻¹
  ∈ O := by
  rw [← O.valuation_le_one_iff, map_inv₀, hx, inv_one]

section Ev

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
  have h3 : (ι.appIso ⊤).inv ≫ ι.appLE (ι ''ᵁ ⊤) ⊤ (by rw [Scheme.Hom.preimage_image_eq]) = 𝟙 _ :=
    by
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

end Ev

theorem appIso_inv_appLE_of_eq {Y : Scheme.{u}} {B B' : Type u} [CommRing B] [CommRing B']
    (ι : Spec (CommRingCat.of B) ⟶ Y) [IsOpenImmersion ι]
    (φ : B →+* B') (κ : Spec (CommRingCat.of B') ⟶ Y)
    (hκ : κ = Spec.map (CommRingCat.ofHom φ) ≫ ι) (e : (⊤ : (Spec (CommRingCat.of B')).Opens) ≤ κ
      ⁻¹ᵁ (ι ''ᵁ ⊤)) :
    (Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫ (ι.appIso ⊤).inv ≫ κ.appLE (ι ''ᵁ ⊤) ⊤ e =
      CommRingCat.ofHom φ ≫ (Scheme.ΓSpecIso (CommRingCat.of B')).inv := by
  subst hκ
  have h2 : (Spec.map (CommRingCat.ofHom φ) ≫ ι).appLE (ι ''ᵁ ⊤) ⊤ e =
      ι.appLE (ι ''ᵁ ⊤) ⊤ (by rw [Scheme.Hom.preimage_image_eq]) ≫
        (Spec.map (CommRingCat.ofHom φ)).appLE ⊤ ⊤ le_top := by
    exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
  have h3 : (ι.appIso ⊤).inv ≫ ι.appLE (ι ''ᵁ ⊤) ⊤ (by rw [Scheme.Hom.preimage_image_eq]) = 𝟙 _ :=
    by
    rw [Scheme.Hom.appIso_inv_appLE]
    exact (Spec (CommRingCat.of B)).presheaf.map_id _
  have h4 : (Spec.map (CommRingCat.ofHom φ)).appLE ⊤ ⊤ le_top = (Spec.map (CommRingCat.ofHom
    φ)).appTop :=
    Scheme.Hom.appLE_eq_app _
  rw [h2, ← Category.assoc (ι.appIso ⊤).inv, h3, Category.id_comp, h4, ←
    Scheme.ΓSpecIso_inv_naturality]

end ChartValueUnique
end AlgebraicCurves.Models.Proofs.PointPlaceClosedImmersion

namespace AlgebraicCurve.CurveModel

open _root_.AlgebraicCurves.Models.Proofs.PointPlaceClosedImmersion
universe u v
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
  _root_.AlgebraicCurve
open _root_.Opposite _root_.TensorProduct


open _root_.AlgebraicCurves.Models.Proofs.PointPlaceClosedImmersion.ChartValueUnique in
theorem eq_pointEquivPlace_of_germ_nonunit_of_isClosedImmersion
    {R₀ : Type u} [CommRing R₀] {K : Type u} [Field K] [IsAlgClosed K] (toK : R₀ →+* K)
    {Y : Scheme.{u}} (g : Y ⟶ Spec (CommRingCat.of R₀))
    {B : Type u} [CommRing B] (ι : Spec (CommRingCat.of B) ⟶ Y) [IsOpenImmersion ι]
    {L : Type v} [Field L] [Algebra K L] (N : CurveModel K L)
    (h : N.C ⟶ pullback g (Spec.map (CommRingCat.ofHom toK))) [IsClosedImmersion h]
    (hh : h ≫ pullback.snd _ _ = N.toBase)
    (f : N.C ⟶ Y) (hf : h ≫ pullback.fst _ _ = f)
    [Nonempty (Scheme.Opens.toScheme (f ⁻¹ᵁ (ι ''ᵁ ⊤)))]
    (z : {q : Spec (CommRingCat.of K) ⟶ N.C // q ≫ N.toBase = 𝟙 _}) (β : B →+* K)
    (hz : z.1 ≫ f = Spec.map (CommRingCat.ofHom β) ≫ ι)
    (Q : Place K L)
    (hQ : ∀ b : B, N.ffEquiv.symm (N.C.germToFunctionField (f ⁻¹ᵁ (ι ''ᵁ ⊤))
        ((f.app (ι ''ᵁ ⊤)).hom ((ι.appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of B)).inv b)))) -
      algebraMap K L (β b) ∈ Q.toValuationSubring.nonunits) :
    Q = N.pointEquivPlace z := by
  classical
  subst hf
  have hzf : z.1 ≫ (h ≫ pullback.fst _ _) = Spec.map (CommRingCat.ofHom β) ≫ ι := by
    simpa only [Category.assoc] using hz
  have hpt : z.1.base (IsLocalRing.closedPoint K) ∈ (h ≫ pullback.fst _ _) ⁻¹ᵁ (ι ''ᵁ ⊤) := by
    change (z.1 ≫ (h ≫ pullback.fst _ _)).base (IsLocalRing.closedPoint K) ∈ ι ''ᵁ ⊤
    rw [hzf, Scheme.Hom.image_top_eq_opensRange]
    exact ⟨_, rfl⟩
  let x : closedPoints N.C := pointEquivClosedPoint N.toBase z
  let φ : (N.C.presheaf.stalk (z.1.base (IsLocalRing.closedPoint K))) →+* L :=
    N.ffEquiv.symm.toRingHom.comp
      (algebraMap (N.C.presheaf.stalk (z.1.base (IsLocalRing.closedPoint K))) N.C.functionField)
  have hrange : φ.range = (N.placeOfPoint x).toValuationSubring.toSubring := N.range_stalk_eq x
  have hread : ∀ t : Γ(N.C, (h ≫ pullback.fst _ _) ⁻¹ᵁ (ι ''ᵁ ⊤)),
      N.ffEquiv.symm (N.C.germToFunctionField ((h ≫ pullback.fst _ _) ⁻¹ᵁ (ι ''ᵁ ⊤)) t) =
        φ ((N.C.presheaf.germ ((h ≫ pullback.fst _ _) ⁻¹ᵁ (ι ''ᵁ ⊤)) _ hpt).hom t) := by
    intro t
    change N.ffEquiv.symm _ = N.ffEquiv.symm ((N.C.presheaf.stalkSpecializes _).hom
      ((N.C.presheaf.germ ((h ≫ pullback.fst _ _) ⁻¹ᵁ (ι ''ᵁ ⊤)) _ hpt).hom t))
    rw [← CommRingCat.comp_apply, TopCat.Presheaf.germ_stalkSpecializes]
  let algB : Algebra R₀ B := (Spec.preimage (ι ≫ g)).hom.toAlgebra
  let algK : Algebra R₀ K := toK.toAlgebra
  have hιg : ι ≫ g = Spec.map (CommRingCat.ofHom (algebraMap R₀ B)) := by
    rw [RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom, Spec.map_preimage]
  let κ' : Spec (CommRingCat.of (B ⊗[R₀] K)) ⟶ pullback g (Spec.map (CommRingCat.ofHom toK)) :=
    (pullbackSpecIso R₀ B K).inv ≫
      pullback.map (Spec.map (CommRingCat.ofHom (algebraMap R₀ B))) (Spec.map (CommRingCat.ofHom
        (algebraMap R₀ K)))
        g (Spec.map (CommRingCat.ofHom toK)) ι (𝟙 _) (𝟙 _)
        (by rw [Category.comp_id, hιg]) (by rw [Category.comp_id, Category.id_comp])
  have hκ'fst : κ' ≫ pullback.fst g (Spec.map (CommRingCat.ofHom toK)) =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[R₀] K)) ≫ ι
        := by
    simp only [κ', Category.assoc, pullback.lift_fst]
    rw [pullbackSpecIso_inv_fst_assoc]
  have hκ'b : κ' ≫ pullback.snd g (Spec.map (CommRingCat.ofHom toK)) = Spec.map (CommRingCat.ofHom
      ((Algebra.TensorProduct.includeRight : K →ₐ[R₀] B ⊗[R₀] K).toRingHom)) := by
    simp only [κ', Category.assoc, pullback.lift_snd, Category.comp_id]
    rw [pullbackSpecIso_inv_snd]
    rfl
  have hκ'range : Set.range κ'.base = (pullback.fst g (Spec.map (CommRingCat.ofHom toK))).base ⁻¹'
    Set.range ι.base := by
    have hsurj : Function.Surjective (pullbackSpecIso R₀ B K).inv.base := fun t =>
      ⟨(pullbackSpecIso R₀ B K).hom.base t, by
        rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id]; rfl⟩
    simp only [κ', Scheme.Hom.comp_base, TopCat.hom_comp, ContinuousMap.coe_comp]
    rw [hsurj.range_comp, Scheme.Pullback.range_map]
    ext t
    simp
  have hκ'V : κ' ''ᵁ ⊤ = (pullback.fst g (Spec.map (CommRingCat.ofHom toK))) ⁻¹ᵁ (ι ''ᵁ ⊤) := by
    apply TopologicalSpace.Opens.ext
    rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Hom.coe_opensRange, hκ'range]
    ext q
    change (pullback.fst g (Spec.map (CommRingCat.ofHom toK))).base q ∈ Set.range ι.base ↔
      (pullback.fst g (Spec.map (CommRingCat.ofHom toK))).base q ∈ (ι ''ᵁ ⊤)
    rw [Scheme.Hom.image_top_eq_opensRange]
    rfl
  have hVaff : IsAffineOpen ((pullback.fst g (Spec.map (CommRingCat.ofHom toK))) ⁻¹ᵁ (ι ''ᵁ ⊤)) :=
    by
    rw [← hκ'V, Scheme.Hom.image_top_eq_opensRange]
    exact isAffineOpen_opensRange κ'
  have hUaff : IsAffineOpen ((h ≫ pullback.fst _ _) ⁻¹ᵁ (ι ''ᵁ ⊤)) := hVaff.preimage h
  have hT : ∀ {U' : (pullback g (Spec.map (CommRingCat.ofHom toK))).Opens} (hU : κ' ''ᵁ ⊤ = U')
      (e' : (⊤ : (Spec (CommRingCat.of (B ⊗[R₀] K))).Opens) ≤ κ' ⁻¹ᵁ U') (s : Γ(pullback g
        (Spec.map (CommRingCat.ofHom toK)), U')),
      ((pullback g (Spec.map (CommRingCat.ofHom toK))).presheaf.map (eqToHom hU.symm).op).hom
        ((κ'.appIso ⊤).inv.hom ((κ'.appLE U' ⊤ e').hom s)) = s := by
    intro U' hU e' s
    subst hU
    have h0 : κ'.appLE (κ' ''ᵁ ⊤) ⊤ e' = (κ'.appIso ⊤).hom := (Scheme.Hom.appIso_hom' κ' ⊤).symm
    have h1 := congrArg (fun ψ => ψ.hom s) (κ'.appIso ⊤).hom_inv_id
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_id, RingHom.id_apply] at h1
    rw [h0, h1]
    simp
  have hle : (⊤ : (Spec (CommRingCat.of (B ⊗[R₀] K))).Opens) ≤ κ' ⁻¹ᵁ ((pullback.fst g (Spec.map
    (CommRingCat.ofHom toK))) ⁻¹ᵁ (ι ''ᵁ ⊤)) := by
    rw [← hκ'V, Scheme.Hom.preimage_image_eq]
  let ΘP : B ⊗[R₀] K →+* Γ(pullback g (Spec.map (CommRingCat.ofHom toK)), (pullback.fst g (Spec.map
    (CommRingCat.ofHom toK))) ⁻¹ᵁ (ι ''ᵁ ⊤)) :=
    (((pullback g (Spec.map (CommRingCat.ofHom toK))).presheaf.map (eqToHom hκ'V.symm).op).hom.comp
      (κ'.appIso ⊤).inv.hom).comp
      (Scheme.ΓSpecIso (CommRingCat.of (B ⊗[R₀] K))).inv.hom
  have hΘPsurj : Function.Surjective ΘP := by
    intro s'
    refine ⟨(Scheme.ΓSpecIso (CommRingCat.of (B ⊗[R₀] K))).hom ((κ'.appLE ((pullback.fst g
      (Spec.map (CommRingCat.ofHom toK))) ⁻¹ᵁ (ι ''ᵁ ⊤)) ⊤ hle).hom s'), ?_⟩
    simp only [ΘP, RingHom.comp_apply]
    have h1 := congrArg (fun ψ => ψ.hom ((κ'.appLE ((pullback.fst g (Spec.map (CommRingCat.ofHom
      toK))) ⁻¹ᵁ (ι ''ᵁ ⊤)) ⊤ hle).hom s'))
      (Scheme.ΓSpecIso (CommRingCat.of (B ⊗[R₀] K))).hom_inv_id
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_id, RingHom.id_apply] at h1
    rw [h1]
    exact hT hκ'V hle s'
  let Θ : B ⊗[R₀] K →+* Γ(N.C, (h ≫ pullback.fst _ _) ⁻¹ᵁ (ι ''ᵁ ⊤)) := (h.app ((pullback.fst g
    (Spec.map (CommRingCat.ofHom toK))) ⁻¹ᵁ (ι ''ᵁ ⊤))).hom.comp ΘP
  have hΘsurj : Function.Surjective Θ := by
    intro s
    obtain ⟨t, rfl⟩ := h.app_surjective ((pullback.fst g (Spec.map (CommRingCat.ofHom toK))) ⁻¹ᵁ (ι
      ''ᵁ ⊤)) hVaff s
    obtain ⟨w, rfl⟩ := hΘPsurj t
    exact ⟨w, rfl⟩
  have hΘPleft : ∀ b : B, ΘP (Algebra.TensorProduct.includeLeftRingHom b) =
      ((pullback.fst g (Spec.map (CommRingCat.ofHom toK))).app (ι ''ᵁ ⊤)).hom ((ι.appIso ⊤).inv
        ((Scheme.ΓSpecIso (CommRingCat.of B)).inv b)) := by
    intro b
    have hle' : (⊤ : (Spec (CommRingCat.of (B ⊗[R₀] K))).Opens) ≤ (κ' ≫ pullback.fst g (Spec.map
      (CommRingCat.ofHom toK))) ⁻¹ᵁ (ι ''ᵁ ⊤) := by
      rw [hκ'fst]
      rintro q -
      change _ ∈ ι ''ᵁ ⊤
      rw [Scheme.Hom.image_top_eq_opensRange]
      exact ⟨_, rfl⟩
    have H := appIso_inv_appLE_of_eq ι (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[R₀] K)
      (κ' ≫ pullback.fst g (Spec.map (CommRingCat.ofHom toK))) hκ'fst hle'
    rw [Scheme.Hom.comp_appLE] at H
    have H' := congrArg (fun ψ => ψ.hom b) H
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at H'
    simp only [ΘP, RingHom.comp_apply]
    rw [← H']
    exact hT hκ'V _ _
  have hΘleft : ∀ b : B, Θ (Algebra.TensorProduct.includeLeftRingHom b) =
      ((h ≫ pullback.fst _ _).app (ι ''ᵁ ⊤)).hom ((ι.appIso ⊤).inv ((Scheme.ΓSpecIso
        (CommRingCat.of B)).inv b)) := by
    intro b
    change (h.app ((pullback.fst g (Spec.map (CommRingCat.ofHom toK))) ⁻¹ᵁ (ι ''ᵁ ⊤))).hom (ΘP _) =
      _
    rw [hΘPleft, Scheme.Hom.comp_app]
    rfl
  have hΘPright : ∀ c : K, ΘP ((Algebra.TensorProduct.includeRight : K →ₐ[R₀] B ⊗[R₀] K) c) =
      cst (pullback.snd g (Spec.map (CommRingCat.ofHom toK))) ((pullback.fst g (Spec.map
        (CommRingCat.ofHom toK))) ⁻¹ᵁ (ι ''ᵁ ⊤)) c := by
    intro c
    have key : ∀ {g₁ g₂ : Spec (CommRingCat.of (B ⊗[R₀] K)) ⟶ Spec (CommRingCat.of K)} (hg : g₁ =
      g₂)
        (e₁ : (⊤ : (Spec (CommRingCat.of (B ⊗[R₀] K))).Opens) ≤ g₁ ⁻¹ᵁ ⊤),
        g₁.appLE ⊤ ⊤ e₁ = g₂.appLE ⊤ ⊤ (hg ▸ e₁) := by
      intro g₁ g₂ hg e₁
      subst hg
      rfl
    have H : (κ'.appLE ((pullback.fst g (Spec.map (CommRingCat.ofHom toK))) ⁻¹ᵁ (ι ''ᵁ ⊤)) ⊤
      hle).hom (cst (pullback.snd g (Spec.map (CommRingCat.ofHom toK))) ((pullback.fst g (Spec.map
      (CommRingCat.ofHom toK))) ⁻¹ᵁ (ι ''ᵁ ⊤)) c) =
        (Scheme.ΓSpecIso (CommRingCat.of (B ⊗[R₀] K))).inv
          ((Algebra.TensorProduct.includeRight : K →ₐ[R₀] B ⊗[R₀] K) c) := by
      simp only [cst]
      rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
      change (((pullback.snd g (Spec.map (CommRingCat.ofHom toK))).appTop ≫ κ'.appTop).hom _) = _
      rw [← Scheme.Hom.comp_appTop, hκ'b]
      have h5 := congrArg (fun χ => χ.hom c) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom
          ((Algebra.TensorProduct.includeRight : K →ₐ[R₀] B ⊗[R₀] K).toRingHom)))
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h5
      exact h5.symm
    simp only [ΘP, RingHom.comp_apply]
    change _ = cst (pullback.snd g (Spec.map (CommRingCat.ofHom toK))) ((pullback.fst g (Spec.map
      (CommRingCat.ofHom toK))) ⁻¹ᵁ (ι ''ᵁ ⊤)) c
    rw [← hT hκ'V hle (cst (pullback.snd g (Spec.map (CommRingCat.ofHom toK))) ((pullback.fst g
      (Spec.map (CommRingCat.ofHom toK))) ⁻¹ᵁ (ι ''ᵁ ⊤)) c), H]
  have hcst : ∀ c : K, (h.app ((pullback.fst g (Spec.map (CommRingCat.ofHom toK))) ⁻¹ᵁ (ι ''ᵁ
    ⊤))).hom (cst (pullback.snd g (Spec.map (CommRingCat.ofHom toK))) ((pullback.fst g (Spec.map
    (CommRingCat.ofHom toK))) ⁻¹ᵁ (ι ''ᵁ ⊤)) c) =
      cst N.toBase ((h ≫ pullback.fst _ _) ⁻¹ᵁ (ι ''ᵁ ⊤)) c := by
    intro c
    rw [← hh]
    simp only [cst]
    have hn := congrArg (fun ψ => ψ.hom ((Scheme.Hom.appTop (pullback.snd g (Spec.map
      (CommRingCat.ofHom toK)))).hom
        ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom c)))
      (h.naturality (homOfLE (le_top : (pullback.fst g (Spec.map (CommRingCat.ofHom toK))) ⁻¹ᵁ (ι
        ''ᵁ ⊤) ≤ ⊤)).op)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at hn
    rw [hn]
    rfl
  have hΘright : ∀ c : K, Θ ((Algebra.TensorProduct.includeRight : K →ₐ[R₀] B ⊗[R₀] K) c) =
      cst N.toBase ((h ≫ pullback.fst _ _) ⁻¹ᵁ (ι ''ᵁ ⊤)) c := by
    intro c
    change (h.app ((pullback.fst g (Spec.map (CommRingCat.ofHom toK))) ⁻¹ᵁ (ι ''ᵁ ⊤))).hom (ΘP _) =
      _
    rw [hΘPright, hcst]
  let rd : Γ(N.C, ((h ≫ pullback.fst _ _) ⁻¹ᵁ (ι ''ᵁ ⊤))) →+* L :=
    N.ffEquiv.symm.toRingHom.comp (N.C.germToFunctionField ((h ≫ pullback.fst _ _) ⁻¹ᵁ (ι ''ᵁ
      ⊤))).hom
  have hrd : ∀ t, rd t = N.ffEquiv.symm (N.C.germToFunctionField ((h ≫ pullback.fst _ _) ⁻¹ᵁ (ι ''ᵁ
    ⊤)) t) := fun t => rfl
  let vl : Γ(N.C, ((h ≫ pullback.fst _ _) ⁻¹ᵁ (ι ''ᵁ ⊤))) →+* K := ev z.1 ((h ≫ pullback.fst _ _)
    ⁻¹ᵁ (ι ''ᵁ ⊤)) hpt
  have good_mem : ∀ t, rd t - algebraMap K L (vl t) ∈ Q.toValuationSubring.nonunits → rd t ∈
    Q.toValuationSubring := by
    intro t ht
    have := add_mem (mem_of_mem_nonunits _ ht) (Q.algebraMap_mem' (vl t))
    simpa using this
  have good_add : ∀ t₁ t₂, rd t₁ - algebraMap K L (vl t₁) ∈ Q.toValuationSubring.nonunits →
      rd t₂ - algebraMap K L (vl t₂) ∈ Q.toValuationSubring.nonunits →
      rd (t₁ + t₂) - algebraMap K L (vl (t₁ + t₂)) ∈ Q.toValuationSubring.nonunits := by
    intro t₁ t₂ h₁ h₂
    have : rd (t₁ + t₂) - algebraMap K L (vl (t₁ + t₂)) =
        (rd t₁ - algebraMap K L (vl t₁)) + (rd t₂ - algebraMap K L (vl t₂)) := by
      simp only [map_add]; ring
    rw [this]
    exact add_mem_nonunits _ h₁ h₂
  have good_mul : ∀ t₁ t₂, rd t₁ - algebraMap K L (vl t₁) ∈ Q.toValuationSubring.nonunits →
      rd t₂ - algebraMap K L (vl t₂) ∈ Q.toValuationSubring.nonunits →
      rd (t₁ * t₂) - algebraMap K L (vl (t₁ * t₂)) ∈ Q.toValuationSubring.nonunits := by
    intro t₁ t₂ h₁ h₂
    have : rd (t₁ * t₂) - algebraMap K L (vl (t₁ * t₂)) =
        rd t₁ * (rd t₂ - algebraMap K L (vl t₂)) + algebraMap K L (vl t₂) * (rd t₁ - algebraMap K L
          (vl t₁)) := by
      simp only [map_mul]; ring
    rw [this]
    exact add_mem_nonunits _ (mul_mem_nonunits_of_mem _ (good_mem t₁ h₁) h₂)
      (mul_mem_nonunits_of_mem _ (Q.algebraMap_mem' _) h₁)
  have good_left : ∀ b : B, rd (Θ (Algebra.TensorProduct.includeLeftRingHom b)) -
      algebraMap K L (vl (Θ (Algebra.TensorProduct.includeLeftRingHom b))) ∈
        Q.toValuationSubring.nonunits := by
    intro b
    rw [hΘleft, hrd]
    change _ - algebraMap K L (ev z.1 ((h ≫ pullback.fst _ _) ⁻¹ᵁ (ι ''ᵁ ⊤)) hpt _) ∈ _
    rw [ev_chart (h ≫ pullback.fst _ _) ι z.1 β hzf hpt b]
    exact hQ b
  have good_right : ∀ c : K, rd (Θ ((Algebra.TensorProduct.includeRight : K →ₐ[R₀] B ⊗[R₀] K) c)) -
      algebraMap K L (vl (Θ ((Algebra.TensorProduct.includeRight : K →ₐ[R₀] B ⊗[R₀] K) c))) ∈
        Q.toValuationSubring.nonunits := by
    intro c
    rw [hΘright, hrd, ffEquiv_symm_germToFunctionField_cst]
    change _ - algebraMap K L (ev z.1 ((h ≫ pullback.fst _ _) ⁻¹ᵁ (ι ''ᵁ ⊤)) hpt _) ∈ _
    rw [ev_cst N.toBase z.1 z.2 _ hpt, sub_self]
    exact zero_mem_nonunits _
  have good_all : ∀ t : Γ(N.C, ((h ≫ pullback.fst _ _) ⁻¹ᵁ (ι ''ᵁ ⊤))), rd t - algebraMap K L (vl
    t) ∈ Q.toValuationSubring.nonunits := by
    intro t
    obtain ⟨w, rfl⟩ := hΘsurj t
    induction w using TensorProduct.inductionOn with
    | tmul b c =>
      have : b ⊗ₜ[R₀] c = Algebra.TensorProduct.includeLeftRingHom b *
          (Algebra.TensorProduct.includeRight : K →ₐ[R₀] B ⊗[R₀] K) c := by
        simp [Algebra.TensorProduct.includeLeftRingHom_apply,
          Algebra.TensorProduct.includeRight_apply,
          Algebra.TensorProduct.tmul_mul_tmul]
      rw [this, map_mul]
      exact good_mul _ _ (good_left b) (good_right c)
    | add w₁ w₂ h₁ h₂ =>
      rw [map_add]
      exact good_add _ _ h₁ h₂
  let xU : ↥((h ≫ pullback.fst _ _) ⁻¹ᵁ (ι ''ᵁ ⊤)) := ⟨_, hpt⟩
  let := TopCat.Presheaf.algebra_section_stalk N.C.presheaf xU
  have := hUaff.isLocalization_stalk xU
  have hφmem : ∀ m : N.C.presheaf.stalk (xU : N.C), φ m ∈ Q.toValuationSubring := by
    intro m
    obtain ⟨⟨s', t'⟩, hst⟩ := IsLocalization.surj (hUaff.primeIdealOf xU).asIdeal.primeCompl m
    have hunit : IsUnit ((N.C.presheaf.germ ((h ≫ pullback.fst _ _) ⁻¹ᵁ (ι ''ᵁ ⊤)) _ hpt).hom (t' :
      Γ(N.C, ((h ≫ pullback.fst _ _) ⁻¹ᵁ (ι ''ᵁ ⊤))))) := by
      have := IsLocalization.map_units (N.C.presheaf.stalk (xU : N.C)) t'
      exact this
    have hvl : vl t' ≠ 0 := by
      have hu := hunit.map (Scheme.stalkClosedPointTo z.1).hom
      rw [← ev_eq_stalkClosedPointTo] at hu
      exact hu.ne_zero
    have hval_c : Q.toValuationSubring.valuation (algebraMap K L (vl t')) = 1 := by
      apply le_antisymm ((Q.toValuationSubring.valuation_le_one_iff _).mpr (Q.algebraMap_mem' _))
      have h' := (Q.toValuationSubring.valuation_le_one_iff _).mpr (Q.algebraMap_mem' (vl t')⁻¹)
      rw [map_inv₀, map_inv₀, inv_le_one₀ (zero_lt_iff.mpr ((map_ne_zero _).mpr
        ((map_ne_zero _).mpr hvl)))] at h'
      exact h'
    have hval_t : Q.toValuationSubring.valuation (rd t') = 1 := by
      have := valuation_eq_one_of_add (good_all t') hval_c
      simpa using this
    have hst' := congrArg φ hst
    simp only [map_mul, TopCat.Presheaf.stalk_open_algebraMap] at hst'
    have hφgerm : ∀ u : Γ(N.C, ((h ≫ pullback.fst _ _) ⁻¹ᵁ (ι ''ᵁ ⊤))), φ ((N.C.presheaf.germ ((h ≫
      pullback.fst _ _) ⁻¹ᵁ (ι ''ᵁ ⊤)) _ hpt).hom u) = rd u := by
      intro u
      rw [hrd, hread]
    erw [hφgerm, hφgerm] at hst'
    have hne : rd t' ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hval_t
      exact zero_ne_one hval_t
    have hm : φ m = rd s' * (rd t')⁻¹ := by
      rw [← hst', mul_assoc, mul_inv_cancel₀ hne, mul_one]
    rw [hm]
    exact mul_mem (good_mem s' (good_all s')) (inv_mem_of_valuation_eq_one hval_t)
  rw [CurveModel.pointEquivPlace_apply]
  refine (place_eq_of_le (N.placeOfPoint x) Q ?_).symm
  intro w hw
  have hw' : w ∈ φ.range := by
    rw [hrange]
    exact hw
  obtain ⟨m, rfl⟩ := hw'
  exact hφmem m
end AlgebraicCurve.CurveModel
end ProofImplementation
