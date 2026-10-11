/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_SmallExtension_IsFibreReading_appLE_of_comp_eq.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Scheme
import Nyll.SchemeTheory.Cohomology.Cech.OrderedAffineCoverCech
import Nyll.AlgebraicCurves.Geometry.Schemes.OrderedAffineCoverComap
import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.AlgebraicCurves.Geometry.Picard.CechObstruction

/-!
# Small Extension Is Fibre Reading app LE of comp eq
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Deformation.Proofs.SmallExtension_IsFibreReading_appLE_of_comp_eq

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

open _root_.AlgebraicGeometry.SmallExtension
open _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover


universe u

theorem _root_.AlgebraicGeometry.SmallExtension.IsFibreReading.appLE_of_comp_eq
    {B₁ : Type u} [CommRing B₁] {k : Type u} [Field k]
    (V : Type u) [AddCommGroup V] [Module k V] [Module B₁ V] (ι : V →ₗ[B₁] B₁)
    {X X' Xk Xk' : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of B₁)) (f' : X' ⟶ Spec (CommRingCat.of B₁))
    (fk : Xk ⟶ Spec (CommRingCat.of k)) (fk' : Xk' ⟶ Spec (CommRingCat.of k))
    (i : Xk ⟶ X) (i' : Xk' ⟶ X')
    (h : X' ⟶ X) (hh : h ≫ f = f')
    (hk : Xk' ⟶ Xk) (hhk : hk ≫ i = i' ≫ h) (hfk : hk ≫ fk = fk')
    (U : X.Opens) (W : Xk.Opens) (hW : W ≤ i ⁻¹ᵁ U)
    (U' : X'.Opens) (hU' : U' ≤ h ⁻¹ᵁ U) (W' : Xk'.Opens) (hW' : W' ≤ i' ⁻¹ᵁ U') (hWk : W' ≤ hk ⁻¹ᵁ
      W)
    (δ : Γ(X, U)) (w : Module.Dual k V →ₗ[k] (OModulePresheaf.unit fk).obj W)
    (w' : Module.Dual k V →ₗ[k] (OModulePresheaf.unit fk').obj W')
    (hw' : ∀ ξ : Module.Dual k V, w' ξ = (hk.appLE W W' hWk).hom (w ξ))
    (hw : IsFibreReading V ι f fk i U W hW δ w) :
    IsFibreReading V ι f' fk' i' U' W' hW' ((h.appLE U U' hU').hom δ) w' := by
  classical
  let algU : Algebra B₁ Γ(X, U) := algebraOfHom f U
  let algU' : Algebra B₁ Γ(X', U') := algebraOfHom f' U'
  let algW : Algebra k Γ(Xk, W) := algebraOfHom fk W
  let algW' : Algebra k Γ(Xk', W') := algebraOfHom fk' W'
  have hcompat : ∀ b : B₁, (h.appLE U U' hU').hom (algebraMap B₁ Γ(X, U) b) = algebraMap B₁ Γ(X',
    U') b := by
    intro b
    change (h.appLE U U' hU').hom ((f.appLE ⊤ U le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of
      B₁)).inv.hom b)) =
      (f'.appLE ⊤ U' le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of B₁)).inv.hom b)
    have := congrArg (fun k => k.hom ((Scheme.ΓSpecIso (CommRingCat.of B₁)).inv.hom b))
      (Scheme.Hom.appLE_comp_appLE h f ⊤ U U' le_top hU')
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
    rw [this]
    subst hh
    rfl
  have hkcompat : ∀ c : k, (hk.appLE W W' hWk).hom (algebraMap k Γ(Xk, W) c) = algebraMap k Γ(Xk',
    W') c := by
    intro c
    change (hk.appLE W W' hWk).hom ((fk.appLE ⊤ W le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of
      k)).inv.hom c)) =
      (fk'.appLE ⊤ W' le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom c)
    have := congrArg (fun q => q.hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom c))
      (Scheme.Hom.appLE_comp_appLE hk fk ⊤ W W' le_top hWk)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
    rw [this]
    subst hfk
    rfl
  have hsq : ∀ s : Γ(X, U), (hk.appLE W W' hWk).hom ((Xk.presheaf.map (homOfLE hW).op).hom ((i.app
    U).hom s)) =
      (Xk'.presheaf.map (homOfLE hW').op).hom ((i'.app U').hom ((h.appLE U U' hU').hom s)) := by
    intro s
    have e1 : (Xk.presheaf.map (homOfLE hW).op).hom ((i.app U).hom s) = (i.appLE U W hW).hom s :=
      rfl
    have e2 : (Xk'.presheaf.map (homOfLE hW').op).hom ((i'.app U').hom ((h.appLE U U' hU').hom s)) =
        (i'.appLE U' W' hW').hom ((h.appLE U U' hU').hom s) := rfl
    rw [e1, e2]
    have a := congrArg (fun q => q.hom s) (Scheme.Hom.appLE_comp_appLE hk i U W W' hW hWk)
    have b := congrArg (fun q => q.hom s) (Scheme.Hom.appLE_comp_appLE i' h U U' W' hU' hW')
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at a b
    rw [a, b]
    have : ∀ (p q : Xk' ⟶ X) (hpq : p = q) (e₁ : W' ≤ p ⁻¹ᵁ U) (e₂ : W' ≤ q ⁻¹ᵁ U), (p.appLE U W'
      e₁).hom s = (q.appLE U W' e₂).hom s := by
      intro p q hpq e₁ e₂; subst hpq; rfl
    exact this _ _ hhk _ _
  obtain ⟨n, v, s, hδ, hwξ⟩ := hw
  refine ⟨n, v, fun j => (h.appLE U U' hU').hom (s j), ?_, ?_⟩
  · rw [← hδ, map_sum]
    simp only [map_mul, hcompat]
  · intro ξ
    rw [hw' ξ, hwξ ξ]
    change (hk.appLE W W' hWk).hom (∑ j, algebraMap k (Xk.presheaf.obj (op W)) (ξ (v j)) *
      (Xk.presheaf.map (homOfLE hW).op).hom ((i.app U).hom (s j))) =
      ∑ j, algebraMap k (Xk'.presheaf.obj (op W')) (ξ (v j)) * (Xk'.presheaf.map (homOfLE
        hW').op).hom ((i'.app U').hom ((h.appLE U U' hU').hom (s j)))
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, hkcompat, hsq]
end AlgebraicCurves.Geometry.Deformation.Proofs.SmallExtension_IsFibreReading_appLE_of_comp_eq
end ProofImplementation
