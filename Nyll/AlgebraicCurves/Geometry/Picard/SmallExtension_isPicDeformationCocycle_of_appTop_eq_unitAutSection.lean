/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_SmallExtension_isPicDeformationCocycle_of_appTop_eq_unitAutSection.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Tactic.Ring.RingNF
import Nyll.SchemeTheory.Cohomology.Cech.OrderedAffineCoverCech
import Nyll.AlgebraicCurves.Geometry.Schemes.OrderedAffineCoverComap
import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.AlgebraicCurves.Geometry.Picard.CechObstruction
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_unitAutSection_trans_and_unitAutSection_refl
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_unitAutSection_pullbackUnitIso_conj_opensI_eq_app_one

/-!
# Small Extension is Pic Deformation Cocycle of app Top eq unit Aut Section
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Picard.Proofs
namespace SmallExtension_isPicDeformationCocycle_of_appTop_eq_unitAutSection

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

universe u

namespace PicDefRescale

theorem uAS_trans {Y : Scheme.{u}} (W : Y.Opens)
    (e₁ e₂ : SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf ≅ SheafOfModules.unit (W :
      Scheme.{u}).ringCatSheaf) :
    Scheme.Modules.unitAutSection W (e₁ ≪≫ e₂) =
      Scheme.Modules.unitAutSection W e₁ * Scheme.Modules.unitAutSection W e₂ :=
  (Scheme.Modules.unitAutSection_trans_and_unitAutSection_refl W).1 e₁ e₂

theorem unit_app_one_res {Y : Scheme.{u}} (ψ : SheafOfModules.unit Y.ringCatSheaf ≅
  SheafOfModules.unit Y.ringCatSheaf)
    {U V : Y.Opens} (i : V ⟶ U) :
    (Y.presheaf.map i.op).hom ((ψ.hom.val.app (op U)).hom (1 : Y.presheaf.obj (op U))) =
      (ψ.hom.val.app (op V)).hom (1 : Y.presheaf.obj (op V)) := by
  have h := PresheafOfModules.naturality_apply ψ.hom.val i.op (1 : Y.presheaf.obj (op U))
  erw [PresheafOfModules.unit_map_one] at h
  exact h.symm

theorem uAS_conj_res {Y : Scheme.{u}} (W : Y.Opens)
    (ψ : SheafOfModules.unit Y.ringCatSheaf ≅ SheafOfModules.unit Y.ringCatSheaf) :
    Scheme.Modules.unitAutSection W
        ((Scheme.Modules.pullbackUnitIso W.ι).symm ≪≫ (Scheme.Modules.pullback W.ι).mapIso ψ ≪≫
          Scheme.Modules.pullbackUnitIso W.ι) =
      (Y.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom
        (Scheme.Modules.unitAutSection ⊤
          ((Scheme.Modules.pullbackUnitIso (⊤ : Y.Opens).ι).symm ≪≫
            (Scheme.Modules.pullback (⊤ : Y.Opens).ι).mapIso ψ ≪≫
            Scheme.Modules.pullbackUnitIso (⊤ : Y.Opens).ι)) := by
  rw [Scheme.Modules.unitAutSection_pullbackUnitIso_conj_opensI_eq_app_one,
    Scheme.Modules.unitAutSection_pullbackUnitIso_conj_opensI_eq_app_one, unit_app_one_res]

variable {X : Scheme.{u}}

theorem res_res {U V : X.Opens} (h : V ≤ U) (x : Γ(X, ⊤)) :
    (X.presheaf.map (homOfLE h).op).hom ((X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom x) =
      (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom x := by
  have hc : X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op ≫ X.presheaf.map (homOfLE h).op =
      X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op := by
    rw [← Functor.map_comp]; rfl
  rw [← hc]; rfl

end PicDefRescale

open PicDefRescale in
theorem _root_.AlgebraicGeometry.SmallExtension.isPicDeformationCocycle_of_appTop_eq_unitAutSection
    {B₁ : Type u} [CommRing B₁] {k : Type u} [Field k]
    (V : Type u) [AddCommGroup V] [Module k V] [Module B₁ V] (ι : V →ₗ[B₁] B₁)
    {X X₀ Xk : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B₁))
    (fk : Xk ⟶ Spec (CommRingCat.of k)) (i : Xk ⟶ X) [IsAffineHom i]
    (g : X₀ ⟶ X) [IsAffineHom g]
    (𝒰 : X.OrderedAffineCover)
    (M : X.Modules)
    (φ₀ φ₀' : (Scheme.Modules.pullback g).obj M ≅ SheafOfModules.unit X₀.ringCatSheaf)
    (u u' : Γ(X, ⊤)) (huu' : u * u' = 1)
    (hu : g.appTop.hom u =
      Scheme.Modules.unitAutSection ⊤
        ((Scheme.Modules.pullbackUnitIso (⊤ : X₀.Opens).ι).symm ≪≫
          (Scheme.Modules.pullback (⊤ : X₀.Opens).ι).mapIso (φ₀.symm ≪≫ φ₀') ≪≫
          Scheme.Modules.pullbackUnitIso (⊤ : X₀.Opens).ι))
    (w : Module.Dual k V →ₗ[k] (OModulePresheaf.unit fk).cochain (𝒰.comap i) 1)
    (hw : SmallExtension.IsPicDeformationCocycle V ι f fk i g 𝒰 M φ₀ w) :
    SmallExtension.IsPicDeformationCocycle V ι f fk i g 𝒰 M φ₀' w := by
  obtain ⟨τ, ea, ea', h1, h2, h3⟩ := hw
  let ru : ∀ a : 𝒰.ι, Γ(X, 𝒰.U a) := fun a => (X.presheaf.map (homOfLE (le_top : 𝒰.U a ≤
    ⊤)).op).hom u
  let ru' : ∀ a : 𝒰.ι, Γ(X, 𝒰.U a) := fun a => (X.presheaf.map (homOfLE (le_top : 𝒰.U a ≤
    ⊤)).op).hom u'
  have hru : ∀ a, ru a * ru' a = 1 := fun a => by
    simp only [ru, ru', ← map_mul, huu', map_one]
  refine ⟨τ, fun a => ea a * ru a, fun a => ea' a * ru' a, fun a => ?_, fun a => ?_, fun s => ?_⟩
  · calc ea a * ru a * (ea' a * ru' a) = (ea a * ea' a) * (ru a * ru' a) := by ring
      _ = 1 := by rw [h1 a, hru a, one_mul]
  · let W : X₀.Opens := g ⁻¹ᵁ 𝒰.U a
    let F : X₀.Modules ⥤ (W : Scheme.{u}).Modules := Scheme.Modules.pullback W.ι
    let t : F.obj ((Scheme.Modules.pullback g).obj M) ≅
        SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf := τ.comap g a
    let q : F.obj (SheafOfModules.unit X₀.ringCatSheaf) ≅
        SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf := Scheme.Modules.pullbackUnitIso W.ι
    have hsplit : t.symm ≪≫ F.mapIso φ₀' ≪≫ q =
        (t.symm ≪≫ F.mapIso φ₀ ≪≫ q) ≪≫
          (q.symm ≪≫ F.mapIso (φ₀.symm ≪≫ φ₀') ≪≫ q) := by
      apply Iso.ext
      change t.inv ≫ F.map φ₀'.hom ≫ q.hom =
        (t.inv ≫ F.map φ₀.hom ≫ q.hom) ≫
          (q.inv ≫ F.map (φ₀.inv ≫ φ₀'.hom) ≫ q.hom)
      symm
      calc
        (t.inv ≫ F.map φ₀.hom ≫ q.hom) ≫
            (q.inv ≫ F.map (φ₀.inv ≫ φ₀'.hom) ≫ q.hom) =
            t.inv ≫ F.map φ₀.hom ≫ F.map (φ₀.inv ≫ φ₀'.hom) ≫ q.hom := by
          exact (Category.assoc t.inv (F.map φ₀.hom ≫ q.hom)
            (q.inv ≫ F.map (φ₀.inv ≫ φ₀'.hom) ≫ q.hom)).trans
            (congrArg (fun z : F.obj ((Scheme.Modules.pullback g).obj M) ⟶
                SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf => t.inv ≫ z)
              ((Category.assoc (F.map φ₀.hom) q.hom
                (q.inv ≫ F.map (φ₀.inv ≫ φ₀'.hom) ≫ q.hom)).trans
                (congrArg (fun z : F.obj (SheafOfModules.unit X₀.ringCatSheaf) ⟶
                    SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf => F.map φ₀.hom ≫ z)
                  (q.hom_inv_id_assoc (F.map (φ₀.inv ≫ φ₀'.hom) ≫ q.hom)))))
        _ = t.inv ≫ F.map (φ₀.hom ≫ φ₀.inv ≫ φ₀'.hom) ≫ q.hom := by
          exact congrArg (fun z : F.obj ((Scheme.Modules.pullback g).obj M) ⟶
              SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf => t.inv ≫ z)
            (F.map_comp_assoc φ₀.hom (φ₀.inv ≫ φ₀'.hom) q.hom).symm
        _ = t.inv ≫ F.map φ₀'.hom ≫ q.hom := by
          exact congrArg (fun z : (Scheme.Modules.pullback g).obj M ⟶
              SheafOfModules.unit X₀.ringCatSheaf => t.inv ≫ F.map z ≫ q.hom)
            (φ₀.hom_inv_id_assoc φ₀'.hom)
    have key : Scheme.Modules.unitAutSection W (t.symm ≪≫ F.mapIso φ₀' ≪≫ q) =
        Scheme.Modules.unitAutSection W (t.symm ≪≫ F.mapIso φ₀ ≪≫ q) *
          Scheme.Modules.unitAutSection W (q.symm ≪≫ F.mapIso (φ₀.symm ≪≫ φ₀') ≪≫ q) :=
      (congrArg (Scheme.Modules.unitAutSection W) hsplit).trans
        (uAS_trans W (t.symm ≪≫ F.mapIso φ₀ ≪≫ q)
          (q.symm ≪≫ F.mapIso (φ₀.symm ≪≫ φ₀') ≪≫ q))
    have hruNat : (g.app (𝒰.U a)).hom (ru a) =
        (X₀.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom (g.appTop.hom u) := by
      exact congrArg (fun φ : Γ(X, ⊤) ⟶ Γ(X₀, W) => φ.hom u)
        (g.naturality (homOfLE (le_top : 𝒰.U a ≤ ⊤)).op)
    have hruSection : (g.app (𝒰.U a)).hom (ru a) =
        Scheme.Modules.unitAutSection W (q.symm ≪≫ F.mapIso (φ₀.symm ≪≫ φ₀') ≪≫ q) :=
      hruNat.trans ((congrArg
        (fun x : Γ(X₀, ⊤) =>
          (X₀.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom x) hu).trans
        (uAS_conj_res W (φ₀.symm ≪≫ φ₀')).symm)
    have h2a : (g.app (𝒰.U a)).hom (ea a) =
        Scheme.Modules.unitAutSection W (t.symm ≪≫ F.mapIso φ₀ ≪≫ q) := h2 a
    exact (map_mul (g.app (𝒰.U a)).hom (ea a) (ru a)).trans
      ((congrArg₂ (fun x y : Γ(X₀, W) => x * y) h2a hruSection).trans key.symm)
  · have hres : (X.presheaf.map (homOfLE (𝒰.inter_le s 0)).op).hom (ru' (s.1 0)) *
        (X.presheaf.map (homOfLE (𝒰.inter_le s 1)).op).hom (ru (s.1 1)) = 1 := by
      simp only [ru, ru', res_res, ← map_mul, ← map_one (X.presheaf.map (homOfLE (le_top : 𝒰.inter
        s ≤ ⊤)).op).hom,
        mul_comm u' u, huu']
    have key : τ.transition s *
          (X.presheaf.map (homOfLE (𝒰.inter_le s 0)).op).hom (ea' (s.1 0) * ru' (s.1 0)) *
          (X.presheaf.map (homOfLE (𝒰.inter_le s 1)).op).hom (ea (s.1 1) * ru (s.1 1)) - 1 =
        τ.transition s *
          (X.presheaf.map (homOfLE (𝒰.inter_le s 0)).op).hom (ea' (s.1 0)) *
          (X.presheaf.map (homOfLE (𝒰.inter_le s 1)).op).hom (ea (s.1 1)) - 1 := by
      rw [map_mul, map_mul]
      calc _ = τ.transition s *
            (X.presheaf.map (homOfLE (𝒰.inter_le s 0)).op).hom (ea' (s.1 0)) *
            (X.presheaf.map (homOfLE (𝒰.inter_le s 1)).op).hom (ea (s.1 1)) *
            ((X.presheaf.map (homOfLE (𝒰.inter_le s 0)).op).hom (ru' (s.1 0)) *
              (X.presheaf.map (homOfLE (𝒰.inter_le s 1)).op).hom (ru (s.1 1))) - 1 := by ring
        _ = _ := by rw [hres, mul_one]
    rw [key]
    exact h3 s
end SmallExtension_isPicDeformationCocycle_of_appTop_eq_unitAutSection
end AlgebraicCurves.Geometry.Picard.Proofs
end ProofImplementation
