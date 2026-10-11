/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Anthropic FLT source material is identified by code comparison;
the exact source-file correspondence remains unresolved.
Upstream repository: https://github.com/anthropics/fermats-last-theorem
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Geometry.Sheaves.ModulesBaseChangeHom
import SchemeTheory.Modules.PullbackUnitComposition

/-!
# Horizontal composition of base-change comparisons

The module base-change comparison for a composite square agrees with the horizontal
composition of the two comparisons, through the canonical pullback and pushforward maps.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_baseChangeHom_comp_horizontal

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace Modules
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry

theorem phE5_map_eqToHom_comp_app {Y : Scheme.{u}} {M N : Y.Modules} (φ : M ⟶ N) {U V : Y.Opens}
    (e : U = V) :
    M.presheaf.map (eqToHom e).op ≫ φ.app U = φ.app V ≫ N.presheaf.map (eqToHom e).op := by
  subst e; simp

theorem phE5_map_eqToHom_comp_map_eqToHom {Y : Scheme.{u}} (M : Y.Modules) {A₁ A₂ B₁ : Y.Opens}
    (a : A₁ = A₂) (b : B₁ = A₁) :
    M.presheaf.map (eqToHom a).op ≫ M.presheaf.map (eqToHom b).op =
      M.presheaf.map (eqToHom (b.trans a)).op := by
  subst a; subst b; simp

theorem phE5_ext_of_unit_app_comp {T T' : Scheme.{u}} (ψ : T' ⟶ T) {M : T.Modules} {N : T'.Modules}
    (f₁ f₂ : (Modules.pullback ψ).obj M ⟶ N)
    (h : ∀ U : T.Opens, ((pullbackPushforwardAdjunction ψ).unit.app M).app U ≫ f₁.app (ψ ⁻¹ᵁ U) =
      ((pullbackPushforwardAdjunction ψ).unit.app M).app U ≫ f₂.app (ψ ⁻¹ᵁ U)) : f₁ = f₂ := by
  apply ((pullbackPushforwardAdjunction ψ).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  refine Scheme.Modules.hom_ext _ _ fun U => ?_
  exact h U

theorem phE5_inv_app_map_eqToHom_hom_app {Y : Scheme.{u}} {P Q : Y.Modules} (c : P ≅ Q) {W₁ W₃ :
    Y.Opens}
    (e : W₃ = W₁) :
    c.inv.app W₁ ≫ P.presheaf.map (eqToHom e).op ≫ c.hom.app W₃ = Q.presheaf.map (eqToHom e).op
        := by
  subst e
  simp [← Scheme.Modules.Hom.comp_app]

theorem _root_.AlgebraicGeometry.Scheme.Modules.baseChangeHom_comp_horizontal
    {X T X' T' X'' T'' : Scheme.{u}} {π : X ⟶ T} {ψ : T' ⟶ T} {π' : X' ⟶ T'} {g' : X' ⟶ X}
    {ψ' : T'' ⟶ T'} {π'' : X'' ⟶ T''} {g'' : X'' ⟶ X'}
    (h₁ : g' ≫ π = π' ≫ ψ) (h₂ : g'' ≫ π' = π'' ≫ ψ') (h₁₂ : (g'' ≫ g') ≫ π = π'' ≫ (ψ' ≫ ψ))
    (F : X.Modules) :
    Scheme.Modules.baseChangeHom h₁₂ F =
      (Scheme.Modules.pullbackComp ψ' ψ).inv.app ((Scheme.Modules.pushforward π).obj F) ≫
        (Scheme.Modules.pullback ψ').map (Scheme.Modules.baseChangeHom h₁ F) ≫
          Scheme.Modules.baseChangeHom h₂ ((Scheme.Modules.pullback g').obj F) ≫
            (Scheme.Modules.pushforward π'').map ((Scheme.Modules.pullbackComp g'' g').hom.app
                F) := by
  apply phE5_ext_of_unit_app_comp (ψ' ≫ ψ)
  intro U
  have e₁ : (π' ≫ ψ) ⁻¹ᵁ U = (g' ≫ π) ⁻¹ᵁ U := by rw [h₁]
  have e₂ : (π'' ≫ ψ') ⁻¹ᵁ (ψ ⁻¹ᵁ U) = (g'' ≫ π') ⁻¹ᵁ (ψ ⁻¹ᵁ U) := by rw [h₂]
  have e₁g : g'' ⁻¹ᵁ ((π' ≫ ψ) ⁻¹ᵁ U) = g'' ⁻¹ᵁ ((g' ≫ π) ⁻¹ᵁ U) := by rw [h₁]
  rw [unit_app_app_comp_baseChangeHom_app π (ψ' ≫ ψ) π'' (g'' ≫ g') h₁₂ F U]
  have s0 : ((pullbackPushforwardAdjunction (ψ' ≫ ψ)).unit.app ((pushforward π).obj F)).app U ≫
      ((pullbackComp ψ' ψ).inv.app ((pushforward π).obj F)).app ((ψ' ≫ ψ) ⁻¹ᵁ U) =
      ((pullbackPushforwardAdjunction ψ).unit.app ((pushforward π).obj F)).app U ≫
      ((pullbackPushforwardAdjunction ψ').unit.app ((Modules.pullback ψ).obj ((pushforward
      π).obj F))).app (ψ ⁻¹ᵁ U) :=
    Scheme.Modules.unit_app_comp_pullbackComp_inv ψ' ψ ((pushforward π).obj F) U
  change _ = (((pullbackPushforwardAdjunction (ψ' ≫ ψ)).unit.app ((pushforward π).obj F)).app U
      ≫ ((pullbackComp ψ' ψ).inv.app ((pushforward π).obj F)).app ((ψ' ≫ ψ) ⁻¹ᵁ U)) ≫
      ((Modules.pullback ψ').map (baseChangeHom h₁ F)).app ((ψ' ≫ ψ) ⁻¹ᵁ U) ≫ (baseChangeHom h₂
      ((Modules.pullback g').obj F)).app ((ψ' ≫ ψ) ⁻¹ᵁ U) ≫ ((pullbackComp g'' g').hom.app
      F).app (π'' ⁻¹ᵁ ((ψ' ≫ ψ) ⁻¹ᵁ U))
  erw [s0]
  have s1 : ((pullbackPushforwardAdjunction ψ').unit.app ((Modules.pullback ψ).obj ((pushforward
      π).obj F))).app (ψ ⁻¹ᵁ U) ≫ ((Modules.pullback ψ').map (baseChangeHom h₁ F)).app ((ψ' ≫ ψ)
      ⁻¹ᵁ U) = (baseChangeHom h₁ F).app (ψ ⁻¹ᵁ U) ≫ ((pullbackPushforwardAdjunction ψ').unit.app
      ((pushforward π').obj ((Modules.pullback g').obj F))).app (ψ ⁻¹ᵁ U) := by
    have n := congrArg (fun t => Scheme.Modules.Hom.app t (ψ ⁻¹ᵁ U))
      ((pullbackPushforwardAdjunction ψ').unit.naturality (baseChangeHom h₁ F))
    simp only [Functor.id_map, Functor.comp_map, Scheme.Modules.Hom.comp_app] at n
    exact n.symm
  change _ = ((pullbackPushforwardAdjunction ψ).unit.app ((pushforward π).obj F)).app U ≫
      (((pullbackPushforwardAdjunction ψ').unit.app ((Modules.pullback ψ).obj ((pushforward
      π).obj F))).app (ψ ⁻¹ᵁ U) ≫ ((Modules.pullback ψ').map (baseChangeHom h₁ F)).app ((ψ' ≫ ψ)
      ⁻¹ᵁ U)) ≫ (baseChangeHom h₂ ((Modules.pullback g').obj F)).app ((ψ' ≫ ψ) ⁻¹ᵁ U) ≫
      ((pullbackComp g'' g').hom.app F).app (π'' ⁻¹ᵁ ((ψ' ≫ ψ) ⁻¹ᵁ U))
  erw [s1]
  have t1 : ((pullbackPushforwardAdjunction ψ).unit.app ((pushforward π).obj F)).app U ≫
      (baseChangeHom h₁ F).app (ψ ⁻¹ᵁ U) = ((pullbackPushforwardAdjunction g').unit.app F).app
      (π ⁻¹ᵁ U) ≫ ((Modules.pullback g').obj F).presheaf.map (eqToHom e₁).op :=
    unit_app_app_comp_baseChangeHom_app π ψ π' g' h₁ F U
  change _ = (((pullbackPushforwardAdjunction ψ).unit.app ((pushforward π).obj F)).app U ≫
      (baseChangeHom h₁ F).app (ψ ⁻¹ᵁ U)) ≫ ((pullbackPushforwardAdjunction ψ').unit.app
      ((pushforward π').obj ((Modules.pullback g').obj F))).app (ψ ⁻¹ᵁ U) ≫ (baseChangeHom h₂
      ((Modules.pullback g').obj F)).app ((ψ' ≫ ψ) ⁻¹ᵁ U) ≫ ((pullbackComp g'' g').hom.app
      F).app (π'' ⁻¹ᵁ ((ψ' ≫ ψ) ⁻¹ᵁ U))
  erw [t1]
  have t2 : ((pullbackPushforwardAdjunction ψ').unit.app ((pushforward π').obj
      ((Modules.pullback g').obj F))).app (ψ ⁻¹ᵁ U) ≫ (baseChangeHom h₂ ((Modules.pullback
      g').obj F)).app ((ψ' ≫ ψ) ⁻¹ᵁ U) = ((pullbackPushforwardAdjunction g'').unit.app
      ((Modules.pullback g').obj F)).app (π' ⁻¹ᵁ (ψ ⁻¹ᵁ U)) ≫ ((Modules.pullback g'').obj
      ((Modules.pullback g').obj F)).presheaf.map (eqToHom e₂).op :=
    unit_app_app_comp_baseChangeHom_app π' ψ' π'' g'' h₂ ((Modules.pullback g').obj F) (ψ ⁻¹ᵁ U)
  change _ = ((pullbackPushforwardAdjunction g').unit.app F).app (π ⁻¹ᵁ U) ≫ ((Modules.pullback
      g').obj F).presheaf.map (eqToHom e₁).op ≫ (((pullbackPushforwardAdjunction ψ').unit.app
      ((pushforward π').obj ((Modules.pullback g').obj F))).app (ψ ⁻¹ᵁ U) ≫ (baseChangeHom h₂
      ((Modules.pullback g').obj F)).app ((ψ' ≫ ψ) ⁻¹ᵁ U)) ≫ ((pullbackComp g'' g').hom.app
      F).app (π'' ⁻¹ᵁ ((ψ' ≫ ψ) ⁻¹ᵁ U))
  erw [t2]
  have u4 : ((Modules.pullback g').obj F).presheaf.map (eqToHom e₁).op ≫
      ((pullbackPushforwardAdjunction g'').unit.app ((Modules.pullback g').obj F)).app (π' ⁻¹ᵁ
      (ψ ⁻¹ᵁ U)) = ((pullbackPushforwardAdjunction g'').unit.app ((Modules.pullback g').obj
      F)).app (g' ⁻¹ᵁ (π ⁻¹ᵁ U)) ≫ ((Modules.pullback g'').obj ((Modules.pullback g').obj
      F)).presheaf.map (eqToHom e₁g).op :=
    phE5_map_eqToHom_comp_app ((pullbackPushforwardAdjunction g'').unit.app ((Modules.pullback
        g').obj F)) e₁
  change _ = ((pullbackPushforwardAdjunction g').unit.app F).app (π ⁻¹ᵁ U) ≫ (((Modules.pullback
      g').obj F).presheaf.map (eqToHom e₁).op ≫ ((pullbackPushforwardAdjunction g'').unit.app
      ((Modules.pullback g').obj F)).app (π' ⁻¹ᵁ (ψ ⁻¹ᵁ U))) ≫ ((Modules.pullback g'').obj
      ((Modules.pullback g').obj F)).presheaf.map (eqToHom e₂).op ≫ ((pullbackComp g''
      g').hom.app F).app (π'' ⁻¹ᵁ ((ψ' ≫ ψ) ⁻¹ᵁ U))
  erw [u4]
  have s3 : ((pullbackPushforwardAdjunction (g'' ≫ g')).unit.app F).app (π ⁻¹ᵁ U) ≫
      ((pullbackComp g'' g').inv.app F).app ((g'' ≫ g') ⁻¹ᵁ (π ⁻¹ᵁ U)) =
      ((pullbackPushforwardAdjunction g').unit.app F).app (π ⁻¹ᵁ U) ≫
      ((pullbackPushforwardAdjunction g'').unit.app ((Modules.pullback g').obj F)).app (g' ⁻¹ᵁ
      (π ⁻¹ᵁ U)) :=
    Scheme.Modules.unit_app_comp_pullbackComp_inv g'' g' F (π ⁻¹ᵁ U)
  change _ = (((pullbackPushforwardAdjunction g').unit.app F).app (π ⁻¹ᵁ U) ≫
      ((pullbackPushforwardAdjunction g'').unit.app ((Modules.pullback g').obj F)).app (g' ⁻¹ᵁ
      (π ⁻¹ᵁ U))) ≫ ((Modules.pullback g'').obj ((Modules.pullback g').obj F)).presheaf.map
      (eqToHom e₁g).op ≫ ((Modules.pullback g'').obj ((Modules.pullback g').obj F)).presheaf.map
      (eqToHom e₂).op ≫ ((pullbackComp g'' g').hom.app F).app (π'' ⁻¹ᵁ ((ψ' ≫ ψ) ⁻¹ᵁ U))
  erw [← s3]
  have m : ((Modules.pullback g'').obj ((Modules.pullback g').obj F)).presheaf.map (eqToHom
      e₁g).op ≫ ((Modules.pullback g'').obj ((Modules.pullback g').obj F)).presheaf.map (eqToHom
      e₂).op = ((Modules.pullback g'').obj ((Modules.pullback g').obj F)).presheaf.map (eqToHom
      (e₂.trans e₁g)).op :=
    phE5_map_eqToHom_comp_map_eqToHom ((Modules.pullback g'').obj ((Modules.pullback g').obj F))
        e₁g e₂
  change _ = ((pullbackPushforwardAdjunction (g'' ≫ g')).unit.app F).app (π ⁻¹ᵁ U) ≫
      ((pullbackComp g'' g').inv.app F).app ((g'' ≫ g') ⁻¹ᵁ (π ⁻¹ᵁ U)) ≫ (((Modules.pullback
      g'').obj ((Modules.pullback g').obj F)).presheaf.map (eqToHom e₁g).op ≫ ((Modules.pullback
      g'').obj ((Modules.pullback g').obj F)).presheaf.map (eqToHom e₂).op) ≫ ((pullbackComp g''
      g').hom.app F).app (π'' ⁻¹ᵁ ((ψ' ≫ ψ) ⁻¹ᵁ U))
  erw [m]
  have fin : ((pullbackComp g'' g').inv.app F).app ((g'' ≫ g') ⁻¹ᵁ (π ⁻¹ᵁ U)) ≫
      ((Modules.pullback g'').obj ((Modules.pullback g').obj F)).presheaf.map (eqToHom (e₂.trans
      e₁g)).op ≫ ((pullbackComp g'' g').hom.app F).app (π'' ⁻¹ᵁ ((ψ' ≫ ψ) ⁻¹ᵁ U)) =
      ((Modules.pullback (g'' ≫ g')).obj F).presheaf.map (eqToHom (e₂.trans e₁g)).op :=
    phE5_inv_app_map_eqToHom_hom_app ((pullbackComp g'' g').app F) (e₂.trans e₁g)
  change _ = ((pullbackPushforwardAdjunction (g'' ≫ g')).unit.app F).app (π ⁻¹ᵁ U) ≫
      (((pullbackComp g'' g').inv.app F).app ((g'' ≫ g') ⁻¹ᵁ (π ⁻¹ᵁ U)) ≫ ((Modules.pullback
      g'').obj ((Modules.pullback g').obj F)).presheaf.map (eqToHom (e₂.trans e₁g)).op ≫
      ((pullbackComp g'' g').hom.app F).app (π'' ⁻¹ᵁ ((ψ' ≫ ψ) ⁻¹ᵁ U)))
  erw [fin]
  rfl

end AlgebraicGeometry.Scheme.Modules
end AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_baseChangeHom_comp_horizontal
end ProofImplementation
