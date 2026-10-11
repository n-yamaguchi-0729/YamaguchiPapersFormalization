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
# Independence of a Cartesian presentation of base change

The isomorphism property of a module base-change comparison is independent of the
chosen scheme realizing the same Cartesian square.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_Modules_isIso_baseChangeHom_iff_of_isPullback

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

theorem invE5_map_eqToHom_comp_app {Y : Scheme.{u}} {M N : Y.Modules} (φ : M ⟶ N) {U V : Y.Opens}
    (e : U = V) :
    M.presheaf.map (eqToHom e).op ≫ φ.app U = φ.app V ≫ N.presheaf.map (eqToHom e).op := by
  subst e; simp

theorem invE5_inv_app_map_eqToHom_id_hom_app {Y : Scheme.{u}} {P Q : Y.Modules} (c : P ≅ Q) {W₁
    W₃ : Y.Opens}
    (e : W₃ = W₁) :
    c.inv.app W₁ ≫ P.presheaf.map (eqToHom e).op ≫ 𝟙 _ ≫ c.hom.app W₃ = Q.presheaf.map (eqToHom
        e).op := by
  subst e
  simp [← Scheme.Modules.Hom.comp_app]

theorem invE5_ext_of_unit_app_comp {T T' : Scheme.{u}} (ψ : T' ⟶ T) {M : T.Modules} {N : T'.Modules}
    (f₁ f₂ : (Modules.pullback ψ).obj M ⟶ N)
    (h : ∀ U : T.Opens, ((pullbackPushforwardAdjunction ψ).unit.app M).app U ≫ f₁.app (ψ ⁻¹ᵁ U) =
      ((pullbackPushforwardAdjunction ψ).unit.app M).app U ≫ f₂.app (ψ ⁻¹ᵁ U)) : f₁ = f₂ := by
  apply ((pullbackPushforwardAdjunction ψ).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  refine Scheme.Modules.hom_ext _ _ fun U => ?_
  exact h U

/-- The equivalence of module sheaves on isomorphic schemes given by pushforward along `e.hom`
    and `e.inv`. -/
noncomputable def invE5_pushforwardIsoEquivalence {Y Y' : Scheme.{u}} (e : Y ≅ Y') : Y.Modules ≌
    Y'.Modules :=
  CategoryTheory.Equivalence.mk (pushforward e.hom) (pushforward e.inv)
    ((pushforwardId Y).symm ≪≫ pushforwardCongr e.hom_inv_id.symm ≪≫ (pushforwardComp e.hom
        e.inv).symm)
    (pushforwardComp e.inv e.hom ≪≫ pushforwardCongr e.inv_hom_id ≪≫ pushforwardId Y')


theorem invE5_baseChangeHom_iso_comp {X T T' X₁ X₂ : Scheme.{u}} {π : X ⟶ T} {ψ : T' ⟶ T}
    {π₂ : X₂ ⟶ T'} {g₂ : X₂ ⟶ X} (θ : X₁ ≅ X₂) (h₂ : g₂ ≫ π = π₂ ≫ ψ)
    (h₁ : (θ.hom ≫ g₂) ≫ π = (θ.hom ≫ π₂) ≫ ψ) (F : X.Modules) :
    baseChangeHom h₁ F =
      baseChangeHom h₂ F ≫ (pushforward π₂).map ((pullbackPushforwardAdjunction θ.hom).unit.app
          ((Modules.pullback g₂).obj F)) ≫
        (pushforwardComp θ.hom π₂).hom.app ((Modules.pullback θ.hom).obj ((Modules.pullback
            g₂).obj F)) ≫
          (pushforward (θ.hom ≫ π₂)).map ((pullbackComp θ.hom g₂).hom.app F) := by
  apply invE5_ext_of_unit_app_comp ψ
  intro U
  have e₁ : ((θ.hom ≫ π₂) ≫ ψ) ⁻¹ᵁ U = ((θ.hom ≫ g₂) ≫ π) ⁻¹ᵁ U := by rw [h₁]
  have e₂ : (π₂ ≫ ψ) ⁻¹ᵁ U = (g₂ ≫ π) ⁻¹ᵁ U := by rw [h₂]
  have e₂θ : θ.hom ⁻¹ᵁ ((π₂ ≫ ψ) ⁻¹ᵁ U) = θ.hom ⁻¹ᵁ ((g₂ ≫ π) ⁻¹ᵁ U) := by rw [h₂]
  rw [unit_app_app_comp_baseChangeHom_app π ψ (θ.hom ≫ π₂) (θ.hom ≫ g₂) h₁ F U]
  change _ = ((pullbackPushforwardAdjunction ψ).unit.app ((pushforward π).obj F)).app U ≫
      (baseChangeHom h₂ F).app (ψ ⁻¹ᵁ U) ≫ ((pullbackPushforwardAdjunction θ.hom).unit.app
      ((Modules.pullback g₂).obj F)).app (π₂ ⁻¹ᵁ (ψ ⁻¹ᵁ U)) ≫ 𝟙 _ ≫ ((pullbackComp θ.hom
      g₂).hom.app F).app ((θ.hom ≫ π₂) ⁻¹ᵁ (ψ ⁻¹ᵁ U))
  have t2 : ((pullbackPushforwardAdjunction ψ).unit.app ((pushforward π).obj F)).app U ≫
      (baseChangeHom h₂ F).app (ψ ⁻¹ᵁ U) = ((pullbackPushforwardAdjunction g₂).unit.app F).app
      (π ⁻¹ᵁ U) ≫ ((Modules.pullback g₂).obj F).presheaf.map (eqToHom e₂).op :=
    unit_app_app_comp_baseChangeHom_app π ψ π₂ g₂ h₂ F U
  change _ = (((pullbackPushforwardAdjunction ψ).unit.app ((pushforward π).obj F)).app U ≫
      (baseChangeHom h₂ F).app (ψ ⁻¹ᵁ U)) ≫ ((pullbackPushforwardAdjunction θ.hom).unit.app
      ((Modules.pullback g₂).obj F)).app (π₂ ⁻¹ᵁ (ψ ⁻¹ᵁ U)) ≫ 𝟙 _ ≫ ((pullbackComp θ.hom
      g₂).hom.app F).app ((θ.hom ≫ π₂) ⁻¹ᵁ (ψ ⁻¹ᵁ U))
  erw [t2]
  have u : ((Modules.pullback g₂).obj F).presheaf.map (eqToHom e₂).op ≫
      ((pullbackPushforwardAdjunction θ.hom).unit.app ((Modules.pullback g₂).obj F)).app (π₂ ⁻¹ᵁ
      (ψ ⁻¹ᵁ U)) = ((pullbackPushforwardAdjunction θ.hom).unit.app ((Modules.pullback g₂).obj
      F)).app (g₂ ⁻¹ᵁ (π ⁻¹ᵁ U)) ≫ ((Modules.pullback θ.hom).obj ((Modules.pullback g₂).obj
      F)).presheaf.map (eqToHom e₂θ).op :=
    invE5_map_eqToHom_comp_app ((pullbackPushforwardAdjunction θ.hom).unit.app
        ((Modules.pullback g₂).obj F)) e₂
  change _ = ((pullbackPushforwardAdjunction g₂).unit.app F).app (π ⁻¹ᵁ U) ≫ (((Modules.pullback
      g₂).obj F).presheaf.map (eqToHom e₂).op ≫ ((pullbackPushforwardAdjunction θ.hom).unit.app
      ((Modules.pullback g₂).obj F)).app (π₂ ⁻¹ᵁ (ψ ⁻¹ᵁ U))) ≫ 𝟙 _ ≫ ((pullbackComp θ.hom
      g₂).hom.app F).app ((θ.hom ≫ π₂) ⁻¹ᵁ (ψ ⁻¹ᵁ U))
  erw [u]
  have s3 : ((pullbackPushforwardAdjunction (θ.hom ≫ g₂)).unit.app F).app (π ⁻¹ᵁ U) ≫
      ((pullbackComp θ.hom g₂).inv.app F).app ((θ.hom ≫ g₂) ⁻¹ᵁ (π ⁻¹ᵁ U)) =
      ((pullbackPushforwardAdjunction g₂).unit.app F).app (π ⁻¹ᵁ U) ≫
      ((pullbackPushforwardAdjunction θ.hom).unit.app ((Modules.pullback g₂).obj F)).app (g₂ ⁻¹ᵁ
      (π ⁻¹ᵁ U)) :=
    Scheme.Modules.unit_app_comp_pullbackComp_inv θ.hom g₂ F (π ⁻¹ᵁ U)
  change _ = (((pullbackPushforwardAdjunction g₂).unit.app F).app (π ⁻¹ᵁ U) ≫
      ((pullbackPushforwardAdjunction θ.hom).unit.app ((Modules.pullback g₂).obj F)).app (g₂ ⁻¹ᵁ
      (π ⁻¹ᵁ U))) ≫ ((Modules.pullback θ.hom).obj ((Modules.pullback g₂).obj F)).presheaf.map
      (eqToHom e₂θ).op ≫ 𝟙 _ ≫ ((pullbackComp θ.hom g₂).hom.app F).app ((θ.hom ≫ π₂) ⁻¹ᵁ (ψ ⁻¹ᵁ U))
  erw [← s3]
  have fin : ((pullbackComp θ.hom g₂).inv.app F).app ((θ.hom ≫ g₂) ⁻¹ᵁ (π ⁻¹ᵁ U)) ≫
      ((Modules.pullback θ.hom).obj ((Modules.pullback g₂).obj F)).presheaf.map (eqToHom e₂θ).op
      ≫ 𝟙 _ ≫ ((pullbackComp θ.hom g₂).hom.app F).app ((θ.hom ≫ π₂) ⁻¹ᵁ (ψ ⁻¹ᵁ U)) =
      ((Modules.pullback (θ.hom ≫ g₂)).obj F).presheaf.map (eqToHom e₂θ).op :=
    invE5_inv_app_map_eqToHom_id_hom_app ((pullbackComp θ.hom g₂).app F) e₂θ
  change _ = ((pullbackPushforwardAdjunction (θ.hom ≫ g₂)).unit.app F).app (π ⁻¹ᵁ U) ≫
      (((pullbackComp θ.hom g₂).inv.app F).app ((θ.hom ≫ g₂) ⁻¹ᵁ (π ⁻¹ᵁ U)) ≫ ((Modules.pullback
      θ.hom).obj ((Modules.pullback g₂).obj F)).presheaf.map (eqToHom e₂θ).op ≫ 𝟙 _ ≫
      ((pullbackComp θ.hom g₂).hom.app F).app ((θ.hom ≫ π₂) ⁻¹ᵁ (ψ ⁻¹ᵁ U)))
  erw [fin]
  rfl

theorem _root_.AlgebraicGeometry.Scheme.Modules.isIso_baseChangeHom_iff_of_isPullback
    {X T T' X₁ X₂ : Scheme.{u}} {π : X ⟶ T} {ψ : T' ⟶ T}
    {π₁ : X₁ ⟶ T'} {g₁ : X₁ ⟶ X} {π₂ : X₂ ⟶ T'} {g₂ : X₂ ⟶ X}
    (h₁ : IsPullback g₁ π₁ π ψ) (h₂ : IsPullback g₂ π₂ π ψ) (F : X.Modules) :
    IsIso (Scheme.Modules.baseChangeHom h₁.w F) ↔ IsIso (Scheme.Modules.baseChangeHom h₂.w F) := by
  obtain ⟨θ, hθg, hθπ⟩ : ∃ θ : X₁ ≅ X₂, θ.hom ≫ g₂ = g₁ ∧ θ.hom ≫ π₂ = π₁ :=
    ⟨h₁.isoIsPullback _ _ h₂, IsPullback.isoIsPullback_hom_fst _ _ h₁ h₂,
        IsPullback.isoIsPullback_hom_snd _ _ h₁ h₂⟩
  subst hθg
  subst hθπ
  rw [invE5_baseChangeHom_iso_comp θ h₂.w h₁.w F]
  have : (pushforward θ.hom).IsEquivalence := (invE5_pushforwardIsoEquivalence
      θ).isEquivalence_functor
  have i0 : IsIso ((pullbackPushforwardAdjunction θ.hom).unit.app ((Modules.pullback g₂).obj F))
      := inferInstance
  have i1 : IsIso ((pushforward π₂).map ((pullbackPushforwardAdjunction θ.hom).unit.app
      ((Modules.pullback g₂).obj F))) :=
    Functor.map_isIso _ _
  have i2 : IsIso ((pushforwardComp θ.hom π₂).hom.app ((Modules.pullback θ.hom).obj
      ((Modules.pullback g₂).obj F))) :=
    inferInstance
  have i3 : IsIso ((pushforward (θ.hom ≫ π₂)).map ((pullbackComp θ.hom g₂).hom.app F)) :=
    Functor.map_isIso _ _
  have i23 : IsIso ((pushforwardComp θ.hom π₂).hom.app ((Modules.pullback θ.hom).obj
      ((Modules.pullback g₂).obj F)) ≫
      (pushforward (θ.hom ≫ π₂)).map ((pullbackComp θ.hom g₂).hom.app F)) :=
    @IsIso.comp_isIso _ _ _ _ _ _ _ i2 i3
  have iW : IsIso ((pushforward π₂).map ((pullbackPushforwardAdjunction θ.hom).unit.app
      ((Modules.pullback g₂).obj F)) ≫
      (pushforwardComp θ.hom π₂).hom.app ((Modules.pullback θ.hom).obj ((Modules.pullback
          g₂).obj F)) ≫
        (pushforward (θ.hom ≫ π₂)).map ((pullbackComp θ.hom g₂).hom.app F)) :=
    @IsIso.comp_isIso _ _ _ _ _ _ _ i1 i23
  constructor
  · intro h
    exact @IsIso.of_isIso_comp_right _ _ _ _ _ (baseChangeHom h₂.w F)
      ((pushforward π₂).map ((pullbackPushforwardAdjunction θ.hom).unit.app ((Modules.pullback
          g₂).obj F)) ≫
        (pushforwardComp θ.hom π₂).hom.app ((Modules.pullback θ.hom).obj ((Modules.pullback
            g₂).obj F)) ≫
          (pushforward (θ.hom ≫ π₂)).map ((pullbackComp θ.hom g₂).hom.app F)) iW h
  · intro h
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ h iW

end AlgebraicGeometry.Scheme.Modules
end Scheme_Modules_isIso_baseChangeHom_iff_of_isPullback
end AlgebraicCurves.Geometry.Sheaves.Proofs
end ProofImplementation
