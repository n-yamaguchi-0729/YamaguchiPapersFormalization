/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_isIso_baseChangeHom_of_forall_exists_isPullback.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesBaseChangeHom
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_baseChangeHom_comp_horizontal
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_isIso_baseChangeHom_iff_of_isPullback
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_isIso_baseChangeHom_of_isOpenImmersion
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_Hom_isIso_of_isIso_app_of_iSup_eq_top
import Nyll.SchemeTheory.Modules.OpenImmersionUnit

/-!
# Local Cartesian tests for the base-change comparison

The base-change comparison is an isomorphism when it is an isomorphism on compatible
Cartesian presentations over neighbourhoods of every point of the new base.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_Modules_isIso_baseChangeHom_of_forall_exists_isPullback

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

theorem n2E5_isIso_baseChangeHom_congr_bottom {X T X' T' : Scheme.{u}} {π : X ⟶ T} {π' : X' ⟶
    T'} {g' : X' ⟶ X}
    {b b' : T' ⟶ T} (eb : b = b') (h : g' ≫ π = π' ≫ b) (h' : g' ≫ π = π' ≫ b') (F : X.Modules) :
    IsIso (baseChangeHom h F) ↔ IsIso (baseChangeHom h' F) := by
  subst eb
  exact Iff.rfl

theorem n2E5_isIso_app_of_isIso_pullback_map {T' S' : Scheme.{u}} (j : S' ⟶ T') [IsOpenImmersion j]
    {M N : T'.Modules} (β : M ⟶ N) (hβ : IsIso ((Scheme.Modules.pullback j).map β))
    (V : T'.Opens) (hV : V ≤ j.opensRange) :
    IsIso (β.app V) := by
  have n := congrArg (fun t => Scheme.Modules.Hom.app t V) ((pullbackPushforwardAdjunction
      j).unit.naturality β)
  simp only [Functor.id_map, Functor.comp_map, Functor.id_obj, Functor.comp_obj,
      Scheme.Modules.Hom.comp_app] at n
  have i1 : IsIso (((pullbackPushforwardAdjunction j).unit.app M).app V) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (bijective_unit_app_of_le_opensRange j M V hV)
  have i2 : IsIso (((pullbackPushforwardAdjunction j).unit.app N).app V) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (bijective_unit_app_of_le_opensRange j N V hV)
  have i3 : IsIso (((pushforward j).map ((Scheme.Modules.pullback j).map β)).app V) :=
    (Hom.isIso_iff_isIso_app.mp hβ) _
  have hc : IsIso ((((pullbackPushforwardAdjunction j).unit.app M).app V) ≫
      ((pushforward j).map ((Scheme.Modules.pullback j).map β)).app V) :=
    @IsIso.comp_isIso _ _ _ _ _ _ _ i1 i3
  exact @IsIso.of_isIso_fac_right _ _ _ _ _ _ _ _ i2 hc n

theorem _root_.AlgebraicGeometry.Scheme.Modules.isIso_baseChangeHom_of_forall_exists_isPullback
    {X T X' T' : Scheme.{u}} {π : X ⟶ T} {ψ : T' ⟶ T} {π' : X' ⟶ T'} {g' : X' ⟶ X}
    (hcart : IsPullback g' π' π ψ) (F : X.Modules)
    (h : ∀ y : T', ∃ (W : T.Opens) (W' : T'.Opens) (_ : y ∈ W') (S S' Y Y' : Scheme.{u})
      (e : S ≅ W.toScheme) (e' : S' ≅ W'.toScheme) (φ : S' ⟶ S)
      (_ : (e'.hom ≫ W'.ι) ≫ ψ = φ ≫ e.hom ≫ W.ι)
      (ρ : Y ⟶ S) (u : Y ⟶ X) (_ : IsPullback u ρ π (e.hom ≫ W.ι))
      (ρ' : Y' ⟶ S') (v : Y' ⟶ Y) (hv : IsPullback v ρ' ρ φ),
      IsIso (Scheme.Modules.baseChangeHom hv.w ((Scheme.Modules.pullback u).obj F))) :
    IsIso (Scheme.Modules.baseChangeHom hcart.w F) := by
  choose W W' hy S S' Y Y' e e' φ heq ρ u hu ρ' v hv hiso using h
  refine Hom.isIso_of_isIso_app_of_iSup_eq_top _ W' ?_ ?_
  · exact eq_top_iff.2 fun y _ => TopologicalSpace.Opens.mem_iSup.2 ⟨y, hy y⟩
  intro y V hVle
  have : IsOpenImmersion ((e' y).hom ≫ (W' y).ι) := inferInstance
  have : IsOpenImmersion ((e y).hom ≫ (W y).ι) := inferInstance
  have sqj := IsPullback.of_hasPullback π' ((e' y).hom ≫ (W' y).ι)
  have hbig : IsPullback (pullback.fst π' ((e' y).hom ≫ (W' y).ι) ≫ g') (pullback.snd π' ((e'
      y).hom ≫ (W' y).ι))
      π (((e' y).hom ≫ (W' y).ι) ≫ ψ) := sqj.paste_horiz hcart
  have ph1 := baseChangeHom_comp_horizontal hcart.w sqj.w hbig.w F
  have ioi1 : IsIso (baseChangeHom sqj.w ((Scheme.Modules.pullback g').obj F)) :=
    isIso_baseChangeHom_of_isOpenImmersion sqj ((Scheme.Modules.pullback g').obj F)
  have hvu : IsPullback (v y ≫ u y) (ρ' y) π (((e' y).hom ≫ (W' y).ι) ≫ ψ) := by
    rw [heq y]
    exact (hv y).paste_horiz (hu y)
  have h12 : (v y ≫ u y) ≫ π = ρ' y ≫ (φ y ≫ (e y).hom ≫ (W y).ι) := ((hv y).paste_horiz (hu y)).w
  have ph2 := baseChangeHom_comp_horizontal (hu y).w (hv y).w h12 F
  have ioi2 : IsIso (baseChangeHom (hu y).w F) := isIso_baseChangeHom_of_isOpenImmersion (hu y) F
  have : IsIso (baseChangeHom (hv y).w ((Scheme.Modules.pullback (u y)).obj F)) := hiso y
  have hA : IsIso (baseChangeHom h12 F) := by
    rw [ph2]
    have j1 : IsIso ((pullbackComp (φ y) ((e y).hom ≫ (W y).ι)).inv.app ((pushforward π).obj F))
        := inferInstance
    have j2 : IsIso ((Scheme.Modules.pullback (φ y)).map (baseChangeHom (hu y).w F)) :=
      @Functor.map_isIso _ _ _ _ _ _ _ _ ioi2
    have j3 : IsIso (baseChangeHom (hv y).w ((Scheme.Modules.pullback (u y)).obj F)) := hiso y
    have j4 : IsIso ((pushforward (ρ' y)).map ((pullbackComp (v y) (u y)).hom.app F)) :=
        Functor.map_isIso _ _
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ j1 (@IsIso.comp_isIso _ _ _ _ _ _ _ j2
        (@IsIso.comp_isIso _ _ _ _ _ _ _ j3 j4))
  have hB : IsIso (baseChangeHom hvu.w F) :=
    (n2E5_isIso_baseChangeHom_congr_bottom (heq y).symm h12 hvu.w F).mp hA
  have hC : IsIso (baseChangeHom hbig.w F) := (isIso_baseChangeHom_iff_of_isPullback hbig hvu
      F).mpr hB
  have hD : IsIso ((Scheme.Modules.pullback ((e' y).hom ≫ (W' y).ι)).map
      (baseChangeHom hcart.w F)) := by
    rw [ph1] at hC
    have h1 := IsIso.of_isIso_comp_left ((pullbackComp ((e' y).hom ≫ (W' y).ι) ψ).inv.app
        ((pushforward π).obj F))
      ((Scheme.Modules.pullback ((e' y).hom ≫ (W' y).ι)).map (baseChangeHom hcart.w F) ≫
        baseChangeHom sqj.w ((Scheme.Modules.pullback g').obj F) ≫
          (pushforward (pullback.snd π' ((e' y).hom ≫ (W' y).ι))).map
            ((pullbackComp (pullback.fst π' ((e' y).hom ≫ (W' y).ι)) g').hom.app F))
    have k2 : IsIso ((pushforward (pullback.snd π' ((e' y).hom ≫ (W' y).ι))).map
        ((pullbackComp (pullback.fst π' ((e' y).hom ≫ (W' y).ι)) g').hom.app F)) :=
            Functor.map_isIso _ _
    have k12 : IsIso (baseChangeHom sqj.w ((Scheme.Modules.pullback g').obj F) ≫
        (pushforward (pullback.snd π' ((e' y).hom ≫ (W' y).ι))).map
          ((pullbackComp (pullback.fst π' ((e' y).hom ≫ (W' y).ι)) g').hom.app F)) :=
      @IsIso.comp_isIso _ _ _ _ _ _ _ ioi1 k2
    exact @IsIso.of_isIso_comp_right _ _ _ _ _
      ((Scheme.Modules.pullback ((e' y).hom ≫ (W' y).ι)).map (baseChangeHom hcart.w F))
      (baseChangeHom sqj.w ((Scheme.Modules.pullback g').obj F) ≫
        (pushforward (pullback.snd π' ((e' y).hom ≫ (W' y).ι))).map
          ((pullbackComp (pullback.fst π' ((e' y).hom ≫ (W' y).ι)) g').hom.app F)) k12 h1
  have hVr : V ≤ ((e' y).hom ≫ (W' y).ι).opensRange := by
    rw [Scheme.Hom.opensRange_comp_of_isIso, Scheme.Opens.opensRange_ι]
    exact hVle
  exact n2E5_isIso_app_of_isIso_pullback_map ((e' y).hom ≫ (W' y).ι) (baseChangeHom hcart.w F)
      hD V hVr

end AlgebraicGeometry.Scheme.Modules
end Scheme_Modules_isIso_baseChangeHom_of_forall_exists_isPullback
end AlgebraicCurves.Geometry.Sheaves.Proofs
end ProofImplementation
