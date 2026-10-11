/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_IsInvertible_eq_zero_of_pullback_map_eq_zero_of_isReduced.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.Topology.Sheaves.Stalks
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.Tactic.Ext
import AlgebraicCurves.Geometry.Picard.Functor
import AlgebraicCurves.Geometry.Schemes.IsClosedImmersion_app_injective_and_exists_of_app_pullback_eq_of_isReduced

/-!
# Scheme Modules Is Invertible eq zero of pullback map eq zero of is Reduced
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_Modules_IsInvertible_eq_zero_of_pullback_map_eq_zero_of_isReduced

universe u


open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.Opposite
open _root_.AlgebraicGeometry
open _root_.TopologicalSpace


namespace AlgebraicGeometry

export _root_.AlgebraicGeometry (Scheme.Modules.hom_ext Scheme.Modules.Hom.app_smul
  Scheme.Modules.Hom.zero_app morphismRestrict_ι Scheme.Modules.pullback Scheme.Hom
  Scheme.Modules.Hom Scheme.Hom.image_preimage_eq_opensRange_inf Scheme.Hom.image_preimage_le Spec
  Scheme Scheme.Modules.restrictFunctor Scheme.Modules.restrictFunctorIsoPullback IsClosedImmersion
  IsReduced Scheme.Modules.pullbackCongr Scheme.Modules Scheme.Hom.comp_apply
  Scheme.Modules.pullbackComp Scheme.Modules.IsInvertible
  IsClosedImmersion.app_injective_and_exists_of_app_pullback_eq_of_isReduced)

namespace Vanish2

open _root_.AlgebraicGeometry


theorem app_apply_eq_zero_of_pullback_map_eq_zero {Z V : Scheme.{u}} (g : Z ⟶ V) {A : V.Modules}
    (τ : A ⟶ (SheafOfModules.unit V.ringCatSheaf : V.Modules))
    (h : (Scheme.Modules.pullback g).map τ = 0)
    (W : V.Opens) (a : Γ(A, W)) : g.app W (τ.app W a) = 0 := by
  let O : V.Modules := SheafOfModules.unit V.ringCatSheaf
  let P : Z.Modules := SheafOfModules.unit Z.ringCatSheaf
  let η : O ⟶ (Scheme.Modules.pushforward g).obj P :=
    SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom
  let adj := Scheme.Modules.pullbackPushforwardAdjunction g
  let κ : (Scheme.Modules.pullback g).obj O ⟶ P :=
    (adj.homEquiv O P).symm η
  have hη : adj.homEquiv O P κ = η := (adj.homEquiv O P).apply_symm_apply η
  have key : τ ≫ η = (0 : A ⟶ (Scheme.Modules.pushforward g).obj P) := by
    have nat := adj.homEquiv_naturality_left τ κ
    rw [hη, h, zero_comp, adj.homAddEquiv_zero] at nat
    exact nat.symm
  have hval := congrArg (fun (φ : A ⟶ (Scheme.Modules.pushforward g).obj P) => φ.app W a) key
  exact hval

end AlgebraicGeometry.Vanish2

namespace AlgebraicGeometry
export _root_.AlgebraicGeometry (Scheme.Modules.hom_ext Scheme.Modules.Hom.app_smul
  Scheme.Modules.Hom.zero_app morphismRestrict_ι Scheme.Modules.pullback Scheme.Hom
  Scheme.Modules.Hom Scheme.Hom.image_preimage_eq_opensRange_inf Scheme.Hom.image_preimage_le Spec
  Scheme Scheme.Modules.restrictFunctor Scheme.Modules.restrictFunctorIsoPullback IsClosedImmersion
  IsReduced Scheme.Modules.pullbackCongr Scheme.Modules Scheme.Hom.comp_apply
  Scheme.Modules.pullbackComp Scheme.Modules.IsInvertible
  IsClosedImmersion.app_injective_and_exists_of_app_pullback_eq_of_isReduced)
namespace Scheme
export _root_.AlgebraicGeometry.Scheme (Modules.hom_ext Modules.Hom.app_smul Modules.Hom.zero_app
  ringCatSheaf Modules.pullback Hom Γ Modules.Hom Hom.image_preimage_eq_opensRange_inf
  Hom.image_preimage_le Modules.restrictFunctor Modules.restrictFunctorIsoPullback restrictFunctor
  Modules.pullbackCongr Modules Opens restrict Hom.comp_apply Modules.pullbackComp
  Modules.IsInvertible)
namespace Modules
export _root_.AlgebraicGeometry.Scheme.Modules (hom_ext Hom.app_smul Hom.zero_app pullback presheaf
  Hom restrictFunctor restrictFunctorIsoPullback pullbackCongr isSheaf
  pullbackPushforwardAdjunction restrict pullbackComp IsInvertible)
end AlgebraicGeometry.Scheme.Modules

open scoped _root_.AlgebraicGeometry in
open scoped _root_.AlgebraicGeometry.Scheme in
open scoped _root_.AlgebraicGeometry.Scheme.Modules in
theorem AlgebraicGeometry.Scheme.Modules.pullback_morphismRestrict_map_restrictFunctor_map_eq_zero
    {X Y : Scheme.{u}} (i : Y ⟶ X) (V : X.Opens) {A B : X.Modules} (σ : A ⟶ B)
    (h : (Scheme.Modules.pullback i).map σ = 0) :
    (Scheme.Modules.pullback (i ∣_ V)).map ((Scheme.Modules.restrictFunctor V.ι).map σ) = 0 := by
  let N : Scheme.Modules.restrictFunctor V.ι ⋙ Scheme.Modules.pullback (i ∣_ V) ≅
      Scheme.Modules.pullback i ⋙ Scheme.Modules.pullback (i ⁻¹ᵁ V).ι :=
    Functor.isoWhiskerRight (Scheme.Modules.restrictFunctorIsoPullback V.ι)
      (Scheme.Modules.pullback (i ∣_ V)) ≪≫
      Scheme.Modules.pullbackComp (i ∣_ V) V.ι ≪≫
      Scheme.Modules.pullbackCongr (morphismRestrict_ι i V) ≪≫
      (Scheme.Modules.pullbackComp (i ⁻¹ᵁ V).ι i).symm
  have hG : (Scheme.Modules.pullback i ⋙ Scheme.Modules.pullback (i ⁻¹ᵁ V).ι).map σ = 0 := by
    change (Scheme.Modules.pullback (i ⁻¹ᵁ V).ι).map ((Scheme.Modules.pullback i).map σ) = 0
    rw [h, Functor.map_zero]
  have nat := N.hom.naturality σ
  rw [hG, comp_zero] at nat
  have hF : (Scheme.Modules.restrictFunctor V.ι ⋙ Scheme.Modules.pullback (i ∣_ V)).map σ = 0 :=
    (cancel_mono (N.hom.app B)).mp (by rw [nat, zero_comp])
  exact hF

namespace AlgebraicGeometry.Scheme.Modules

open AlgebraicGeometry.Vanish2 in
theorem
  _root_.AlgebraicGeometry.Scheme.Modules.IsInvertible.eq_zero_of_pullback_map_eq_zero_of_isReduced
    {X Y₁ Y₂ : Scheme.{u}} [IsReduced X] (i₁ : Y₁ ⟶ X) (i₂ : Y₂ ⟶ X)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂]
    (hcover : Set.range i₁.base ∪ Set.range i₂.base = Set.univ)
    {L : X.Modules} (hL : Scheme.Modules.IsInvertible L)
    (σ : Scheme.Modules.Hom (SheafOfModules.unit X.ringCatSheaf) L)
    (h₁ : (Scheme.Modules.pullback i₁).map σ = 0) (h₂ : (Scheme.Modules.pullback i₂).map σ = 0) :
    σ = (HasZeroMorphisms.zero (C := X.Modules) (SheafOfModules.unit X.ringCatSheaf) L).zero := by
  classical
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let σ' : O ⟶ L := σ
  have h₁' : (Scheme.Modules.pullback i₁).map σ' = 0 := h₁
  have h₂' : (Scheme.Modules.pullback i₂).map σ' = 0 := h₂
  have loc : ∀ x : X, ∃ V : X.Opens, x ∈ V ∧
      ∀ W' : (V : Scheme.{u}).Opens, σ'.app (V.ι ''ᵁ W') (1 : Γ(X, V.ι ''ᵁ W')) = 0 := by
    intro x
    obtain ⟨V, hxV, ⟨e⟩⟩ := hL.exists_trivialization x
    refine ⟨V, hxV, fun W' => ?_⟩
    let e' : (Scheme.Modules.restrictFunctor V.ι).obj L ≅
        (SheafOfModules.unit (V : Scheme.{u}).ringCatSheaf : (V : Scheme.{u}).Modules) :=
      (Scheme.Modules.restrictFunctorIsoPullback V.ι).app L ≪≫ e
    let τ : (Scheme.Modules.restrictFunctor V.ι).obj O ⟶
        (SheafOfModules.unit (V : Scheme.{u}).ringCatSheaf : (V : Scheme.{u}).Modules) :=
      (Scheme.Modules.restrictFunctor V.ι).map σ' ≫ e'.hom
    have hτ : ∀ {Y : Scheme.{u}} (i : Y ⟶ X), (Scheme.Modules.pullback i).map σ' = 0 →
        (Scheme.Modules.pullback (i ∣_ V)).map τ = 0 := by
      intro Y i hi
      change (Scheme.Modules.pullback (i ∣_ V)).map (_ ≫ _) = 0
      erw [Functor.map_comp,
        pullback_morphismRestrict_map_restrictFunctor_map_eq_zero i V σ' hi, zero_comp]
    have k₁ := app_apply_eq_zero_of_pullback_map_eq_zero (i₁ ∣_ V) τ (hτ i₁ h₁') W' (1 : Γ(X, V.ι
      ''ᵁ W'))
    have k₂ := app_apply_eq_zero_of_pullback_map_eq_zero (i₂ ∣_ V) τ (hτ i₂ h₂') W' (1 : Γ(X, V.ι
      ''ᵁ W'))
    have hcovV : Set.range (i₁ ∣_ V).base ∪ Set.range (i₂ ∣_ V).base = Set.univ := by
      apply Set.eq_univ_of_forall
      intro v
      have hv : (V.ι.base v) ∈ Set.range i₁.base ∪ Set.range i₂.base := by rw [hcover]; trivial
      rcases hv with ⟨y, hy⟩ | ⟨y, hy⟩
      · left
        have hyV : y ∈ i₁ ⁻¹ᵁ V := by
          change i₁.base y ∈ V
          rw [hy]; exact v.2
        refine ⟨⟨y, hyV⟩, ?_⟩
        apply V.ι.isOpenEmbedding.injective
        erw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply]
        exact hy
      · right
        have hyV : y ∈ i₂ ⁻¹ᵁ V := by
          change i₂.base y ∈ V
          rw [hy]; exact v.2
        refine ⟨⟨y, hyV⟩, ?_⟩
        apply V.ι.isOpenEmbedding.injective
        erw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply]
        exact hy
    have inj :=
      (AlgebraicGeometry.IsClosedImmersion.app_injective_and_exists_of_app_pullback_eq_of_isReduced
      (i₁ ∣_ V) (i₂ ∣_ V) hcovV W').1
    have hf : τ.app W' (1 : Γ(X, V.ι ''ᵁ W')) = 0 := by
      apply inj
      refine Prod.ext ?_ ?_
      · exact k₁.trans (map_zero ((i₁ ∣_ V).app W').hom).symm
      · exact k₂.trans (map_zero ((i₂ ∣_ V).app W').hom).symm
    have : IsIso (e'.hom.app W') :=
      Scheme.Modules.Hom.isIso_iff_isIso_app.mp e'.isIso_hom W'
    have hinj : Function.Injective (e'.hom.app W') :=
      (ConcreteCategory.bijective_of_isIso (e'.hom.app W')).1
    apply hinj
    change τ.app W' (1 : Γ(X, V.ι ''ᵁ W')) = e'.hom.app W' 0
    rw [hf]
    exact (map_zero _).symm
  have hall : ∀ U : X.Opens, σ'.app U (1 : Γ(X, U)) = 0 := by
    intro U
    apply TopCat.Presheaf.section_ext ⟨L.presheaf, L.isSheaf⟩ U
    intro x hxU
    obtain ⟨V, hxV, hV⟩ := loc x
    have hW : V.ι ''ᵁ (V.ι ⁻¹ᵁ U) ≤ U := Scheme.Hom.image_preimage_le V.ι U
    have hxW : x ∈ V.ι ''ᵁ (V.ι ⁻¹ᵁ U) := by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf]
      exact ⟨by simpa using hxV, hxU⟩
    rw [← TopCat.Presheaf.germ_res_apply L.presheaf (homOfLE hW) x hxW,
      ← TopCat.Presheaf.germ_res_apply L.presheaf (homOfLE hW) x hxW]
    congr 1
    rw [map_zero]
    have nat := congrArg (fun φ => (ModuleCat.Hom.hom φ) (show Γ(O, U) from (1 : Γ(X, U))))
      (σ'.val.naturality (homOfLE hW).op)
    change σ'.app (V.ι ''ᵁ (V.ι ⁻¹ᵁ U)) (X.presheaf.map (homOfLE hW).op (1 : Γ(X, U))) =
      L.presheaf.map (homOfLE hW).op (σ'.app U (1 : Γ(X, U))) at nat
    rw [map_one] at nat
    change L.presheaf.map (homOfLE hW).op (σ'.app U (1 : Γ(X, U))) = 0
    rw [← nat]
    exact hV _
  change σ' = 0
  apply Scheme.Modules.hom_ext
  intro U
  ext a
  rw [Scheme.Modules.Hom.zero_app]
  have e1 : a = (show Γ(X, U) from a) • (show Γ(O, U) from (1 : Γ(X, U))) :=
    (mul_one (show Γ(X, U) from a)).symm
  rw [e1, Scheme.Modules.Hom.app_smul, hall U, smul_zero]
  rfl
end AlgebraicGeometry.Scheme.Modules

end Scheme_Modules_IsInvertible_eq_zero_of_pullback_map_eq_zero_of_isReduced
end AlgebraicCurves.Geometry.Sheaves.Proofs
end ProofImplementation
