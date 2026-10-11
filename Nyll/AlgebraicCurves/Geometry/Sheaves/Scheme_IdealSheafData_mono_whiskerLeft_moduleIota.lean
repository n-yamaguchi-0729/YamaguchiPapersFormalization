/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_IdealSheafData_mono_whiskerLeft_moduleIota.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Geometry.Sheaves.IdealSheafModule
import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesLocallyFreeOfRank
import Nyll.SchemeTheory.Modules.Monoidal
import Nyll.SchemeTheory.Modules.PullbackMonoidal
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_Hom_mono_iff_injective

/-!
# Tensoring the inclusion of an ideal module

Proves that tensoring the ideal inclusion by a locally free module preserves its monomorphism.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_IdealSheafData_mono_whiskerLeft_moduleIota

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.Opposite
open _root_.TopologicalSpace


namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace IdealSheafData
open _root_.AlgebraicGeometry.Scheme.IdealSheafData
open _root_.AlgebraicGeometry.Scheme.IdealSheafData
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry

namespace MonoWhisker

section general

variable {C D : Type*} [Category C] [Category D]

lemma mono_map_of_natIso {F G : C ⥤ D} (e : F ≅ G) {A B : C} (f : A ⟶ B) [Mono (G.map f)] :
    Mono (F.map f) := by
  have : F.map f = e.hom.app A ≫ G.map f ≫ e.inv.app B := by
    rw [← Category.assoc, ← e.hom.naturality f, Category.assoc, Iso.hom_inv_id_app,
      Category.comp_id]
  rw [this]
  have i1 : Mono (e.hom.app A) := IsIso.mono_of_iso _
  have i2 : Mono (e.inv.app B) := IsIso.mono_of_iso _
  have i3 : Mono (G.map f ≫ e.inv.app B) := @mono_comp _ _ _ _ _ _ ‹Mono (G.map f)› _ i2
  exact @mono_comp _ _ _ _ _ _ i1 _ i3

end general

section monoidal

variable {C : Type*} [Category C] [Abelian C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C]

scoped instance preservesColimit_tensorRight (P : C) {J : Type*} [Category J] (K : J ⥤ C) :
    PreservesColimit K (tensorRight P) :=
  preservesColimit_of_natIso K (BraidedCategory.tensorLeftIsoTensorRight P)

omit [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C] in
lemma mono_sigmaMap {ι : Type*} [Finite ι] {f g : ι → C} (p : ∀ i, f i ⟶ g i) (hp : ∀ i, Mono (p i))
    [HasCoproduct f] [HasCoproduct g] :
    Mono (Limits.Sigma.map p) := by
  let : Fintype ι := Fintype.ofFinite ι
  have : HasFiniteBiproducts C := Abelian.hasFiniteBiproducts
  have : ∀ i, Mono (p i) := hp
  have H : Limits.Sigma.map p ≫ (biproduct.isoCoproduct g).inv =
      (biproduct.isoCoproduct f).inv ≫ biproduct.map p := by
    rw [biproduct.isoCoproduct_inv, biproduct.isoCoproduct_inv]
    apply Limits.Sigma.hom_ext
    intro i
    rw [Limits.Sigma.ι_map_assoc, Limits.Sigma.ι_comp_desc, Limits.Sigma.ι_comp_desc_assoc,
      biproduct.ι_map]
  have : Limits.Sigma.map p =
      ((biproduct.isoCoproduct f).inv ≫ biproduct.map p) ≫ (biproduct.isoCoproduct g).hom := by
    rw [← H, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [this]
  have i1 : Mono (biproduct.isoCoproduct f).inv := IsIso.mono_of_iso _
  have i2 : Mono (biproduct.isoCoproduct g).hom := IsIso.mono_of_iso _
  have i0 : Mono (biproduct.map p) := biproduct.map_mono p
  have i3 : Mono ((biproduct.isoCoproduct f).inv ≫ biproduct.map p) := @mono_comp _ _ _ _ _ _ i1 _
    i0
  exact @mono_comp _ _ _ _ _ _ i3 _ i2

omit [Abelian C] [SymmetricCategory C] [MonoidalClosed C] in
lemma mono_unit_whiskerLeft {P Q : C} (h : P ⟶ Q) [Mono h] : Mono (𝟙_ C ◁ h) := by
  have : 𝟙_ C ◁ h = (λ_ P).hom ≫ h ≫ (λ_ Q).inv := by
    rw [← Category.assoc, ← leftUnitor_naturality, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [this]
  have i1 : Mono (λ_ P).hom := IsIso.mono_of_iso _
  have i2 : Mono (λ_ Q).inv := IsIso.mono_of_iso _
  have i3 : Mono (h ≫ (λ_ Q).inv) := @mono_comp _ _ _ _ _ _ ‹Mono h› _ i2
  exact @mono_comp _ _ _ _ _ _ i1 _ i3

lemma mono_sigmaUnit_whiskerLeft {ι : Type*} [Finite ι] {P Q : C} (h : P ⟶ Q) [Mono h]
    [HasCoproduct (fun _ : ι => 𝟙_ C)] :
    Mono ((∐ fun _ : ι => 𝟙_ C) ◁ h) := by
  let f : ι → C := fun _ => 𝟙_ C
  let σP : (∐ fun b => (tensorRight P).obj (f b)) ⟶ (tensorRight P).obj (∐ f) := sigmaComparison
    (tensorRight P) f
  let σQ : (∐ fun b => (tensorRight Q).obj (f b)) ⟶ (tensorRight Q).obj (∐ f) := sigmaComparison
    (tensorRight Q) f
  let Sm : (∐ fun b => (tensorRight P).obj (f b)) ⟶ (∐ fun b => (tensorRight Q).obj (f b)) :=
    Limits.Sigma.map (fun _ => 𝟙_ C ◁ h)
  let wh : (tensorRight P).obj (∐ f) ⟶ (tensorRight Q).obj (∐ f) := (∐ f) ◁ h
  have hnat : Sm ≫ σQ = σP ≫ wh := by
    apply Limits.Sigma.hom_ext
    intro i
    have e1 : Sigma.ι (fun b => (tensorRight P).obj (f b)) i ≫ Sm =
        (𝟙_ C ◁ h) ≫ Sigma.ι (fun b => (tensorRight Q).obj (f b)) i :=
      Limits.Sigma.ι_map (fun _ => 𝟙_ C ◁ h) i
    have e2 : Sigma.ι (fun b => (tensorRight Q).obj (f b)) i ≫ σQ = (tensorRight Q).map (Sigma.ι f
      i) :=
      ι_comp_sigmaComparison (tensorRight Q) f i
    have e3 : Sigma.ι (fun b => (tensorRight P).obj (f b)) i ≫ σP = (tensorRight P).map (Sigma.ι f
      i) :=
      ι_comp_sigmaComparison (tensorRight P) f i
    have e4 : (𝟙_ C ◁ h) ≫ (tensorRight Q).map (Sigma.ι f i) = (tensorRight P).map (Sigma.ι f i) ≫
      wh :=
      whisker_exchange (Sigma.ι f i) h
    have L : Sigma.ι (fun b => (tensorRight P).obj (f b)) i ≫ (Sm ≫ σQ) =
        (𝟙_ C ◁ h) ≫ (tensorRight Q).map (Sigma.ι f i) :=
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ σQ) e1)).trans
        ((Category.assoc _ _ _).trans (congrArg ((𝟙_ C ◁ h) ≫ ·) e2))
    have R : Sigma.ι (fun b => (tensorRight P).obj (f b)) i ≫ (σP ≫ wh) = (tensorRight P).map
      (Sigma.ι f i) ≫ wh :=
      (Category.assoc _ _ _).symm.trans (congrArg (· ≫ wh) e3)
    exact L.trans (e4.trans R.symm)
  have hσP : IsIso σP := inferInstance
  let σPinv : (tensorRight P).obj (∐ f) ⟶ (∐ fun b => (tensorRight P).obj (f b)) := inv σP
  have heq : wh = σPinv ≫ Sm ≫ σQ :=
    ((IsIso.inv_hom_id_assoc σP wh).symm).trans (congrArg (σPinv ≫ ·) hnat.symm)
  have hm : Mono Sm := mono_sigmaMap (f := fun b => (tensorRight P).obj (f b)) (g := fun b =>
    (tensorRight Q).obj (f b))
    (fun _ => 𝟙_ C ◁ h) (fun _ => mono_unit_whiskerLeft h)
  have hQ : Mono σQ := IsIso.mono_of_iso _
  have hP : Mono σPinv := IsIso.mono_of_iso _
  have hm2 : Mono (Sm ≫ σQ) := @mono_comp _ _ _ _ _ _ hm _ hQ
  have hfin : Mono (σPinv ≫ Sm ≫ σQ) := @mono_comp _ _ _ _ _ _ hP _ hm2
  have hwh : Mono wh := heq ▸ hfin
  exact hwh

end monoidal

section scheme

variable {X : Scheme.{u}}

lemma mono_pullback_map_of_mono (V : X.Opens) {M N : X.Modules} (φ : M ⟶ N) [Mono φ] :
    Mono ((Scheme.Modules.pullback V.ι).map φ) := by
  have : Mono ((Scheme.Modules.restrictFunctor V.ι).map φ) := by
    rw [Scheme.Modules.Hom.mono_iff_injective]
    intro W
    exact (Scheme.Modules.Hom.mono_iff_injective φ).mp inferInstance (V.ι ''ᵁ W)
  exact mono_map_of_natIso (Scheme.Modules.restrictFunctorIsoPullback V.ι).symm _

lemma image_preimage_eq_inf (V U : X.Opens) : V.ι ''ᵁ (V.ι ⁻¹ᵁ U) = V ⊓ U := by
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]

lemma app_res {M N : X.Modules} (φ : M ⟶ N) {W' W : X.Opens} (h : W' ≤ W) (s : Γ(M, W)) :
    φ.app W' (M.presheaf.map (homOfLE h).op s) = N.presheaf.map (homOfLE h).op (φ.app W s) := by
  have hnat := φ.mapPresheaf.naturality (homOfLE h).op
  have hx := ConcreteCategory.congr_hom hnat s
  simp only [ConcreteCategory.comp_apply, Scheme.Modules.mapPresheaf_app] at hx
  exact hx

lemma mono_of_forall_exists_mono_pullback {M N : X.Modules} (φ : M ⟶ N)
    (h : ∀ x : X, ∃ V : X.Opens, x ∈ V ∧ Mono ((Scheme.Modules.pullback V.ι).map φ)) : Mono φ := by
  rw [Scheme.Modules.Hom.mono_iff_injective]
  intro U
  rw [injective_iff_map_eq_zero]
  intro s hs
  choose V hxV hV using h
  let Fsh : TopCat.Sheaf AddCommGrpCat X.carrier := ⟨M.presheaf, M.isSheaf⟩
  have hle : ∀ y : U, V y.1 ⊓ U ≤ U := fun _ => inf_le_right
  refine Fsh.eq_of_locally_eq' (fun y : U => V y.1 ⊓ U) U (fun y => homOfLE (hle y))
    (fun y hy => Opens.mem_iSup.mpr ⟨⟨y, hy⟩, hxV y, hy⟩) s 0 fun y => ?_
  rw [map_zero]
  have := hV y.1
  have : Mono ((Scheme.Modules.restrictFunctor (V y.1).ι).map φ) :=
    mono_map_of_natIso (Scheme.Modules.restrictFunctorIsoPullback _) φ
  have hinj : Function.Injective (φ.app ((V y.1).ι ''ᵁ ((V y.1).ι ⁻¹ᵁ U))) :=
    (Scheme.Modules.Hom.mono_iff_injective _).mp this ((V y.1).ι ⁻¹ᵁ U)
  rw [image_preimage_eq_inf] at hinj
  apply hinj
  change φ.app _ (M.presheaf.map (homOfLE (hle y)).op s) = φ.app _ 0
  rw [map_zero, app_res, hs, map_zero]

theorem mono_whiskerLeft_moduleι' (I : X.IdealSheafData) {n : ℕ} (F : X.Modules)
    (hF : Scheme.Modules.IsLocallyFreeOfRank n F) : Mono (F ◁ I.moduleι) := by
  have : Mono I.moduleι :=
    ⟨fun g g' w => (cancel_mono (kernel.ι I.subschemeι.unitToPushforwardUnit)).mp w⟩
  apply mono_of_forall_exists_mono_pullback
  intro x
  obtain ⟨V, hxV, ⟨e⟩⟩ := hF.exists_trivialization x
  refine ⟨V, hxV, ?_⟩
  let Fr : V.toScheme.Modules := SheafOfModules.free.{u} (ULift.{u} (Fin n))
  let e' : @Iso V.toScheme.Modules _ ((Scheme.Modules.pullback V.ι).obj F) Fr := e
  have : Mono ((Scheme.Modules.pullback V.ι).map I.moduleι) := mono_pullback_map_of_mono V I.moduleι
  rw [Functor.Monoidal.map_whiskerLeft]
  have : Mono ((Scheme.Modules.pullback V.ι).obj F ◁ (Scheme.Modules.pullback V.ι).map I.moduleι)
    := by
    have heq : (Scheme.Modules.pullback V.ι).obj F ◁ (Scheme.Modules.pullback V.ι).map I.moduleι =
        (e'.hom ▷ _ ≫ Fr ◁ (Scheme.Modules.pullback V.ι).map I.moduleι) ≫ e'.inv ▷ _ := by
      rw [← whisker_exchange, Category.assoc, ← comp_whiskerRight, Iso.hom_inv_id, id_whiskerRight,
        Category.comp_id]
    rw [heq]
    have h1 : Mono (Fr ◁ (Scheme.Modules.pullback V.ι).map I.moduleι) :=
      mono_sigmaUnit_whiskerLeft (C := V.toScheme.Modules) (ι := ULift.{u} (Fin n))
        ((Scheme.Modules.pullback V.ι).map I.moduleι)
    have h4 : Mono (e'.hom ▷ (Scheme.Modules.pullback V.ι).obj I.module) := IsIso.mono_of_iso _
    have h5 : Mono (e'.inv ▷ (Scheme.Modules.pullback V.ι).obj (𝟙_ X.Modules)) :=
      IsIso.mono_of_iso _
    have h2 : Mono (e'.hom ▷ (Scheme.Modules.pullback V.ι).obj I.module ≫
        Fr ◁ (Scheme.Modules.pullback V.ι).map I.moduleι) := @mono_comp _ _ _ _ _ _ h4 _ h1
    exact @mono_comp _ _ _ _ _ _ h2 _ h5
  have h6 : Mono (Functor.LaxMonoidal.μ (Scheme.Modules.pullback V.ι) F (𝟙_ X.Modules)) :=
    IsIso.mono_of_iso _
  have h7 : Mono (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback V.ι) F I.module) :=
    IsIso.mono_of_iso _
  have h3 : Mono ((Scheme.Modules.pullback V.ι).obj F ◁ (Scheme.Modules.pullback V.ι).map
    I.moduleι ≫
      Functor.LaxMonoidal.μ (Scheme.Modules.pullback V.ι) F (𝟙_ X.Modules)) := @mono_comp _ _ _ _
        _ _ this _ h6
  exact @mono_comp _ _ _ _ _ _ h7 _ h3

end scheme

end MonoWhisker

theorem mono_whiskerLeft_moduleι {X : Scheme.{u}} (I : X.IdealSheafData) {n : ℕ} (F : X.Modules)
    (hF : Scheme.Modules.IsLocallyFreeOfRank n F) : Mono (F ◁ I.moduleι) :=
  MonoWhisker.mono_whiskerLeft_moduleι' I F hF

end AlgebraicGeometry.Scheme.IdealSheafData

theorem _root_.AlgebraicGeometry.Scheme.IdealSheafData.mono_whiskerLeft_moduleIota {X :
  Scheme.{u}} (I : X.IdealSheafData) {n : ℕ} (F : X.Modules)
    (hF : Scheme.Modules.IsLocallyFreeOfRank n F) : Mono (F ◁ I.moduleι) :=
  AlgebraicGeometry.Scheme.IdealSheafData.mono_whiskerLeft_moduleι I F hF
end AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_IdealSheafData_mono_whiskerLeft_moduleIota
end ProofImplementation

open _root_.PresheafOfModules.PullbackMonoidal
  (instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb) in
attribute [-instance]
  AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap
  AlgebraicGeometry.Scheme.Modules.pullback_monoidal
  AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization'
  AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap
  AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal
  AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap
  AlgebraicGeometry.Scheme.Modules.sheafifyPullback_lifting
  PresheafOfModules.PullbackMonoidal.pullback_monoidal
  PresheafOfModules.PullbackMonoidal.isIso_δ
  PresheafOfModules.pushforward_laxMonoidal
  PresheafOfModules.PullbackMonoidal.isIso_η
  PresheafOfModules.free_monoidal
  PresheafOfModules.restrictScalars_laxMonoidal
  PresheafOfModules.PullbackMonoidal.isIso_δ_gS
  PresheafOfModules.pullback_oplaxMonoidal
  instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb
  PresheafOfModules.pullback_monoidal'
attribute [-simp] PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app
