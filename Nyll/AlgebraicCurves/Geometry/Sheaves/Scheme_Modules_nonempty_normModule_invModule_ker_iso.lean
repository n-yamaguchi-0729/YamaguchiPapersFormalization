/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_nonempty_normModule_invModule_ker_iso.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Geometry.Sheaves.IdealSheafModule
import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesNormModule
import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesSectionZeroScheme
import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesLocallyFreeOfRank
import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.SchemeTheory.Modules.Monoidal
import Nyll.SchemeTheory.Modules.TensorSections
import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesIhomSections
import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesDet
import Nyll.AlgebraicCurves.Geometry.Schemes.Scheme_Hom_isInvertible_ker_of_comp_eq_id
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_normModule
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_isIso_ev_app_tensorUnit
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_isInvertible_det_of_isLocallyFreeOfRank
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_isLocallyFreeOfRank_pushforward_of_isFinite_of_flat_of_locallyTrivialOver
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_exists_nonempty_pullback_preimage_iso_tensorUnit_of_isFinite
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_exists_iso_invModule_zeroSchemeIdeal
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_zeroSchemeIdeal_invModuleSection
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsLocallyFreeOfRank_exists_basis
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq
import Nyll.AlgebraicCurves.Valuations.Algebra_IsStandardSmoothOfRelativeDimension_isDiscreteValuationRing_localization_atPrime
import Nyll.AlgebraicCurves.Valuations.Ideal_span_algebraNorm_eq_of_ker_eq_span_of_isDiscreteValuationRing
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_ideal_zeroSchemeIdeal_eq_span_of_app_eq_smul
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_exists_isFrameOn_normModule_and_app_eq_norm_smul

/-!
# Scheme Modules nonempty norm Module inv Module ker iso
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_Modules_nonempty_normModule_invModule_ker_iso
attribute [-instance] TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module
  TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing
  TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module
  TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower
  TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing
  TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module
  TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup
  TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower
  CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup
  CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup
  CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite
  CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free
attribute [-simp] AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq
  TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq
  TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec
  TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec
  TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec
  CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app
  PresheafOfModules.pushforwardCongr_inv_app_app_apply
  PresheafOfModules.pushforwardNatTrans_app_app_apply
  PresheafOfModules.pushforwardCongr_hom_app_app_apply

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.Opposite

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace Modules
open _root_.AlgebraicGeometry.Scheme.Modules
namespace NormPoint
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry

variable {K : Type u} [Field K] {X X' : Scheme.{u}}

/--
The section of the norm module induced by a section upstairs and the inverse norm-unit
evaluation.
-/
noncomputable def detSection (π : X' ⟶ X) (d : ℕ) [IsIso (normModuleUnitEval π d)]
    {L : X'.Modules} (s : 𝟙_ X'.Modules ⟶ L) : 𝟙_ X.Modules ⟶ normModule π d L :=
  inv (normModuleUnitEval π d) ≫ (normModuleFunctor π d).map s


theorem ideal_zeroSchemeIdeal_detSection_eq_span_norm
    (π : X' ⟶ X) [IsAffineHom π] (d : ℕ) [IsIso (normModuleUnitEval π d)]
    {P : X'.Modules} (hN : IsInvertible (normModule π d P)) (ι' : 𝟙_ X'.Modules ⟶ P)
    (U : X.affineOpens)
    (e : Fin d → Γ((pushforward π).obj (𝟙_ X'.Modules), U.1))
    (he : ∀ (W : X.Opens) (hW : W ≤ U.1),
      ∃ b : Module.Basis (Fin d) Γ(X, W) Γ((pushforward π).obj (𝟙_ X'.Modules), W),
        ∀ i, b i = ((pushforward π).obj (𝟙_ X'.Modules)).presheaf.map (homOfLE hW).op (e i))
    (s : Γ(P, π ⁻¹ᵁ U.1)) (hs : IsFrameOn s (π ⁻¹ᵁ U.1))
    (g : Γ(X', π ⁻¹ᵁ U.1)) (hg : ι'.app (π ⁻¹ᵁ U.1) (toUnitSection _ 1) = g • s) :
    letI : Algebra Γ(X, U.1) Γ(X', π ⁻¹ᵁ U.1) := (π.app U.1).hom.toAlgebra
    (zeroSchemeIdeal (detSection π d ι')).ideal U = Ideal.span {Algebra.norm Γ(X, U.1) g} := by
  let : Algebra Γ(X, U.1) Γ(X', π ⁻¹ᵁ U.1) := (π.app U.1).hom.toAlgebra
  obtain ⟨Ω, hΩ, hσ⟩ := exists_isFrameOn_normModule_and_app_eq_norm_smul π d ι' U.1 e he s hs g hg
  have := hN.ideal_zeroSchemeIdeal_eq_span_of_app_eq_smul Ω hΩ (detSection π d ι') (Algebra.norm
    Γ(X, U.1) g)
    hσ U le_rfl
  rw [this]
  congr 2
  change (X.presheaf.map (homOfLE (le_refl U.1)).op) _ = _
  rw [show (homOfLE (le_refl U.1)).op = 𝟙 _ from rfl, CategoryTheory.Functor.map_id]
  rfl

theorem presheaf_map_congr {M : X.Modules} {A B : X.Opens} (f g : op A ⟶ op B) (m : Γ(M, A)) :
    M.presheaf.map f m = M.presheaf.map g m := by
  have hfg : f = g := Quiver.Hom.unop_inj (Subsingleton.elim _ _)
  subst hfg
  rfl


theorem isFrameOn_of_isFrameOn_restrict {M : X.Modules} (V : X.Opens)
    (s₀ : Γ(M.restrict V.ι, ⊤)) (h : IsFrameOn (M := M.restrict V.ι) s₀ ⊤) :
    IsFrameOn (M := M) (M.presheaf.map (eqToHom V.ι_image_top.symm).op (show Γ(M, V.ι ''ᵁ ⊤) from
      s₀)) V := by
  intro W hWV _
  obtain ⟨W₀, rfl⟩ : ∃ W₀, V.ι ''ᵁ W₀ = W := ⟨V.ι ⁻¹ᵁ W, image_preimage_eq_of_le hWV⟩
  have hb₀ := h (W := W₀) le_top le_top
  have heq : (fun a : Γ((V : Scheme.{u}), W₀) =>
      a • (M.restrict V.ι).presheaf.map (homOfLE (le_top : W₀ ≤ ⊤)).op s₀) =
      (fun a : Γ(X, V.ι ''ᵁ W₀) => a • (show Γ(M, V.ι ''ᵁ W₀) from
        (M.restrict V.ι).presheaf.map (homOfLE (le_top : W₀ ≤ ⊤)).op s₀)) := by
    funext a; exact restrict_smul_eq _ a _
  rw [heq, Scheme.Modules.restrict_map] at hb₀
  have helt : M.presheaf.map (homOfLE hWV).op
      (M.presheaf.map (eqToHom V.ι_image_top.symm).op (show Γ(M, V.ι ''ᵁ ⊤) from s₀)) =
      M.presheaf.map (V.ι.opensFunctor.map (homOfLE (le_top : W₀ ≤ ⊤))).op (show Γ(M, V.ι ''ᵁ ⊤)
        from s₀) := by
    rw [← CategoryTheory.comp_apply, ← Functor.map_comp]
    exact presheaf_map_congr _ _ _
  rw [helt]
  exact hb₀


theorem exists_isFrameOn_and_app_eq_coeff_smul {P : X.Modules} (ι' : 𝟙_ X.Modules ⟶ P) (V : X.Opens)
    (τ : P.restrict V.ι ≅ 𝟙_ (V : Scheme.{u}).Modules) :
    ∃ s : Γ(P, V), IsFrameOn s V ∧ ι'.app V (toUnitSection V 1) = (coeff ι' V τ.hom) • s := by
  let s₀ : Γ(P.restrict V.ι, ⊤) := τ.inv.app ⊤ (toUnitSection ⊤ 1)
  have hs₀ : IsFrameOn (M := P.restrict V.ι) s₀ ⊤ :=
    (isFrameOn_unitSection (X := (V : Scheme.{u})) (U := ⊤) ⊤).map_iso τ.symm
  refine ⟨P.presheaf.map (eqToHom V.ι_image_top.symm).op (show Γ(P, V.ι ''ᵁ ⊤) from s₀),
    isFrameOn_of_isFrameOn_restrict V s₀ hs₀, ?_⟩
  set r₀ : Γ((V : Scheme.{u}), ⊤) := ofUnitSection ⊤ (τ.hom.app ⊤ (restrictSection ι' V)) with hr₀
  have hcoeff : coeff ι' V τ.hom = V.topIso.hom r₀ := rfl
  have e1 : τ.hom.app ⊤ (restrictSection ι' V) = r₀ • toUnitSection ⊤ 1 := by
    apply ofUnitSection_injective
    rw [ofUnitSection_smul, ofUnitSection_toUnitSection, mul_one]
  have e2 : restrictSection ι' V = r₀ • s₀ := by
    have := congrArg (τ.inv.app ⊤) e1
    rw [Scheme.Modules.Hom.app_smul] at this
    refine Eq.trans ?_ this
    change _ = (τ.hom.app ⊤ ≫ τ.inv.app ⊤) (restrictSection ι' V)
    rw [← Scheme.Modules.Hom.comp_app, τ.hom_inv_id, Scheme.Modules.Hom.id_app]
    rfl
  have e3 : ι'.app V (toUnitSection V 1) =
      P.presheaf.map (eqToHom V.ι_image_top.symm).op (restrictSection ι' V) := by
    have nat := (ι'.mapPresheaf).naturality (eqToHom V.ι_image_top.symm).op
    have := congrFun (congrArg (fun f => (ConcreteCategory.hom f : Γ(𝟙_ X.Modules, V.ι ''ᵁ ⊤) →
      Γ(P, V))) nat)
      (toUnitSection (V.ι ''ᵁ ⊤) 1)
    simp only [mapPresheaf_app] at this
    refine Eq.trans ?_ this
    change ι'.app V (toUnitSection V 1) = ι'.app V ((𝟙_ X.Modules).presheaf.map _ (toUnitSection _
      1))
    congr 1
    apply ofUnitSection_injective
    rw [ofUnitSection_map, ofUnitSection_toUnitSection, ofUnitSection_toUnitSection, map_one]
  rw [e3, e2, restrict_smul_eq (M := P) ⊤ r₀ s₀, Scheme.Modules.map_smul, hcoeff]
  congr 1

theorem opens_eq_top_of_mem {W : (Spec (CommRingCat.of K)).Opens} {p : Spec (CommRingCat.of K)} (hp
  : p ∈ W) :
    W = ⊤ := by
  ext q
  simp only [TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
  rwa [Subsingleton.elim q p]

theorem opens_eq_bot_of_not_mem {W : (Spec (CommRingCat.of K)).Opens} {p : Spec (CommRingCat.of K)}
    (hp : p ∉ W) : W = ⊥ := by
  ext q
  simp only [TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
  rwa [Subsingleton.elim q p]


theorem zeroSchemeIdeal_detSection_invModuleSection
    (t : X ⟶ Spec (CommRingCat.of K)) (t' : X' ⟶ Spec (CommRingCat.of K))
    [IsSeparated t] [IsSeparated t'] [SmoothOfRelativeDimension 1 t] [SmoothOfRelativeDimension 1
      t']
    (π : X' ⟶ X) (hπ : π ≫ t = t') [IsFinite π] [Flat π] [LocallyOfFinitePresentation π]
    (d : ℕ) (hd : ∀ y : X, π.finrank y = d) [IsIso (normModuleUnitEval π d)]
    (x' : {q : Spec (CommRingCat.of K) ⟶ X' // q ≫ t' = 𝟙 _}) :
    zeroSchemeIdeal (detSection π d (x'.1.ker).invModuleSection) = (x'.1 ≫ π).ker := by
  classical
  set x : Spec (CommRingCat.of K) ⟶ X := x'.1 ≫ π with hxdef
  have hxt : x ≫ t = 𝟙 _ := by rw [hxdef, Category.assoc, hπ, x'.2]
  have : IsClosedImmersion (x'.1 ≫ t') := by rw [x'.2]; infer_instance
  have : IsClosedImmersion x'.1 := IsClosedImmersion.of_comp x'.1 t'
  have : IsClosedImmersion (x ≫ t) := by rw [hxt]; infer_instance
  have : IsClosedImmersion x := IsClosedImmersion.of_comp x t
  have hI' : (x'.1.ker).IsInvertible := Scheme.Hom.isInvertible_ker_of_comp_eq_id (p := t') x'.1
    x'.2
  set P : X'.Modules := (x'.1.ker).invModule with hPdef
  have hP : IsInvertible P := hI'.isInvertible_invModule
  have hN : IsInvertible (normModule π d P) := IsInvertible.normModule π d hd hP
  set ι' : 𝟙_ X'.Modules ⟶ P := (x'.1.ker).invModuleSection with hι'
  have hZι' : zeroSchemeIdeal ι' = x'.1.ker := hI'.zeroSchemeIdeal_invModuleSection
  have hE : IsLocallyFreeOfRank d ((pushforward π).obj (𝟙_ X'.Modules)) :=
    isLocallyFreeOfRank_pushforward_of_isFinite_of_flat_of_locallyTrivialOver π d hd (𝟙_ X'.Modules)
      (fun y => IsInvertible.exists_nonempty_pullback_preimage_iso_tensorUnit_of_isFinite π
        (isInvertible_unit X') y)
  set pt : Spec (CommRingCat.of K) := IsLocalRing.closedPoint K with hpt
  let Good (U : X.affineOpens) : Prop :=
    (∃ e : Fin d → Γ((pushforward π).obj (𝟙_ X'.Modules), U.1), ∀ (W : X.Opens) (hW : W ≤ U.1),
      ∃ b : Module.Basis (Fin d) Γ(X, W) Γ((pushforward π).obj (𝟙_ X'.Modules), W),
        ∀ i, b i = ((pushforward π).obj (𝟙_ X'.Modules)).presheaf.map (homOfLE hW).op (e i)) ∧
    (Nonempty (P.restrict (π ⁻¹ᵁ U.1).ι ≅ 𝟙_ ((π ⁻¹ᵁ U.1 : X'.Opens) : Scheme.{u}).Modules)) ∧
    RingHom.IsStandardSmoothOfRelativeDimension 1 (t.appLE ⊤ U.1 le_top).hom
  have hgood : ∀ y : X, ∃ U : X.affineOpens, y ∈ U.1 ∧ Good U := by
    intro y
    obtain ⟨V₁, hyV₁, e₁, he₁⟩ := hE.exists_basis y
    obtain ⟨V₂, hyV₂, ⟨τ₂⟩⟩ :=
      IsInvertible.exists_nonempty_pullback_preimage_iso_tensorUnit_of_isFinite π hP y
    obtain ⟨W₀, hW₀, V₃, hV₃, hyV₃, hle₃, hsm₃⟩ :=
      SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := 1) (f := t) y
    have hW₀top : W₀ = ⊤ := opens_eq_top_of_mem (p := t.base y) (hle₃ hyV₃)
    subst hW₀top
    obtain ⟨r, hrle, hyr⟩ :=
      hV₃.exists_basicOpen_le (V := V₁ ⊓ V₂) ⟨y, ⟨hyV₁, hyV₂⟩⟩ hyV₃
    have hUaff : IsAffineOpen (X.basicOpen r) := hV₃.basicOpen r
    have hUV₃ : X.basicOpen r ≤ V₃ := X.basicOpen_le r
    have hUV₁ : X.basicOpen r ≤ V₁ := hrle.trans inf_le_left
    refine ⟨⟨X.basicOpen r, hUaff⟩, hyr,
      ⟨fun i => ((pushforward π).obj (𝟙_ X'.Modules)).presheaf.map (homOfLE hUV₁).op (e₁ i), ?_⟩,
        ⟨?_⟩, ?_⟩
    · intro W hW
      obtain ⟨b, hb⟩ := he₁ W (hW.trans hUV₁)
      refine ⟨b, fun i => ?_⟩
      rw [hb i, ← CategoryTheory.comp_apply, ← Functor.map_comp]
      rfl
    · exact restrictIsoOfLE (by
        change π ⁻¹ᵁ X.basicOpen r ≤ π ⁻¹ᵁ V₂
        exact fun z hz => (hrle.trans inf_le_right) hz) τ₂
    · have hloc : RingHom.IsStandardSmoothOfRelativeDimension 0
          (X.presheaf.map (homOfLE hUV₃).op).hom := by
        let := (X.presheaf.map (homOfLE hUV₃).op).hom.toAlgebra
        have : IsLocalization.Away r Γ(X, X.basicOpen r) := hV₃.isLocalization_basicOpen r
        exact RingHom.IsStandardSmoothOfRelativeDimension.algebraMap_isLocalizationAway r
      have := RingHom.IsStandardSmoothOfRelativeDimension.comp hloc hsm₃
      rwa [← CommRingCat.hom_comp, Scheme.Hom.appLE_map] at this
  choose Uof hyU hgoodU using hgood
  apply Scheme.IdealSheafData.ext_of_iSup_eq_top Uof
  · exact top_le_iff.mp fun y _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hyU y⟩
  intro y
  set U : X.affineOpens := Uof y with hUdef
  obtain ⟨⟨e, he⟩, ⟨τ⟩, hsm⟩ := hgoodU y
  let alg : Algebra Γ(X, U.1) Γ(X', π ⁻¹ᵁ U.1) := (π.app U.1).hom.toAlgebra
  have hUaff' : IsAffineOpen (π ⁻¹ᵁ U.1) := U.2.preimage π
  have hker' : (x'.1.ker).ideal ⟨π ⁻¹ᵁ U.1, hUaff'⟩ = RingHom.ker (x'.1.app (π ⁻¹ᵁ U.1)).hom :=
    Scheme.Hom.ker_apply x'.1 ⟨π ⁻¹ᵁ U.1, hUaff'⟩
  have hker : (x.ker).ideal U = RingHom.ker (x.app U.1).hom := Scheme.Hom.ker_apply x U
  by_cases hxU : x.base pt ∈ U.1
  · obtain ⟨s, hs, hgs⟩ := exists_isFrameOn_and_app_eq_coeff_smul ι' (π ⁻¹ᵁ U.1) τ
    set g : Γ(X', π ⁻¹ᵁ U.1) := coeff ι' (π ⁻¹ᵁ U.1) τ.hom with hgdef
    have hgspan : RingHom.ker (x'.1.app (π ⁻¹ᵁ U.1)).hom = Ideal.span {g} := by
      rw [← hker', ← hZι']
      exact ((IsInvertible.coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq hP ι').2 ⟨π ⁻¹ᵁ U.1, hUaff'⟩
        τ).1
    have hloc := ideal_zeroSchemeIdeal_detSection_eq_span_norm π d hN ι' U e he s hs g hgs
    obtain ⟨b₀, -⟩ := he U.1 le_rfl
    let b₁ : Module.Basis (Fin d) Γ(X, U.1) Γ(X', π ⁻¹ᵁ U.1) := Module.Basis.ofRepr
      { toFun := fun v => b₀.repr v, invFun := fun c => b₀.repr.symm c,
        map_add' := fun v w => b₀.repr.map_add v w, map_smul' := fun r v => b₀.repr.map_smul r v,
        left_inv := fun v => b₀.repr.symm_apply_apply v, right_inv := fun c =>
          b₀.repr.apply_symm_apply c }
    have : Module.Free Γ(X, U.1) Γ(X', π ⁻¹ᵁ U.1) := Module.Free.of_basis b₁
    have : Module.Finite Γ(X, U.1) Γ(X', π ⁻¹ᵁ U.1) := Module.Finite.of_basis b₁
    have hx'U : x'.1.base pt ∈ π ⁻¹ᵁ U.1 := by
      rw [hxdef] at hxU
      exact hxU
    have htop : x'.1 ⁻¹ᵁ (π ⁻¹ᵁ U.1) = ⊤ := opens_eq_top_of_mem (p := pt) hx'U
    let tail : Γ(Spec (CommRingCat.of K), x'.1 ⁻¹ᵁ (π ⁻¹ᵁ U.1)) ⟶ CommRingCat.of K :=
      (Spec (CommRingCat.of K)).presheaf.map (eqToHom htop.symm).op ≫ (Scheme.ΓSpecIso
        (CommRingCat.of K)).hom
    have : IsIso tail := by dsimp only [tail]; infer_instance
    have hinj : Function.Injective tail.hom := (asIso tail).commRingCatIsoToRingEquiv.injective
    let χ : Γ(X', π ⁻¹ᵁ U.1) →+* K := (x'.1.app (π ⁻¹ᵁ U.1) ≫ tail).hom
    have hkerχ : RingHom.ker χ = RingHom.ker (x'.1.app (π ⁻¹ᵁ U.1)).hom := by
      ext a
      simp only [RingHom.mem_ker]
      exact map_eq_zero_iff tail.hom hinj
    have key : ∀ k : K, χ ((π.app U.1).hom ((t.appLE ⊤ U.1 le_top).hom
        ((Scheme.ΓSpecIso (CommRingCat.of K)).inv k))) = k := by
      intro k
      change ((Scheme.ΓSpecIso _).inv ≫ (t.appLE ⊤ U.1 le_top ≫ π.app U.1 ≫ x'.1.app (π ⁻¹ᵁ U.1) ≫
        (Spec (CommRingCat.of K)).presheaf.map (eqToHom htop.symm).op) ≫ (Scheme.ΓSpecIso _).hom) k
          = k
      have hmid : t.appLE ⊤ U.1 le_top ≫ π.app U.1 ≫ x'.1.app (π ⁻¹ᵁ U.1) ≫
          (Spec (CommRingCat.of K)).presheaf.map (eqToHom htop.symm).op = 𝟙 _ := by
        have h1 : π.app U.1 ≫ x'.1.app (π ⁻¹ᵁ U.1) = x.app U.1 := (Scheme.Hom.comp_app x'.1 π
          U.1).symm
        have e' : (⊤ : (Spec (CommRingCat.of K)).Opens) ≤ x ⁻¹ᵁ U.1 :=
          le_of_eq htop.symm
        have h4 : x.app U.1 ≫
            (Spec (CommRingCat.of K)).presheaf.map (eqToHom htop.symm).op =
            x.appLE U.1 ⊤ e' := by
          exact congrArg
            (fun i : op (x ⁻¹ᵁ U.1) ⟶ op (⊤ : (Spec (CommRingCat.of K)).Opens) =>
              x.app U.1 ≫ (Spec (CommRingCat.of K)).presheaf.map i)
            (Subsingleton.elim _ _)
        rw [reassoc_of% h1]
        refine (congrArg (fun h => t.appLE ⊤ U.1 le_top ≫ h) h4).trans ?_
        have hcomp : t.appLE ⊤ U.1 le_top ≫ x.appLE U.1 ⊤ e' =
            (x ≫ t).appLE ⊤ ⊤ le_top :=
          Scheme.Hom.appLE_comp_appLE x t ⊤ U.1 ⊤ le_top e'
        have hid : (x ≫ t).appLE ⊤ ⊤ le_top =
            Scheme.Hom.appLE (𝟙 (Spec (CommRingCat.of K))) ⊤ ⊤ le_top :=
          congrArg (fun h : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of K) =>
            h.appLE ⊤ ⊤ le_top) hxt
        exact hcomp.trans (hid.trans
          ((Scheme.Hom.appLE_eq_app (𝟙 (Spec (CommRingCat.of K)))).trans
            (Scheme.Hom.id_app ⊤)))
      rw [hmid, Category.id_comp, Iso.inv_hom_id]
      rfl
    have hχ : Function.Surjective (χ.comp (algebraMap Γ(X, U.1) Γ(X', π ⁻¹ᵁ U.1))) := fun k => ⟨_,
      key k⟩
    set 𝔪 : Ideal Γ(X, U.1) := RingHom.ker (χ.comp (algebraMap Γ(X, U.1) Γ(X', π ⁻¹ᵁ U.1))) with
      h𝔪def
    have h𝔪max : 𝔪.IsMaximal := RingHom.ker_isMaximal_of_surjective _ hχ
    have h𝔪ker : 𝔪 = RingHom.ker (x.app U.1).hom := by
      ext a
      simp only [h𝔪def, RingHom.mem_ker, RingHom.coe_comp, Function.comp_apply]
      change tail.hom ((x'.1.app (π ⁻¹ᵁ U.1)).hom ((π.app U.1).hom a)) = 0 ↔ _
      rw [map_eq_zero_iff tail.hom hinj]
      exact Iff.rfl
    let algK : Algebra K Γ(X, U.1) :=
      ((t.appLE ⊤ U.1 le_top).hom.comp
        ((Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.symm : K →+* _)).toAlgebra
    have : Algebra.IsStandardSmoothOfRelativeDimension 1 K Γ(X, U.1) :=
      RingHom.IsStandardSmoothOfRelativeDimension.comp hsm
        (RingHom.IsStandardSmoothOfRelativeDimension.equiv
          (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.symm)
    obtain ⟨hdom, hdvr⟩ :=
      Algebra.IsStandardSmoothOfRelativeDimension.isDiscreteValuationRing_localization_atPrime (k
        := K) 𝔪
    rw [hloc, hker, ← h𝔪ker]
    exact Ideal.span_algebraNorm_eq_of_ker_eq_span_of_isDiscreteValuationRing χ hχ g (hkerχ.trans
      hgspan) 𝔪 rfl
      (Localization.AtPrime 𝔪)
  · obtain ⟨s, hs, hgs⟩ := exists_isFrameOn_and_app_eq_coeff_smul ι' (π ⁻¹ᵁ U.1) τ
    set g : Γ(X', π ⁻¹ᵁ U.1) := coeff ι' (π ⁻¹ᵁ U.1) τ.hom with hgdef
    have hgspan : RingHom.ker (x'.1.app (π ⁻¹ᵁ U.1)).hom = Ideal.span {g} := by
      rw [← hker', ← hZι']
      exact ((IsInvertible.coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq hP ι').2 ⟨π ⁻¹ᵁ U.1, hUaff'⟩
        τ).1
    have hloc := ideal_zeroSchemeIdeal_detSection_eq_span_norm π d hN ι' U e he s hs g hgs
    have hx'U : x'.1.base pt ∉ π ⁻¹ᵁ U.1 := fun h => hxU (by rw [hxdef]; exact h)
    have hbot : x'.1 ⁻¹ᵁ (π ⁻¹ᵁ U.1) = ⊥ := opens_eq_bot_of_not_mem (p := pt) hx'U
    have : Subsingleton Γ(Spec (CommRingCat.of K), x'.1 ⁻¹ᵁ (π ⁻¹ᵁ U.1)) := by
      rw [hbot]; exact CommRingCat.subsingleton_of_isTerminal (Spec (CommRingCat.of
        K)).sheaf.isTerminalOfEmpty
    have hgunit : IsUnit g := by
      rw [← Ideal.span_singleton_eq_top, ← hgspan, Ideal.eq_top_iff_one, RingHom.mem_ker]
      exact Subsingleton.elim _ _
    rw [hloc, hker, Ideal.span_singleton_eq_top.mpr (hgunit.map _)]
    have hbot' : x ⁻¹ᵁ U.1 = ⊥ := opens_eq_bot_of_not_mem (p := pt) hxU
    have : Subsingleton Γ(Spec (CommRingCat.of K), x ⁻¹ᵁ U.1) := by
      rw [hbot']; exact CommRingCat.subsingleton_of_isTerminal (Spec (CommRingCat.of
        K)).sheaf.isTerminalOfEmpty
    symm
    rw [Ideal.eq_top_iff_one, RingHom.mem_ker]
    exact Subsingleton.elim _ _

end AlgebraicGeometry.Scheme.Modules.NormPoint

open AlgebraicGeometry.Scheme.Modules.NormPoint in
theorem _root_.AlgebraicGeometry.Scheme.Modules.nonempty_normModule_invModule_ker_iso
    {K : Type u} [Field K] {X X' : Scheme.{u}}
    (t : X ⟶ Spec (CommRingCat.of K)) (t' : X' ⟶ Spec (CommRingCat.of K))
    [IsSeparated t] [IsSeparated t'] [SmoothOfRelativeDimension 1 t] [SmoothOfRelativeDimension 1
      t']
    (π : X' ⟶ X) (hπ : π ≫ t = t') [IsFinite π] [Flat π] [LocallyOfFinitePresentation π]
    (d : ℕ) (hd : ∀ y : X, π.finrank y = d)
    (x' : {q : Spec (CommRingCat.of K) ⟶ X' // q ≫ t' = 𝟙 _}) :
    Nonempty (Scheme.Modules.normModule π d (x'.1.ker).invModule ≅ ((x'.1 ≫ π).ker).invModule) := by
  have hI' : (x'.1.ker).IsInvertible := Scheme.Hom.isInvertible_ker_of_comp_eq_id (p := t') x'.1
    x'.2
  have hx : (x'.1 ≫ π) ≫ t = 𝟙 _ := by rw [Category.assoc, hπ, x'.2]
  have hI : ((x'.1 ≫ π).ker).IsInvertible := Scheme.Hom.isInvertible_ker_of_comp_eq_id (p := t)
    (x'.1 ≫ π) hx
  have hN : Scheme.Modules.IsInvertible (Scheme.Modules.normModule π d (x'.1.ker).invModule) :=
    Scheme.Modules.IsInvertible.normModule π d hd hI'.isInvertible_invModule
  have : IsIso (Scheme.Modules.normModuleUnitEval π d) := by
    have hE : Scheme.Modules.IsLocallyFreeOfRank d
        ((Scheme.Modules.pushforward π).obj (𝟙_ X'.Modules)) :=
      Scheme.Modules.isLocallyFreeOfRank_pushforward_of_isFinite_of_flat_of_locallyTrivialOver π d
        hd (𝟙_ X'.Modules)
        (fun y =>
          Scheme.Modules.IsInvertible.exists_nonempty_pullback_preimage_iso_tensorUnit_of_isFinite π
          (Scheme.Modules.isInvertible_unit X') y)
    exact (Scheme.Modules.isInvertible_det_of_isLocallyFreeOfRank hE).isIso_ev_app_tensorUnit
  obtain ⟨e, -⟩ := hN.exists_iso_invModule_zeroSchemeIdeal (detSection π d
    (x'.1.ker).invModuleSection)
    (by rw [zeroSchemeIdeal_detSection_invModuleSection t t' π hπ d hd x']; exact hI)
  rw [zeroSchemeIdeal_detSection_invModuleSection t t' π hπ d hd x'] at e
  exact ⟨e⟩
end AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_nonempty_normModule_invModule_ker_iso
end ProofImplementation

open AlgebraicGeometry.Scheme.IdealSheafData in
open AlgebraicGeometry.Scheme in
open PresheafOfModules.PullbackMonoidal in
attribute [-instance]
  AlgebraicGeometry.Scheme.Hom.opensMapFinal
  AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid
  AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited
  SheafOfModules.isIso_ihomModelToIhom
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub
  IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop
  IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero
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
  AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap
  AlgebraicGeometry.Scheme.Modules.pullback_monoidal
  AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization'
  AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap
  AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal
  AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap
  AlgebraicGeometry.Scheme.Modules.sheafifyPullback_lifting
  TwoChartCech.Sections.M0_moduleA
  TwoChartCech.Sections.M1_module
  TwoChartCech.Cover.A01_algebra
  TwoChartCech.Cover.A0_algebra
  TwoChartCech.Cover.A1_commRing
  TwoChartCech.Cover.A1_algebra
  TwoChartCech.Sections.M01_module
  TwoChartCech.Sections.M0_addCommGroup
  TwoChartCech.Sections.M0_tower
  TwoChartCech.Sections.M01_addCommGroup
attribute [-instance] TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower
  TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module
  TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup
  TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower
  CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup
  CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup
  CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite
  CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free
attribute [-simp] AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection
  AlgebraicGeometry.Scheme.Modules.pullbackSection_def
  AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection
  AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec
  AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right
  AlgebraicGeometry.Scheme.Modules.map_unitSection
  AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply
  AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left
  AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ
  PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom
  SheafOfModules.ihomSectionsEquivFamily_unit
  AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app
  AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right
  AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left
  AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply
  SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app
  AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app
  AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app
  AlgebraicGeometry.Scheme.IdealSheafData.sres_sres
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app
attribute [-simp] AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app PresheafOfModules.freeεIso_hom_app
  PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.RelPicard.SubPicCondition.mk.injEq
  AlgebraicGeometry.RelPicard.SubPicCondition.mk.sizeOf_spec
  GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply
  GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec
  NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe
  GoodReductionJacobian.RelativeGroupLaw.mk.injEq
  NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom
  NeronModelInfra.schemeHomOverToOverHom_left
  NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver
  AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.injEq
  AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.sizeOf_spec
  AlgebraicGeometry.RelPicard.SubPicCondition.onClasses_mk
  AlgebraicGeometry.RelPicard.relSubPicPresheaf_map_coe
  GoodReductionJacobian.relativeGroupLawOfGrpObj_inv
  GoodReductionJacobian.relativeGroupLawOfGrpObj_mul
  GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe
  GoodReductionJacobian.relativeGroupLawOfGrpObj_one
  GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left
  AlgebraicGeometry.RelPicard.algEquivZeroGroupCut_toSubPicCondition
  AlgebraicGeometry.RelPicard.rigSection_snd
  AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L
  AlgebraicGeometry.RelPicard.rigSection_snd_assoc
attribute [-simp] NeronModelInfra.schemeHomOverComp_id_left
  NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe
  NeronModelInfra.schemeHomOverComp_coe AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq
  TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq
  TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec
  TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec
  TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec
  CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app
  PresheafOfModules.pushforwardCongr_inv_app_app_apply
  PresheafOfModules.pushforwardNatTrans_app_app_apply
  PresheafOfModules.pushforwardCongr_hom_app_app_apply
