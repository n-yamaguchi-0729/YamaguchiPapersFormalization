/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_SmoothProperCurve_exists_twoChart_of_section_invModule.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Geometrically.Integral
import AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import SchemeTheory.Cohomology.Cech.TwoAffineOpenCover
import AlgebraicCurves.Geometry.Curves.SmoothProperCurveFiniteMapData
import AlgebraicCurves.Geometry.Sheaves.ModulesSectionZeroScheme
import SchemeTheory.Modules.TensorSections
import AlgebraicCurves.RelativeDivisors.Cartier
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_exists_ratio_section
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq
import AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_zeroSchemeIdeal_invModuleSection
import AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import AlgebraicCurves.Geometry.Schemes.Scheme_Hom_isInvertible_ker_of_comp_eq_id
import AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_pow
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsFrameOn_nonempty_pullback_iso_unit
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_isFrameOn_app_of_disjoint_support_zeroSchemeIdeal

/-!
# SmoothProperCurve exists twoChart of section invModule

A section of an invertible module with the prescribed zero locus produces a two-chart cover and
inverse coordinate sections.
-/

section ProofImplementation

namespace AlgebraicCurves.Models.Gluing.Proofs
namespace SmoothProperCurve_exists_twoChart_of_section_invModule
attribute [-instance] SheafOfModules.isIso_ihomModelToIhom
attribute [-instance] PresheafOfModules.PullbackMonoidal.pullback_monoidal
attribute [-instance] PresheafOfModules.PullbackMonoidal.isIso_δ
attribute [-instance] PresheafOfModules.pushforward_laxMonoidal
attribute [-instance] PresheafOfModules.PullbackMonoidal.isIso_η
attribute [-instance] PresheafOfModules.free_monoidal
attribute [-instance] PresheafOfModules.restrictScalars_laxMonoidal
attribute [-instance] PresheafOfModules.PullbackMonoidal.isIso_δ_gS
attribute [-instance] PresheafOfModules.pullback_oplaxMonoidal
open _root_.PresheafOfModules.PullbackMonoidal
  (instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb)
in
attribute [-instance]
  instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb
attribute [-instance] PresheafOfModules.pullback_monoidal'
attribute [-instance] AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap
attribute [-instance] AlgebraicGeometry.Scheme.Modules.pullback_monoidal
attribute [-instance] AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization'
attribute [-instance] AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap
attribute [-instance] AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal
attribute [-instance] AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap
attribute [-instance] AlgebraicGeometry.Scheme.Modules.sheafifyPullback_lifting
attribute [-simp] PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom
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
  PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app

universe u

open scoped TensorProduct
open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.SmoothProperCurve
open _root_.NeronModelInfra

open _root_.CategoryTheory.MonoidalCategory
open _root_.Opposite

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace SmoothProperCurve
namespace ORDERCHART
open _root_.AlgebraicGeometry.SmoothProperCurve
open _root_.AlgebraicGeometry

noncomputable section

open _root_.AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

lemma ringMap_map {W₁ W₂ W₃ : X.Opens} (k₁ : op W₁ ⟶ op W₂) (k₂ : op W₂ ⟶ op W₃) (k : op W₁ ⟶ op W₃)
    (a : Γ(X, W₁)) : X.presheaf.map k₂ (X.presheaf.map k₁ a) = X.presheaf.map k a := by
  rw [show k = k₁ ≫ k₂ from Quiver.Hom.unop_inj (Subsingleton.elim _ _), X.presheaf.map_comp]
  rfl

lemma isUnit_of_le_basicOpen {U : X.Opens} (f : Γ(X, U)) (h : U ≤ X.basicOpen f) : IsUnit f := by
  have h1 : IsUnit (X.presheaf.map (homOfLE (X.basicOpen_le f)).op f) :=
    RingedSpace.isUnit_res_basicOpen (X := X.toLocallyRingedSpace.toRingedSpace) f
  have h2 := h1.map (X.presheaf.map (homOfLE h).op).hom
  have h3 : (X.presheaf.map (homOfLE h).op).hom (X.presheaf.map (homOfLE (X.basicOpen_le f)).op f) =
      X.presheaf.map (𝟙 (op U)) f := ringMap_map _ _ _ _
  rw [h3, X.presheaf.map_id] at h2
  exact h2

variable {M : X.Modules}

lemma mem_basicOpen_coeff_iff (hM : IsInvertible M) (s : 𝟙_ X.Modules ⟶ M) (A : X.affineOpens)
    (τ : M.restrict A.1.ι ≅ 𝟙_ (A.1 : Scheme.{u}).Modules) {x : X} (hxA : x ∈ A.1) :
    x ∈ X.basicOpen (coeff s A.1 τ.hom) ↔ x ∉ (zeroSchemeIdeal s).support := by
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem (U := A) hxA,
    ((IsInvertible.coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq hM s).2 A τ).1,
    Scheme.zeroLocus_span, Scheme.zeroLocus_singleton, Set.mem_compl_iff, not_not]
  rfl

lemma isUnit_coeff (hM : IsInvertible M) (s : 𝟙_ X.Modules ⟶ M) (A : X.affineOpens)
    (τ : M.restrict A.1.ι ≅ 𝟙_ (A.1 : Scheme.{u}).Modules)
    (hA : ∀ x ∈ A.1, x ∉ (zeroSchemeIdeal s).support) : IsUnit (coeff s A.1 τ.hom) :=
  isUnit_of_le_basicOpen _ fun x hxA => (mem_basicOpen_coeff_iff hM s A τ hxA).2 (hA x hxA)

section ratio

variable (hM : IsInvertible M) (s t : 𝟙_ X.Modules ⟶ M)
  (f : Γ(X, (zeroSchemeIdeal t).support.compl))
  (hf : ∀ (A : X.affineOpens) (hA : A.1 ≤ (zeroSchemeIdeal t).support.compl)
    (τ : M.restrict A.1.ι ≅ 𝟙_ (A.1 : Scheme.{u}).Modules),
    (X.presheaf.map (homOfLE hA).op).hom f * coeff t A.1 τ.hom = coeff s A.1 τ.hom)

include hM hf

lemma mem_basicOpen_ratio_iff (A : X.affineOpens) (hA : A.1 ≤ (zeroSchemeIdeal t).support.compl)
    (τ : M.restrict A.1.ι ≅ 𝟙_ (A.1 : Scheme.{u}).Modules) {x : X} (hxA : x ∈ A.1) :
    x ∈ X.basicOpen f ↔ x ∉ (zeroSchemeIdeal s).support := by
  have hct : IsUnit (coeff t A.1 τ.hom) := isUnit_coeff hM t A τ fun y hy => hA hy
  have e := hf A hA τ
  have hres : X.basicOpen ((X.presheaf.map (homOfLE hA).op).hom f) = A.1 ⊓ X.basicOpen f :=
    Scheme.basicOpen_res _ _ _
  have key : A.1 ⊓ X.basicOpen f = X.basicOpen (coeff s A.1 τ.hom) := by
    rw [← e, Scheme.basicOpen_mul, X.basicOpen_of_isUnit hct, hres, inf_comm
      (A.1 ⊓ X.basicOpen f) A.1,
      ← inf_assoc, inf_idem]
  rw [← mem_basicOpen_coeff_iff hM s A τ hxA, ← key]
  exact ⟨fun h => ⟨hxA, h⟩, fun h => h.2⟩

lemma inf_eq_basicOpen_ratio :
    (zeroSchemeIdeal t).support.compl ⊓ (zeroSchemeIdeal s).support.compl = X.basicOpen f := by
  ext x
  change x ∈ ((zeroSchemeIdeal t).support.compl : Set X) ∩ (zeroSchemeIdeal s).support.compl ↔
    x ∈ (X.basicOpen f : Set X)
  constructor
  · rintro ⟨hxU, hxV⟩
    obtain ⟨A, hxA, hAU, ⟨τ⟩⟩ := hM.exists_restrict_iso (V := (zeroSchemeIdeal t).support.compl) hxU
    exact (mem_basicOpen_ratio_iff hM s t f hf A hAU τ hxA).2 hxV
  · intro hx
    have hxU : x ∈ (zeroSchemeIdeal t).support.compl := X.basicOpen_le f hx
    obtain ⟨A, hxA, hAU, ⟨τ⟩⟩ := hM.exists_restrict_iso (V := (zeroSchemeIdeal t).support.compl) hxU
    exact ⟨hxU, (mem_basicOpen_ratio_iff hM s t f hf A hAU τ hxA).1 hx⟩

end ratio

theorem main
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (m : ℕ) (hm : 1 ≤ m)
    (s : 𝟙_ C.Modules ⟶ (ε.1.ker ^ m).invModule)
    (hs : ∀ x ∈ Set.range ε.1.base, x ∉ (Scheme.Modules.zeroSchemeIdeal s).support) :
    ∃ (U V : C.Opens) (_ : U ⊔ V = ⊤)
      (_ : ∀ x : C, x ∈ U ↔ x ∉ Set.range ε.1.base)
      (_ : ∀ x : C, x ∈ V ↔ x ∉ (Scheme.Modules.zeroSchemeIdeal s).support)
      (f : Γ(C, U)) (g : Γ(C, V))
      (_ : U ⊓ V = C.basicOpen f) (_ : U ⊓ V = C.basicOpen g)
      (_ : (C.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op).hom f *
        (C.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op).hom g = 1),
      ∀ W : C.affineOpens, ∀ hW : (W : C.Opens) ≤ V,
        (ε.1.ker ^ m).ideal W = Ideal.span {(C.presheaf.map (homOfLE hW).op).hom g} := by
  classical
  have : IsClosedImmersion (ε.1 ≫ c) := by rw [ε.2]; infer_instance
  have : IsClosedImmersion ε.1 := IsClosedImmersion.of_comp ε.1 c
  have hkI : ε.1.ker.IsInvertible := Scheme.Hom.isInvertible_ker_of_comp_eq_id ε.1 ε.2
  have hI : (ε.1.ker ^ m).IsInvertible := hkI.pow m
  have hM : IsInvertible (ε.1.ker ^ m).invModule := hI.isInvertible_invModule
  let t : 𝟙_ C.Modules ⟶ (ε.1.ker ^ m).invModule := (ε.1.ker ^ m).invModuleSection
  have hZt : zeroSchemeIdeal t = ε.1.ker ^ m := hI.zeroSchemeIdeal_invModuleSection
  have hm0 : m ≠ 0 := by omega
  have hsuppI : ((ε.1.ker ^ m).support : Set C) = Set.range ε.1.base := by
    rw [Scheme.IdealSheafData.support_pow _ m hm0, Scheme.Hom.support_ker]
    exact ε.1.isClosedEmbedding.isClosed_range.closure_eq
  have hsuppt : ∀ x : C, x ∈ (zeroSchemeIdeal t).support ↔ x ∈ Set.range ε.1.base := by
    intro x
    rw [hZt, ← hsuppI]
    rfl
  let U : C.Opens := (zeroSchemeIdeal t).support.compl
  let V : C.Opens := (zeroSchemeIdeal s).support.compl
  have hU : ∀ x : C, x ∈ U ↔ x ∉ Set.range ε.1.base := fun x => by
    rw [← hsuppt]
    rfl
  have hV : ∀ x : C, x ∈ V ↔ x ∉ (zeroSchemeIdeal s).support := fun x => Iff.rfl
  have hUV : U ⊔ V = ⊤ := by
    rw [eq_top_iff]
    intro x _
    rw [TopologicalSpace.Opens.mem_sup]
    by_cases hx : x ∈ (zeroSchemeIdeal s).support
    · exact Or.inl ((hU x).2 fun hxε => hs x hxε hx)
    · exact Or.inr hx
  obtain ⟨f, hf⟩ := IsInvertible.exists_ratio_section hM s t
  obtain ⟨g, hg⟩ := IsInvertible.exists_ratio_section hM t s
  have hbf : U ⊓ V = C.basicOpen f := inf_eq_basicOpen_ratio hM s t f hf
  have hbg : U ⊓ V = C.basicOpen g := by
    rw [inf_comm]
    exact inf_eq_basicOpen_ratio hM t s g hg
  have hfg : (C.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op).hom f *
      (C.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op).hom g = 1 := by
    let ι := {A : C.affineOpens // A.1 ≤ U ⊓ V ∧
      Nonempty ((ε.1.ker ^ m).invModule.restrict A.1.ι ≅ 𝟙_ (A.1 : Scheme.{u}).Modules)}
    have hcover : U ⊓ V ≤ ⨆ A : ι, (A.1.1 : C.Opens) := by
      intro x hx
      obtain ⟨A, hxA, hAUV, hτ⟩ := hM.exists_restrict_iso (V := U ⊓ V) hx
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨A, hAUV, hτ⟩, hxA⟩
    apply C.sheaf.eq_of_locally_eq' (fun A : ι => (A.1.1 : C.Opens)) (U ⊓ V)
      (fun A => homOfLE A.2.1) hcover
    rintro ⟨A, hAUV, ⟨τ⟩⟩
    have hAU : A.1 ≤ U := hAUV.trans inf_le_left
    have hAV : A.1 ≤ V := hAUV.trans inf_le_right
    have hct : IsUnit (coeff t A.1 τ.hom) := isUnit_coeff hM t A τ fun y hy => hAU hy
    have hcs : IsUnit (coeff s A.1 τ.hom) := isUnit_coeff hM s A τ fun y hy => hAV hy
    have e1 := hf A hAU τ
    have e2 := hg A hAV τ
    change (C.presheaf.map (homOfLE hAUV).op).hom
        ((C.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op).hom f *
          (C.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op).hom g) =
      (C.presheaf.map (homOfLE hAUV).op).hom 1
    rw [map_mul, map_one]
    have h1 : (C.presheaf.map (homOfLE hAUV).op).hom
        ((C.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op).hom f) =
        (C.presheaf.map (homOfLE hAU).op).hom f := ringMap_map _ _ _ _
    have h2 : (C.presheaf.map (homOfLE hAUV).op).hom
        ((C.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op).hom g) =
        (C.presheaf.map (homOfLE hAV).op).hom g := ringMap_map _ _ _ _
    rw [h1, h2]
    rw [← (hcs.mul hct).mul_left_inj, one_mul,
      show (C.presheaf.map (homOfLE hAU).op).hom f * (C.presheaf.map (homOfLE hAV).op).hom g *
          (coeff s A.1 τ.hom * coeff t A.1 τ.hom) =
        ((C.presheaf.map (homOfLE hAU).op).hom f * coeff t A.1 τ.hom) *
          ((C.presheaf.map (homOfLE hAV).op).hom g * coeff s A.1 τ.hom) by ring,
      e1, e2]
  have hgen : ∀ W : C.affineOpens, ∀ hW : (W : C.Opens) ≤ V,
      (ε.1.ker ^ m).ideal W = Ideal.span {(C.presheaf.map (homOfLE hW).op).hom g} := by
    intro W hWV
    have hdisjV : Disjoint (V : Set C) (zeroSchemeIdeal s).support := by
      rw [Set.disjoint_iff]
      rintro x ⟨hxV, hxZ⟩
      exact hxV hxZ
    have hframe := IsInvertible.isFrameOn_app_of_disjoint_support_zeroSchemeIdeal hM s V hdisjV
    obtain ⟨e⟩ := hframe.nonempty_pullback_iso_unit W.1 le_top hWV
    let τ : (ε.1.ker ^ m).invModule.restrict W.1.ι ≅ 𝟙_ (W.1 : Scheme.{u}).Modules :=
      restrictIsoOfLE le_rfl e
    have hcs : IsUnit (coeff s W.1 τ.hom) := isUnit_coeff hM s W τ fun y hy => hWV hy
    have e2 := hg W hWV τ
    calc (ε.1.ker ^ m).ideal W = (zeroSchemeIdeal t).ideal W := by rw [hZt]
      _ = Ideal.span {coeff t W.1 τ.hom} :=
          ((IsInvertible.coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq hM t).2 W τ).1
      _ = Ideal.span {(C.presheaf.map (homOfLE hWV).op).hom g * coeff s W.1 τ.hom} := by rw [e2]
      _ = Ideal.span {(C.presheaf.map (homOfLE hWV).op).hom g} :=
          Ideal.span_singleton_mul_right_unit hcs _
  exact ⟨U, V, hUV, hU, hV, f, g, hbf, hbg, hfg, hgen⟩

end

end AlgebraicGeometry.SmoothProperCurve.ORDERCHART

theorem _root_.AlgebraicGeometry.SmoothProperCurve.exists_twoChart_of_section_invModule
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (m : ℕ) (hm : 1 ≤ m)
    (s : 𝟙_ C.Modules ⟶ (ε.1.ker ^ m).invModule)
    (hs : ∀ x ∈ Set.range ε.1.base, x ∉ (Scheme.Modules.zeroSchemeIdeal s).support) :
    ∃ (U V : C.Opens) (_ : U ⊔ V = ⊤)
      (_ : ∀ x : C, x ∈ U ↔ x ∉ Set.range ε.1.base)
      (_ : ∀ x : C, x ∈ V ↔ x ∉ (Scheme.Modules.zeroSchemeIdeal s).support)
      (f : Γ(C, U)) (g : Γ(C, V))
      (_ : U ⊓ V = C.basicOpen f) (_ : U ⊓ V = C.basicOpen g)
      (_ : (C.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op).hom f *
        (C.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op).hom g = 1),
      ∀ W : C.affineOpens, ∀ hW : (W : C.Opens) ≤ V,
        (ε.1.ker ^ m).ideal W = Ideal.span {(C.presheaf.map (homOfLE hW).op).hom g} :=
  AlgebraicGeometry.SmoothProperCurve.ORDERCHART.main R c ε m hm s hs
end SmoothProperCurve_exists_twoChart_of_section_invModule
end AlgebraicCurves.Models.Gluing.Proofs
end ProofImplementation

attribute [-instance] AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg
attribute [-instance] AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt
attribute [-instance] AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup
attribute [-instance] AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd
attribute [-instance] AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub
open _root_.AlgebraicGeometry.Scheme.IdealSheafData.IdealHom
  (instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop)
in
attribute [-instance]
  instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop
open _root_.AlgebraicGeometry.Scheme.IdealSheafData.IdealHom
  (instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop)
in
attribute [-instance]
  instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop
attribute [-instance] AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat
attribute [-instance] AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero
attribute [-instance] AlgebraicGeometry.ChowDatum.hι_closed
attribute [-instance] AlgebraicGeometry.ChowDatumProj.hιN_closed
attribute [-instance] AlgebraicGeometry.ChowDatumProj.hp_proper
attribute [-instance] AlgebraicGeometry.ChowDatum.hp_isoU
attribute [-instance] AlgebraicGeometry.ChowDatum.hp_proper
attribute [-instance] AlgebraicGeometry.ProjSpace.algebraAway
attribute [-instance] AlgebraicGeometry.ProjSpace.instIsProperProdOverπ
attribute [-instance] AlgebraicGeometry.ChowDatumProj.hp_isoU
attribute [-instance] AlgebraicGeometry.ProjSpace.isProper_π
attribute [-instance] AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial
attribute [-instance] SheafOfModules.isIso_ihomModelToIhom
attribute [-instance] PresheafOfModules.PullbackMonoidal.pullback_monoidal
attribute [-instance] PresheafOfModules.PullbackMonoidal.isIso_δ
attribute [-instance] PresheafOfModules.pushforward_laxMonoidal
attribute [-instance] PresheafOfModules.PullbackMonoidal.isIso_η
attribute [-instance] PresheafOfModules.free_monoidal
attribute [-instance] PresheafOfModules.restrictScalars_laxMonoidal
attribute [-instance] PresheafOfModules.PullbackMonoidal.isIso_δ_gS
attribute [-instance] PresheafOfModules.pullback_oplaxMonoidal
open _root_.PresheafOfModules.PullbackMonoidal
  (instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb)
in
attribute [-instance]
  instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb
attribute [-instance] PresheafOfModules.pullback_monoidal'
attribute [-instance] AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap
attribute [-instance] AlgebraicGeometry.Scheme.Modules.pullback_monoidal
attribute [-instance] AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization'
attribute [-instance] AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap
attribute [-instance] AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal
attribute [-instance] AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap
attribute [-instance] AlgebraicGeometry.Scheme.Modules.sheafifyPullback_lifting
attribute [-simp] AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right
  AlgebraicGeometry.Scheme.Modules.map_unitSection
  AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply
  AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left
  AlgebraicGeometry.Scheme.Modules.tensorPow_zero
  AlgebraicGeometry.Scheme.Modules.tensorPow_succ
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
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app
  AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.injEq
  AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.sizeOf_spec
  AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec
  AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq
  PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom
  SheafOfModules.ihomSectionsEquivFamily_unit
  AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app
  AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right
  AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left
  AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply
  SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app
  AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply
attribute [-simp] AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply
  PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app
