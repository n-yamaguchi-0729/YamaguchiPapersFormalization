/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_exists_shortExact_thickening_unit.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.CategoryTheory.Abelian.DiagramLemmas.KernelCokernelComp
import Nyll.AlgebraicCurves.Geometry.Sheaves.IdealSheafModule
import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesLocallyFreeOfRank
import Nyll.SchemeTheory.Modules.Monoidal
import Nyll.SchemeTheory.Modules.PullbackMonoidal
import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesProjectionMorphism
import Nyll.SchemeTheory.Modules.PullbackLocalSection
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_Hom_epi_iff_locallySurjective
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_mono_whiskerLeft_moduleIota
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_isIso_projectionMorphism_of_iso_free
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_isIso_pullback_map_projectionMorphism_iff
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_Hom_isIso_of_forall_exists_isIso_pullback_map
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_pullbackTensorUnitObjIso_hom_app_pullbackLocalSection_unitSection
import Nyll.AlgebraicCurves.RelativeDivisors.Cartier
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_exists_tensor_iso_mul_module
import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_isLocallyFreeOfRank_one_iff_isInvertible
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_tensor
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_isInvertible_module
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_pow
import Mathlib.Util.WithWeakNamespace

/-!
# Short exact sequences of ideal thickenings

The unit map for a closed subscheme and tensoring by locally free module sheaves give
short exact sequences. Cokernels for successive powers of an invertible ideal yield
the exact sequence of thickened restrictions.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_IdealSheafData_IsInvertible_exists_shortExact_thickening_unit
attribute [-instance]
  SheafOfModules.isIso_ihomModelToIhom
attribute [-simp]
  PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom
  SheafOfModules.ihomSectionsEquivFamily_unit
  AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply
  SheafOfModules.ihomEval_unit_app
  AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right
  AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left
  AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply
  SheafOfModules.unit_ihomSectionsEquivFamily
  AlgebraicGeometry.Scheme.Modules.familyOfHom_app
  AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.Opposite
open _root_.TopologicalSpace
open _root_.CategoryTheory.Functor.LaxMonoidal
open _root_.CategoryTheory.Functor.OplaxMonoidal

noncomputable section

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace IdealSheafData
open _root_.AlgebraicGeometry.Scheme.IdealSheafData
end AlgebraicGeometry.Scheme.IdealSheafData
namespace AlgebraicGeometry.Scheme.IdealSheafData
with_weak_namespace _root_.AlgebraicCurves.Geometry.Sheaves.Proofs
open scoped Scheme_IdealSheafData_IsInvertible_exists_shortExact_thickening_unit.AlgebraicGeometry
  Scheme_IdealSheafData_IsInvertible_exists_shortExact_thickening_unit.AlgebraicGeometry.Scheme in
with_weak_namespace Scheme_IdealSheafData_IsInvertible_exists_shortExact_thickening_unit
with_weak_namespace AlgebraicGeometry.Scheme
open scoped IdealSheafData in
with_weak_namespace IdealSheafData
private noncomputable def _root_.AlgebraicGeometry.Scheme.IdealSheafData.uMod
    {X : Scheme.{u}} (I : X.IdealSheafData) :
    ((𝟙_ X.Modules : X.Modules) ⟶
      ((Scheme.Modules.pushforward I.subschemeι).obj (𝟙_ I.subscheme.Modules) : X.Modules)) :=
  I.subschemeι.unitToPushforwardUnit

end AlgebraicGeometry.Scheme.IdealSheafData
namespace AlgebraicGeometry.Scheme.IdealSheafData
with_weak_namespace _root_.AlgebraicCurves.Geometry.Sheaves.Proofs
open scoped Scheme_IdealSheafData_IsInvertible_exists_shortExact_thickening_unit.AlgebraicGeometry
  Scheme_IdealSheafData_IsInvertible_exists_shortExact_thickening_unit.AlgebraicGeometry.Scheme in
with_weak_namespace Scheme_IdealSheafData_IsInvertible_exists_shortExact_thickening_unit
with_weak_namespace AlgebraicGeometry.Scheme
open scoped IdealSheafData in
with_weak_namespace IdealSheafData
private theorem _root_.AlgebraicGeometry.Scheme.IdealSheafData.moduleι_comp_uMod
    {X : Scheme.{u}} (I : X.IdealSheafData) :
    I.moduleι ≫ I.uMod = 0 :=
  kernel.condition I.subschemeι.unitToPushforwardUnit

end AlgebraicGeometry.Scheme.IdealSheafData
namespace AlgebraicGeometry.Scheme.IdealSheafData
with_weak_namespace _root_.AlgebraicCurves.Geometry.Sheaves.Proofs
open scoped Scheme_IdealSheafData_IsInvertible_exists_shortExact_thickening_unit.AlgebraicGeometry
  Scheme_IdealSheafData_IsInvertible_exists_shortExact_thickening_unit.AlgebraicGeometry.Scheme in
with_weak_namespace Scheme_IdealSheafData_IsInvertible_exists_shortExact_thickening_unit
with_weak_namespace AlgebraicGeometry.Scheme
open scoped IdealSheafData in
with_weak_namespace IdealSheafData
private theorem _root_.AlgebraicGeometry.Scheme.IdealSheafData.mono_moduleι'
    {X : Scheme.{u}} (I : X.IdealSheafData) :
    Mono I.moduleι :=
  ⟨fun _ _ w => (cancel_mono (kernel.ι I.subschemeι.unitToPushforwardUnit)).mp w⟩

end AlgebraicGeometry.Scheme.IdealSheafData
namespace AlgebraicGeometry.Scheme.IdealSheafData
with_weak_namespace _root_.AlgebraicCurves.Geometry.Sheaves.Proofs
open scoped Scheme_IdealSheafData_IsInvertible_exists_shortExact_thickening_unit.AlgebraicGeometry
  Scheme_IdealSheafData_IsInvertible_exists_shortExact_thickening_unit.AlgebraicGeometry.Scheme in
with_weak_namespace Scheme_IdealSheafData_IsInvertible_exists_shortExact_thickening_unit
with_weak_namespace AlgebraicGeometry.Scheme
open scoped IdealSheafData in
with_weak_namespace IdealSheafData
private theorem _root_.AlgebraicGeometry.Scheme.IdealSheafData.epi_uMod
    {X : Scheme.{u}} (I : X.IdealSheafData) : Epi I.uMod := by
  refine (AlgebraicGeometry.Scheme.Modules.Hom.epi_iff_locallySurjective _).mpr ?_
  intro U s x hxU
  obtain ⟨V, hV, hxV, hVU⟩ := (Opens.isBasis_iff_nbhd.mp (Scheme.isBasis_affineOpens X)) hxU
  refine ⟨V, hVU, hxV, ?_⟩
  have hsurj :=
    (isClosedImmersion_iff_isAffineHom.mp (inferInstance : IsClosedImmersion I.subschemeι)).2 V hV
  obtain ⟨a, ha⟩ := hsurj
    ((Scheme.Modules.presheaf ((SheafOfModules.pushforward I.subschemeι.toRingCatSheafHom).obj
      (SheafOfModules.unit I.subscheme.ringCatSheaf))).map (homOfLE hVU).op s)
  exact ⟨a, ha⟩

end AlgebraicGeometry.Scheme.IdealSheafData
namespace AlgebraicGeometry.Scheme.IdealSheafData
with_weak_namespace _root_.AlgebraicCurves.Geometry.Sheaves.Proofs
open scoped Scheme_IdealSheafData_IsInvertible_exists_shortExact_thickening_unit.AlgebraicGeometry
  Scheme_IdealSheafData_IsInvertible_exists_shortExact_thickening_unit.AlgebraicGeometry.Scheme in
with_weak_namespace Scheme_IdealSheafData_IsInvertible_exists_shortExact_thickening_unit
with_weak_namespace AlgebraicGeometry.Scheme
open scoped IdealSheafData in
with_weak_namespace IdealSheafData
private noncomputable def _root_.AlgebraicGeometry.Scheme.IdealSheafData.unitSeq
    {X : Scheme.{u}} (I : X.IdealSheafData) :
    ShortComplex X.Modules :=
  ShortComplex.mk I.moduleι I.uMod I.moduleι_comp_uMod

end AlgebraicGeometry.Scheme.IdealSheafData
namespace AlgebraicGeometry.Scheme.IdealSheafData
with_weak_namespace _root_.AlgebraicCurves.Geometry.Sheaves.Proofs
open scoped Scheme_IdealSheafData_IsInvertible_exists_shortExact_thickening_unit.AlgebraicGeometry
  Scheme_IdealSheafData_IsInvertible_exists_shortExact_thickening_unit.AlgebraicGeometry.Scheme in
with_weak_namespace Scheme_IdealSheafData_IsInvertible_exists_shortExact_thickening_unit
with_weak_namespace AlgebraicGeometry.Scheme
open scoped IdealSheafData in
with_weak_namespace IdealSheafData
private theorem _root_.AlgebraicGeometry.Scheme.IdealSheafData.shortExact_unitSeq
    {X : Scheme.{u}} (I : X.IdealSheafData) : I.unitSeq.ShortExact := by
  have := I.epi_uMod
  have := I.mono_moduleι'
  refine ShortComplex.ShortExact.mk' ?_
    (by change Mono I.moduleι; infer_instance) (by change Epi I.uMod; infer_instance)
  exact ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel I.subschemeι.unitToPushforwardUnit)

end AlgebraicGeometry.Scheme.IdealSheafData
namespace AlgebraicGeometry.Scheme.IdealSheafData
with_weak_namespace _root_.AlgebraicCurves.Geometry.Sheaves.Proofs
open scoped Scheme_IdealSheafData_IsInvertible_exists_shortExact_thickening_unit.AlgebraicGeometry
  Scheme_IdealSheafData_IsInvertible_exists_shortExact_thickening_unit.AlgebraicGeometry.Scheme in
with_weak_namespace Scheme_IdealSheafData_IsInvertible_exists_shortExact_thickening_unit
with_weak_namespace AlgebraicGeometry.Scheme
open scoped IdealSheafData in
with_weak_namespace IdealSheafData
private noncomputable def _root_.AlgebraicGeometry.Scheme.IdealSheafData.tensorSeq
    {X : Scheme.{u}} (I : X.IdealSheafData)
    (F : X.Modules) : ShortComplex X.Modules :=
  ShortComplex.mk (F ◁ I.moduleι) (F ◁ I.uMod)
    (by
      change (tensorLeft F).map _ ≫ (tensorLeft F).map _ = 0
      rw [← Functor.map_comp, I.moduleι_comp_uMod]
      exact Functor.map_zero _ _ _)

end AlgebraicGeometry.Scheme.IdealSheafData
namespace AlgebraicGeometry.Scheme.IdealSheafData
with_weak_namespace _root_.AlgebraicCurves.Geometry.Sheaves.Proofs
open scoped Scheme_IdealSheafData_IsInvertible_exists_shortExact_thickening_unit.AlgebraicGeometry
  Scheme_IdealSheafData_IsInvertible_exists_shortExact_thickening_unit.AlgebraicGeometry.Scheme in
with_weak_namespace Scheme_IdealSheafData_IsInvertible_exists_shortExact_thickening_unit
with_weak_namespace AlgebraicGeometry.Scheme
open scoped IdealSheafData in
with_weak_namespace IdealSheafData
private theorem _root_.AlgebraicGeometry.Scheme.IdealSheafData.shortExact_tensorSeq
    {X : Scheme.{u}} (I : X.IdealSheafData)
    {n : ℕ} (F : X.Modules) (hF : Scheme.Modules.IsLocallyFreeOfRank n F) :
    (I.tensorSeq F).ShortExact := by
  have := I.mono_whiskerLeft_moduleIota F hF
  have := I.epi_uMod
  let G : X.Modules ⥤ X.Modules := tensorLeft F
  have hcok : IsColimit (CokernelCofork.ofπ (I.tensorSeq F).g (I.tensorSeq F).zero) := by
    have h0 := I.shortExact_unitSeq.gIsCokernel
    have h1 := CokernelCofork.mapIsColimit _ h0 G
    refine IsColimit.ofIsoColimit h1 (Cofork.ext (Iso.refl _) ?_)
    erw [Category.comp_id]
    rfl
  refine ShortComplex.ShortExact.mk' (ShortComplex.exact_of_g_is_cokernel _ hcok) ?_ ?_
  · change Mono (F ◁ I.moduleι); infer_instance
  · change Epi ((tensorLeft F).map I.uMod); infer_instance

end AlgebraicGeometry.Scheme.IdealSheafData
namespace Ws31IdealSES

variable {Z X : Scheme.{u}}

theorem isIso_projectionMorphism (i : Z ⟶ X) {m : ℕ} (G : X.Modules)
    (hG : Scheme.Modules.IsLocallyFreeOfRank m G) :
    IsIso (Scheme.Modules.projectionMorphism i G) := by
  apply Scheme.Modules.Hom.isIso_of_forall_exists_isIso_pullback_map
  intro x
  obtain ⟨U, hx, ⟨e⟩⟩ := hG.exists_trivialization x
  refine ⟨U, hx, ?_⟩
  rw [Scheme.Modules.isIso_pullback_map_projectionMorphism_iff]
  exact Scheme.Modules.isIso_projectionMorphism_of_iso_free (i ∣_ U) _ e

/-- View a section of the unit module as a regular function. -/
abbrev toFun (U : X.Opens) (s : Γ(𝟙_ X.Modules, U)) : Γ(X, U) := s

lemma eq_smul_unitSection (U : X.Opens) (s : Γ(𝟙_ X.Modules, U)) :
    s = toFun U s • Scheme.Modules.unitSection U :=
  (Scheme.Modules.smul_unitSection (toFun U s)).symm

theorem pullbackTensorUnitObjIso_hom_app_pullbackLocalSection (f : Z ⟶ X) (U : X.Opens)
    (s : Γ(𝟙_ X.Modules, U)) :
    (Scheme.Modules.pullbackTensorUnitObjIso f).hom.app (f ⁻¹ᵁ U)
        (Scheme.Modules.pullbackLocalSection f s) =
      f.app U (toFun U s) := by
  conv_lhs => rw [eq_smul_unitSection U s]
  rw [Scheme.Modules.pullbackLocalSection_smul, Scheme.Modules.Hom.app_smul,
    Scheme.Modules.pullbackTensorUnitObjIso_hom_app_pullbackLocalSection_unitSection]
  exact Scheme.Modules.smul_unitSection _

section

/-- The native pushforward is right adjoint to the canonical module pullback. -/
local instance pushforward_isRightAdjoint (f : Z ⟶ X) :
    (SheafOfModules.pushforward.{u} f.toRingCatSheafHom).IsRightAdjoint :=
  (Scheme.Modules.pullbackPushforwardAdjunction f).isRightAdjoint

theorem η_pullback_eq (f : Z ⟶ X) :
    η (Scheme.Modules.pullback f) = SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom := by
  apply Scheme.Modules.pullback_hom_ext
  intro U s
  change (Scheme.Modules.pullbackTensorUnitObjIso f).hom.app (f ⁻¹ᵁ U)
    (Scheme.Modules.pullbackLocalSection f s) = _
  rw [pullbackTensorUnitObjIso_hom_app_pullbackLocalSection]
  change _ = Scheme.Modules.Hom.app
    (((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).symm
      f.unitToPushforwardUnit) (f ⁻¹ᵁ U) (Scheme.Modules.pullbackLocalSection f s)
  exact (Scheme.Modules.homEquiv_symm_app_pullbackLocalSection
    (X := Z) (Y := X) (φ := f) (L := (𝟙_ X.Modules : X.Modules))
    (N := (𝟙_ Z.Modules : Z.Modules)) (U := U) f.unitToPushforwardUnit s).symm

end

/-- The canonical map from the unit module to its pushforward along `i`. -/
abbrev uX (i : Z ⟶ X) :
    ((𝟙_ X.Modules : X.Modules) ⟶
      ((Scheme.Modules.pushforward i).obj (𝟙_ Z.Modules) : X.Modules)) :=
  i.unitToPushforwardUnit

theorem unit_app_eq (i : Z ⟶ X) (G : X.Modules) :
    (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app G =
      (λ_ G).inv ≫ (uX i ▷ G) ≫ Scheme.Modules.projectionMorphism i G := by
  rw [Scheme.Modules.projectionMorphism_def, ← Adjunction.homEquiv_naturality_left,
    ← Adjunction.homEquiv_naturality_left, ← Adjunction.homEquiv_id]
  congr 1
  rw [Scheme.Modules.projectionMorphismMate_def]
  rw [Functor.Monoidal.μIso_inv, ← δ_natural_left_assoc, ← comp_whiskerRight_assoc]
  have hc : (Scheme.Modules.pullback i).map (uX i) ≫
      (Scheme.Modules.pullbackPushforwardAdjunction i).counit.app (𝟙_ Z.Modules) =
        η (Scheme.Modules.pullback i) := by
    rw [η_pullback_eq]
    rfl
  rw [hc, left_unitality_hom, ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id]

theorem rightUnitor_hom_comp_leftUnitor_inv (G : X.Modules) :
    (ρ_ G).hom ≫ (λ_ G).inv = (β_ G (𝟙_ X.Modules)).hom := by
  rw [← braiding_leftUnitor, Category.assoc, Iso.hom_inv_id, Category.comp_id]

theorem whiskerLeft_moduleι_comp_unit (I : X.IdealSheafData) (G : X.Modules) :
    ((G ◁ I.moduleι) ≫ (ρ_ G).hom) ≫
      (Scheme.Modules.pullbackPushforwardAdjunction I.subschemeι).unit.app G = 0 := by
  rw [unit_app_eq, Category.assoc, ← Category.assoc (ρ_ G).hom, rightUnitor_hom_comp_leftUnitor_inv,
    ← Category.assoc (β_ _ _).hom, ← BraidedCategory.braiding_naturality_right, Category.assoc,
    ← Category.assoc (G ◁ I.moduleι),
    ← MonoidalCategory.whiskerLeft_comp]
  change (tensorLeft G).map (I.moduleι ≫ I.uMod) ≫ _ = 0
  rw [I.moduleι_comp_uMod, Functor.map_zero, zero_comp]

theorem exists_shortExact_unit (I : X.IdealSheafData) {m : ℕ} (G : X.Modules)
    (hG : Scheme.Modules.IsLocallyFreeOfRank m G) :
    ∃ w : ((G ◁ I.moduleι) ≫ (ρ_ G).hom) ≫
        (Scheme.Modules.pullbackPushforwardAdjunction I.subschemeι).unit.app G = 0,
      (ShortComplex.mk ((G ◁ I.moduleι) ≫ (ρ_ G).hom)
        ((Scheme.Modules.pullbackPushforwardAdjunction I.subschemeι).unit.app G) w).ShortExact := by
  have := isIso_projectionMorphism I.subschemeι G hG
  refine ⟨whiskerLeft_moduleι_comp_unit I G, ?_⟩
  refine ShortComplex.shortExact_of_iso ?_ (I.shortExact_tensorSeq G hG)
  refine ShortComplex.isoMk (Iso.refl _) (ρ_ G)
    ((β_ G _) ≪≫ asIso (Scheme.Modules.projectionMorphism I.subschemeι G)) ?_ ?_
  · change 𝟙 _ ≫ ((G ◁ I.moduleι) ≫ (ρ_ G).hom) = (G ◁ I.moduleι) ≫ (ρ_ G).hom
    rw [Category.id_comp]
  · change (ρ_ G).hom ≫ (Scheme.Modules.pullbackPushforwardAdjunction I.subschemeι).unit.app G =
      (G ◁ I.uMod) ≫ (β_ G _).hom ≫ Scheme.Modules.projectionMorphism I.subschemeι G
    rw [unit_app_eq, ← Category.assoc (ρ_ G).hom, rightUnitor_hom_comp_leftUnitor_inv,
      ← Category.assoc (β_ _ _).hom, ← BraidedCategory.braiding_naturality_right, Category.assoc]
    rfl

theorem epi_unit_app (I : X.IdealSheafData) {m : ℕ} (G : X.Modules)
    (hG : Scheme.Modules.IsLocallyFreeOfRank m G) :
    Epi ((Scheme.Modules.pullbackPushforwardAdjunction I.subschemeι).unit.app G) := by
  obtain ⟨w, h⟩ := exists_shortExact_unit I G hG
  exact h.epi_g

end Ws31IdealSES

end

noncomputable section

namespace Ws31X2

open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}}

theorem mult {I J : X.IdealSheafData} (hI : I.IsInvertible) (hJ : J.IsInvertible) :
    ∃ μ : I.module ⊗ J.module ≅ (I * J).module,
      μ.hom ≫ (I * J).moduleι = (I.moduleι ⊗ₘ J.moduleι) ≫ (λ_ (𝟙_ X.Modules)).hom :=
  Scheme.IdealSheafData.IsInvertible.exists_tensor_iso_mul_module hI hJ

/-- The module isomorphism induced by equality of ideal sheaves. -/
def moduleCongr {I J : X.IdealSheafData} (h : I = J) : I.module ≅ J.module := eqToIso (by rw [h])

lemma moduleCongr_hom_moduleι {I J : X.IdealSheafData} (h : I = J) :
    (moduleCongr h).hom ≫ J.moduleι = I.moduleι := by
  subst h
  change 𝟙 I.module ≫ I.moduleι = I.moduleι
  exact Category.id_comp I.moduleι

/-- Tensor the ideal inclusion with `G` and apply the right unitor. -/
abbrev fI (I : X.IdealSheafData) (G : X.Modules) : G ⊗ I.module ⟶ G :=
  (G ◁ I.moduleι) ≫ (ρ_ G).hom

theorem shortExact_cokernelSequence {C : Type*} [Category C] [Abelian C] {A B D : C}
    (f : A ⟶ B) (g : B ⟶ D)
    [Mono g] :
    ((kernelCokernelCompSequence f g).sc
      (kernelCokernelCompSequence_exact f g).toIsComplex 3).ShortExact := by
  have hE := kernelCokernelCompSequence_exact f g
  refine ShortComplex.ShortExact.mk' (hE.exact 3) ?_ ?_
  · have hδ : (kernelCokernelCompSequence f g).map' 2 3 = 0 := by
      apply (isZero_kernel_of_mono g).eq_of_src
    exact (hE.exact 2).mono_g hδ
  · change Epi ((kernelCokernelCompSequence f g).map' 4 5)
    infer_instance

/-- The short complex of cokernels of a composable pair of morphisms. -/
abbrev cokernelSequence {C : Type*} [Category C] [Abelian C] {A B D : C} (f : A ⟶ B) (g : B ⟶ D) :
    ShortComplex C :=
  ShortComplex.mk (cokernel.map f (f ≫ g) (𝟙 _) g (by simp))
    (cokernel.map (f ≫ g) g f (𝟙 _) (by simp))
    (by ext; simp)

theorem shortExact_cokernelSequence' {C : Type*} [Category C] [Abelian C] {A B D : C}
    (f : A ⟶ B) (g : B ⟶ D)
    [Mono g] : (cokernelSequence f g).ShortExact :=
  shortExact_cokernelSequence f g

theorem tensor_moduleι_comp_leftUnitor (I J : X.IdealSheafData) :
    (I.moduleι ⊗ₘ J.moduleι) ≫ (λ_ (𝟙_ X.Modules)).hom =
      I.module ◁ J.moduleι ≫ (ρ_ I.module).hom ≫ I.moduleι := by
  rw [MonoidalCategory.unitors_equal, MonoidalCategory.tensorHom_def', Category.assoc,
    MonoidalCategory.rightUnitor_naturality]

theorem comp_fI_eq {I J K : X.IdealSheafData} (G : X.Modules) (μ : I.module ⊗ J.module ⟶ K.module)
    (hμ : μ ≫ K.moduleι = (I.moduleι ⊗ₘ J.moduleι) ≫ (λ_ (𝟙_ X.Modules)).hom) :
    ((α_ G I.module J.module).hom ≫ (G ◁ μ)) ≫ fI K G = fI J (G ⊗ I.module) ≫ fI I G := by
  simp only [fI, Category.assoc]
  rw [← MonoidalCategory.whiskerLeft_comp_assoc, hμ, tensor_moduleι_comp_leftUnitor,
    MonoidalCategory.rightUnitor_tensor_hom]
  simp only [Category.assoc, MonoidalCategory.associator_naturality_right_assoc,
    MonoidalCategory.whiskerLeft_comp]

theorem main {𝓘 : X.IdealSheafData} (h𝓘 : 𝓘.IsInvertible) (G : X.Modules)
    (hG : IsInvertible G) (j : ℕ) :
    ∃ S : ShortComplex X.Modules, S.ShortExact ∧
      Nonempty (S.X₁ ≅ (Scheme.Modules.pushforward ((𝓘 ^ j).subschemeι)).obj
        ((Scheme.Modules.pullback ((𝓘 ^ j).subschemeι)).obj (G ⊗ 𝓘.module))) ∧
      ∃ (e₂ : S.X₂ ≅ (Scheme.Modules.pushforward ((𝓘 ^ (j + 1)).subschemeι)).obj
          ((Scheme.Modules.pullback ((𝓘 ^ (j + 1)).subschemeι)).obj G))
        (e₃ : S.X₃ ≅ (Scheme.Modules.pushforward 𝓘.subschemeι).obj
          ((Scheme.Modules.pullback 𝓘.subschemeι).obj G)),
        (Scheme.Modules.pullbackPushforwardAdjunction ((𝓘 ^ (j + 1)).subschemeι)).unit.app G ≫
          e₂.inv ≫ S.g ≫ e₃.hom
          = (Scheme.Modules.pullbackPushforwardAdjunction 𝓘.subschemeι).unit.app G := by
  have hG1 : IsLocallyFreeOfRank 1 G := (isLocallyFreeOfRank_one_iff_isInvertible G).mpr hG
  have hG' : IsInvertible (G ⊗ 𝓘.module) := hG.tensor h𝓘.isInvertible_module
  have hG'1 : IsLocallyFreeOfRank 1 (G ⊗ 𝓘.module) :=
    (isLocallyFreeOfRank_one_iff_isInvertible _).mpr hG'
  obtain ⟨w₁, h₁⟩ := Ws31IdealSES.exists_shortExact_unit (𝓘 ^ j) (G ⊗ 𝓘.module) hG'1
  obtain ⟨w₂, h₂⟩ := Ws31IdealSES.exists_shortExact_unit (𝓘 ^ (j + 1)) G hG1
  obtain ⟨w₃, h₃⟩ := Ws31IdealSES.exists_shortExact_unit 𝓘 G hG1
  have : Mono (fI 𝓘 G) := h₃.mono_f
  let f := fI (𝓘 ^ j) (G ⊗ 𝓘.module)
  let g := fI 𝓘 G
  refine ⟨cokernelSequence f g, shortExact_cokernelSequence' f g, ?_, ?_⟩
  · exact ⟨(h₁.gIsCokernel.coconePointUniqueUpToIso (cokernelIsCokernel f)).symm⟩
  · obtain ⟨μ, hμ⟩ := mult h𝓘 (h𝓘.pow j)
    let μ' : 𝓘.module ⊗ (𝓘 ^ j).module ≅ (𝓘 ^ (j + 1)).module :=
      μ ≪≫ moduleCongr (pow_succ' 𝓘 j).symm
    let σ : (G ⊗ 𝓘.module) ⊗ (𝓘 ^ j).module ≅ G ⊗ (𝓘 ^ (j + 1)).module :=
      (α_ G 𝓘.module ((𝓘 ^ j).module)) ≪≫ whiskerLeftIso G μ'
    have hσ : σ.hom ≫ fI (𝓘 ^ (j + 1)) G = f ≫ g := by
      have hμ' : μ'.hom ≫ (𝓘 ^ (j + 1)).moduleι =
          (𝓘.moduleι ⊗ₘ (𝓘 ^ j).moduleι) ≫ (λ_ (𝟙_ X.Modules)).hom := by
        rw [Iso.trans_hom, Category.assoc, moduleCongr_hom_moduleι, hμ]
      have h := comp_fI_eq (I := 𝓘) (J := 𝓘 ^ j) (K := 𝓘 ^ (j + 1)) G μ'.hom hμ'
      rw [← MonoidalCategory.whiskerLeftIso_hom, ← Iso.trans_hom] at h
      exact h
    let e₂ : cokernel (f ≫ g) ≅ _ :=
      (cokernelIsoOfEq hσ.symm ≪≫ cokernelEpiComp σ.hom (fI (𝓘 ^ (j + 1)) G)) ≪≫
      (h₂.gIsCokernel.coconePointUniqueUpToIso (cokernelIsCokernel (fI (𝓘 ^ (j + 1)) G))).symm
    let e₃ : cokernel g ≅ _ := (h₃.gIsCokernel.coconePointUniqueUpToIso (cokernelIsCokernel g)).symm
    refine ⟨e₂, e₃, ?_⟩
    have h2 :
        (Scheme.Modules.pullbackPushforwardAdjunction ((𝓘 ^ (j + 1)).subschemeι)).unit.app G ≫
          e₂.inv
        = cokernel.π (f ≫ g) := by
      change (Scheme.Modules.pullbackPushforwardAdjunction ((𝓘 ^ (j + 1)).subschemeι)).unit.app G ≫
        ((h₂.gIsCokernel.coconePointUniqueUpToIso (cokernelIsCokernel (fI (𝓘 ^ (j + 1)) G))).hom ≫
          ((cokernelEpiComp σ.hom (fI (𝓘 ^ (j + 1)) G)).inv ≫ (cokernelIsoOfEq hσ.symm).inv)) = _
      have hA :
          (Scheme.Modules.pullbackPushforwardAdjunction ((𝓘 ^ (j + 1)).subschemeι)).unit.app G ≫
          (h₂.gIsCokernel.coconePointUniqueUpToIso (cokernelIsCokernel (fI (𝓘 ^ (j + 1)) G))).hom
          = cokernel.π (fI (𝓘 ^ (j + 1)) G) :=
        h₂.gIsCokernel.comp_coconePointUniqueUpToIso_hom (cokernelIsCokernel (fI (𝓘 ^ (j + 1)) G))
          WalkingParallelPair.one
      rw [reassoc_of% hA, cokernelEpiComp_inv, cokernel.π_desc_assoc]
      exact π_comp_cokernelIsoOfEq_inv hσ.symm
    have h3 : cokernel.π g ≫ e₃.hom =
        (Scheme.Modules.pullbackPushforwardAdjunction 𝓘.subschemeι).unit.app G :=
      h₃.gIsCokernel.comp_coconePointUniqueUpToIso_inv
        (cokernelIsCokernel g) WalkingParallelPair.one
    rw [← Category.assoc, h2]
    change cokernel.π (f ≫ g) ≫ cokernel.map (f ≫ g) g f (𝟙 _) (by simp) ≫ e₃.hom = _
    rw [← Category.assoc, cokernel.π_desc]
    simpa using h3

end Ws31X2

end

theorem
  _root_.AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible.exists_shortExact_thickening_unit
    {X : Scheme.{u}} {𝓘 : X.IdealSheafData} (h𝓘 : 𝓘.IsInvertible)
    (G : X.Modules) (hG : Scheme.Modules.IsInvertible G) (j : ℕ) :
    ∃ S : ShortComplex X.Modules, S.ShortExact ∧
      Nonempty (S.X₁ ≅ (Scheme.Modules.pushforward ((𝓘 ^ j).subschemeι)).obj
        ((Scheme.Modules.pullback ((𝓘 ^ j).subschemeι)).obj (G ⊗ 𝓘.module))) ∧
      ∃ (e₂ : S.X₂ ≅ (Scheme.Modules.pushforward ((𝓘 ^ (j + 1)).subschemeι)).obj
          ((Scheme.Modules.pullback ((𝓘 ^ (j + 1)).subschemeι)).obj G))
        (e₃ : S.X₃ ≅ (Scheme.Modules.pushforward 𝓘.subschemeι).obj
          ((Scheme.Modules.pullback 𝓘.subschemeι).obj G)),
        (Scheme.Modules.pullbackPushforwardAdjunction ((𝓘 ^ (j + 1)).subschemeι)).unit.app G ≫
          e₂.inv ≫ S.g ≫ e₃.hom
          = (Scheme.Modules.pullbackPushforwardAdjunction 𝓘.subschemeι).unit.app G :=
  Ws31X2.main h𝓘 G hG j
end Scheme_IdealSheafData_IsInvertible_exists_shortExact_thickening_unit
end AlgebraicCurves.Geometry.Sheaves.Proofs
end ProofImplementation

open _root_.PresheafOfModules.PullbackMonoidal in
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
  SheafOfModules.isIso_ihomModelToIhom
attribute [-simp]
  PresheafOfModules.freeεIso_hom_app
  PresheafOfModules.freeμIso_hom_app
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add
  AlgebraicGeometry.Scheme.Modules.tensorPow_zero
  AlgebraicGeometry.Scheme.Modules.tensorPow_succ
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right
  AlgebraicGeometry.Scheme.Modules.map_unitSection
  AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply
  AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left
  PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom
  SheafOfModules.ihomSectionsEquivFamily_unit
  AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply
  SheafOfModules.ihomEval_unit_app
  AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right
  AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left
  AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply
  SheafOfModules.unit_ihomSectionsEquivFamily
  AlgebraicGeometry.Scheme.Modules.familyOfHom_app
  AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply
