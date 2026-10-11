/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_stage_sectionsOf_baseChange_equiv_of_locallyTrivial.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.SchemeTheory.Cohomology.Cech.TwoAffineOpenCover
import Nyll.AlgebraicCurves.Cohomology.Cech.TwoChartCechSectionsOf
import Nyll.AlgebraicCurves.Geometry.Picard.StageHom
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_exists_linearEquiv_sections_baseChange_of_locallyTrivial
import Mathlib.Util.WithWeakNamespace

/-!
Compatible scalar-extension equivalences of locally trivial module sections at an affine algebra
stage.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs
namespace Scheme_TwoAffineOpenCover_exists_stage_sectionsOf_baseChange_equiv_of_locallyTrivial
attribute [-simp] AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.Opposite
open _root_.AlgebraicGeometry
open _root_.TensorProduct
open _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover
open _root_.AlgebraicGeometry.RelPicard.LFP

noncomputable section

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace Modules
open _root_.AlgebraicGeometry.Scheme.Modules
namespace StageTransport
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry

open _root_.AlgebraicGeometry.Scheme.Modules

section Comp

variable {X Y Z : Scheme.{u}} (κ : X ⟶ Y) (f : Y ⟶ Z)

theorem pullbackComp_unit_unit (M : Z.Modules) (U : Z.Opens) (m : Γ(M, U)) :
    (((pullbackComp κ f).hom.app M).app ((κ ≫ f) ⁻¹ᵁ U))
      ((((pullbackPushforwardAdjunction κ).unit.app ((Scheme.Modules.pullback f).obj M)).app (f
        ⁻¹ᵁ U))
        ((((pullbackPushforwardAdjunction f).unit.app M).app U) m)) =
    (((pullbackPushforwardAdjunction (κ ≫ f)).unit.app M).app U) m := by
  have h := unit_conjugateEquiv ((pullbackPushforwardAdjunction f).comp
    (pullbackPushforwardAdjunction κ))
    (pullbackPushforwardAdjunction (κ ≫ f)) (pullbackComp κ f).inv M
  rw [conjugateEquiv_pullbackComp_inv, Adjunction.comp_unit_app] at h
  have h3 := congrArg (fun φ => Scheme.Modules.Hom.app φ U m) h
  change ((((pullbackPushforwardAdjunction κ).unit.app ((Scheme.Modules.pullback f).obj M)).app
    (f ⁻¹ᵁ U))
      ((((pullbackPushforwardAdjunction f).unit.app M).app U) m)) =
    (((pullbackComp κ f).inv.app M).app ((κ ≫ f) ⁻¹ᵁ U))
      ((((pullbackPushforwardAdjunction (κ ≫ f)).unit.app M).app U) m) at h3
  rw [h3]
  let W : X.Opens := (κ ≫ f) ⁻¹ᵁ U
  let b : Γ((Scheme.Modules.pullback (κ ≫ f)).obj M, W) :=
    (((pullbackPushforwardAdjunction (κ ≫ f)).unit.app M).app U) m
  have he : (pullbackComp κ f).inv.app M ≫ (pullbackComp κ f).hom.app M = 𝟙 _ :=
    Iso.inv_hom_id_app (pullbackComp κ f) M
  have happ : ((pullbackComp κ f).inv.app M).app W ≫
      ((pullbackComp κ f).hom.app M).app W = 𝟙 _ :=
    (Scheme.Modules.Hom.comp_app _ _).symm.trans
      ((congrArg (fun φ : (Scheme.Modules.pullback (κ ≫ f)).obj M ⟶
        (Scheme.Modules.pullback (κ ≫ f)).obj M => φ.app W) he).trans
        (Scheme.Modules.Hom.id_app _))
  exact (ConcreteCategory.comp_apply _ _ b).symm.trans
    (ConcreteCategory.congr_hom happ b)

end Comp

section Congr

variable {X Y : Scheme.{u}} {p q : X ⟶ Y} (e : p = q)

theorem pullbackCongr_unit (M : Y.Modules) (U : Y.Opens) (W : X.Opens) (hp : W ≤ p ⁻¹ᵁ U) (hq :
    W ≤ q ⁻¹ᵁ U)
    (m : Γ(M, U)) :
    ((Scheme.Modules.pullback q).obj M).presheaf.map (homOfLE hp).op
      ((((pullbackCongr e).hom.app M).app (p ⁻¹ᵁ U))
        ((((pullbackPushforwardAdjunction p).unit.app M).app U) m)) =
    ((Scheme.Modules.pullback q).obj M).presheaf.map (homOfLE hq).op
      ((((pullbackPushforwardAdjunction q).unit.app M).app U) m) := by
  subst e
  rfl

end Congr

section IsoUnit

variable {X Y : Scheme.{u}} (κ : X ⟶ Y) [IsIso κ]

theorem isIso_unit_app_of_isIso (N : Y.Modules) : IsIso ((pullbackPushforwardAdjunction
    κ).unit.app N) := by
  rw [← Adjunction.unit_leftAdjointUniq_hom_app (restrictAdjunction κ)
    (pullbackPushforwardAdjunction κ) N]
  have : IsIso ((restrictAdjunction κ).unit.app N) := by
    refine Hom.isIso_iff_isIso_app.mpr fun U => ?_
    rw [restrictAdjunction_unit_app_app]
    have hU : κ ''ᵁ κ ⁻¹ᵁ U = U := by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Hom.opensRange_of_isIso, top_inf_eq]
    have hiso : IsIso (N.presheaf.map (eqToHom hU).op) := inferInstance
    rw [show homOfLE (κ.image_preimage_le U) = eqToHom hU from Subsingleton.elim _ _]
    exact hiso
  have h2 : IsIso ((pushforward κ).map
      (((restrictAdjunction κ).leftAdjointUniq (pullbackPushforwardAdjunction κ)).hom.app N)) :=
    ((pushforward κ).mapIso (((restrictAdjunction κ).leftAdjointUniq
      (pullbackPushforwardAdjunction κ)).app N)).isIso_hom
  exact IsIso.comp_isIso' this h2

end IsoUnit

section Scalars

variable {X Y : Scheme.{u}} (κ : X ⟶ Y)

theorem pushforward_smul (P : X.Modules) (V : Y.Opens) (s : Γ(Y, V)) (y : Γ((pushforward κ).obj
    P, V)) :
    s • y = (show Γ(P, κ ⁻¹ᵁ V) from (κ.app V).hom s • (show Γ(P, κ ⁻¹ᵁ V) from y)) := rfl

theorem appLE_algebraMap_eq' {A : Type u} [CommRing A] (q₀ : Y ⟶ Spec (.of A)) (q' : X ⟶ Spec
    (.of A))
    (hκ : κ ≫ q₀ = q') (V : Y.Opens) (W : X.Opens) (h : W ≤ κ ⁻¹ᵁ V) (a : A) :
    (κ.appLE V W h).hom (((Scheme.ΓSpecIso (.of A)).inv ≫ q₀.appLE ⊤ V le_top).hom a) =
      ((Scheme.ΓSpecIso (.of A)).inv ≫ q'.appLE ⊤ W le_top).hom a := by
  subst hκ
  have hcomp : q₀.appLE ⊤ V le_top ≫ κ.appLE V W h =
      (κ ≫ q₀).appLE ⊤ W le_top :=
    Scheme.Hom.appLE_comp_appLE κ q₀ ⊤ V W le_top h
  have hfull : ((Scheme.ΓSpecIso (.of A)).inv ≫ q₀.appLE ⊤ V le_top) ≫
      κ.appLE V W h = (Scheme.ΓSpecIso (.of A)).inv ≫ (κ ≫ q₀).appLE ⊤ W le_top :=
    (Category.assoc _ _ _).trans
      (congrArg (fun ψ => (Scheme.ΓSpecIso (.of A)).inv ≫ ψ) hcomp)
  exact (CommRingCat.comp_apply
    ((Scheme.ΓSpecIso (.of A)).inv ≫ q₀.appLE ⊤ V le_top) (κ.appLE V W h) a).symm.trans
    (DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hfull) a)

end Scalars

end AlgebraicGeometry.Scheme.Modules.StageTransport

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace Modules
open _root_.AlgebraicGeometry.Scheme.Modules
namespace StageTransport
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry

theorem unit_app_map {X' X₀ : Scheme.{u}} (σ : X' ⟶ X₀) (M : X₀.Modules) {U V : X₀.Opens} (h : V
    ≤ U)
    (h' : σ ⁻¹ᵁ V ≤ σ ⁻¹ᵁ U) (m : Γ(M, U)) :
    (((Scheme.Modules.pullbackPushforwardAdjunction σ).unit.app M).app V).hom (M.presheaf.map
      (homOfLE h).op m) =
      ((Scheme.Modules.pullback σ).obj M).presheaf.map (homOfLE h').op
        ((((Scheme.Modules.pullbackPushforwardAdjunction σ).unit.app M).app U).hom m) := by
  have hn := ((Scheme.Modules.pullbackPushforwardAdjunction σ).unit.app
    M).mapPresheaf.naturality (homOfLE h).op
  have hx := ConcreteCategory.congr_hom hn m
  refine hx.trans ?_
  have : ((TopologicalSpace.Opens.map σ.base).map (homOfLE h)) = homOfLE h' := Subsingleton.elim _ _
  change (((Scheme.Modules.pullback σ).obj M).presheaf.map
    ((TopologicalSpace.Opens.map σ.base).map (homOfLE h)).op) _ = _
  rw [this]
  rfl

theorem tmul_eq_smul_one_tmul {R A N : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup N] [Module R N]
    (a : A) (n : N) : a ⊗ₜ[R] n = a • ((1 : A) ⊗ₜ[R] n) := by
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

end AlgebraicGeometry.Scheme.Modules.StageTransport

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace TwoAffineOpenCover
open _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover
namespace StageBC
open _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry

open _root_.AlgebraicGeometry.Scheme.Modules

theorem exists_linearEquiv_transport
    {A' : Type u} [CommRing A'] {X' Z X₀ : Scheme.{u}} (κ : X' ⟶ Z) [IsIso κ] (fZ : Z ⟶ X₀) (σ :
      X' ⟶ X₀)
    (hκf : κ ≫ fZ = σ) (sZ : Z ⟶ Spec (.of A')) (snd' : X' ⟶ Spec (.of A')) (hκs : κ ≫ sZ = snd')
    (M : X₀.Modules) (U : X₀.Opens) (U' : X'.Opens) (hU' : U' = σ ⁻¹ᵁ U) :
    letI := moduleSectionsOfHom sZ ((Scheme.Modules.pullback fZ).obj M) (fZ ⁻¹ᵁ U)
    letI := moduleSectionsOfHom snd' ((Scheme.Modules.pullback σ).obj M) U'
    ∃ T : Γ((Scheme.Modules.pullback fZ).obj M, fZ ⁻¹ᵁ U) ≃ₗ[A'] Γ((Scheme.Modules.pullback
      σ).obj M, U'),
      ∀ m : Γ(M, U), T ((((Scheme.Modules.pullbackPushforwardAdjunction fZ).unit.app M).app
        U).hom m) =
        ((Scheme.Modules.pullback σ).obj M).presheaf.map (homOfLE hU'.le).op
          ((((Scheme.Modules.pullbackPushforwardAdjunction σ).unit.app M).app U).hom m) := by
  let := moduleSectionsOfHom sZ ((Scheme.Modules.pullback fZ).obj M) (fZ ⁻¹ᵁ U)
  let := moduleSectionsOfHom snd' ((Scheme.Modules.pullback σ).obj M) U'
  let τ : (Scheme.Modules.pullback fZ).obj M ⟶
      (Scheme.Modules.pushforward κ).obj ((Scheme.Modules.pullback σ).obj M) :=
    (Scheme.Modules.pullbackPushforwardAdjunction κ).unit.app ((Scheme.Modules.pullback fZ).obj M) ≫
      (Scheme.Modules.pushforward κ).map
        ((Scheme.Modules.pullbackComp κ fZ).hom.app M ≫ (Scheme.Modules.pullbackCongr
          hκf).hom.app M)
  have hτ : IsIso τ := IsIso.comp_isIso'
    (AlgebraicGeometry.Scheme.Modules.StageTransport.isIso_unit_app_of_isIso κ _)
    (((Scheme.Modules.pushforward κ).mapIso
      ((Scheme.Modules.pullbackComp κ fZ).app M ≪≫ (Scheme.Modules.pullbackCongr hκf).app
        M)).isIso_hom)
  have hW' : U' = κ ⁻¹ᵁ (fZ ⁻¹ᵁ U) := by rw [hU', ← Scheme.Hom.comp_preimage, hκf]
  let T₀ : Γ((Scheme.Modules.pullback fZ).obj M, fZ ⁻¹ᵁ U) →+ Γ((Scheme.Modules.pullback σ).obj
    M, U') :=
    (((Scheme.Modules.pullback σ).obj M).presheaf.map (homOfLE hW'.le).op).hom.comp (τ.app (fZ
      ⁻¹ᵁ U)).hom
  have hT₀ : Function.Bijective T₀ := by
    change Function.Bijective
      ((((Scheme.Modules.pullback σ).obj M).presheaf.map (homOfLE hW'.le).op).hom ∘ (τ.app (fZ
        ⁻¹ᵁ U)).hom)
    refine Function.Bijective.comp ?_ ?_
    · have hiso : IsIso (((Scheme.Modules.pullback σ).obj M).presheaf.map (eqToHom hW').op) :=
      inferInstance
      rw [show homOfLE hW'.le = eqToHom hW' from Subsingleton.elim _ _]
      exact ((CategoryTheory.forget AddCommGrpCat).mapIso
        (asIso (((Scheme.Modules.pullback σ).obj M).presheaf.map (eqToHom
          hW').op))).toEquiv.bijective
    · have := hτ
      exact ((CategoryTheory.forget AddCommGrpCat).mapIso (asIso (τ.app (fZ ⁻¹ᵁ
        U)))).toEquiv.bijective
  have hT₀_smul : ∀ (a : A') (n : Γ((Scheme.Modules.pullback fZ).obj M, fZ ⁻¹ᵁ U)), T₀ (a • n) =
    a • T₀ n := by
    intro a n
    change ((Scheme.Modules.pullback σ).obj M).presheaf.map (homOfLE hW'.le).op
        ((τ.app (fZ ⁻¹ᵁ U)).hom ((((Scheme.ΓSpecIso (.of A')).inv ≫ sZ.appLE ⊤ (fZ ⁻¹ᵁ U)
          le_top).hom a) • n)) =
      (((Scheme.ΓSpecIso (.of A')).inv ≫ snd'.appLE ⊤ U' le_top).hom a) •
        ((Scheme.Modules.pullback σ).obj M).presheaf.map (homOfLE hW'.le).op ((τ.app (fZ ⁻¹ᵁ
          U)).hom n)
    rw [← AlgebraicGeometry.Scheme.Modules.StageTransport.appLE_algebraMap_eq'
      κ sZ snd' hκs (fZ ⁻¹ᵁ U) U' hW'.le a]
    erw [Scheme.Modules.Hom.app_smul]
    rw [AlgebraicGeometry.Scheme.Modules.StageTransport.pushforward_smul,
      Scheme.Modules.map_smul]
    rfl
  let T : Γ((Scheme.Modules.pullback fZ).obj M, fZ ⁻¹ᵁ U) ≃ₗ[A'] Γ((Scheme.Modules.pullback
    σ).obj M, U') :=
    LinearEquiv.ofBijective
      { toFun := T₀, map_add' := T₀.map_add, map_smul' := hT₀_smul } hT₀
  refine ⟨T, fun m => ?_⟩
  change ((Scheme.Modules.pullback σ).obj M).presheaf.map (homOfLE hW'.le).op
    ((((Scheme.Modules.pullbackComp κ fZ).hom.app M ≫ (Scheme.Modules.pullbackCongr hκf).hom.app
      M).app
      (κ ⁻¹ᵁ (fZ ⁻¹ᵁ U)))
      ((((Scheme.Modules.pullbackPushforwardAdjunction κ).unit.app ((Scheme.Modules.pullback
        fZ).obj M)).app
        (fZ ⁻¹ᵁ U)) ((((Scheme.Modules.pullbackPushforwardAdjunction fZ).unit.app M).app U) m))) = _
  let W : X'.Opens := κ ⁻¹ᵁ (fZ ⁻¹ᵁ U)
  let n : Γ((Scheme.Modules.pullback κ).obj ((Scheme.Modules.pullback fZ).obj M), W) :=
    ((Scheme.Modules.pullbackPushforwardAdjunction κ).unit.app ((Scheme.Modules.pullback fZ).obj
      M)).app
      (fZ ⁻¹ᵁ U) (((Scheme.Modules.pullbackPushforwardAdjunction fZ).unit.app M).app U m)
  rw [Scheme.Modules.Hom.comp_app]
  exact (congrArg (fun x : Γ((Scheme.Modules.pullback σ).obj M, W) =>
    ((Scheme.Modules.pullback σ).obj M).presheaf.map (homOfLE hW'.le).op x)
    (ConcreteCategory.comp_apply _ _ n)).trans
    ((congrArg (fun x : Γ((Scheme.Modules.pullback (κ ≫ fZ)).obj M, W) =>
      ((Scheme.Modules.pullback σ).obj M).presheaf.map (homOfLE hW'.le).op
        (((Scheme.Modules.pullbackCongr hκf).hom.app M).app W x))
      (AlgebraicGeometry.Scheme.Modules.StageTransport.pullbackComp_unit_unit κ fZ M U m)).trans
      (AlgebraicGeometry.Scheme.Modules.StageTransport.pullbackCongr_unit
        hκf M U U' hW'.le hU'.le m))


theorem isIso_lift_stage
    {R A₀ A' : Type u} [CommRing R] [CommRing A₀] [CommRing A'] [Algebra R A₀] [Algebra R A']
      [Algebra A₀ A']
    [IsScalarTower R A₀ A'] {X : Scheme.{u}} (c : X ⟶ Spec (.of R))
    (σ : Limits.pullback c (specMap R A') ⟶ Limits.pullback c (specMap R A₀))
    (hfst : σ ≫ Limits.pullback.fst c (specMap R A₀) = Limits.pullback.fst c (specMap R A'))
    (hsnd : σ ≫ Limits.pullback.snd c (specMap R A₀) = Limits.pullback.snd c (specMap R A') ≫
      specMap A₀ A') :
    IsIso (Limits.pullback.lift σ (Limits.pullback.snd c (specMap R A')) hsnd) := by
  have htower : specMap A₀ A' ≫ specMap R A₀ = specMap R A' := by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq R A₀ A']
  have w : (Limits.pullback.fst (Limits.pullback.snd c (specMap R A₀)) (specMap A₀ A') ≫
      Limits.pullback.fst c (specMap R A₀)) ≫ c =
      Limits.pullback.snd (Limits.pullback.snd c (specMap R A₀)) (specMap A₀ A') ≫ specMap R A'
        := by
    rw [Category.assoc, Limits.pullback.condition, Limits.pullback.condition_assoc, htower]
  refine ⟨⟨Limits.pullback.lift _ _ w, ?_, ?_⟩⟩
  · apply Limits.pullback.hom_ext
    · rw [Category.assoc, Limits.pullback.lift_fst, Limits.pullback.lift_fst_assoc, hfst,
      Category.id_comp]
    · rw [Category.assoc, Limits.pullback.lift_snd, Limits.pullback.lift_snd, Category.id_comp]
  · apply Limits.pullback.hom_ext
    · rw [Category.assoc, Limits.pullback.lift_fst, Category.id_comp]
      apply Limits.pullback.hom_ext
      · rw [Category.assoc, hfst, Limits.pullback.lift_fst]
      · rw [Category.assoc, hsnd, Limits.pullback.lift_snd_assoc, Limits.pullback.condition]
    · rw [Category.assoc, Limits.pullback.lift_snd, Limits.pullback.lift_snd, Category.id_comp]

theorem exists_linearEquiv_sections_stage
    {R A₀ A' : Type u} [CommRing R] [CommRing A₀] [CommRing A'] [Algebra R A₀] [Algebra R A']
      [Algebra A₀ A']
    [IsScalarTower R A₀ A'] {X : Scheme.{u}} (c : X ⟶ Spec (.of R))
    (σ : Limits.pullback c (specMap R A') ⟶ Limits.pullback c (specMap R A₀))
    (hfst : σ ≫ Limits.pullback.fst c (specMap R A₀) = Limits.pullback.fst c (specMap R A'))
    (hsnd : σ ≫ Limits.pullback.snd c (specMap R A₀) = Limits.pullback.snd c (specMap R A') ≫
      specMap A₀ A')
    (M : (Limits.pullback c (specMap R A₀)).Modules)
    (htriv : ∀ x, ∃ (V : (Limits.pullback c (specMap R A₀)).Opens), x ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj M ≅ SheafOfModules.unit V.toScheme.ringCatSheaf))
    (U : (Limits.pullback c (specMap R A₀)).Opens) (hU : IsAffineOpen U)
    (U' : (Limits.pullback c (specMap R A')).Opens) (hU' : U' = σ ⁻¹ᵁ U) :
    letI := moduleSectionsOfHom (Limits.pullback.snd c (specMap R A₀)) M U
    letI := moduleSectionsOfHom (Limits.pullback.snd c (specMap R A')) ((Scheme.Modules.pullback
      σ).obj M) U'
    ∃ e : A' ⊗[A₀] Γ(M, U) ≃ₗ[A'] Γ((Scheme.Modules.pullback σ).obj M, U'),
      ∀ m : Γ(M, U), e ((1 : A') ⊗ₜ[A₀] m) =
        ((Scheme.Modules.pullback σ).obj M).presheaf.map (homOfLE hU'.le).op
          ((((Scheme.Modules.pullbackPushforwardAdjunction σ).unit.app M).app U).hom m) := by
  let := moduleSectionsOfHom (Limits.pullback.snd c (specMap R A₀)) M U
  let := moduleSectionsOfHom (Limits.pullback.snd c (specMap R A')) ((Scheme.Modules.pullback
    σ).obj M) U'
  have := isIso_lift_stage c σ hfst hsnd
  obtain ⟨eZ, heZ⟩ := Scheme.Modules.exists_linearEquiv_sections_baseChange_of_locallyTrivial
    (Limits.pullback.snd c (specMap R A₀)) M htriv U hU A'
  obtain ⟨T, hT⟩ := exists_linearEquiv_transport (Limits.pullback.lift σ (Limits.pullback.snd c
    (specMap R A')) hsnd)
    (Limits.pullback.fst (Limits.pullback.snd c (specMap R A₀)) (specMap A₀ A')) σ
      (Limits.pullback.lift_fst _ _ _)
    (Limits.pullback.snd (Limits.pullback.snd c (specMap R A₀)) (specMap A₀ A'))
      (Limits.pullback.snd c (specMap R A'))
    (Limits.pullback.lift_snd _ _ _) M U U' hU'
  exact ⟨eZ.trans T, fun m => by rw [LinearEquiv.trans_apply, heZ, hT]⟩

end AlgebraicGeometry.Scheme.TwoAffineOpenCover.StageBC

open _root_.AlgebraicCurves.Geometry.Schemes.Proofs in
open Scheme_TwoAffineOpenCover_exists_stage_sectionsOf_baseChange_equiv_of_locallyTrivial in
with_weak_namespace _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover
theorem exists_stage_sectionsOf_baseChange_equiv_of_locallyTrivial
    {R : Type u} [CommRing R] {C : Scheme.{u}} (𝒱 : C.TwoAffineOpenCover) (c : C ⟶ Spec (.of R))
    (A₀ A' : Type u) [CommRing A₀] [CommRing A'] [Algebra R A₀] [Algebra R A'] [Algebra A₀ A']
      [IsScalarTower R A₀ A']
    (M : (Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A₀)).Modules)
    (htriv : ∀ x, ∃ (V : (Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A₀)).Opens), x
      ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj M ≅ SheafOfModules.unit
        V.toScheme.ringCatSheaf)) :
    ∃ (e0 : A' ⊗[A₀] ((𝒱.pullback c A₀).sectionsOf (Limits.pullback.snd c
      (Scheme.TwoAffineOpenCover.specMap R A₀)) M).M0 ≃ₗ[A']
          ((𝒱.pullback c A').sectionsOf (Limits.pullback.snd c
            (Scheme.TwoAffineOpenCover.specMap R A'))
            ((Scheme.Modules.pullback (RelPicard.baseChangeSnd c (RelPicard.LFP.stageHom R
              (IsScalarTower.toAlgHom R A₀ A')))).obj M)).M0)
      (e1 : A' ⊗[A₀] ((𝒱.pullback c A₀).sectionsOf (Limits.pullback.snd c
        (Scheme.TwoAffineOpenCover.specMap R A₀)) M).M1 ≃ₗ[A']
          ((𝒱.pullback c A').sectionsOf (Limits.pullback.snd c
            (Scheme.TwoAffineOpenCover.specMap R A'))
            ((Scheme.Modules.pullback (RelPicard.baseChangeSnd c (RelPicard.LFP.stageHom R
              (IsScalarTower.toAlgHom R A₀ A')))).obj M)).M1)
      (e01 : A' ⊗[A₀] ((𝒱.pullback c A₀).sectionsOf (Limits.pullback.snd c
        (Scheme.TwoAffineOpenCover.specMap R A₀)) M).M01 ≃ₗ[A']
          ((𝒱.pullback c A').sectionsOf (Limits.pullback.snd c
            (Scheme.TwoAffineOpenCover.specMap R A'))
            ((Scheme.Modules.pullback (RelPicard.baseChangeSnd c (RelPicard.LFP.stageHom R
              (IsScalarTower.toAlgHom R A₀ A')))).obj M)).M01),
      (∀ x, e01 ((((𝒱.pullback c A₀).sectionsOf (Limits.pullback.snd c
        (Scheme.TwoAffineOpenCover.specMap R A₀)) M).r0.baseChange A') x) =
        ((𝒱.pullback c A').sectionsOf (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap
          R A'))
            ((Scheme.Modules.pullback (RelPicard.baseChangeSnd c (RelPicard.LFP.stageHom R
              (IsScalarTower.toAlgHom R A₀ A')))).obj M)).r0 (e0 x)) ∧
      (∀ x, e01 ((((𝒱.pullback c A₀).sectionsOf (Limits.pullback.snd c
        (Scheme.TwoAffineOpenCover.specMap R A₀)) M).r1.baseChange A') x) =
        ((𝒱.pullback c A').sectionsOf (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap
          R A'))
            ((Scheme.Modules.pullback (RelPicard.baseChangeSnd c (RelPicard.LFP.stageHom R
              (IsScalarTower.toAlgHom R A₀ A')))).obj M)).r1 (e1 x)) ∧
      (∀ m, e0 ((1 : A') ⊗ₜ[A₀] m) =
        ((Scheme.Modules.pullback (RelPicard.baseChangeSnd c (RelPicard.LFP.stageHom R
          (IsScalarTower.toAlgHom R A₀ A')))).obj M).presheaf.map
          (homOfLE (Scheme.TwoAffineOpenCover.baseChangeSnd_preimage_U0 𝒱 c
            (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R A₀ A'))).ge).op
          ((((Scheme.Modules.pullbackPushforwardAdjunction (RelPicard.baseChangeSnd c
            (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R A₀ A')))).unit.app M).app
            ((𝒱.pullback c A₀).U0)).hom m)) ∧
      (∀ m, e1 ((1 : A') ⊗ₜ[A₀] m) =
        ((Scheme.Modules.pullback (RelPicard.baseChangeSnd c (RelPicard.LFP.stageHom R
          (IsScalarTower.toAlgHom R A₀ A')))).obj M).presheaf.map
          (homOfLE (Scheme.TwoAffineOpenCover.baseChangeSnd_preimage_U1 𝒱 c
            (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R A₀ A'))).ge).op
          ((((Scheme.Modules.pullbackPushforwardAdjunction (RelPicard.baseChangeSnd c
            (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R A₀ A')))).unit.app M).app
            ((𝒱.pullback c A₀).U1)).hom m)) ∧
      (∀ m, e01 ((1 : A') ⊗ₜ[A₀] m) =
        ((Scheme.Modules.pullback (RelPicard.baseChangeSnd c (RelPicard.LFP.stageHom R
          (IsScalarTower.toAlgHom R A₀ A')))).obj M).presheaf.map
          (homOfLE (Scheme.TwoAffineOpenCover.baseChangeSnd_preimage_inf 𝒱 c
            (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R A₀ A'))).ge).op
          ((((Scheme.Modules.pullbackPushforwardAdjunction (RelPicard.baseChangeSnd c
            (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R A₀ A')))).unit.app M).app
            ((𝒱.pullback c A₀).U0 ⊓ (𝒱.pullback c A₀).U1)).hom m)) ∧
      (∀ (s : ((𝒱.pullback c A₀).cover (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap
        R A₀))).A0)
          (m : ((𝒱.pullback c A₀).sectionsOf (Limits.pullback.snd c
            (Scheme.TwoAffineOpenCover.specMap R A₀)) M).M0),
        e0 ((1 : A') ⊗ₜ[A₀] (s • m)) =
          (show ((𝒱.pullback c A').cover (Limits.pullback.snd c
            (Scheme.TwoAffineOpenCover.specMap R A'))).A0 from
            ((RelPicard.baseChangeSnd c (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R A₀
              A'))).appLE ((𝒱.pullback c A₀).U0)
              ((𝒱.pullback c A').U0) (Scheme.TwoAffineOpenCover.baseChangeSnd_preimage_U0 𝒱 c
                (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R A₀ A'))).ge).hom s) •
            e0 ((1 : A') ⊗ₜ[A₀] m)) ∧
      (∀ (s : ((𝒱.pullback c A₀).cover (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap
        R A₀))).A1)
          (m : ((𝒱.pullback c A₀).sectionsOf (Limits.pullback.snd c
            (Scheme.TwoAffineOpenCover.specMap R A₀)) M).M1),
        e1 ((1 : A') ⊗ₜ[A₀] (s • m)) =
          (show ((𝒱.pullback c A').cover (Limits.pullback.snd c
            (Scheme.TwoAffineOpenCover.specMap R A'))).A1 from
            ((RelPicard.baseChangeSnd c (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R A₀
              A'))).appLE ((𝒱.pullback c A₀).U1)
              ((𝒱.pullback c A').U1) (Scheme.TwoAffineOpenCover.baseChangeSnd_preimage_U1 𝒱 c
                (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R A₀ A'))).ge).hom s) •
            e1 ((1 : A') ⊗ₜ[A₀] m)) ∧
      (∀ (s : ((𝒱.pullback c A₀).cover (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap
        R A₀))).A01)
          (m : ((𝒱.pullback c A₀).sectionsOf (Limits.pullback.snd c
            (Scheme.TwoAffineOpenCover.specMap R A₀)) M).M01),
        e01 ((1 : A') ⊗ₜ[A₀] (s • m)) =
          (show ((𝒱.pullback c A').cover (Limits.pullback.snd c
            (Scheme.TwoAffineOpenCover.specMap R A'))).A01 from
            ((RelPicard.baseChangeSnd c (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R A₀
              A'))).appLE
              ((𝒱.pullback c A₀).U0 ⊓ (𝒱.pullback c A₀).U1) ((𝒱.pullback c A').U0 ⊓ (𝒱.pullback
                c A').U1)
              (Scheme.TwoAffineOpenCover.baseChangeSnd_preimage_inf 𝒱 c (RelPicard.LFP.stageHom
                R (IsScalarTower.toAlgHom R A₀ A'))).ge).hom s) •
            e01 ((1 : A') ⊗ₜ[A₀] m)) := by
  have hfst : RelPicard.baseChangeSnd c (stageHom R (IsScalarTower.toAlgHom R A₀ A')) ≫
      Limits.pullback.fst c (specMap R A₀) = Limits.pullback.fst c (specMap R A') :=
    baseChangeSnd_fst c _
  have hsnd : RelPicard.baseChangeSnd c (stageHom R (IsScalarTower.toAlgHom R A₀ A')) ≫
      Limits.pullback.snd c (specMap R A₀) = Limits.pullback.snd c (specMap R A') ≫ specMap A₀ A' :=
    Limits.pullback.lift_snd _ _ _
  obtain ⟨e0, he0⟩ :=
    AlgebraicGeometry.Scheme.TwoAffineOpenCover.StageBC.exists_linearEquiv_sections_stage c _
      hfst hsnd M htriv
    (𝒱.pullback c A₀).U0 (𝒱.pullback c A₀).isAffineOpen_U0 (𝒱.pullback c A').U0
    (baseChangeSnd_preimage_U0 𝒱 c (stageHom R (IsScalarTower.toAlgHom R A₀ A'))).symm
  obtain ⟨e1, he1⟩ :=
    AlgebraicGeometry.Scheme.TwoAffineOpenCover.StageBC.exists_linearEquiv_sections_stage c _
      hfst hsnd M htriv
    (𝒱.pullback c A₀).U1 (𝒱.pullback c A₀).isAffineOpen_U1 (𝒱.pullback c A').U1
    (baseChangeSnd_preimage_U1 𝒱 c (stageHom R (IsScalarTower.toAlgHom R A₀ A'))).symm
  obtain ⟨e01, he01⟩ :=
    AlgebraicGeometry.Scheme.TwoAffineOpenCover.StageBC.exists_linearEquiv_sections_stage c _
      hfst hsnd M htriv
    ((𝒱.pullback c A₀).U0 ⊓ (𝒱.pullback c A₀).U1) (𝒱.pullback c A₀).isAffineOpen_inf
    ((𝒱.pullback c A').U0 ⊓ (𝒱.pullback c A').U1)
    (baseChangeSnd_preimage_inf 𝒱 c (stageHom R (IsScalarTower.toAlgHom R A₀ A'))).symm
  refine ⟨e0, e1, e01, ?_, ?_, he0, he1, he01, ?_, ?_, ?_⟩
  · intro x
    let S := (𝒱.pullback c A₀).sectionsOf (Limits.pullback.snd c (specMap R A₀)) M
    let T := (𝒱.pullback c A').sectionsOf (Limits.pullback.snd c (specMap R A'))
      ((Scheme.Modules.pullback (RelPicard.baseChangeSnd c
        (stageHom R (IsScalarTower.toAlgHom R A₀ A')))).obj M)
    let E01 : A' ⊗[A₀] S.M01 ≃ₗ[A'] T.M01 := e01
    let E : A' ⊗[A₀] S.M0 ≃ₗ[A'] T.M0 := e0
    let F : A' ⊗[A₀] S.M0 →ₗ[A'] T.M01 := E01.toLinearMap.comp (S.r0.baseChange A')
    let G : A' ⊗[A₀] S.M0 →ₗ[A'] T.M01 := T.r0.comp E.toLinearMap
    change F x = G x
    induction x using TensorProduct.inductionOn with
    | add x y hx hy =>
      exact (F.map_add x y).trans
        ((congrArg₂ (fun x y => x + y) hx hy).trans (G.map_add x y).symm)
    | tmul a m =>
      rw [AlgebraicGeometry.Scheme.Modules.StageTransport.tmul_eq_smul_one_tmul a m,
        F.map_smul, G.map_smul]
      congr 1
      change E01 ((S.r0.baseChange A') ((1 : A') ⊗ₜ[A₀] m)) =
        T.r0 (E ((1 : A') ⊗ₜ[A₀] m))
      rw [LinearMap.baseChange_tmul]
      erw [he0, he01]
      erw [AlgebraicGeometry.Scheme.Modules.StageTransport.unit_app_map _ M inf_le_left
        (Scheme.Hom.preimage_mono _ inf_le_left) m]
      change (((Scheme.Modules.pullback _).obj M).presheaf.map _ ≫ ((Scheme.Modules.pullback
        _).obj M).presheaf.map _) _ =
        (((Scheme.Modules.pullback _).obj M).presheaf.map _ ≫ ((Scheme.Modules.pullback _).obj
          M).presheaf.map _) _
      rw [← Functor.map_comp, ← Functor.map_comp]
      rfl
  · intro x
    let S := (𝒱.pullback c A₀).sectionsOf (Limits.pullback.snd c (specMap R A₀)) M
    let T := (𝒱.pullback c A').sectionsOf (Limits.pullback.snd c (specMap R A'))
      ((Scheme.Modules.pullback (RelPicard.baseChangeSnd c
        (stageHom R (IsScalarTower.toAlgHom R A₀ A')))).obj M)
    let E01 : A' ⊗[A₀] S.M01 ≃ₗ[A'] T.M01 := e01
    let E : A' ⊗[A₀] S.M1 ≃ₗ[A'] T.M1 := e1
    let F : A' ⊗[A₀] S.M1 →ₗ[A'] T.M01 := E01.toLinearMap.comp (S.r1.baseChange A')
    let G : A' ⊗[A₀] S.M1 →ₗ[A'] T.M01 := T.r1.comp E.toLinearMap
    change F x = G x
    induction x using TensorProduct.inductionOn with
    | add x y hx hy =>
      exact (F.map_add x y).trans
        ((congrArg₂ (fun x y => x + y) hx hy).trans (G.map_add x y).symm)
    | tmul a m =>
      rw [AlgebraicGeometry.Scheme.Modules.StageTransport.tmul_eq_smul_one_tmul a m,
        F.map_smul, G.map_smul]
      congr 1
      change E01 ((S.r1.baseChange A') ((1 : A') ⊗ₜ[A₀] m)) =
        T.r1 (E ((1 : A') ⊗ₜ[A₀] m))
      rw [LinearMap.baseChange_tmul]
      erw [he1, he01]
      erw [AlgebraicGeometry.Scheme.Modules.StageTransport.unit_app_map _ M inf_le_right
        (Scheme.Hom.preimage_mono _ inf_le_right) m]
      change (((Scheme.Modules.pullback _).obj M).presheaf.map _ ≫ ((Scheme.Modules.pullback
        _).obj M).presheaf.map _) _ =
        (((Scheme.Modules.pullback _).obj M).presheaf.map _ ≫ ((Scheme.Modules.pullback _).obj
          M).presheaf.map _) _
      rw [← Functor.map_comp, ← Functor.map_comp]
      rfl
  · intro s m
    erw [he0, he0, Scheme.Modules.Hom.app_smul]
    erw [AlgebraicGeometry.Scheme.Modules.StageTransport.pushforward_smul
      (RelPicard.baseChangeSnd c (stageHom R (IsScalarTower.toAlgHom R A₀ A')))
      ((Scheme.Modules.pullback (RelPicard.baseChangeSnd c (stageHom R (IsScalarTower.toAlgHom R
        A₀ A')))).obj M) ((𝒱.pullback c A₀).U0) s]
    rw [Scheme.Modules.map_smul]
    rfl
  · intro s m
    erw [he1, he1, Scheme.Modules.Hom.app_smul]
    erw [AlgebraicGeometry.Scheme.Modules.StageTransport.pushforward_smul
      (RelPicard.baseChangeSnd c (stageHom R (IsScalarTower.toAlgHom R A₀ A')))
      ((Scheme.Modules.pullback (RelPicard.baseChangeSnd c (stageHom R (IsScalarTower.toAlgHom R
        A₀ A')))).obj M) ((𝒱.pullback c A₀).U1) s]
    rw [Scheme.Modules.map_smul]
    rfl
  · intro s m
    erw [he01, he01, Scheme.Modules.Hom.app_smul]
    erw [AlgebraicGeometry.Scheme.Modules.StageTransport.pushforward_smul
      (RelPicard.baseChangeSnd c (stageHom R (IsScalarTower.toAlgHom R A₀ A')))
      ((Scheme.Modules.pullback (RelPicard.baseChangeSnd c (stageHom R (IsScalarTower.toAlgHom R
        A₀ A')))).obj M) (((𝒱.pullback c A₀).U0 ⊓ (𝒱.pullback c A₀).U1)) s]
    rw [Scheme.Modules.map_smul]
    rfl

end
end Scheme_TwoAffineOpenCover_exists_stage_sectionsOf_baseChange_equiv_of_locallyTrivial
end AlgebraicCurves.Geometry.Schemes.Proofs
end ProofImplementation
