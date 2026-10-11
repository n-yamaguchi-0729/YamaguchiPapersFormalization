/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_bijective_appTop_of_isProper_of_flat_of_locallyOfFinitePresentation_of_isLocalRing.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Spec
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.CategoryTheory.ConcreteCategory.Basic
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Algebra.Ring.ULift
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Tactic.Choose
import Nyll.SchemeTheory.Descent.SubalgebraStages
import Nyll.SchemeTheory.Descent.SubalgebraStages_nonempty_isLimit_cone
import Nyll.AlgebraicCurves.Geometry.Schemes.exists_fg_subalgebra_isProper_flat_isPullback_of_isProper_of_flat_of_locallyOfFinitePresentation
import Nyll.AlgebraicCurves.Foundations.CommutativeAlgebra.IsLocalRing_exists_subalgebra_coe_eq_isNoetherianRing_isLocalRing_isUnit_iff
import Nyll.AlgebraicCurves.Geometry.Schemes.bijective_appTop_of_bijective_appTop_pullback_snd_of_faithfullyFlat
import Nyll.AlgebraicCurves.Geometry.Schemes.bijective_appTop_of_isProper_of_flat_of_isNoetherianRing_of_isLocalRing

/-!
# bijective app Top of is Proper of flat of locally Of Finite Presentation of is Local Ring
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs
namespace bijective_appTop_of_isProper_of_flat_of_locallyOfFinitePresentation_of_isLocalRing
attribute [-instance] IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty
  AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed
  AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU
  AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway
  AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU
  AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial
  AdicCompletion.instIsLocalRingMaximalIdeal
attribute [-simp] IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply
  IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of
  IsDirectLimit.Equiv_apply AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec
  AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq
  AlgebraicGeometry.ChowDatum.mk.injEq

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace NewLocalAux

theorem bijective_appTop_of_iso {P P' Y : Scheme.{u}} (e : P ≅ P') (s : P ⟶ Y) (s' : P' ⟶ Y) (w :
  e.hom ≫ s' = s)
    (h : Function.Bijective s'.appTop) : Function.Bijective s.appTop := by
  rw [← w, Scheme.Hom.comp_appTop]
  have : IsIso e.hom.appTop := ⟨⟨e.inv.appTop, by rw [← Scheme.Hom.comp_appTop, e.inv_hom_id]; simp,
    by rw [← Scheme.Hom.comp_appTop, e.hom_inv_id]; simp⟩⟩
  have he : Function.Bijective e.hom.appTop := (ConcreteCategory.isIso_iff_bijective _).mp
    inferInstance
  change Function.Bijective (e.hom.appTop.hom ∘ s'.appTop.hom)
  exact he.comp h

theorem bijective_ΓSpecIso_inv_comp_iff {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R) :
    Function.Bijective ((Scheme.ΓSpecIso R).inv ≫ f.appTop).hom ↔ Function.Bijective f.appTop := by
  have he : Function.Bijective (Scheme.ΓSpecIso R).inv :=
    (ConcreteCategory.isIso_iff_bijective _).mp inferInstance
  change Function.Bijective (f.appTop.hom ∘ (Scheme.ΓSpecIso R).inv.hom) ↔ _
  exact Function.Bijective.of_comp_iff _ he

section stage

variable {T : Type u} [CommRing T] {R : Type u} [CommRing R] [IsLocalRing R] [Algebra T R]
  (S : Subalgebra T R) [IsLocalRing ↥S] (hunit : ∀ x : ↥S, IsUnit x ↔ IsUnit (x : R))

/-- The residue-field homomorphism induced by the local subalgebra inclusion. -/
noncomputable def resMap : (↥S ⧸ IsLocalRing.maximalIdeal ↥S) →+* (R ⧸ IsLocalRing.maximalIdeal R)
  :=
  Ideal.Quotient.lift _ ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal R)).comp (algebraMap ↥S R))
    (by
    intro a ha
    rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem, IsLocalRing.mem_maximalIdeal,
      mem_nonunits_iff]
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at ha
    exact fun h => ha ((hunit a).mpr h))

lemma resMap_mk (a : ↥S) : resMap S hunit (Ideal.Quotient.mk _ a) =
    Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) (a : R) :=
  Ideal.Quotient.lift_mk _ _ _
include hunit in
theorem bijective_stage [IsNoetherianRing ↥S] {X₀ : Scheme.{u}} (f₀ : X₀ ⟶ Spec (CommRingCat.of T))
    [IsProper f₀] [Flat f₀]
    (h : Function.Bijective (pullback.snd (pullback.snd f₀ (Spec.map (CommRingCat.ofHom (algebraMap
      T R))))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R))))).appTop) :
    Function.Bijective (pullback.snd f₀ (Spec.map (CommRingCat.ofHom (algebraMap T ↥S)))).appTop :=
      by
  classical
  let ιR : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of T) :=
    Spec.map (CommRingCat.ofHom (algebraMap T R))
  let ιS : Spec (CommRingCat.of ↥S) ⟶ Spec (CommRingCat.of T) :=
    Spec.map (CommRingCat.ofHom (algebraMap T ↥S))
  let q : pullback f₀ ιS ⟶ Spec (CommRingCat.of ↥S) := pullback.snd f₀ ιS
  have : IsProper q := by
    have : MorphismProperty.IsStableUnderBaseChange
        (@IsProper : MorphismProperty Scheme.{u}) :=
          AlgebraicGeometry.IsProper.isStableUnderBaseChange
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := (@IsProper : MorphismProperty Scheme.{u}))
      (IsPullback.of_hasPullback f₀ ιS) inferInstance
  have : Flat q := by
    have : MorphismProperty.IsStableUnderBaseChange
        (@Flat : MorphismProperty Scheme.{u}) := AlgebraicGeometry.Flat.isStableUnderBaseChange
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := (@Flat : MorphismProperty Scheme.{u}))
      (IsPullback.of_hasPullback f₀ ιS) inferInstance
  let kS : Type u := ↥S ⧸ IsLocalRing.maximalIdeal ↥S
  let κ : Type u := R ⧸ IsLocalRing.maximalIdeal R
  let : Field kS := Ideal.Quotient.field _
  let : Field κ := Ideal.Quotient.field _
  let : Algebra kS κ := (resMap S hunit).toAlgebra
  let mkS : Spec (CommRingCat.of kS) ⟶ Spec (CommRingCat.of ↥S) :=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal ↥S)))
  let mkR : Spec (CommRingCat.of κ) ⟶ Spec (CommRingCat.of R) :=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R)))
  let e : Spec (CommRingCat.of κ) ⟶ Spec (CommRingCat.of kS) := Spec.map (CommRingCat.ofHom
    (algebraMap kS κ))
  let F : Scheme.{u} := pullback q mkS
  let fF : F ⟶ Spec (CommRingCat.of kS) := pullback.snd q mkS
  have : CompactSpace ↥F :=
    @QuasiCompact.compactSpace_of_compactSpace _ _ fF
      (by
        have : MorphismProperty.IsStableUnderBaseChange
            (@QuasiCompact : MorphismProperty Scheme.{u}) :=
          AlgebraicGeometry.quasiCompact_isStableUnderBaseChange
        exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
          (P := (@QuasiCompact : MorphismProperty Scheme.{u}))
          (IsPullback.of_hasPullback q mkS) inferInstance)
      (inferInstance : CompactSpace (PrimeSpectrum kS))
  have : QuasiSeparatedSpace ↥F :=
    @quasiSeparatedSpace_of_quasiSeparated _ _ fF inferInstance
      (by
        have : MorphismProperty.IsStableUnderBaseChange
            (@QuasiSeparated : MorphismProperty Scheme.{u}) :=
          AlgebraicGeometry.quasiSeparated_isStableUnderBaseChange
        exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
          (P := (@QuasiSeparated : MorphismProperty Scheme.{u}))
          (IsPullback.of_hasPullback q mkS) inferInstance)
  have hring : CommRingCat.ofHom (algebraMap T ↥S) ≫
      CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal ↥S)) ≫ CommRingCat.ofHom
        (algebraMap kS κ) =
      CommRingCat.ofHom (algebraMap T R) ≫ CommRingCat.ofHom (Ideal.Quotient.mk
        (IsLocalRing.maximalIdeal R)) := by
    ext x
    change resMap S hunit (Ideal.Quotient.mk _ (algebraMap T ↥S x)) = Ideal.Quotient.mk _
      (algebraMap T R x)
    rw [resMap_mk]
    rfl
  have hbase : e ≫ mkS ≫ ιS = mkR ≫ ιR := by
    simp only [e, mkS, ιS, mkR, ιR, ← Spec.map_comp, Category.assoc]
    exact congrArg Spec.map hring
  have sq1 : IsPullback (pullback.fst fF e ≫ pullback.fst q mkS ≫ pullback.fst f₀ ιS) (pullback.snd
    fF e)
      f₀ (e ≫ mkS ≫ ιS) :=
    IsPullback.paste_horiz (IsPullback.of_hasPullback fF e)
      (IsPullback.paste_horiz (IsPullback.of_hasPullback q mkS) (IsPullback.of_hasPullback f₀ ιS))
  have sq2 : IsPullback (pullback.fst (pullback.snd f₀ ιR) mkR ≫ pullback.fst f₀ ιR)
      (pullback.snd (pullback.snd f₀ ιR) mkR) f₀ (mkR ≫ ιR) :=
    IsPullback.paste_horiz (IsPullback.of_hasPullback (pullback.snd f₀ ιR) mkR)
      (IsPullback.of_hasPullback f₀ ιR)
  rw [hbase] at sq1
  have hF : Function.Bijective (pullback.snd fF e).appTop :=
    bijective_appTop_of_iso (sq1.isoIsPullback _ _ sq2) _ _ (sq1.isoIsPullback_hom_snd _ _ sq2) h
  have : Module.Free kS κ := Module.Free.of_divisionRing kS κ
  have : Nontrivial κ := inferInstance
  have : Module.FaithfullyFlat kS κ := @Module.FaithfullyFlat.instOfNontrivialOfFree kS κ _ _ _
    ‹Nontrivial κ› ‹Module.Free kS κ›
  have hk : Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of kS)).inv ≫ fF.appTop).hom :=
    AlgebraicGeometry.bijective_appTop_of_bijective_appTop_pullback_snd_of_faithfullyFlat fF κ
      ((bijective_ΓSpecIso_inv_comp_iff _).mpr hF)
  exact AlgebraicGeometry.bijective_appTop_of_isProper_of_flat_of_isNoetherianRing_of_isLocalRing
    (A := CommRingCat.of ↥S) q ((bijective_ΓSpecIso_inv_comp_iff _).mp hk)

end stage

end NewLocalAux

open NewLocalAux _root_.AlgebraicGeometry.SubalgebraStages in
theorem NewLocalAux.main {X : Scheme.{u}} {R : Type u} [CommRing R] [IsLocalRing R]
    (g : X ⟶ Spec (CommRingCat.of R)) [IsProper g] [Flat g] [LocallyOfFinitePresentation g]
    (h : Function.Bijective (pullback.snd g (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R))))).appTop) :
    Function.Bijective g.appTop := by
  classical
  let : Algebra (ULift.{u} ℤ) R := ((algebraMap ℤ R).comp (ULift.ringEquiv (R :=
    ℤ)).toRingHom).toAlgebra
  have : IsNoetherianRing (ULift.{u} ℤ) := isNoetherianRing_of_ringEquiv ℤ (ULift.ringEquiv (R :=
    ℤ)).symm
  obtain ⟨T, hT, -, X₀, f₀, π, hprop, hflat, sq⟩ :=
    AlgebraicGeometry.ProperFlatFinitePresentationDescent
      (A₀ := ULift.{u} ℤ) g ∅
  have := hprop
  have := hflat
  have : Algebra.FiniteType (ULift.{u} ℤ) ↥T := (Subalgebra.fg_iff_finiteType _).mp hT
  have : IsNoetherianRing ↥T := Algebra.FiniteType.isNoetherianRing (ULift.{u} ℤ) ↥T
  let ιT : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of ↥T) := specHomTop (A₀ := ↥T) (A := R)
  let mkR : Spec (CommRingCat.of (R ⧸ IsLocalRing.maximalIdeal R)) ⟶ Spec (CommRingCat.of R) :=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R)))
  have h' : Function.Bijective (pullback.snd (pullback.snd f₀ ιT) mkR).appTop := by
    have e1 : IsPullback sq.isoPullback.hom g (pullback.snd f₀ ιT) (𝟙 _) :=
      IsPullback.of_horiz_isIso ⟨by rw [sq.isoPullback_hom_snd, Category.comp_id]⟩
    have sqa : IsPullback (pullback.fst g mkR ≫ sq.isoPullback.hom) (pullback.snd g mkR)
      (pullback.snd f₀ ιT)
        (mkR ≫ 𝟙 _) :=
      IsPullback.paste_horiz (IsPullback.of_hasPullback g mkR) e1
    rw [Category.comp_id] at sqa
    exact bijective_appTop_of_iso
      ((IsPullback.of_hasPullback (pullback.snd f₀ ιT) mkR).isoIsPullback _ _ sqa) _ _
      ((IsPullback.of_hasPullback (pullback.snd f₀ ιT) mkR).isoIsPullback_hom_snd _ _ sqa) h
  let ι : Type u := {T' : Subalgebra ↥T R // T'.FG}
  have : Nonempty ι := ⟨⟨⊥, Subalgebra.fg_bot⟩⟩
  have : IsDirected ι (· ≤ ·) := ⟨fun T₁ T₂ =>
    ⟨⟨T₁.1 ⊔ T₂.1, T₁.2.sup T₂.2⟩, (le_sup_left : T₁.1 ≤ T₁.1 ⊔ T₂.1), (le_sup_right : T₂.1 ≤ T₁.1
      ⊔ T₂.1)⟩⟩
  have hN : ∀ i : ι, IsNoetherianRing ↥(i.1) := fun i =>
    have : Algebra.FiniteType ↥T ↥(i.1) := (Subalgebra.fg_iff_finiteType _).mp i.2
    Algebra.FiniteType.isNoetherianRing ↥T ↥(i.1)
  have hLS := fun i : ι =>
    @IsLocalRing.exists_subalgebra_coe_eq_isNoetherianRing_isLocalRing_isUnit_iff ↥T _ R _ _ _ i.1
      (hN i)
  choose S hS using hLS
  have hSmono : Monotone S := by
    intro i j hij x hx
    have hx' : (x : R) ∈ (S i : Set R) := hx
    rw [(hS i).1] at hx'
    obtain ⟨t, ht, u, hu, hum, hxu⟩ := hx'
    have : (x : R) ∈ (S j : Set R) := by
      rw [(hS j).1]
      exact ⟨t, hij ht, u, hij hu, hum, hxu⟩
    exact this
  let So : ι →o Subalgebra ↥T R := ⟨S, hSmono⟩
  have hcov : ∀ a : R, ∃ i, a ∈ So i := by
    intro a
    let T' : Subalgebra ↥T R := Algebra.adjoin ↥T {a}
    have hT' : T'.FG := ⟨{a}, by rw [Finset.coe_singleton]⟩
    refine ⟨⟨T', hT'⟩, ?_⟩
    have : a ∈ (S ⟨T', hT'⟩ : Set R) := by
      rw [(hS ⟨T', hT'⟩).1]
      refine ⟨a, Algebra.self_mem_adjoin_singleton _ a, 1, T'.one_mem, ?_, mul_one a⟩
      exact fun h1 => (IsLocalRing.maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).mpr
        h1)
    exact this
  obtain ⟨hc⟩ := AlgebraicGeometry.SubalgebraStages.nonempty_isLimit_cone So hcov f₀
  have : QuasiCompact f₀ := inferInstance
  have : QuasiSeparated f₀ := inferInstance
  have hstage : ∀ i : ι, Function.Bijective (pullback.snd f₀ (specHom So i)).appTop := fun i => by
    have : IsNoetherianRing ↥(S i) := (hS i).2.1
    have : IsLocalRing ↥(S i) := (hS i).2.2.1
    exact bijective_stage (S i) (hS i).2.2.2 f₀ h'
  have key1 : ∀ (i : ι) (a : ↥(S i)),
      (pullback.snd f₀ ιT).appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv (a : R)) =
        ((cone So f₀).π.app (op i)).appTop
          ((pullback.snd f₀ (specHom So i)).appTop ((Scheme.ΓSpecIso (CommRingCat.of ↥(S i))).inv
            a)) := by
    intro i a
    have n1 : _ = _ ≫ (specLeg So i).appTop :=
      Scheme.ΓSpecIso_inv_naturality (R := CommRingCat.of ↥(So i)) (S := CommRingCat.of R) _
    have e1 := congrArg (fun φ => φ.hom a) n1
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e1
    have n2 := congrArg Scheme.Hom.appTop (cone_π_app_snd So f₀ (op i))
    rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop] at n2
    have e2 := congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of ↥(S i))).inv a)) n2
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e2
    rw [e2]
    exact congrArg _ e1
  have key2 : ∀ {i j : ιᵒᵖ} (φ : j ⟶ i) (a : ↥(S i.unop)),
      ((diagram So f₀).map φ).appTop ((pullback.snd f₀ (specHom So i.unop)).appTop
          ((Scheme.ΓSpecIso (CommRingCat.of ↥(S i.unop))).inv a)) =
        (pullback.snd f₀ (specHom So j.unop)).appTop
          ((Scheme.ΓSpecIso (CommRingCat.of ↥(S j.unop))).inv (Subalgebra.inclusion (So.mono
            φ.unop.le) a)) := by
    intro i j φ a
    have n1 : _ = _ ≫ (specTrans So φ.unop.le).appTop :=
      Scheme.ΓSpecIso_inv_naturality (R := CommRingCat.of ↥(So i.unop)) (S := CommRingCat.of ↥(So
        j.unop)) _
    have e1 := congrArg (fun ψ => ψ.hom a) n1
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e1
    have n2 := congrArg Scheme.Hom.appTop (diagram_map_snd So f₀ φ)
    rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop] at n2
    have e2 := congrArg (fun ψ => ψ.hom ((Scheme.ΓSpecIso (CommRingCat.of ↥(S i.unop))).inv a)) n2
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e2
    rw [e2]
    exact congrArg _ e1.symm
  have main : Function.Bijective (pullback.snd f₀ ιT).appTop := by
    have hΓR : ∀ x : Γ(Spec (CommRingCat.of R), ⊤),
        x = (Scheme.ΓSpecIso (CommRingCat.of R)).inv ((Scheme.ΓSpecIso (CommRingCat.of R)).hom x) :=
      fun x => (CategoryTheory.Iso.hom_inv_id_apply _ x).symm
    constructor
    · rw [injective_iff_map_eq_zero]
      intro x hx
      obtain ⟨i, hi⟩ := hcov ((Scheme.ΓSpecIso (CommRingCat.of R)).hom x)
      let a : ↥(S i) := ⟨_, hi⟩
      have hxa : x = (Scheme.ΓSpecIso (CommRingCat.of R)).inv (a : R) := hΓR x
      rw [hxa, key1 i a] at hx
      obtain ⟨j, φ, hj⟩ := exists_appTop_map_eq_zero_of_isLimit (diagram So f₀) (cone So f₀) hc _ hx
      rw [key2 φ a] at hj
      have hΓj : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of ↥(S j.unop))).inv :=
        ((ConcreteCategory.isIso_iff_bijective _).mp inferInstance).1
      have h0 : Subalgebra.inclusion (So.mono φ.unop.le) a = 0 := by
        apply hΓj
        apply (hstage j.unop).1
        refine hj.trans ?_
        rw [map_zero, map_zero]
      have ha0 : (a : R) = 0 := congrArg (fun y : ↥(S j.unop) => (y : R)) h0
      have : x = (Scheme.ΓSpecIso (CommRingCat.of R)).inv (0 : R) := ha0 ▸ hxa
      exact this.trans (map_zero _)
    · intro s
      obtain ⟨i, t, hst⟩ := exists_appTop_π_eq_of_isLimit (diagram So f₀) (cone So f₀) hc s
      obtain ⟨z, rfl⟩ := (hstage i.unop).2 t
      have hz : z = (Scheme.ΓSpecIso (CommRingCat.of ↥(S i.unop))).inv
          ((Scheme.ΓSpecIso (CommRingCat.of ↥(S i.unop))).hom z) :=
        (CategoryTheory.Iso.hom_inv_id_apply _ z).symm
      refine ⟨(Scheme.ΓSpecIso (CommRingCat.of R)).inv
        (((Scheme.ΓSpecIso (CommRingCat.of ↥(S i.unop))).hom z : ↥(S i.unop)) : R), ?_⟩
      rw [key1 i.unop, ← hz]
      exact hst.symm
  exact bijective_appTop_of_iso sq.isoPullback g _ sq.isoPullback_hom_snd main

end bijective_appTop_of_isProper_of_flat_of_locallyOfFinitePresentation_of_isLocalRing
end AlgebraicCurves.Geometry.Schemes.Proofs

namespace AlgebraicGeometry

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

open _root_.AlgebraicCurves.Geometry.Schemes.Proofs in
open bijective_appTop_of_isProper_of_flat_of_locallyOfFinitePresentation_of_isLocalRing in
theorem bijective_appTop_of_isProper_of_flat_of_locallyOfFinitePresentation_of_isLocalRing
    {X : Scheme.{u}} {A : CommRingCat.{u}} [IsLocalRing A]
    (p : X ⟶ Spec A) [IsProper p] [Flat p] [LocallyOfFinitePresentation p]
    (h : Function.Bijective (pullback.snd p (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A))))).appTop) :
    Function.Bijective p.appTop :=
  NewLocalAux.main (R := ↑A) p h
end AlgebraicGeometry
end ProofImplementation

attribute [-instance] AlgebraicGeometry.SubalgebraStages.compactSpace_pullback
  AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback
  AlgebraicGeometry.SubalgebraStages.compactSpace_obj
  AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj
  AlgebraicGeometry.SubalgebraStages.quasiCompact_snd
  AlgebraicGeometry.SubalgebraStages.isAffineHom_leg
  AlgebraicGeometry.SubalgebraStages.isAffineHom_trans
  AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map
  AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd
  AlgebraicGeometry.SubalgebraStages.isCofiltered_op
  IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty
  AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed
  AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU
  AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway
  AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU
  AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial
  AdicCompletion.instIsLocalRingMaximalIdeal
attribute [-simp] AlgebraicGeometry.SubalgebraStages.specCone_π_app
  AlgebraicGeometry.SubalgebraStages.specLeg_specHom
  AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt
  AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj
  AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map
  AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd
  AlgebraicGeometry.SubalgebraStages.specTrans_specHom
  AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app
  AlgebraicGeometry.SubalgebraStages.specDiagram_map
  AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst
  AlgebraicGeometry.SubalgebraStages.leg_trans IsDirectLimit.Module.linearEquiv_symm_apply
  IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply
  IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply
  AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec
  AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq
