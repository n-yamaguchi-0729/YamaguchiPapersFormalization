/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_exists_isNoetherianRing_model_of_fg_subalgebra_model_of_locIsoOnBase_unit_faces.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Spec
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.Algebra.Algebra.Subalgebra.Tower
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.CategoryTheory.EqToHom
import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.AlgebraicCurves.Geometry.Picard.PolarisationRosati
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.Product
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.BaseChange
import Nyll.AlgebraicCurves.Foundations.Algebra.Mathlib_Algebra_IsDirectLimit
import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesPullbackMonoidalV2
import Nyll.AlgebraicCurves.Geometry.Picard.Polarisation_locIsoOnBase_faces_pullback_cube_iff_of_isPullback
import Nyll.JacobianVarieties.Picard.RigidifiedLineBundle_exists_rigidified_cube_pullback_of_isPullback
import Nyll.AlgebraicCurves.Geometry.Picard.Polarisation_exists_locIsoOnBase_pullback_unit_stage_of_locIsoOnBase_pullback_unit_of_isDirectLimit
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.Theorems.AbelianSchemePropertyBundle_of_isPullback
import Nyll.AlgebraicCurves.Geometry.Picard.Polarisation_LocIsoOnBase_pullback_of_comp_eq
import Nyll.AlgebraicCurves.Geometry.Picard.Polarisation_LocIsoOnBase_equivalence

/-!
# Noetherian models preserving the three unit faces
-/

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.NoetherianUnitFaceModel
attribute [-instance]
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
  TwoChartCech.Cover.A0_commRing
  TwoChartCech.Sections.M1_tower
  TwoChartCech.Sections.M01_moduleA
  TwoChartCech.Sections.M0_module
  TwoChartCech.Sections.M1_moduleA
  TwoChartCech.Sections.M1_addCommGroup
  TwoChartCech.Cover.A01_commRing
  TwoChartCech.Sections.M01_tower
  CoherentBaseChange.TwoTermComplex.C0_module
  CoherentBaseChange.TwoTermComplex.C0_addCommGroup
  CoherentBaseChange.TwoTermComplex.C1_module
  CoherentBaseChange.TwoTermComplex.C1_addCommGroup
  CoherentBaseChange.TwoTermComplex.C0_free
  CoherentBaseChange.TwoTermComplex.C1_finite
  CoherentBaseChange.TwoTermComplex.C0_finite
  CoherentBaseChange.TwoTermComplex.C1_free
  SheafOfModules.isIso_ihomModelToIhom
attribute [-simp]
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right
  AlgebraicGeometry.Scheme.Modules.map_unitSection
  AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply
  AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left
  AlgebraicGeometry.Scheme.Modules.tensorPow_zero
  AlgebraicGeometry.Scheme.Modules.tensorPow_succ
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0
  TwoChartCech.Sections.mk.injEq
  TwoChartCech.Cover.mk.injEq
  TwoChartCech.GrothendieckComplex.mk.injEq
  TwoChartCech.Sections.mk.sizeOf_spec
  TwoChartCech.Cover.mk.sizeOf_spec
  TwoChartCech.Cover.lineBundle_r0_apply
  TwoChartCech.GrothendieckComplex.mk.sizeOf_spec
  TwoChartCech.Cover.lineBundle_r1_apply
  CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec
  CoherentBaseChange.TwoTermComplex.mk.injEq
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
  AlgebraicGeometry.schemeFibreEndo_snd
  AlgebraicGeometry.schemeFibreEndo_fst


open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian
open _root_.AlgebraicGeometry.Polarisation
open _root_.AlgebraicGeometry.RelPicard


namespace CFDStages

variable {A₀ : Type} [CommRing A₀] {A : Type} [CommRing A] [Algebra A₀ A] (B : Subalgebra A₀ A)

/-- Finitely generated subalgebras containing the fixed initial stage. -/
abbrev Idx : Type := {T : Subalgebra A₀ A // T.FG ∧ B ≤ T}

/-- The ring at a finitely generated subalgebra stage. -/
abbrev G (i : Idx B) : Type := ↥i.1

/-- The transition ring homomorphism between two ordered stages. -/
def φ (i j : Idx B) (h : i ≤ j) :
    G B i →+* G B j := (Subalgebra.inclusion (show i.1 ≤ j.1 from h)).toRingHom

/-- The inclusion of a stage into the ambient algebra. -/
def g (i : Idx B) : G B i →+* A := (i.1).val.toRingHom

/-- Transition maps preserve the underlying element of the ambient algebra. -/
@[scoped simp] theorem φ_apply (i j : Idx B) (h : i ≤ j) (x : G B i) :
    (φ B i j h x : A) = (x : A) := rfl
/-- The stage inclusion is the subtype coercion. -/
@[scoped simp] theorem g_apply (i : Idx B) (x : G B i) : g B i x = (x : A) := rfl
/-- Stage inclusions commute with the transition maps. -/
theorem g_comp_φ (i j : Idx B) (h : i ≤ j) : (g B j).comp (φ B i j h) = g B i := rfl

scoped instance : DirectedSystem (G B) (fun i j h => ⇑(φ B i j h)) where
  map_self _ _ := rfl
  map_map _ _ _ _ _ _ := rfl

private def _root_.CFDStages.sup (i j : Idx B) :
    Idx B := ⟨i.1 ⊔ j.1, i.2.1.sup j.2.1, le_sup_of_le_left i.2.2⟩


export _root_.CFDStages (sup)

scoped instance : IsDirected (Idx B) (· ≤ ·) :=
  ⟨fun i j => ⟨sup B i j, (le_sup_left : i.1 ≤ i.1 ⊔ j.1), (le_sup_right : j.1 ≤ i.1 ⊔ j.1)⟩⟩

/-- A finitely generated initial algebra is itself an admissible stage. -/
theorem nonempty (hB : B.FG) : Nonempty (Idx B) := ⟨⟨B, hB, le_rfl⟩⟩

/-- The ambient algebra is the direct limit of finitely generated stages above the initial one. -/
theorem isDirectLimit (hB : B.FG) : IsDirectLimit (fun i j h => ⇑(φ B i j h)) (fun i => ⇑(g B i))
  where
  surj m := by
    refine ⟨⟨B ⊔ Algebra.adjoin A₀ {m}, hB.sup ⟨{m},
      by rw [Finset.coe_singleton]⟩, le_sup_left⟩, ⟨m, ?_⟩, rfl⟩
    exact Algebra.mem_sup_right (Algebra.self_mem_adjoin_singleton A₀ m)
  inj i j mi mj h := ⟨sup B i j, (le_sup_left : i.1 ≤ i.1 ⊔ j.1), (le_sup_right : j.1 ≤ i.1 ⊔ j.1),
    Subtype.ext h⟩
  compatibility _ _ _ _ := rfl

end CFDStages

open scoped _root_.JacobianVarieties.Picard.Proofs.NoetherianUnitFaceModel.CFDStages


namespace CFDAsm

/-- An isomorphism of modules gives a local isomorphism over the base. -/
theorem ofIso {S' : Type} [CommRing S'] {Q : Scheme.{0}} (q : Q ⟶ Spec (CommRingCat.of S'))
    {M M' : Q.Modules}
    (e : M ≅ M') : LocIsoOnBase q M M' := fun _ => ⟨⊤, trivial, ⟨(Scheme.Modules.pullback _).mapIso
      e⟩⟩

/-- Local triviality of the pulled-back module persists under a further base change. -/
theorem rebase {S₁ : Type} [CommRing S₁] {X : Scheme.{0}} (fX : X ⟶ Spec (CommRingCat.of S₁))
    {R R' : Type} [CommRing R] [CommRing R'] (s : S₁ →+* R) (s' : S₁ →+* R') (t : R →+* R') (ht :
      t.comp s = s')
    (N : X.Modules)
    (h : LocIsoOnBase (pullback.snd fX (Spec.map (CommRingCat.ofHom s)))
      ((Scheme.Modules.pullback (pullback.fst fX (Spec.map (CommRingCat.ofHom s)))).obj N) (𝟙_ _)) :
    LocIsoOnBase (pullback.snd fX (Spec.map (CommRingCat.ofHom s')))
      ((Scheme.Modules.pullback (pullback.fst fX (Spec.map (CommRingCat.ofHom s')))).obj N) (𝟙_ _)
        := by
  have hs : Spec.map (CommRingCat.ofHom t) ≫ Spec.map (CommRingCat.ofHom s) = Spec.map
    (CommRingCat.ofHom s') := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ht]
  let ρ : pullback fX (Spec.map (CommRingCat.ofHom s')) ⟶ pullback fX (Spec.map (CommRingCat.ofHom
    s)) :=
    pullback.lift (pullback.fst fX _) (pullback.snd fX _ ≫ Spec.map (CommRingCat.ofHom t))
      (by rw [pullback.condition, Category.assoc, hs])
  have hρ₁ : ρ ≫ pullback.fst fX _ = pullback.fst fX _ := pullback.lift_fst _ _ _
  have hρ₂ : ρ ≫ pullback.snd fX _ = pullback.snd fX _ ≫ Spec.map (CommRingCat.ofHom t) :=
    pullback.lift_snd _ _ _
  have h' := AlgebraicGeometry.Polarisation.LocIsoOnBase.pullback_of_comp_eq (pullback.snd fX
    (Spec.map (CommRingCat.ofHom s'))) ρ
    (Spec.map (CommRingCat.ofHom t)) hρ₂ h
  have EQ := AlgebraicGeometry.Polarisation.LocIsoOnBase.equivalence (pullback.snd fX (Spec.map
    (CommRingCat.ofHom s')))
  refine EQ.trans (EQ.trans (ofIso _ ?_) h') (ofIso _ (Scheme.Modules.pullbackTensorUnitObjIso ρ))
  exact ((Scheme.Modules.pullbackComp ρ _).app N ≪≫ (Scheme.Modules.pullbackCongr hρ₁).app N).symm

end CFDAsm

open scoped _root_.JacobianVarieties.Picard.Proofs.NoetherianUnitFaceModel.CFDStages


end JacobianVarieties.Picard.Proofs.NoetherianUnitFaceModel

namespace AlgebraicGeometry.RelPicard.RigidifiedLineBundle

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
open scoped JacobianVarieties.Picard.Proofs.NoetherianUnitFaceModel.CFDStages

open _root_.JacobianVarieties.Picard.Proofs.NoetherianUnitFaceModel in
open CFDStages CFDAsm in
/-- Descend the rigidified bundle and its three locally trivial faces to a Noetherian base. -/
theorem
exists_isNoetherianRing_model_of_fg_subalgebra_model_of_locIsoOnBase_unit_faces
    {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f)
    (M : RigidifiedLineBundle (prodStr f f) ((L.prod L).one (𝟙 (Spec (CommRingCat.of S)))) f)
    (h₁ : LocIsoOnBase (prodStr f f)
      ((Scheme.Modules.pullback
        (pullback.lift
          (pullback.lift (L.one (prodStr f f)).1 (pullback.fst f f) (by rw [(L.one _).2]))
          (pullback.snd f f)
          (by
            rw [pullback.lift_fst_assoc, (L.one _).2]
            exact pullback.condition))).obj M.L) (𝟙_ _))
    (h₂ : LocIsoOnBase (prodStr f f)
      ((Scheme.Modules.pullback
        (pullback.lift
          (pullback.lift (pullback.fst f f) (L.one (prodStr f f)).1 (by rw [(L.one _).2]))
          (pullback.snd f f)
          (by rw [pullback.lift_fst_assoc]; exact pullback.condition))).obj M.L) (𝟙_ _))
    (h₃ : LocIsoOnBase (prodStr f f)
      ((Scheme.Modules.pullback
        (pullback.lift (𝟙 _) (L.one (prodStr f f)).1
          (by rw [Category.id_comp, (L.one _).2]))).obj M.L) (𝟙_ _))
    (S₁ : Subalgebra ℤ S) (hS₁ : S₁.FG)
      (A₁ : Scheme.{0}) (f₁ : A₁ ⟶ Spec (CommRingCat.of ↥S₁)) (L₁ : RelativeGroupLaw ↥S₁ f₁)
      (hA₁ : AbelianSchemePropertyBundle ↥S₁ f₁)
      (a : A ⟶ A₁) (ha : IsPullback a f f₁ (Spec.map (CommRingCat.ofHom S₁.val.toRingHom)))
      (hLa : ∀ (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t f),
        (L.mul t P Q).1 ≫ a = (L₁.mul (t ≫ Spec.map (CommRingCat.ofHom S₁.val.toRingHom))
          ⟨P.1 ≫ a, by rw [Category.assoc, ha.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ a, by rw [Category.assoc, ha.w, ← Category.assoc, Q.2]⟩).1)
      (M₁ : RigidifiedLineBundle (prodStr f₁ f₁) ((L₁.prod L₁).one (𝟙 (Spec (CommRingCat.of ↥S₁))))
        f₁)
    (hM : Nonempty (M.L ≅ (Scheme.Modules.pullback
        (pullback.map (prodStr f f) f (prodStr f₁ f₁) f₁
          (pullback.map f f f₁ f₁ a a (Spec.map (CommRingCat.ofHom S₁.val.toRingHom)) ha.w.symm
            ha.w.symm)
          a (Spec.map (CommRingCat.ofHom S₁.val.toRingHom))
          (by
            have h1 : pullback.map f f f₁ f₁ a a (Spec.map (CommRingCat.ofHom S₁.val.toRingHom))
              ha.w.symm ha.w.symm ≫
                pullback.fst f₁ f₁ = pullback.fst f f ≫ a := pullback.lift_fst _ _ _
            change (pullback.fst f f ≫ f) ≫ Spec.map (CommRingCat.ofHom S₁.val.toRingHom) =
              pullback.map f f f₁ f₁ a a (Spec.map (CommRingCat.ofHom S₁.val.toRingHom)) ha.w.symm
                ha.w.symm ≫
                pullback.fst f₁ f₁ ≫ f₁
            rw [Category.assoc, ← Category.assoc (pullback.map _ _ _ _ _ _ _ _ _), h1,
              Category.assoc, ha.w])
          ha.w.symm)).obj M₁.L)) :
    ∃ (S₀ : Type) (_ : CommRing S₀) (_ : IsNoetherianRing S₀) (A₀ : Scheme) (f₀ : A₀ ⟶ Spec
      (CommRingCat.of S₀))
      (L₀ : RelativeGroupLaw S₀ f₀) (_ : AbelianSchemePropertyBundle S₀ f₀)
      (M₀ : RigidifiedLineBundle (prodStr f₀ f₀) ((L₀.prod L₀).one (𝟙 (Spec (CommRingCat.of S₀))))
        f₀),
      LocIsoOnBase (prodStr f₀ f₀)
        ((Scheme.Modules.pullback
          (pullback.lift
            (pullback.lift (L₀.one (prodStr f₀ f₀)).1 (pullback.fst f₀ f₀) (by rw [(L₀.one _).2]))
            (pullback.snd f₀ f₀)
            (by
              rw [pullback.lift_fst_assoc, (L₀.one _).2]
              exact pullback.condition))).obj M₀.L) (𝟙_ _) ∧
      LocIsoOnBase (prodStr f₀ f₀)
        ((Scheme.Modules.pullback
          (pullback.lift
            (pullback.lift (pullback.fst f₀ f₀) (L₀.one (prodStr f₀ f₀)).1 (by rw [(L₀.one _).2]))
            (pullback.snd f₀ f₀)
            (by rw [pullback.lift_fst_assoc]; exact pullback.condition))).obj M₀.L) (𝟙_ _) ∧
      LocIsoOnBase (prodStr f₀ f₀)
        ((Scheme.Modules.pullback
          (pullback.lift (𝟙 _) (L₀.one (prodStr f₀ f₀)).1
            (by rw [Category.id_comp, (L₀.one _).2]))).obj M₀.L) (𝟙_ _) ∧
      (Nonempty (M₀.L ≅ (RigidifiedLineBundle.unit (c := prodStr f₀ f₀) (ε := (L₀.prod L₀).one (𝟙
        (Spec (CommRingCat.of S₀)))) f₀).L) →
        Nonempty (M.L ≅ (RigidifiedLineBundle.unit (c := prodStr f f) (ε := (L.prod L).one (𝟙 (Spec
          (CommRingCat.of S)))) f).L)) := by
  classical
  obtain ⟨eM⟩ := hM
  have : IsProper f₁ := hA₁.proper
  have : QuasiCompact (prodStr f₁ f₁) := inferInstance
  have : QuasiSeparated (prodStr f₁ f₁) := inferInstance
  have hne : Nonempty (Idx S₁) := nonempty S₁ hS₁
  have hDL := isDirectLimit S₁ hS₁
  let i₀ : Idx S₁ := ⟨S₁, hS₁, le_rfl⟩
  have hF := AlgebraicGeometry.Polarisation.locIsoOnBase_faces_pullback_cube_iff_of_isPullback L₁
    S₁.val.toRingHom L a ha hLa M₁.L
  have EQ := AlgebraicGeometry.Polarisation.LocIsoOnBase.equivalence (prodStr f f)
  have d₁ := hF.1.mp (EQ.trans (ofIso _ ((Scheme.Modules.pullback _).mapIso eM).symm) h₁)
  have d₂ := hF.2.1.mp (EQ.trans (ofIso _ ((Scheme.Modules.pullback _).mapIso eM).symm) h₂)
  have d₃ := hF.2.2.mp (EQ.trans (ofIso _ ((Scheme.Modules.pullback _).mapIso eM).symm) h₃)
  obtain ⟨k₁, hk₁, e₁⟩ :=
    exists_locIsoOnBase_pullback_unit_stage_of_locIsoOnBase_pullback_unit_of_isDirectLimit
      (φ S₁) (g S₁) hDL i₀ (prodStr f₁ f₁) _ ((M₁.isInvertible).pullback _) d₁
  obtain ⟨k₂, hk₂, e₂⟩ :=
    exists_locIsoOnBase_pullback_unit_stage_of_locIsoOnBase_pullback_unit_of_isDirectLimit
      (φ S₁) (g S₁) hDL i₀ (prodStr f₁ f₁) _ ((M₁.isInvertible).pullback _) d₂
  obtain ⟨k₃, hk₃, e₃⟩ :=
    exists_locIsoOnBase_pullback_unit_stage_of_locIsoOnBase_pullback_unit_of_isDirectLimit
      (φ S₁) (g S₁) hDL i₀ (prodStr f₁ f₁) _ ((M₁.isInvertible).pullback _) d₃
  obtain ⟨k₁₂, h₁, h₂'⟩ := exists_ge_ge k₁ k₂
  obtain ⟨k, h₁₂, h₃'⟩ := exists_ge_ge k₁₂ k₃
  have hk : i₀ ≤ k := hk₁.trans (h₁.trans h₁₂)
  have r₁ := rebase (prodStr f₁ f₁) (φ S₁ i₀ k₁ hk₁) (φ S₁ i₀ k hk) (φ S₁ k₁ k (h₁.trans h₁₂)) rfl
    _ e₁
  have r₂ := rebase (prodStr f₁ f₁) (φ S₁ i₀ k₂ hk₂) (φ S₁ i₀ k hk) (φ S₁ k₂ k (h₂'.trans h₁₂)) rfl
    _ e₂
  have r₃ := rebase (prodStr f₁ f₁) (φ S₁ i₀ k₃ hk₃) (φ S₁ i₀ k hk) (φ S₁ k₃ k h₃') rfl _ e₃
  let S₀ : Type := G S₁ k
  have : IsNoetherianRing S₀ := by
    have : Algebra.FiniteType ℤ ↥k.1 := (Subalgebra.fg_iff_finiteType _).mp k.2.1
    exact Algebra.FiniteType.isNoetherianRing ℤ ↥k.1
  let σ : Spec (CommRingCat.of S₀) ⟶ Spec (CommRingCat.of ↥S₁) := Spec.map (CommRingCat.ofHom (φ S₁
    i₀ k hk))
  let f₀ : pullback f₁ σ ⟶ Spec (CommRingCat.of S₀) := pullback.snd f₁ σ
  let L₀ : RelativeGroupLaw S₀ f₀ := L₁.baseChange σ
  have ha₀ : IsPullback (pullback.fst f₁ σ) f₀ f₁ σ := IsPullback.of_hasPullback f₁ σ
  have hA₀ : AbelianSchemePropertyBundle S₀ f₀ :=
    GoodReductionJacobian.AbelianSchemePropertyBundle.of_isPullback hA₁ ha₀
  have hLa₀ : ∀ (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of S₀)) (P Q : SchemeHomOver t f₀),
      (L₀.mul t P Q).1 ≫ pullback.fst f₁ σ = (L₁.mul (t ≫ σ)
        ⟨P.1 ≫ pullback.fst f₁ σ, by rw [Category.assoc, ha₀.w, ← Category.assoc, P.2]⟩
        ⟨Q.1 ≫ pullback.fst f₁ σ, by rw [Category.assoc, ha₀.w, ← Category.assoc, Q.2]⟩).1 :=
    fun T t P Q => congrArg Subtype.val (L₁.baseChangePointToBase_mul σ t P Q)
  obtain ⟨M₀, hM₀⟩ := exists_rigidified_cube_pullback_of_isPullback
    L₁ (φ S₁ i₀ k hk) L₀ (pullback.fst f₁ σ) ha₀ hLa₀ M₁
  have hF₀ := AlgebraicGeometry.Polarisation.locIsoOnBase_faces_pullback_cube_iff_of_isPullback
    L₁ (φ S₁ i₀ k hk) L₀ (pullback.fst f₁ σ) ha₀ hLa₀ M₁.L
  refine ⟨S₀, inferInstance, inferInstance, pullback f₁ σ, f₀, L₀, hA₀, M₀, ?_, ?_, ?_, ?_⟩
  · rw [hM₀]; exact hF₀.1.mpr r₁
  · rw [hM₀]; exact hF₀.2.1.mpr r₂
  · rw [hM₀]; exact hF₀.2.2.mpr r₃
  · rintro ⟨e₀⟩
    have hσ : Spec.map (CommRingCat.ofHom (g S₁ k)) ≫ σ = Spec.map (CommRingCat.ofHom
      S₁.val.toRingHom) := by
      change Spec.map (CommRingCat.ofHom (g S₁ k)) ≫ Spec.map (CommRingCat.ofHom (φ S₁ i₀ k hk)) = _
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
      rfl
    let ψ : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of S₀) := Spec.map (CommRingCat.ofHom (g S₁
      k))
    let c : A ⟶ pullback f₁ σ := pullback.lift a (f ≫ ψ) (by rw [Category.assoc, hσ]; exact ha.w)
    have hc₁ : c ≫ pullback.fst f₁ σ = a := pullback.lift_fst _ _ _
    have hc₂ : c ≫ f₀ = f ≫ ψ := pullback.lift_snd _ _ _
    let cc : pullback f f ⟶ pullback f₀ f₀ := pullback.map f f f₀ f₀ c c ψ hc₂.symm hc₂.symm
    have hcc₁ : cc ≫ pullback.fst f₀ f₀ = pullback.fst f f ≫ c := pullback.lift_fst _ _ _
    have hcc₂ : cc ≫ pullback.snd f₀ f₀ = pullback.snd f f ≫ c := pullback.lift_snd _ _ _
    let γ : pullback (prodStr f f) f ⟶ pullback (prodStr f₀ f₀) f₀ :=
      pullback.map (prodStr f f) f (prodStr f₀ f₀) f₀ cc c ψ
        (by
          change (pullback.fst f f ≫ f) ≫ ψ = cc ≫ pullback.fst f₀ f₀ ≫ f₀
          rw [← Category.assoc, hcc₁, Category.assoc, Category.assoc, hc₂])
        hc₂.symm
    have hγ₁ : γ ≫ pullback.fst (prodStr f₀ f₀) f₀ = pullback.fst (prodStr f f) f ≫ cc :=
      pullback.lift_fst _ _ _
    have hγ₂ : γ ≫ pullback.snd (prodStr f₀ f₀) f₀ = pullback.snd (prodStr f f) f ≫ c :=
      pullback.lift_snd _ _ _
    let aa := pullback.map f f f₁ f₁ a a (Spec.map (CommRingCat.ofHom S₁.val.toRingHom)) ha.w.symm
      ha.w.symm
    have haa₁ : aa ≫ pullback.fst f₁ f₁ = pullback.fst f f ≫ a := pullback.lift_fst _ _ _
    have haa₂ : aa ≫ pullback.snd f₁ f₁ = pullback.snd f f ≫ a := pullback.lift_snd _ _ _
    let bb := pullback.map f₀ f₀ f₁ f₁ (pullback.fst f₁ σ) (pullback.fst f₁ σ) σ ha₀.w.symm
      ha₀.w.symm
    have hbb₁ : bb ≫ pullback.fst f₁ f₁ = pullback.fst f₀ f₀ ≫ pullback.fst f₁ σ :=
      pullback.lift_fst _ _ _
    have hbb₂ : bb ≫ pullback.snd f₁ f₁ = pullback.snd f₀ f₀ ≫ pullback.fst f₁ σ :=
      pullback.lift_snd _ _ _
    have hccbb : cc ≫ bb = aa := by
      apply pullback.hom_ext
      · rw [Category.assoc, hbb₁, ← Category.assoc, hcc₁, Category.assoc, hc₁, haa₁]
      · rw [Category.assoc, hbb₂, ← Category.assoc, hcc₂, Category.assoc, hc₁, haa₂]
    obtain ⟨AAA, hAAA₁, hAAA₂, ⟨hAAA⟩⟩ : ∃ AAA : pullback (prodStr f f) f ⟶ pullback (prodStr f₁
      f₁) f₁,
        AAA ≫ pullback.fst _ _ = pullback.fst _ _ ≫ aa ∧ AAA ≫ pullback.snd _ _ = pullback.snd _ _
          ≫ a ∧
          Nonempty (M.L ≅ (Scheme.Modules.pullback AAA).obj M₁.L) :=
      ⟨_, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _, ⟨eM⟩⟩
    obtain ⟨BBB, hBBB, hBBB₁, hBBB₂⟩ : ∃ BBB : pullback (prodStr f₀ f₀) f₀ ⟶ pullback (prodStr f₁
      f₁) f₁,
        M₀.L = (Scheme.Modules.pullback BBB).obj M₁.L ∧ BBB ≫ pullback.fst _ _ = pullback.fst _ _ ≫
          bb ∧
          BBB ≫ pullback.snd _ _ = pullback.snd _ _ ≫ pullback.fst f₁ σ :=
      ⟨_, hM₀, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
    have key : γ ≫ BBB = AAA := by
      apply pullback.hom_ext
      · rw [Category.assoc, hBBB₁, ← Category.assoc, hγ₁, Category.assoc, hccbb, hAAA₁]
      · rw [Category.assoc, hBBB₂, ← Category.assoc, hγ₂, Category.assoc, hc₁, hAAA₂]
    refine ⟨hAAA ≪≫ (Scheme.Modules.pullbackCongr key.symm).app M₁.L ≪≫
      ((Scheme.Modules.pullbackComp γ BBB).app M₁.L).symm ≪≫
      (Scheme.Modules.pullback γ).mapIso (eqToIso hBBB.symm ≪≫ e₀) ≪≫
        Scheme.Modules.pullbackUnitIso γ⟩
end AlgebraicGeometry.RelPicard.RigidifiedLineBundle
end ProofImplementation

attribute [-instance]
  IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty
  PresheafOfModules.PullbackMonoidal.pullback_monoidal
  PresheafOfModules.PullbackMonoidal.isIso_δ
  PresheafOfModules.pushforward_laxMonoidal
  PresheafOfModules.PullbackMonoidal.isIso_η
  PresheafOfModules.free_monoidal
  PresheafOfModules.restrictScalars_laxMonoidal
  PresheafOfModules.PullbackMonoidal.isIso_δ_gS
  PresheafOfModules.pullback_oplaxMonoidal
open _root_.PresheafOfModules.PullbackMonoidal in
attribute [-instance]
  instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb
attribute [-instance]
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
  TwoChartCech.Cover.A0_commRing
  TwoChartCech.Sections.M1_tower
  TwoChartCech.Sections.M01_moduleA
  TwoChartCech.Sections.M0_module
  TwoChartCech.Sections.M1_moduleA
  TwoChartCech.Sections.M1_addCommGroup
  TwoChartCech.Cover.A01_commRing
  TwoChartCech.Sections.M01_tower
  CoherentBaseChange.TwoTermComplex.C0_module
  CoherentBaseChange.TwoTermComplex.C0_addCommGroup
  CoherentBaseChange.TwoTermComplex.C1_module
  CoherentBaseChange.TwoTermComplex.C1_addCommGroup
attribute [-instance]
  CoherentBaseChange.TwoTermComplex.C0_free
  CoherentBaseChange.TwoTermComplex.C1_finite
  CoherentBaseChange.TwoTermComplex.C0_finite
  CoherentBaseChange.TwoTermComplex.C1_free
  SheafOfModules.isIso_ihomModelToIhom
attribute [-simp]
  GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase
  GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe
  GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe
  GoodReductionJacobian.RelativeGroupLaw.baseChange_inv
  GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase
  GoodReductionJacobian.RelativeGroupLaw.baseChange_mul
  GoodReductionJacobian.RelativeGroupLaw.baseChange_one
  NeronModelInfra.fibreRestrictAlong_coe_comp_snd
  NeronModelInfra.fibreRestrictAlong_coe_comp_fst
  NeronModelInfra.fibreRestrictAlong_coe_comp_fst_assoc
  NeronModelInfra.fibreRestrictAlong_coe_comp_snd_assoc
  GoodReductionJacobian.RelativeGroupLaw.fibre_inv
  GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe
  GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase
  GoodReductionJacobian.RelativeGroupLaw.fibre_mul
  GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase
  GoodReductionJacobian.RelativeGroupLaw.fibre_one
  GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe
  IsDirectLimit.Module.linearEquiv_symm_apply
  IsDirectLimit.linearEquiv_symm_apply
  IsDirectLimit.lift_of
  IsDirectLimit.Module.linearEquiv_apply
  IsDirectLimit.Module.lift_of
  IsDirectLimit.Equiv_apply
  PresheafOfModules.freeεIso_hom_app
  PresheafOfModules.freeμIso_hom_app
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right
  AlgebraicGeometry.Scheme.Modules.map_unitSection
  AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply
  AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero
attribute [-simp]
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left
  AlgebraicGeometry.Scheme.Modules.tensorPow_zero
  AlgebraicGeometry.Scheme.Modules.tensorPow_succ
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0
  TwoChartCech.Sections.mk.injEq
  TwoChartCech.Cover.mk.injEq
  TwoChartCech.GrothendieckComplex.mk.injEq
  TwoChartCech.Sections.mk.sizeOf_spec
  TwoChartCech.Cover.mk.sizeOf_spec
  TwoChartCech.Cover.lineBundle_r0_apply
  TwoChartCech.GrothendieckComplex.mk.sizeOf_spec
  TwoChartCech.Cover.lineBundle_r1_apply
  CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec
  CoherentBaseChange.TwoTermComplex.mk.injEq
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
  AlgebraicGeometry.schemeFibreEndo_snd
  AlgebraicGeometry.schemeFibreEndo_fst
