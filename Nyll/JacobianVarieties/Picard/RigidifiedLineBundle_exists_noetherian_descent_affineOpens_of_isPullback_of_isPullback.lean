/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_exists_noetherian_descent_affineOpens_of_isPullback_of_isPullback.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Spec
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.RingTheory.FiniteType
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.Algebra.Algebra.Subalgebra.Tower
import Mathlib.Order.DirectedInverseSystem
import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.JacobianVarieties.Picard.Representation
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroCut
import Nyll.AlgebraicCurves.Geometry.Picard.PolarisationRosati
import Nyll.AlgebraicCurves.Foundations.Algebra.Mathlib_Algebra_IsDirectLimit
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.Theorems.RelativeGroupLaw_exists_isPullback_comp_eq_mul_eq_of_isPullback_of_comp_eq
import Nyll.AlgebraicCurves.Geometry.Schemes.isPullback_pullbackMap_fst_comp_of_isPullback_of_isPullback
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_exists_isInvertible_pullback_map_iso_unit_nonempty_pullback_iso_of_isDirectLimit

/-!
Noetherian descent of rigidified line bundles on affine opens.
Finite subalgebra stages descend the group law, the invertible module and its rigidification.
-/

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.NoetherianAffineDescent
attribute [-instance]
  AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instSMulFamilies
  AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instModulePreGlue
  AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instModuleFamilies
  SheafOfModules.isIso_ihomModelToIhom
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
attribute [-instance]
  CoherentBaseChange.TwoTermComplex.C0_addCommGroup
  CoherentBaseChange.TwoTermComplex.C1_module
  CoherentBaseChange.TwoTermComplex.C1_addCommGroup
  CoherentBaseChange.TwoTermComplex.C0_free
  CoherentBaseChange.TwoTermComplex.C1_finite
  CoherentBaseChange.TwoTermComplex.C0_finite
  CoherentBaseChange.TwoTermComplex.C1_free
attribute [-simp]
  GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase
  GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe
  GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe
  GoodReductionJacobian.RelativeGroupLaw.baseChange_inv
  GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase
  GoodReductionJacobian.RelativeGroupLaw.baseChange_mul
  GoodReductionJacobian.RelativeGroupLaw.baseChange_one
  NeronModelInfra.schemeHomOverComp_id_left
  NeronModelInfra.schemeHomOverComp_id_right
  NeronModelInfra.schemeHomOverId_coe
  NeronModelInfra.schemeHomOverComp_coe
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
  AlgebraicGeometry.schemeFibreEndo_snd
  AlgebraicGeometry.schemeFibreEndo_fst
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right
  AlgebraicGeometry.Scheme.Modules.map_unitSection
attribute [-simp]
  AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply
  AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left
  AlgebraicGeometry.Scheme.Modules.tensorPow_zero
  AlgebraicGeometry.Scheme.Modules.tensorPow_succ
  AlgebraicGeometry.Scheme.Modules.glueComponent_glueMk
  AlgebraicGeometry.Scheme.Modules.UnitCocycle.mk.injEq
  AlgebraicGeometry.Scheme.Modules.UnitCocycle.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add
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
  PresheafOfModules.freeεIso_hom_app
  PresheafOfModules.freeμIso_hom_app
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
attribute [-simp] CoherentBaseChange.TwoTermComplex.mk.injEq

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.RelPicard
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian
open _root_.AlgebraicGeometry.Polarisation

noncomputable section

namespace RigidifiedDescentAux

namespace FGStages

variable {A₀ : Type} [CommRing A₀] {A : Type} [CommRing A] [Algebra A₀ A] (B : Subalgebra A₀ A)

/-- The finitely generated subalgebras containing the prescribed stage. -/
abbrev Idx : Type := {T : Subalgebra A₀ A // T.FG ∧ B ≤ T}

/-- The ring of a finitely generated stage. -/
abbrev G (i : Idx B) : Type := ↥i.1

/-- The inclusion between comparable stages. -/
abbrev φ (i j : Idx B) (h : i ≤ j) :
    G B i →+* G B j := (Subalgebra.inclusion (show i.1 ≤ j.1 from h)).toRingHom

/-- The canonical map from a stage to the ambient algebra. -/
abbrev g (i : Idx B) : G B i →+* A := algebraMap ↥i.1 A

/-- Stage transition maps preserve the underlying ambient element. -/
theorem φ_apply (i j : Idx B) (h : i ≤ j) (x : G B i) : (φ B i j h x : A) = (x : A) := rfl
/-- The stage map is the subtype inclusion. -/
theorem g_apply (i : Idx B) (x : G B i) : g B i x = (x : A) := rfl

scoped instance : DirectedSystem (G B) (fun i j h => ⇑(φ B i j h)) where
  map_self _ _ := rfl
  map_map _ _ _ _ _ _ := rfl

private def _root_.RigidifiedDescentAux.FGStages.sup (i j : Idx B) :
    Idx B := ⟨i.1 ⊔ j.1, i.2.1.sup j.2.1, le_sup_of_le_left i.2.2⟩

export _root_.RigidifiedDescentAux.FGStages (sup)

scoped instance : IsDirected (Idx B) (· ≤ ·) :=
  ⟨fun i j => ⟨sup B i j, (le_sup_left : i.1 ≤ i.1 ⊔ j.1), (le_sup_right : j.1 ≤ i.1 ⊔ j.1)⟩⟩

/-- A finitely generated initial stage gives an inhabited index type. -/
theorem nonempty (hB : B.FG) : Nonempty (Idx B) := ⟨⟨B, hB, le_rfl⟩⟩

/-- The finitely generated stages have the ambient algebra as their direct limit. -/
theorem isDirectLimit (hB : B.FG) : IsDirectLimit (fun i j h => ⇑(φ B i j h)) (fun i => ⇑(g B i))
  where
  surj m := by
    refine ⟨⟨B ⊔ Algebra.adjoin A₀ {m}, hB.sup ⟨{m},
      by rw [Finset.coe_singleton]⟩, le_sup_left⟩, ⟨m, ?_⟩, rfl⟩
    exact Algebra.mem_sup_right (Algebra.self_mem_adjoin_singleton A₀ m)
  inj i j mi mj h := ⟨sup B i j, (le_sup_left : i.1 ≤ i.1 ⊔ j.1), (le_sup_right : j.1 ≤ i.1 ⊔ j.1),
    Subtype.ext h⟩
  compatibility _ _ _ _ := rfl

/-- The stage maps commute with transitions. -/
theorem g_comp_φ (i j : Idx B) (h : i ≤ j) : (g B j).comp (φ B i j h) = g B i := RingHom.ext fun _
  => rfl

private theorem _root_.RigidifiedDescentAux.FGStages.isNoetherianRing [IsNoetherianRing A₀]
    (i : Idx B) : IsNoetherianRing (G B i) := by
  have := (Subalgebra.fg_iff_finiteType i.1).mp i.2.1
  exact Algebra.FiniteType.isNoetherianRing A₀ ↥i.1

export _root_.RigidifiedDescentAux.FGStages (isNoetherianRing)

end FGStages

open scoped
  _root_.JacobianVarieties.Picard.Proofs.NoetherianAffineDescent.RigidifiedDescentAux.FGStages

/-- A multiplication-compatible pullback map preserves the identity section. -/
theorem one_comp_eq_one {R R₁ : Type} [CommRing R] [CommRing R₁] {A A₁ : Scheme.{0}}
    {f : A ⟶ Spec (CommRingCat.of R)} {f₁ : A₁ ⟶ Spec (CommRingCat.of R₁)}
    (L : RelativeGroupLaw R f) (L₁ : RelativeGroupLaw R₁ f₁) (φ : R₁ →+* R)
    (a : A ⟶ A₁) (ha : IsPullback a f f₁ (Spec.map (CommRingCat.ofHom φ)))
    (hLa : ∀ (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
      (L.mul t P Q).1 ≫ a = (L₁.mul (t ≫ Spec.map (CommRingCat.ofHom φ))
        ⟨P.1 ≫ a, by rw [Category.assoc, ha.w, ← Category.assoc, P.2]⟩
        ⟨Q.1 ≫ a, by rw [Category.assoc, ha.w, ← Category.assoc, Q.2]⟩).1)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) :
    (L.one t).1 ≫ a = (L₁.one (t ≫ Spec.map (CommRingCat.ofHom φ))).1 := by
  have key : ∀ {t₁ : T ⟶ Spec (CommRingCat.of R₁)} (x : SchemeHomOver t₁ f₁), L₁.mul t₁ x x = x → x
    = L₁.one t₁ := by
    intro t₁ x hxx
    calc x = L₁.mul t₁ (L₁.mul t₁ (L₁.inv t₁ x) x) x := by rw [L₁.inv_mul_cancel, L₁.one_mul]
      _ = L₁.mul t₁ (L₁.inv t₁ x) (L₁.mul t₁ x x) := by rw [L₁.mul_assoc]
      _ = L₁.one t₁ := by rw [hxx, L₁.inv_mul_cancel]
  have h := hLa T t (L.one t) (L.one t)
  rw [L.one_mul] at h
  exact congrArg Subtype.val (key ⟨(L.one t).1 ≫ a,
    by rw [Category.assoc, ha.w, ← Category.assoc, (L.one t).2]⟩
    (Subtype.ext h.symm))

/-- Every identity section is pulled back from the identity over the base. -/
theorem one_coe_eq_comp_one {R : Type} [CommRing R] {A : Scheme.{0}}
    {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) :
    (L.one t).1 = t ≫ (L.one (𝟙 (Spec (CommRingCat.of R)))).1 := by
  have h := L.one_natural (𝟙 (Spec (CommRingCat.of R))) t t (Category.comp_id t)
  exact (congrArg Subtype.val h).symm

section Sections

variable {R R₁ : Type} [CommRing R] [CommRing R₁]

/-- The first projection of the rigidifying section. -/
@[reassoc] theorem rigSection_fst {C T : Scheme.{0}} (c : C ⟶ Spec (CommRingCat.of R))
    (t : T ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) : rigSection c t ε ≫ pullback.fst c t = t ≫
      ε.1 :=
  pullback.lift_fst _ _ _

/-- The second projection of the rigidifying section. -/
@[reassoc] theorem rigSection_snd {C T : Scheme.{0}} (c : C ⟶ Spec (CommRingCat.of R))
    (t : T ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) : rigSection c t ε ≫ pullback.snd c t = 𝟙 T
      :=
  pullback.lift_snd _ _ _

/-- The rigidifying section lies over the given base map. -/
theorem rigSection_fst_comp {C T : Scheme.{0}} (c : C ⟶ Spec (CommRingCat.of R))
    (t : T ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) : rigSection c t ε ≫ (pullback.fst c t ≫ c)
      = t := by
  rw [← Category.assoc, rigSection_fst, Category.assoc, ε.2, Category.comp_id]

variable {A T A₁ X₁ : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of R)) (t : T ⟶ Spec (CommRingCat.of
  R))
  (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f)
  (f₁ : A₁ ⟶ Spec (CommRingCat.of R₁)) (g₁ : X₁ ⟶ Spec (CommRingCat.of R₁))
  (ε₁ : SchemeHomOver (𝟙 (Spec (CommRingCat.of R₁))) f₁)
  (ι : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of R₁)) (a : A ⟶ A₁) (u : T ⟶ X₁)
  (e₁ : f ≫ ι = a ≫ f₁) (e₂ : t ≫ ι = u ≫ g₁) (hε : ε.1 ≫ a = ι ≫ ε₁.1)

include hε in
/-- Compatible pullback maps transport rigidifying sections. -/
theorem rigSection_comp_pullbackMap :
    rigSection f t ε ≫ pullback.map f t f₁ g₁ a u ι e₁ e₂ = u ≫ rigSection f₁ g₁ ε₁ := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, rigSection_fst_assoc, Category.assoc, hε, ←
      Category.assoc, e₂,
      Category.assoc, rigSection_fst]
  · rw [Category.assoc, pullback.lift_snd, rigSection_snd_assoc, Category.assoc, rigSection_snd,
      Category.comp_id]

include hε in
/-- The iterated pullback comparison transports the rigidifying section. -/
theorem rigSection_comp_eq_comp_pullbackMap_rigSection
    (d : pullback f t ⟶ pullback (pullback.fst f₁ g₁ ≫ f₁) ι) (v : T ⟶ pullback g₁ ι)
    (hd₁ : d ≫ pullback.fst _ _ = pullback.map f t f₁ g₁ a u ι e₁ e₂) (hd₂ : d ≫ pullback.snd _ _ =
      pullback.fst f t ≫ f)
    (hv₁ : v ≫ pullback.fst _ _ = u) (hv₂ : v ≫ pullback.snd _ _ = t)
    (e₃ : g₁ ≫ 𝟙 _ = rigSection f₁ g₁ ε₁ ≫ (pullback.fst f₁ g₁ ≫ f₁)) (e₄ : ι ≫ 𝟙 _ = 𝟙 _ ≫ ι) :
    rigSection f t ε ≫ d =
      v ≫ pullback.map g₁ ι (pullback.fst f₁ g₁ ≫ f₁) ι (rigSection f₁ g₁ ε₁) (𝟙 _) (𝟙 _) e₃ e₄
        := by
  apply pullback.hom_ext
  · rw [Category.assoc, hd₁, rigSection_comp_pullbackMap f t ε f₁ g₁ ε₁ ι a u e₁ e₂ hε,
      Category.assoc,
      pullback.lift_fst, ← Category.assoc, hv₁]
  · rw [Category.assoc, hd₂, rigSection_fst_comp, Category.assoc, pullback.lift_snd,
      Category.comp_id, hv₂]

end Sections

open scoped
  _root_.JacobianVarieties.Picard.Proofs.NoetherianAffineDescent.RigidifiedDescentAux.FGStages

section Modules

/-- Transport a trivialization through compatible pullback isomorphisms. -/
theorem nonempty_pullback_pullback_iso_unit {U XR Q P : Scheme.{0}} (eU : U ≅ XR) (e : Q ≅ P)
    (r : U ⟶ Q) (sR : XR ⟶ P)
    (h : eU.hom ≫ sR = r ≫ e.hom) (N : Q.Modules)
    (hN : Nonempty ((Scheme.Modules.pullback r).obj N ≅ SheafOfModules.unit U.ringCatSheaf)) :
    Nonempty ((Scheme.Modules.pullback sR).obj ((Scheme.Modules.pullback e.inv).obj N) ≅
      SheafOfModules.unit XR.ringCatSheaf) := by
  have h' : sR ≫ e.inv = eU.inv ≫ r := by
    rw [← cancel_epi eU.hom, ← Category.assoc, h, Category.assoc, e.hom_inv_id, Category.comp_id,
      eU.hom_inv_id_assoc]
  exact ⟨(Scheme.Modules.pullbackComp sR e.inv).app N ≪≫ (Scheme.Modules.pullbackCongr h').app N ≪≫
    ((Scheme.Modules.pullbackComp eU.inv r).app N).symm ≪≫ (Scheme.Modules.pullback eU.inv).mapIso
      hN.some ≪≫
    Scheme.Modules.pullbackUnitIso eU.inv⟩

/-- Recover a pullback isomorphism through an isomorphism of source schemes. -/
theorem nonempty_iso_pullback {X P P' : Scheme.{0}} (e : X ≅ P) (cX : P ⟶ P') (gA : X ⟶ P')
    (hgA : gA = e.hom ≫ cX) (M' : P'.Modules) (N : X.Modules)
    (h : Nonempty ((Scheme.Modules.pullback cX).obj M' ≅ (Scheme.Modules.pullback e.inv).obj N)) :
    Nonempty (N ≅ (Scheme.Modules.pullback gA).obj M') := by
  obtain ⟨e₁⟩ := h
  exact ⟨((Scheme.Modules.pullbackCongr hgA).app M' ≪≫ ((Scheme.Modules.pullbackComp e.hom cX).app
    M').symm ≪≫
    (Scheme.Modules.pullback e.hom).mapIso e₁ ≪≫ (Scheme.Modules.pullbackComp e.hom e.inv).app N ≪≫
    (Scheme.Modules.pullbackCongr e.hom_inv_id).app N ≪≫ (Scheme.Modules.pullbackId X).app N).symm⟩

end Modules

open scoped
  _root_.JacobianVarieties.Picard.Proofs.NoetherianAffineDescent.RigidifiedDescentAux.FGStages

end RigidifiedDescentAux

open scoped
  _root_.JacobianVarieties.Picard.Proofs.NoetherianAffineDescent.RigidifiedDescentAux.FGStages
open scoped _root_.JacobianVarieties.Picard.Proofs.NoetherianAffineDescent.RigidifiedDescentAux

end

open scoped
  _root_.JacobianVarieties.Picard.Proofs.NoetherianAffineDescent.RigidifiedDescentAux.FGStages
open scoped _root_.JacobianVarieties.Picard.Proofs.NoetherianAffineDescent.RigidifiedDescentAux

open _root_.JacobianVarieties.Picard.Proofs.NoetherianAffineDescent.RigidifiedDescentAux

end JacobianVarieties.Picard.Proofs.NoetherianAffineDescent

namespace AlgebraicGeometry.RelPicard.RigidifiedLineBundle
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
open scoped
  _root_.JacobianVarieties.Picard.Proofs.NoetherianAffineDescent.RigidifiedDescentAux.FGStages
open _root_.JacobianVarieties.Picard.Proofs.NoetherianAffineDescent.RigidifiedDescentAux in
open Scheme.Modules GoodReductionJacobian.RelativeGroupLaw in
/-- Descend an affine-open restriction and its rigidification to a Noetherian base model. -/
theorem
exists_noetherian_descent_affineOpens_of_isPullback_of_isPullback
    {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f)
    {X : Scheme.{0}} (g : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFinitePresentation g]
    (M : RigidifiedLineBundle f (L.one (𝟙 (Spec (CommRingCat.of R)))) g) (U : X.affineOpens)
    (S₁ : Subalgebra ℤ R) (hS₁ : S₁.FG)
    (A₁ : Scheme.{0}) (f₁ : A₁ ⟶ Spec (CommRingCat.of ↥S₁)) (L₁ : RelativeGroupLaw ↥S₁ f₁) (hA₁ :
      AbelianSchemePropertyBundle ↥S₁ f₁)
    (a₁ : A ⟶ A₁) (ha₁ : IsPullback a₁ f f₁ (Spec.map (CommRingCat.ofHom (algebraMap ↥S₁ R))))
    (hLa₁ : (∀ (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
      (L.mul t P Q).1 ≫ a₁ = (L₁.mul (t ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥S₁ R)))
        ⟨P.1 ≫ a₁, by rw [Category.assoc, ha₁.w, ← Category.assoc, P.2]⟩
        ⟨Q.1 ≫ a₁, by rw [Category.assoc, ha₁.w, ← Category.assoc, Q.2]⟩).1))
    (X₁ : Scheme.{0}) (g₁ : X₁ ⟶ Spec (CommRingCat.of ↥S₁)) [LocallyOfFiniteType g₁] [QuasiCompact
      g₁] [QuasiSeparated g₁]
    (u₁ : ((U : X.Opens) : Scheme.{0}) ⟶ X₁)
    (hu₁ : IsPullback u₁ ((U : X.Opens).ι ≫ g) g₁ (Spec.map (CommRingCat.ofHom (algebraMap ↥S₁
      R)))) :
    ∃ (R₀ : Type) (_ : CommRing R₀) (_ : IsNoetherianRing R₀) (φ : R₀ →+* R)
        (A₀ : Scheme.{0}) (f₀ : A₀ ⟶ Spec (CommRingCat.of R₀)) (L₀ : RelativeGroupLaw R₀ f₀) (_ :
          AbelianSchemePropertyBundle R₀ f₀)
        (X₀ : Scheme.{0}) (g₀ : X₀ ⟶ Spec (CommRingCat.of R₀)) (_ : LocallyOfFiniteType g₀)
        (M₀ : RigidifiedLineBundle f₀ (L₀.one (𝟙 (Spec (CommRingCat.of R₀)))) g₀)
        (a : A ⟶ A₀) (ha : IsPullback a f f₀ (Spec.map (CommRingCat.ofHom φ)))
        (u : ((U : X.Opens) : Scheme.{0}) ⟶ X₀) (hu : IsPullback u ((U : X.Opens).ι ≫ g) g₀
          (Spec.map (CommRingCat.ofHom φ))),
        (∀ (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
          (L.mul t P Q).1 ≫ a = (L₀.mul (t ≫ Spec.map (CommRingCat.ofHom φ))
            ⟨P.1 ≫ a, by rw [Category.assoc, ha.w, ← Category.assoc, P.2]⟩
            ⟨Q.1 ≫ a, by rw [Category.assoc, ha.w, ← Category.assoc, Q.2]⟩).1) ∧
        Nonempty ((M.pullbackAlong (⟨(U : X.Opens).ι, rfl⟩ : SchemeHomOver ((U : X.Opens).ι ≫ g)
          g)).L ≅
          (Scheme.Modules.pullback
            (pullback.map f ((U : X.Opens).ι ≫ g) f₀ g₀ a u (Spec.map (CommRingCat.ofHom φ))
              ha.w.symm hu.w.symm)).obj M₀.L) := by
  classical
  have := hA₁.proper
  have : Nonempty (FGStages.Idx S₁) := FGStages.nonempty S₁ hS₁
  have hqc : QuasiCompact (pullback.fst f₁ g₁ ≫ f₁) := inferInstance
  have hqs : QuasiSeparated (pullback.fst f₁ g₁ ≫ f₁) := inferInstance
  have hs₁ : (rigSection f₁ g₁ (L₁.one (𝟙 (Spec (CommRingCat.of ↥S₁))))) ≫ (pullback.fst f₁ g₁ ≫
    f₁) = g₁ := rigSection_fst_comp _ _ _
  have hε₁ : (L.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ a₁ = (Spec.map (CommRingCat.ofHom
    (algebraMap ↥S₁ R))) ≫ (L₁.one (𝟙 (Spec (CommRingCat.of ↥S₁)))).1 := by
    rw [one_comp_eq_one L L₁ (algebraMap ↥S₁ R) a₁ ha₁ hLa₁ (𝟙 _), one_coe_eq_comp_one L₁,
      Category.id_comp]
  have hc₁ := AlgebraicGeometry.isPullback_pullbackMap_fst_comp_of_isPullback_of_isPullback f₁ g₁
    (Spec.map (CommRingCat.ofHom (algebraMap ↥S₁ R))) f ((U : X.Opens).ι ≫ g) a₁ u₁ ha₁ hu₁
  have h𝓛 := (M.pullbackAlong (⟨(U : X.Opens).ι, rfl⟩ : SchemeHomOver ((U : X.Opens).ι ≫ g)
    g)).isInvertible.pullback hc₁.isoPullback.inv
  have hsq₁ : hu₁.isoPullback.hom ≫ pullback.map g₁ (Spec.map (CommRingCat.ofHom (algebraMap ↥S₁
    R))) (pullback.fst f₁ g₁ ≫ f₁) (Spec.map (CommRingCat.ofHom (algebraMap ↥S₁ R))) (rigSection f₁
    g₁ (L₁.one (𝟙 (Spec (CommRingCat.of ↥S₁))))) (𝟙 _) (𝟙 _)
        (by
          rw [hs₁, Category.comp_id]) (by rw [Category.comp_id, Category.id_comp]) =
      rigSection f ((U : X.Opens).ι ≫ g) (L.one (𝟙 (Spec (CommRingCat.of R)))) ≫
        hc₁.isoPullback.hom :=
    (rigSection_comp_eq_comp_pullbackMap_rigSection f ((U : X.Opens).ι ≫ g) (L.one (𝟙 (Spec
      (CommRingCat.of R)))) f₁ g₁ (L₁.one (𝟙 (Spec (CommRingCat.of ↥S₁)))) (Spec.map
      (CommRingCat.ofHom (algebraMap ↥S₁ R))) a₁ u₁ ha₁.w.symm hu₁.w.symm hε₁
      hc₁.isoPullback.hom hu₁.isoPullback.hom (IsPullback.isoPullback_hom_fst _)
        (IsPullback.isoPullback_hom_snd _)
      (IsPullback.isoPullback_hom_fst _) (IsPullback.isoPullback_hom_snd _)
      (by
        rw [hs₁, Category.comp_id]) (by rw [Category.comp_id, Category.id_comp])).symm
  have htriv := nonempty_pullback_pullback_iso_unit hu₁.isoPullback hc₁.isoPullback _ _ hsq₁ _
    (M.pullbackAlong (⟨(U : X.Opens).ι, rfl⟩ : SchemeHomOver ((U : X.Opens).ι ≫ g) g)).rigidified
  obtain ⟨k, hik, 𝓛k, h𝓛k, ⟨erig⟩, hcmp⟩ :=
    exists_isInvertible_pullback_map_iso_unit_nonempty_pullback_iso_of_isDirectLimit
      (FGStages.φ S₁) (FGStages.g S₁) (FGStages.isDirectLimit S₁ hS₁) (⟨S₁, hS₁, le_rfl⟩ :
        FGStages.Idx S₁)
      (pullback.fst f₁ g₁ ≫ f₁) g₁ (rigSection f₁ g₁ (L₁.one (𝟙 (Spec (CommRingCat.of ↥S₁))))) hs₁
        _ h𝓛 htriv
  have : IsNoetherianRing (FGStages.G S₁ k) := FGStages.isNoetherianRing S₁ k
  obtain ⟨A₂, f₂, L₂, hA₂, a₂, ha₂, b, hb, hab, hLa₂, hLb⟩ :=
    exists_isPullback_comp_eq_mul_eq_of_isPullback_of_comp_eq L
      (algebraMap ↥S₁ R) (FGStages.g S₁ k) (FGStages.φ S₁ (⟨S₁, hS₁, le_rfl⟩ : FGStages.Idx S₁) k
        hik) (FGStages.g_comp_φ S₁ (⟨S₁, hS₁, le_rfl⟩ : FGStages.Idx S₁) k hik)
      A₁ f₁ L₁ hA₁ a₁ ha₁ hLa₁
  have hSpec : (Spec.map (CommRingCat.ofHom (FGStages.g S₁ k))) ≫ (Spec.map (CommRingCat.ofHom
    (FGStages.φ S₁ (⟨S₁, hS₁, le_rfl⟩ : FGStages.Idx S₁) k hik))) = (Spec.map (CommRingCat.ofHom
    (algebraMap ↥S₁ R))) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, FGStages.g_comp_φ]
  obtain ⟨u₂, hu₂₁, hu₂₂⟩ : ∃ u₂ : ((U : X.Opens) : Scheme.{0}) ⟶ pullback g₁ (Spec.map
    (CommRingCat.ofHom (FGStages.φ S₁ (⟨S₁, hS₁, le_rfl⟩ : FGStages.Idx S₁) k hik))),
      u₂ ≫ pullback.fst g₁ (Spec.map (CommRingCat.ofHom (FGStages.φ S₁ (⟨S₁, hS₁, le_rfl⟩ :
        FGStages.Idx S₁) k hik))) = u₁ ∧ u₂ ≫ pullback.snd g₁ (Spec.map (CommRingCat.ofHom
        (FGStages.φ S₁ (⟨S₁, hS₁, le_rfl⟩ : FGStages.Idx S₁) k hik))) = ((U : X.Opens).ι ≫ g) ≫
        (Spec.map (CommRingCat.ofHom (FGStages.g S₁ k))) :=
    ⟨pullback.lift u₁ (((U : X.Opens).ι ≫ g) ≫ (Spec.map (CommRingCat.ofHom (FGStages.g S₁ k))))
      (by rw [Category.assoc, hSpec]; exact hu₁.w),
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have hu₂ : IsPullback u₂ ((U : X.Opens).ι ≫ g) (pullback.snd g₁ (Spec.map (CommRingCat.ofHom
    (FGStages.φ S₁ (⟨S₁, hS₁, le_rfl⟩ : FGStages.Idx S₁) k hik)))) (Spec.map (CommRingCat.ofHom
    (FGStages.g S₁ k))) := by
    refine IsPullback.of_right (h₁₂ := pullback.fst g₁ (Spec.map (CommRingCat.ofHom (FGStages.φ S₁
      (⟨S₁, hS₁, le_rfl⟩ : FGStages.Idx S₁) k hik)))) (v₁₃ := g₁) (h₂₂ := (Spec.map
      (CommRingCat.ofHom (FGStages.φ S₁ (⟨S₁, hS₁, le_rfl⟩ : FGStages.Idx S₁) k hik)))) ?_ hu₂₂
      (IsPullback.of_hasPullback g₁ (Spec.map (CommRingCat.ofHom (FGStages.φ S₁ (⟨S₁, hS₁, le_rfl⟩
        : FGStages.Idx S₁) k hik))))
    rw [hu₂₁, hSpec]
    exact hu₁
  have hε₂ : (L₂.one (𝟙 (Spec (CommRingCat.of (FGStages.G S₁ k))))).1 ≫ b = (Spec.map
    (CommRingCat.ofHom (FGStages.φ S₁ (⟨S₁, hS₁, le_rfl⟩ : FGStages.Idx S₁) k hik))) ≫ (L₁.one (𝟙
    (Spec (CommRingCat.of ↥S₁)))).1 := by
    rw [one_comp_eq_one L₂ L₁ (FGStages.φ S₁ (⟨S₁, hS₁, le_rfl⟩ : FGStages.Idx S₁) k hik) b hb hLb
      (𝟙 _), one_coe_eq_comp_one L₁, Category.id_comp]
  have hc₂ := AlgebraicGeometry.isPullback_pullbackMap_fst_comp_of_isPullback_of_isPullback f₁ g₁
    (Spec.map (CommRingCat.ofHom (FGStages.φ S₁ (⟨S₁, hS₁, le_rfl⟩ : FGStages.Idx S₁) k hik))) f₂
    (pullback.snd g₁ (Spec.map (CommRingCat.ofHom (FGStages.φ S₁ (⟨S₁, hS₁, le_rfl⟩ : FGStages.Idx
      S₁) k hik)))) b (pullback.fst g₁ (Spec.map (CommRingCat.ofHom (FGStages.φ S₁ (⟨S₁, hS₁,
      le_rfl⟩ : FGStages.Idx S₁) k hik)))) hb (IsPullback.of_hasPullback g₁ (Spec.map
      (CommRingCat.ofHom (FGStages.φ S₁ (⟨S₁, hS₁, le_rfl⟩ : FGStages.Idx S₁) k hik))))
  have hsq₂ := rigSection_comp_eq_comp_pullbackMap_rigSection f₂ (pullback.snd g₁ (Spec.map
    (CommRingCat.ofHom (FGStages.φ S₁ (⟨S₁, hS₁, le_rfl⟩ : FGStages.Idx S₁) k hik)))) (L₂.one (𝟙
    (Spec (CommRingCat.of (FGStages.G S₁ k))))) f₁ g₁ (L₁.one (𝟙 (Spec (CommRingCat.of ↥S₁))))
      (Spec.map (CommRingCat.ofHom (FGStages.φ S₁ (⟨S₁, hS₁, le_rfl⟩ : FGStages.Idx S₁) k hik))) b
        (pullback.fst g₁ (Spec.map (CommRingCat.ofHom (FGStages.φ S₁ (⟨S₁, hS₁, le_rfl⟩ :
        FGStages.Idx S₁) k hik)))) hb.w.symm (IsPullback.of_hasPullback g₁ (Spec.map
        (CommRingCat.ofHom (FGStages.φ S₁ (⟨S₁, hS₁, le_rfl⟩ : FGStages.Idx S₁) k hik)))).w.symm hε₂
      hc₂.isoPullback.hom (𝟙 _) (IsPullback.isoPullback_hom_fst _) (IsPullback.isoPullback_hom_snd
        _)
      (Category.id_comp _) (Category.id_comp _)
        (by rw [hs₁, Category.comp_id]) (by rw [Category.comp_id, Category.id_comp])
  rw [Category.id_comp] at hsq₂
  refine ⟨FGStages.G S₁ k, inferInstance, inferInstance, (FGStages.g S₁ k), A₂, f₂, L₂, hA₂,
    pullback g₁ (Spec.map (CommRingCat.ofHom (FGStages.φ S₁ (⟨S₁, hS₁, le_rfl⟩ : FGStages.Idx S₁) k
    hik))), pullback.snd g₁ (Spec.map (CommRingCat.ofHom (FGStages.φ S₁ (⟨S₁, hS₁, le_rfl⟩ :
    FGStages.Idx S₁) k hik))),
    inferInstance,
    { L := (Scheme.Modules.pullback hc₂.isoPullback.hom).obj 𝓛k
      isInvertible := h𝓛k.pullback _
      rigidified := ⟨(Scheme.Modules.pullbackComp _ _).app 𝓛k ≪≫ (Scheme.Modules.pullbackCongr
        hsq₂).app 𝓛k ≪≫ erig⟩ },
    a₂, ha₂, u₂, hu₂, hLa₂, ?_⟩
  have hmap : pullback.map f ((U : X.Opens).ι ≫ g) f₂ (pullback.snd g₁ (Spec.map (CommRingCat.ofHom
    (FGStages.φ S₁ (⟨S₁, hS₁, le_rfl⟩ : FGStages.Idx S₁) k hik)))) a₂ u₂ (Spec.map
    (CommRingCat.ofHom (FGStages.g S₁ k))) ha₂.w.symm hu₂.w.symm ≫
      pullback.map f₂ (pullback.snd g₁ (Spec.map (CommRingCat.ofHom (FGStages.φ S₁ (⟨S₁, hS₁,
        le_rfl⟩ : FGStages.Idx S₁) k hik)))) f₁ g₁ b (pullback.fst g₁ (Spec.map (CommRingCat.ofHom
        (FGStages.φ S₁ (⟨S₁, hS₁, le_rfl⟩ : FGStages.Idx S₁) k hik)))) (Spec.map (CommRingCat.ofHom
        (FGStages.φ S₁ (⟨S₁, hS₁, le_rfl⟩ : FGStages.Idx S₁) k hik))) hb.w.symm
        (IsPullback.of_hasPullback g₁ (Spec.map (CommRingCat.ofHom (FGStages.φ S₁ (⟨S₁, hS₁,
          le_rfl⟩ : FGStages.Idx S₁) k hik)))).w.symm =
      pullback.map f ((U : X.Opens).ι ≫ g) f₁ g₁ a₁ u₁ (Spec.map (CommRingCat.ofHom (algebraMap ↥S₁
        R))) ha₁.w.symm hu₁.w.symm := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, hab]
    · simp only [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, hu₂₁]
  have h₁ : (hc₁.isoPullback.inv ≫ pullback.map f ((U : X.Opens).ι ≫ g) f₂ (pullback.snd g₁
    (Spec.map (CommRingCat.ofHom (FGStages.φ S₁ (⟨S₁, hS₁, le_rfl⟩ : FGStages.Idx S₁) k hik)))) a₂
    u₂ (Spec.map (CommRingCat.ofHom (FGStages.g S₁ k))) ha₂.w.symm hu₂.w.symm ≫
        hc₂.isoPullback.hom) ≫ pullback.fst (pullback.fst f₁ g₁ ≫ f₁) (Spec.map (CommRingCat.ofHom
          (FGStages.φ S₁ (⟨S₁, hS₁, le_rfl⟩ : FGStages.Idx S₁) k hik))) = pullback.fst
          (pullback.fst f₁ g₁ ≫ f₁) (Spec.map (CommRingCat.ofHom (algebraMap ↥S₁ R))) := by
    simp only [Category.assoc, IsPullback.isoPullback_hom_fst, hmap]
    rw [Iso.inv_comp_eq]
    exact hc₁.isoPullback_hom_fst.symm
  have h₂ : (hc₁.isoPullback.inv ≫ pullback.map f ((U : X.Opens).ι ≫ g) f₂ (pullback.snd g₁
    (Spec.map (CommRingCat.ofHom (FGStages.φ S₁ (⟨S₁, hS₁, le_rfl⟩ : FGStages.Idx S₁) k hik)))) a₂
    u₂ (Spec.map (CommRingCat.ofHom (FGStages.g S₁ k))) ha₂.w.symm hu₂.w.symm ≫
        hc₂.isoPullback.hom) ≫ pullback.snd (pullback.fst f₁ g₁ ≫ f₁) (Spec.map (CommRingCat.ofHom
          (FGStages.φ S₁ (⟨S₁, hS₁, le_rfl⟩ : FGStages.Idx S₁) k hik))) = pullback.snd
          (pullback.fst f₁ g₁ ≫ f₁) (Spec.map (CommRingCat.ofHom (algebraMap ↥S₁ R))) ≫ (Spec.map
          (CommRingCat.ofHom (FGStages.g S₁ k))) := by
    simp only [Category.assoc, IsPullback.isoPullback_hom_snd, pullback.lift_fst_assoc, ha₂.w]
    rw [Iso.inv_comp_eq, hc₁.isoPullback_hom_snd_assoc, Category.assoc]
  have key := nonempty_iso_pullback hc₁.isoPullback
    (hc₁.isoPullback.inv ≫ pullback.map f ((U : X.Opens).ι ≫ g) f₂ (pullback.snd g₁ (Spec.map
      (CommRingCat.ofHom (FGStages.φ S₁ (⟨S₁, hS₁, le_rfl⟩ : FGStages.Idx S₁) k hik)))) a₂ u₂
      (Spec.map (CommRingCat.ofHom (FGStages.g S₁ k))) ha₂.w.symm hu₂.w.symm ≫
      hc₂.isoPullback.hom) _ (Iso.hom_inv_id_assoc _ _).symm 𝓛k _ (hcmp _ h₁ h₂)
  exact ⟨key.some ≪≫ ((Scheme.Modules.pullbackComp _ _).app 𝓛k).symm⟩
end AlgebraicGeometry.RelPicard.RigidifiedLineBundle
end ProofImplementation

attribute [-instance]
  IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty
  AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instSMulFamilies
  AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instModulePreGlue
  AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instModuleFamilies
  SheafOfModules.isIso_ihomModelToIhom
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
attribute [-instance]
  CoherentBaseChange.TwoTermComplex.C0_module
  CoherentBaseChange.TwoTermComplex.C0_addCommGroup
  CoherentBaseChange.TwoTermComplex.C1_module
  CoherentBaseChange.TwoTermComplex.C1_addCommGroup
  CoherentBaseChange.TwoTermComplex.C0_free
  CoherentBaseChange.TwoTermComplex.C1_finite
  CoherentBaseChange.TwoTermComplex.C0_finite
  CoherentBaseChange.TwoTermComplex.C1_free
attribute [-simp]
  IsDirectLimit.Module.linearEquiv_symm_apply
  IsDirectLimit.linearEquiv_symm_apply
  IsDirectLimit.lift_of
  IsDirectLimit.Module.linearEquiv_apply
  IsDirectLimit.Module.lift_of
  IsDirectLimit.Equiv_apply
  GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase
  GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe
  GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe
  GoodReductionJacobian.RelativeGroupLaw.baseChange_inv
  GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase
  GoodReductionJacobian.RelativeGroupLaw.baseChange_mul
  GoodReductionJacobian.RelativeGroupLaw.baseChange_one
  NeronModelInfra.schemeHomOverComp_id_left
  NeronModelInfra.schemeHomOverComp_id_right
  NeronModelInfra.schemeHomOverId_coe
  NeronModelInfra.schemeHomOverComp_coe
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
attribute [-simp]
  GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe
  AlgebraicGeometry.schemeFibreEndo_snd
  AlgebraicGeometry.schemeFibreEndo_fst
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right
  AlgebraicGeometry.Scheme.Modules.map_unitSection
  AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply
  AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left
  AlgebraicGeometry.Scheme.Modules.tensorPow_zero
  AlgebraicGeometry.Scheme.Modules.tensorPow_succ
  AlgebraicGeometry.Scheme.Modules.glueComponent_glueMk
  AlgebraicGeometry.Scheme.Modules.UnitCocycle.mk.injEq
  AlgebraicGeometry.Scheme.Modules.UnitCocycle.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add
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
  PresheafOfModules.freeεIso_hom_app
  PresheafOfModules.freeμIso_hom_app
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0
  TwoChartCech.Sections.mk.injEq
  TwoChartCech.Cover.mk.injEq
  TwoChartCech.GrothendieckComplex.mk.injEq
attribute [-simp]
  TwoChartCech.Sections.mk.sizeOf_spec
  TwoChartCech.Cover.mk.sizeOf_spec
  TwoChartCech.Cover.lineBundle_r0_apply
  TwoChartCech.GrothendieckComplex.mk.sizeOf_spec
  TwoChartCech.Cover.lineBundle_r1_apply
  CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec
  CoherentBaseChange.TwoTermComplex.mk.injEq
