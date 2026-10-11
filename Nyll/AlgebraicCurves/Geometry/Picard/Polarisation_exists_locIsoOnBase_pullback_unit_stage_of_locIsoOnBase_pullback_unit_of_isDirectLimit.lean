/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Polarisation_exists_locIsoOnBase_pullback_unit_stage_of_locIsoOnBase_pullback_unit_of_isDirectLimit.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Nyll.AlgebraicCurves.Foundations.Algebra.Mathlib_Algebra_IsDirectLimit
import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.AlgebraicCurves.Geometry.Picard.PolarisationRosati
import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesPullbackMonoidalV2
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_exists_nonempty_iso_pullback_of_nonempty_iso_pullback_of_isDirectLimit
import Nyll.AlgebraicCurves.Geometry.Schemes.exists_forall_specMap_base_mem_of_isDirectLimit

/-!
# Polarisation exists loc Iso On Base pullback unit stage of loc Iso On Base pullback unit
of is Direct Limit
-/

section ProofImplementation

open _root_.AlgebraicGeometry.Scheme.Modules (
  exists_nonempty_iso_pullback_of_nonempty_iso_pullback_of_isDirectLimit)

namespace AlgebraicCurves.Geometry.Picard.Proofs.PolarisationLimitDescent
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
  SheafOfModules.isIso_ihomModelToIhom
attribute [-simp] AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right
  AlgebraicGeometry.Scheme.Modules.map_unitSection
  AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply
  AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left
  AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq
  TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq
  TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec
  TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec
  TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec
  CoherentBaseChange.TwoTermComplex.mk.injEq
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

universe u


open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.Polarisation


noncomputable section

namespace LocIsoLimit

theorem nonempty_iso_restrict {X Y : Scheme.{u}} (g : X ⟶ Y) {U U' : Y.Opens} (hU : U' ≤ U)
    {M M' : X.Modules}
    (h : Nonempty ((Scheme.Modules.pullback (g ⁻¹ᵁ U).ι).obj M ≅ (Scheme.Modules.pullback (g ⁻¹ᵁ
      U).ι).obj M')) :
    Nonempty ((Scheme.Modules.pullback (g ⁻¹ᵁ U').ι).obj M ≅ (Scheme.Modules.pullback (g ⁻¹ᵁ
      U').ι).obj M') := by
  obtain ⟨e⟩ := h
  have hle : g ⁻¹ᵁ U' ≤ g ⁻¹ᵁ U := g.preimage_mono hU
  have hfac : X.homOfLE hle ≫ (g ⁻¹ᵁ U).ι = (g ⁻¹ᵁ U').ι := X.homOfLE_ι hle
  exact ⟨((Scheme.Modules.pullbackCongr hfac).app M).symm ≪≫ ((Scheme.Modules.pullbackComp _ _).app
    M).symm ≪≫
    (Scheme.Modules.pullback (X.homOfLE hle)).mapIso e ≪≫
    (Scheme.Modules.pullbackComp _ _).app M' ≪≫ (Scheme.Modules.pullbackCongr hfac).app M'⟩

theorem exists_basicOpen_cover {R : Type u} [CommRing R] {X : Scheme.{u}} (g : X ⟶ Spec
  (CommRingCat.of R))
    {M M' : X.Modules} (h : LocIsoOnBase g M M') :
    ∃ (s : Finset R), (∀ p : Spec (CommRingCat.of R), ∃ r ∈ s, p ∈ PrimeSpectrum.basicOpen r) ∧
      ∀ r ∈ s, Nonempty ((Scheme.Modules.pullback (g ⁻¹ᵁ PrimeSpectrum.basicOpen r).ι).obj M ≅
        (Scheme.Modules.pullback (g ⁻¹ᵁ PrimeSpectrum.basicOpen r).ι).obj M') := by
  classical
  have key : ∀ p : PrimeSpectrum R, ∃ r : R, p ∈ PrimeSpectrum.basicOpen r ∧
      Nonempty ((Scheme.Modules.pullback (g ⁻¹ᵁ PrimeSpectrum.basicOpen r).ι).obj M ≅
        (Scheme.Modules.pullback (g ⁻¹ᵁ PrimeSpectrum.basicOpen r).ι).obj M') := by
    intro p
    obtain ⟨U, hp, hU⟩ := h p
    obtain ⟨_, ⟨r, rfl⟩, hpr, hrU⟩ :=
      (PrimeSpectrum.isTopologicalBasis_basic_opens (R := R)).exists_subset_of_mem_open hp U.isOpen
    exact ⟨r, hpr, nonempty_iso_restrict g (U := U) (U' := PrimeSpectrum.basicOpen r) (fun x hx =>
      hrU hx) hU⟩
  choose r hr hiso using key
  obtain ⟨t, ht⟩ := (isCompact_univ (X := PrimeSpectrum R)).elim_finite_subcover
    (fun p : PrimeSpectrum R => ((PrimeSpectrum.basicOpen (r p) : TopologicalSpace.Opens
      (PrimeSpectrum R)) : Set (PrimeSpectrum R)))
    (fun p => (PrimeSpectrum.basicOpen (r p)).isOpen) (fun p _ => Set.mem_iUnion.mpr ⟨p, hr p⟩)
  refine ⟨t.image r, ?_, ?_⟩
  · intro p
    obtain ⟨q, hq⟩ := Set.mem_iUnion.mp (ht (Set.mem_univ p))
    obtain ⟨hqt, hpq⟩ := Set.mem_iUnion.mp hq
    exact ⟨r q, Finset.mem_image_of_mem r hqt, hpq⟩
  · intro r' hr'
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hr'
    exact hiso q

section limit

variable {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirected ι (· ≤ ·)]
  {G : ι → Type u} [∀ i, CommRing (G i)] (φ : ∀ i j : ι, i ≤ j → G i →+* G j)
  [DirectedSystem G fun i j h => ⇑(φ i j h)]
  {R : Type u} [CommRing R] (g : ∀ i, G i →+* R)
  (hR : IsDirectLimit (fun i j h => ⇑(φ i j h)) fun i => ⇑(g i))

theorem specMap_base_apply {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) (p :
  PrimeSpectrum B) :
    (Spec.map (CommRingCat.ofHom f)).base p = PrimeSpectrum.comap f p := rfl

theorem comap_mem_basicOpen_iff {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) (p :
  PrimeSpectrum B) (x : A) :
    PrimeSpectrum.comap f p ∈ PrimeSpectrum.basicOpen x ↔ p ∈ PrimeSpectrum.basicOpen (f x) := by
  rw [PrimeSpectrum.mem_basicOpen, PrimeSpectrum.mem_basicOpen, PrimeSpectrum.comap_asIdeal,
    Ideal.mem_comap]
omit [Nonempty ι] in
include hR in
theorem exists_stage_lifts (i : ι) (s : Finset R) :
    ∃ (j : ι) (_ : i ≤ j) (r' : R → G j), ∀ r ∈ s, g j (r' r) = r := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨i, le_rfl, fun _ => 0, fun r hr => absurd hr (Finset.notMem_empty r)⟩
  | insert a s ha ih =>
    obtain ⟨j, hij, r', hr'⟩ := ih
    obtain ⟨j₁, m, hm⟩ := hR.surj a
    obtain ⟨k, hjk, hj₁k⟩ := directed_of (· ≤ ·) j j₁
    refine ⟨k, hij.trans hjk, fun r => if r = a then φ j₁ k hj₁k m else φ j k hjk (r' r), ?_⟩
    intro r hr
    dsimp only
    rcases Finset.mem_insert.mp hr with rfl | hr
    · rw [ite_eq_left rfl, hR.compatibility]; exact hm
    · have hne : r ≠ a := fun h => ha (h ▸ hr)
      rw [ite_eq_right hne, hR.compatibility]; exact hr' r hr
include hR in
theorem exists_stage_cover (s : Finset R) (hcov : ∀ p : PrimeSpectrum R, ∃ r ∈ s, p ∈
  PrimeSpectrum.basicOpen r)
    (j : ι) (r' : R → G j) (hr' : ∀ r ∈ s, g j (r' r) = r) :
    ∃ (k : ι) (hjk : j ≤ k), ∀ q : PrimeSpectrum (G k), ∃ r ∈ s, q ∈ PrimeSpectrum.basicOpen (φ j k
      hjk (r' r)) := by
  let W : (Spec (CommRingCat.of (G j))).Opens := ⨆ r ∈ s, PrimeSpectrum.basicOpen (r' r)
  have hW : ∀ p : Spec (CommRingCat.of R), (Spec.map (CommRingCat.ofHom (g j))).base p ∈ W := by
    intro p
    obtain ⟨r, hrs, hp⟩ := hcov p
    have hmem : PrimeSpectrum.comap (g j) p ∈ PrimeSpectrum.basicOpen (r' r) :=
      (comap_mem_basicOpen_iff (g j) p (r' r)).mpr ((hr' r hrs).symm ▸ hp)
    have hmap : (Spec.map (CommRingCat.ofHom (g j))).base p =
        PrimeSpectrum.comap (g j) p := specMap_base_apply (g j) p
    have hmem' : (Spec.map (CommRingCat.ofHom (g j))).base p ∈
        PrimeSpectrum.basicOpen (r' r) := hmap.symm ▸ hmem
    exact TopologicalSpace.Opens.mem_iSup.mpr
      ⟨r, TopologicalSpace.Opens.mem_iSup.mpr ⟨hrs, hmem'⟩⟩
  obtain ⟨k, hjk, hk⟩ := AlgebraicGeometry.exists_forall_specMap_base_mem_of_isDirectLimit φ g hR j
    W hW
  refine ⟨k, hjk, fun q => ?_⟩
  have hmap : (Spec.map (CommRingCat.ofHom (φ j k hjk))).base q =
      PrimeSpectrum.comap (φ j k hjk) q := specMap_base_apply (φ j k hjk) q
  have hq : PrimeSpectrum.comap (φ j k hjk) q ∈ W := hmap ▸ hk q
  obtain ⟨r, hr⟩ := TopologicalSpace.Opens.mem_iSup.mp hq
  obtain ⟨hrs, hq'⟩ := TopologicalSpace.Opens.mem_iSup.mp hr
  exact ⟨r, hrs, (comap_mem_basicOpen_iff _ _ _).mp hq'⟩

end limit

theorem nonempty_iso_unit_of_comp_eq {W Y Z : Scheme.{u}} (d : W ⟶ Y) (a : Y ⟶ Z) (b : W ⟶ Z) (hd :
  d ≫ a = b)
    (N : Z.Modules) (h : Nonempty ((Scheme.Modules.pullback a).obj N ≅ 𝟙_ _)) :
    Nonempty ((Scheme.Modules.pullback b).obj N ≅ 𝟙_ _) := by
  obtain ⟨e⟩ := h
  exact ⟨((Scheme.Modules.pullbackCongr hd).app N).symm ≪≫ ((Scheme.Modules.pullbackComp d a).app
    N).symm ≪≫
    (Scheme.Modules.pullback d).mapIso e ≪≫ Scheme.Modules.pullbackTensorUnitObjIso d⟩

theorem nonempty_iso_unit_iff {W Y Z : Scheme.{u}} (j : W ⟶ Y) (a : Y ⟶ Z) (N : Z.Modules) :
    Nonempty ((Scheme.Modules.pullback j).obj ((Scheme.Modules.pullback a).obj N) ≅
        (Scheme.Modules.pullback j).obj (𝟙_ _)) ↔
      Nonempty ((Scheme.Modules.pullback (j ≫ a)).obj N ≅ 𝟙_ _) := by
  constructor
  · rintro ⟨e⟩
    exact ⟨((Scheme.Modules.pullbackComp j a).app N).symm ≪≫ e ≪≫
      Scheme.Modules.pullbackTensorUnitObjIso j⟩
  · rintro ⟨e⟩
    exact ⟨(Scheme.Modules.pullbackComp j a).app N ≪≫ e ≪≫ (Scheme.Modules.pullbackTensorUnitObjIso
      j).symm⟩

section main

variable {ι : Type u} [Preorder ι]
  {G : ι → Type u} [∀ i, CommRing (G i)] (φ : ∀ i j : ι, i ≤ j → G i →+* G j)
  [DirectedSystem G fun i j h => ⇑(φ i j h)]
  {R : Type u} [CommRing R] (g : ∀ i, G i →+* R)
  (hR : IsDirectLimit (fun i j h => ⇑(φ i j h)) fun i => ⇑(g i))

include hR in
theorem g_comp_φ (i j : ι) (hij : i ≤ j) : (g j).comp (φ i j hij) = g i :=
  RingHom.ext fun x => hR.compatibility i j hij x
omit hR in
theorem φ_comp_φ (i j k : ι) (hij : i ≤ j) (hjk : j ≤ k) : (φ j k hjk).comp (φ i j hij) = φ i k
  (hij.trans hjk) :=
  RingHom.ext fun x => DirectedSystem.map_map (f := fun i j h => ⇑(φ i j h)) hij hjk x
include hR in
theorem spec_g_comp (i j : ι) (hij : i ≤ j) :
    Spec.map (CommRingCat.ofHom (g j)) ≫ Spec.map (CommRingCat.ofHom (φ i j hij)) = Spec.map
      (CommRingCat.ofHom (g i)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, g_comp_φ φ g hR i j hij]

theorem spec_φ_comp (i j k : ι) (hij : i ≤ j) (hjk : j ≤ k) :
    Spec.map (CommRingCat.ofHom (φ j k hjk)) ≫ Spec.map (CommRingCat.ofHom (φ i j hij)) =
      Spec.map (CommRingCat.ofHom (φ i k (hij.trans hjk))) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, φ_comp_φ φ i j k hij hjk]

variable (i : ι) {X : Scheme.{u}} (fX : X ⟶ Spec (CommRingCat.of (G i))) (N : X.Modules)

private abbrev _root_.LocIsoLimit.trans (j k : ι) (hij : i ≤ j) (hjk : j ≤ k) :
    pullback fX (Spec.map (CommRingCat.ofHom (φ i k (hij.trans hjk)))) ⟶
      pullback fX (Spec.map (CommRingCat.ofHom (φ i j hij))) :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (φ j k hjk)))
    (by rw [pullback.condition, Category.assoc, spec_φ_comp φ i j k hij hjk])
export _root_.LocIsoLimit (trans)


/-- The morphism from the limit base change to the base change at stage j. -/
abbrev toStage (j : ι) (hij : i ≤ j) :
    pullback fX (Spec.map (CommRingCat.ofHom (g i))) ⟶ pullback fX (Spec.map (CommRingCat.ofHom (φ
      i j hij))) :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (g j)))
    (by rw [pullback.condition, Category.assoc, spec_g_comp φ g hR i j hij])

theorem base_comp_apply {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f ≫ g).base x = g.base (f.base x) :=
  Scheme.Hom.comp_apply f g x

variable [Nonempty ι] [IsDirected ι (· ≤ ·)]

include hR in
theorem piece [QuasiCompact fX] [QuasiSeparated fX] (hN : Scheme.Modules.IsInvertible N)
    (j : ι) (hij : i ≤ j) (r' : G j)
    (h : Nonempty ((Scheme.Modules.pullback
        ((pullback.snd fX (Spec.map (CommRingCat.ofHom (g i)))) ⁻¹ᵁ PrimeSpectrum.basicOpen (g j
          r')).ι).obj
          ((Scheme.Modules.pullback (pullback.fst fX (Spec.map (CommRingCat.ofHom (g i))))).obj N) ≅
      (Scheme.Modules.pullback
        ((pullback.snd fX (Spec.map (CommRingCat.ofHom (g i)))) ⁻¹ᵁ PrimeSpectrum.basicOpen (g j
          r')).ι).obj (𝟙_ _))) :
    ∃ (k₀ : ι) (hjk₀ : j ≤ k₀), ∀ (k : ι) (hk : k₀ ≤ k),
      Nonempty ((Scheme.Modules.pullback
        ((pullback.snd fX (Spec.map (CommRingCat.ofHom (φ i k ((hij.trans hjk₀).trans hk))))) ⁻¹ᵁ
            PrimeSpectrum.basicOpen (φ j k (hjk₀.trans hk) r')).ι).obj
          ((Scheme.Modules.pullback (pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i k
            ((hij.trans hjk₀).trans hk)))))).obj N) ≅
      (Scheme.Modules.pullback
        ((pullback.snd fX (Spec.map (CommRingCat.ofHom (φ i k ((hij.trans hjk₀).trans hk))))) ⁻¹ᵁ
            PrimeSpectrum.basicOpen (φ j k (hjk₀.trans hk) r')).ι).obj (𝟙_ _)) := by
  let Xj := pullback fX (Spec.map (CommRingCat.ofHom (φ i j hij)))
  let V : Xj.Opens := (pullback.snd fX (Spec.map (CommRingCat.ofHom (φ i j hij)))) ⁻¹ᵁ
    PrimeSpectrum.basicOpen r'
  let fV : (V : Scheme.{u}) ⟶ Spec (CommRingCat.of (G j)) := V.ι ≫ pullback.snd fX _
  have hVc : IsCompact (V : Set Xj) :=
    (pullback.snd fX (Spec.map (CommRingCat.ofHom (φ i j hij)))).isCompact_preimage
      (PrimeSpectrum.isCompact_basicOpen r')
  have : CompactSpace (V : Scheme.{u}) := isCompact_iff_compactSpace.mp hVc
  have : QuasiCompact fV := quasiCompact_of_compactSpace fV
  have : QuasiSeparated fV := inferInstance
  let a : (V : Scheme.{u}) ⟶ X := V.ι ≫ pullback.fst fX _
  let 𝓛₁ : (V : Scheme.{u}).Modules := (Scheme.Modules.pullback a).obj N
  have h𝓛₁ : Scheme.Modules.IsInvertible 𝓛₁ := hN.pullback a
  have hunit : Scheme.Modules.IsInvertible (𝟙_ ((V : Scheme.{u}).Modules)) :=
    Scheme.Modules.isInvertible_unit _
  have wc : (pullback.fst fV (Spec.map (CommRingCat.ofHom (g j))) ≫ a) ≫ fX =
      pullback.snd fV (Spec.map (CommRingCat.ofHom (g j))) ≫ Spec.map (CommRingCat.ofHom (g i)) :=
        by
    have h1 : pullback.fst fV (Spec.map (CommRingCat.ofHom (g j))) ≫ fV =
        pullback.snd fV _ ≫ Spec.map (CommRingCat.ofHom (g j)) := pullback.condition
    have h1' := reassoc_of% h1
    simp only [a, Category.assoc]
    rw [pullback.condition, ← spec_g_comp φ g hR i j hij, ← h1']
    simp only [fV, Category.assoc]
  let c : pullback fV (Spec.map (CommRingCat.ofHom (g j))) ⟶ pullback fX (Spec.map
    (CommRingCat.ofHom (g i))) :=
    pullback.lift (pullback.fst fV _ ≫ a) (pullback.snd fV _) wc
  have hc_range : Set.range c ⊆
      Set.range ((pullback.snd fX (Spec.map (CommRingCat.ofHom (g i)))) ⁻¹ᵁ PrimeSpectrum.basicOpen
        (g j r')).ι := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    change (pullback.snd fX (Spec.map (CommRingCat.ofHom (g i)))).base (c.base y) ∈
      PrimeSpectrum.basicOpen (g j r')
    rw [← base_comp_apply, pullback.lift_snd]
    have e1 : (Spec.map (CommRingCat.ofHom (g j))).base ((pullback.snd fV (Spec.map
      (CommRingCat.ofHom (g j)))).base y) ∈
        PrimeSpectrum.basicOpen r' := by
      rw [← base_comp_apply, ← pullback.condition, base_comp_apply]
      change (pullback.snd fX (Spec.map (CommRingCat.ofHom (φ i j hij)))).base (V.ι.base _) ∈
        PrimeSpectrum.basicOpen r'
      exact (Scheme.Opens.range_ι V).subset ⟨(pullback.fst fV (Spec.map (CommRingCat.ofHom (g
        j)))).base y, rfl⟩
    exact (comap_mem_basicOpen_iff (g j) _ r').mp e1
  let c' := IsOpenImmersion.lift _ c hc_range
  have hc' : c' ≫ ((pullback.snd fX (Spec.map (CommRingCat.ofHom (g i)))) ⁻¹ᵁ
    PrimeSpectrum.basicOpen (g j r')).ι ≫
      pullback.fst fX (Spec.map (CommRingCat.ofHom (g i))) = pullback.fst fV (Spec.map
        (CommRingCat.ofHom (g j))) ≫ a := by
    rw [← Category.assoc, IsOpenImmersion.lift_fac, pullback.lift_fst]
  have hiso : Nonempty ((Scheme.Modules.pullback (pullback.fst fV (Spec.map (CommRingCat.ofHom (g
    j))))).obj 𝓛₁ ≅
      (Scheme.Modules.pullback (pullback.fst fV (Spec.map (CommRingCat.ofHom (g j))))).obj (𝟙_ _))
        :=
    (nonempty_iso_unit_iff _ a N).mpr (nonempty_iso_unit_of_comp_eq c' _ _ hc' N
      ((nonempty_iso_unit_iff _ _ N).mp h))
  obtain ⟨k₀, hjk₀, ⟨e₀⟩⟩ :=
    exists_nonempty_iso_pullback_of_nonempty_iso_pullback_of_isDirectLimit φ g hR j fV
      𝓛₁ (𝟙_ _) h𝓛₁ hunit hiso
  have e₀' := (nonempty_iso_unit_iff _ a N).mp ⟨e₀⟩
  refine ⟨k₀, hjk₀, fun k hk => ?_⟩
  let hik : i ≤ k := (hij.trans hjk₀).trans hk
  let Xk := pullback fX (Spec.map (CommRingCat.ofHom (φ i k hik)))
  let U' : Xk.Opens := (pullback.snd fX (Spec.map (CommRingCat.ofHom (φ i k hik)))) ⁻¹ᵁ
    PrimeSpectrum.basicOpen (φ j k (hjk₀.trans hk) r')
  let t : Xk ⟶ Xj := trans φ i fX j k hij (hjk₀.trans hk)
  have ht_snd : t ≫ pullback.snd fX _ = pullback.snd fX _ ≫ Spec.map (CommRingCat.ofHom (φ j k
    (hjk₀.trans hk))) :=
    pullback.lift_snd _ _ _
  have ht_fst : t ≫ pullback.fst fX _ = pullback.fst fX _ := pullback.lift_fst _ _ _
  have hU'_range : Set.range (U'.ι ≫ t) ⊆ Set.range V.ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    change (pullback.snd fX (Spec.map (CommRingCat.ofHom (φ i j hij)))).base ((U'.ι ≫ t).base z) ∈
      PrimeSpectrum.basicOpen r'
    rw [← base_comp_apply, Category.assoc, ht_snd, ← Category.assoc, base_comp_apply]
    refine (comap_mem_basicOpen_iff (φ j k (hjk₀.trans hk)) _ r').mpr ?_
    exact (Scheme.Opens.range_ι U').subset ⟨z, rfl⟩
  let d₁ : (U' : Scheme.{u}) ⟶ (V : Scheme.{u}) := IsOpenImmersion.lift V.ι (U'.ι ≫ t) hU'_range
  have hd₁ : d₁ ≫ V.ι = U'.ι ≫ t := IsOpenImmersion.lift_fac _ _ _
  have wd : d₁ ≫ fV = (U'.ι ≫ pullback.snd fX _ ≫ Spec.map (CommRingCat.ofHom (φ k₀ k hk))) ≫
      Spec.map (CommRingCat.ofHom (φ j k₀ hjk₀)) := by
    simp only [fV, Category.assoc]
    rw [← Category.assoc d₁, hd₁, Category.assoc, ht_snd, spec_φ_comp φ j k₀ k hjk₀ hk]
  let d : (U' : Scheme.{u}) ⟶ pullback fV (Spec.map (CommRingCat.ofHom (φ j k₀ hjk₀))) :=
    pullback.lift d₁ (U'.ι ≫ pullback.snd fX _ ≫ Spec.map (CommRingCat.ofHom (φ k₀ k hk))) wd
  have hd : d ≫ pullback.fst fV (Spec.map (CommRingCat.ofHom (φ j k₀ hjk₀))) ≫ a =
      U'.ι ≫ pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i k hik))) := by
    rw [← Category.assoc, pullback.lift_fst]
    simp only [a]
    rw [← Category.assoc, hd₁, Category.assoc, ht_fst]
  exact (nonempty_iso_unit_iff _ _ N).mpr (nonempty_iso_unit_of_comp_eq d _ _ hd N e₀')
include hR in
theorem main [QuasiCompact fX] [QuasiSeparated fX] (hN : Scheme.Modules.IsInvertible N)
    (h : LocIsoOnBase (Limits.pullback.snd fX (Spec.map (CommRingCat.ofHom (g i))))
      ((Scheme.Modules.pullback (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (g i))))).obj
        N)
      (𝟙_ ((Limits.pullback fX (Spec.map (CommRingCat.ofHom (g i)))).Modules))) :
    ∃ (k : ι) (hik : i ≤ k),
      LocIsoOnBase (Limits.pullback.snd fX (Spec.map (CommRingCat.ofHom (φ i k hik))))
        ((Scheme.Modules.pullback (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i k
          hik))))).obj N)
        (𝟙_ ((Limits.pullback fX (Spec.map (CommRingCat.ofHom (φ i k hik)))).Modules)) := by
  classical
  obtain ⟨s, hcov, hiso⟩ := exists_basicOpen_cover _ h
  obtain ⟨j, hij, r', hr'⟩ := exists_stage_lifts φ g hR i s
  have hpiece : ∀ r ∈ s, ∃ (k₀ : ι) (hjk₀ : j ≤ k₀), ∀ (k : ι) (hk : k₀ ≤ k),
      Nonempty ((Scheme.Modules.pullback
        ((pullback.snd fX (Spec.map (CommRingCat.ofHom (φ i k ((hij.trans hjk₀).trans hk))))) ⁻¹ᵁ
            PrimeSpectrum.basicOpen (φ j k (hjk₀.trans hk) (r' r))).ι).obj
          ((Scheme.Modules.pullback (pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i k
            ((hij.trans hjk₀).trans hk)))))).obj N) ≅
      (Scheme.Modules.pullback
        ((pullback.snd fX (Spec.map (CommRingCat.ofHom (φ i k ((hij.trans hjk₀).trans hk))))) ⁻¹ᵁ
            PrimeSpectrum.basicOpen (φ j k (hjk₀.trans hk) (r' r))).ι).obj (𝟙_ _)) := by
    intro r hr
    refine piece φ g hR i fX N hN j hij (r' r) ?_
    rw [hr' r hr]
    exact hiso r hr
  choose k₀ hjk₀ hk₀ using hpiece
  obtain ⟨k₂, hjk₂, hcov₂⟩ := exists_stage_cover φ g hR s hcov j r' hr'
  let K : R → ι := fun r => if hr : r ∈ s then k₀ r hr else j
  obtain ⟨k, hk⟩ := Finset.exists_le (insert k₂ (s.image K))
  have hk₂k : k₂ ≤ k := hk k₂ (Finset.mem_insert_self _ _)
  have hKk : ∀ r (hr : r ∈ s), k₀ r hr ≤ k := fun r hr => by
    have h1 := hk (K r) (Finset.mem_insert_of_mem (Finset.mem_image_of_mem K hr))
    have h2 : K r = k₀ r hr := dite_eq_left hr
    rw [h2] at h1
    exact h1
  refine ⟨k, (hij.trans hjk₂).trans hk₂k, ?_⟩
  intro q
  obtain ⟨r, hrs, hq⟩ := hcov₂ ((Spec.map (CommRingCat.ofHom (φ k₂ k hk₂k))).base q)
  have hq' := (comap_mem_basicOpen_iff (φ k₂ k hk₂k) q (φ j k₂ hjk₂ (r' r))).mp hq
  have hφ : φ k₂ k hk₂k (φ j k₂ hjk₂ (r' r)) = φ j k (hjk₂.trans hk₂k) (r' r) :=
    DirectedSystem.map_map (f := fun i j h => ⇑(φ i j h)) hjk₂ hk₂k _
  rw [hφ] at hq'
  exact ⟨PrimeSpectrum.basicOpen (φ j k (hjk₂.trans hk₂k) (r' r)), hq', hk₀ r hrs k (hKk r hrs)⟩

end main

end LocIsoLimit

end
end AlgebraicCurves.Geometry.Picard.Proofs.PolarisationLimitDescent

namespace AlgebraicGeometry.Polarisation

open _root_.AlgebraicCurves.Geometry.Picard.Proofs.PolarisationLimitDescent
universe u
open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.Polarisation


theorem exists_locIsoOnBase_pullback_unit_stage_of_locIsoOnBase_pullback_unit_of_isDirectLimit
    {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirected ι (· ≤ ·)]
    {G : ι → Type u} [∀ i, CommRing (G i)] (φ : ∀ i j : ι, i ≤ j → G i →+* G j)
    [DirectedSystem G fun i j h => ⇑(φ i j h)]
    {R : Type u} [CommRing R] (g : ∀ i, G i →+* R)
    (hR : IsDirectLimit (fun i j h => ⇑(φ i j h)) fun i => ⇑(g i))
    (i : ι) {X : Scheme.{u}} (fX : X ⟶ Spec (CommRingCat.of (G i))) [QuasiCompact fX]
      [QuasiSeparated fX]
    (N : X.Modules) (hN : Scheme.Modules.IsInvertible N)
    (h : LocIsoOnBase (Limits.pullback.snd fX (Spec.map (CommRingCat.ofHom (g i))))
      ((Scheme.Modules.pullback (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (g i))))).obj
        N)
      (𝟙_ ((Limits.pullback fX (Spec.map (CommRingCat.ofHom (g i)))).Modules))) :
    ∃ (k : ι) (hik : i ≤ k),
      LocIsoOnBase (Limits.pullback.snd fX (Spec.map (CommRingCat.ofHom (φ i k hik))))
        ((Scheme.Modules.pullback (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i k
          hik))))).obj N)
        (𝟙_ ((Limits.pullback fX (Spec.map (CommRingCat.ofHom (φ i k hik)))).Modules)) :=
  LocIsoLimit.main φ g hR i fX N hN h
end AlgebraicGeometry.Polarisation
end ProofImplementation

open PresheafOfModules.PullbackMonoidal in
attribute [-instance]
  pullback_monoidal
  isIso_δ
open _root_.PresheafOfModules in
attribute [-instance]
  pushforward_laxMonoidal
open PresheafOfModules.PullbackMonoidal in
attribute [-instance]
  isIso_η
open _root_.PresheafOfModules in
attribute [-instance]
  free_monoidal
  restrictScalars_laxMonoidal
open PresheafOfModules.PullbackMonoidal in
attribute [-instance]
  isIso_δ_gS
open _root_.PresheafOfModules in
attribute [-instance]
  pullback_oplaxMonoidal
open PresheafOfModules.PullbackMonoidal in
attribute [-instance]
  instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb
open _root_.PresheafOfModules in
attribute [-instance]
  pullback_monoidal'
open _root_.AlgebraicGeometry.Scheme.Modules in
attribute [-instance]
  preservesBinaryProducts_opensMap
  pullback_monoidal
  sheafify_isLocalization'
  preservesTerminal_opensMap
  pullback₀_monoidal
  preservesFiniteProducts_opensMap
  sheafifyPullback_lifting
open TwoChartCech.Sections in
attribute [-instance]
  M0_moduleA
  M1_module
open TwoChartCech.Cover in
attribute [-instance]
  A01_algebra
  A0_algebra
  A1_commRing
  A1_algebra
open TwoChartCech.Sections in
attribute [-instance]
  M01_module
  M0_addCommGroup
  M0_tower
  M01_addCommGroup
open TwoChartCech.Cover in
attribute [-instance]
  A0_commRing
open TwoChartCech.Sections in
attribute [-instance]
  M1_tower
  M01_moduleA
  M0_module
  M1_moduleA
  M1_addCommGroup
open TwoChartCech.Cover in
attribute [-instance]
  A01_commRing
open TwoChartCech.Sections in
attribute [-instance]
  M01_tower
open CoherentBaseChange.TwoTermComplex in
attribute [-instance]
  C0_module
  C0_addCommGroup
  C1_module
  C1_addCommGroup
  C0_free
attribute [-instance] CoherentBaseChange.TwoTermComplex.C1_finite
  CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free
  SheafOfModules.isIso_ihomModelToIhom
attribute [-simp] PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right
  AlgebraicGeometry.Scheme.Modules.map_unitSection
  AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply
  AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left
  AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq
  TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq
  TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec
  TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec
  TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec
  CoherentBaseChange.TwoTermComplex.mk.injEq
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
