/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_bijective_appTop_pullback_snd_residue_of_bijective_appTop_of_isReduced.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Geometry.Schemes.isPreconnected_preimage_closedPoint_of_isProper_of_bijective_appTop
import AlgebraicCurves.Geometry.Schemes.finite_appTop_of_isProper_of_isNoetherianRing

/-!
# Global sections on residue fibres of reduced proper schemes
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs
namespace bijective_appTop_pullback_snd_residue_of_bijective_appTop_of_isReduced
attribute [-instance] AlgebraicGeometry.OModulePresheaf.isScalarTower
  AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder
  AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype
  AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx
  AlgebraicGeometry.OModulePresheaf.addCommGroup
  AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx
  AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA
  TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra
  TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module
  TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower
  TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing
  TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module
  TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup
  TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower
  CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup
  CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup
  CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite
  CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free
  AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero
  AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower
  AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ
  AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ
  AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp
  AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ
attribute [-instance] AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul
  AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower
  AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul
  AlgebraicGeometry.OModulePresheaf.Leray.biC_module
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I
  DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II
  DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I
  AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed
  AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU
  AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway
  AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU
  AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial
  ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup
  ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg
  ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid
  ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule
  ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero
  ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul
  ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup
  ProjSpaceCech.Idx.instDecidableEq
attribute [-instance] ProjSpaceCech.Twist.Mon.instDecidableEq
  ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule
attribute [-simp] AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq
  AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq
  TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq
  TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec
  TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec
  TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec
  CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj
  AlgebraicGeometry.OModulePresheaf.restrOpen_obj
  AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq
  AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj
  AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app
  AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj
  AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U
  AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq
  AlgebraicGeometry.OModulePresheaf.Hom.id_app
  AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply
  AlgebraicGeometry.OModulePresheaf.AffHom.comp_app
  AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe
  AlgebraicGeometry.OModulePresheaf.AffHom.id_app
  AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app
  AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec
attribute [-simp] AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq
  AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq
  AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply
  AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq
  AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U
  AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq
  AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq
  DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq
  DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec
  DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec
  AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq
  AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq
  ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq
  ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Hom.mk.injEq

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace HconnAux

theorem bijective_of_finite_of_isReduced_of_idempotent {κ : Type*} [Field κ] [IsAlgClosed κ]
    {A : Type*} [CommRing A] [IsReduced A] [Nontrivial A] (ψ : κ →+* A) (hfin : ψ.Finite)
    (hidem : ∀ e : A, IsIdempotentElem e → e = 0 ∨ e = 1) : Function.Bijective ψ := by
  classical
  let : Algebra κ A := ψ.toAlgebra
  have : Module.Finite κ A := hfin
  have : IsArtinianRing A := IsArtinianRing.of_finite κ A
  have huniq : ∀ I J : MaximalSpectrum A, I = J := by
    intro I J
    by_contra hIJ
    let E := IsArtinianRing.equivPi A
    let v : (K : MaximalSpectrum A) → A ⧸ K.asIdeal := fun K => if K = I then 1 else 0
    have hv : IsIdempotentElem v := by
      change v * v = v
      funext K
      by_cases hK : K = I <;> simp [v, hK]
    have he : IsIdempotentElem (E.symm v) := by
      change E.symm v * E.symm v = E.symm v
      rw [← map_mul, hv.eq]
    rcases hidem _ he with h0 | h1
    · have : v = 0 := by simpa using congrArg E h0
      have := congrFun this I
      simp [v] at this
    · have : v = 1 := by simpa using congrArg E h1
      have := congrFun this J
      simp [v, Ne.symm hIJ] at this
  obtain ⟨M, hM⟩ := Ideal.exists_maximal A
  have : IsLocalRing A :=
    IsLocalRing.of_unique_max_ideal ⟨M, hM, fun N hN => congrArg MaximalSpectrum.asIdeal (huniq ⟨N,
      hN⟩ ⟨M, hM⟩)⟩
  have hmax : IsLocalRing.maximalIdeal A = ⊥ := by
    obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := A)
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top] at hn
    refine le_bot_iff.mp (fun x hx => ?_)
    have hxn : x ^ n ∈ (IsLocalRing.maximalIdeal A) ^ n := Ideal.pow_mem_pow hx n
    rw [hn] at hxn
    exact (IsReduced.eq_zero x ⟨n, (Submodule.mem_bot A).mp hxn⟩ : x = 0)
  have : NoZeroDivisors A := ⟨fun {a b} hab => by
    by_contra h
    push Not at h
    have ha : IsUnit a := by
      by_contra hna
      exact h.1 ((Submodule.mem_bot A).mp (hmax ▸ (IsLocalRing.mem_maximalIdeal a).mpr hna))
    exact h.2 ((ha.mul_right_eq_zero).mp hab)⟩
  have : IsDomain A := NoZeroDivisors.to_isDomain A
  exact IsAlgClosed.algebraMap_bijective_of_isIntegral (k := κ) (K := A)

theorem idempotent_eq_zero_or_one (Y : Scheme.{u}) [IsReduced Y] [PreconnectedSpace Y]
    (e : Γ(Y, ⊤)) (he : IsIdempotentElem e) : e = 0 ∨ e = 1 := by
  set U := Y.basicOpen e with hU
  set V := Y.basicOpen (1 - e) with hV
  have hcov : ∀ y : Y, y ∈ U ∨ y ∈ V := by
    intro y
    rw [hU, hV, Scheme.mem_basicOpen_top, Scheme.mem_basicOpen_top, map_sub, map_one]
    exact IsLocalRing.isUnit_or_isUnit_of_add_one (by ring)
  have hdisj : U ⊓ V = ⊥ := by
    rw [hU, hV, ← Scheme.basicOpen_mul]
    have : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he.eq, sub_self]
    rw [this, Scheme.basicOpen_zero]
  have hcompl : (U : Set Y)ᶜ = (V : Set Y) := by
    ext y
    constructor
    · intro hy
      rcases hcov y with h | h
      · exact absurd h hy
      · exact h
    · intro hy hyU
      have : y ∈ (U ⊓ V : Y.Opens) := ⟨hyU, hy⟩
      rw [hdisj] at this
      exact this
  have hclopen : IsClopen (U : Set Y) := by
    refine ⟨⟨?_⟩, U.isOpen⟩
    rw [hcompl]; exact V.isOpen
  rcases isClopen_iff.mp hclopen with h | h
  · left
    have : U = ⊥ := TopologicalSpace.Opens.ext h
    rw [hU, AlgebraicGeometry.basicOpen_eq_bot_iff] at this
    exact this
  · right
    have hVe : (V : Set Y) = ∅ := by rw [← hcompl, h, Set.compl_univ]
    have : V = ⊥ := TopologicalSpace.Opens.ext hVe
    rw [hV, AlgebraicGeometry.basicOpen_eq_bot_iff] at this
    exact (sub_eq_zero.mp this).symm

end HconnAux

theorem
  _root_.AlgebraicGeometry.bijective_appTop_pullback_snd_residue_of_bijective_appTop_of_isReduced
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [IsAlgClosed (IsLocalRing.ResidueField R)]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]
    (hΓ : Function.Bijective f.appTop)
    [IsReduced (pullback f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))] :
    Function.Bijective
      (pullback.snd f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))).appTop := by
  classical
  set κ := IsLocalRing.ResidueField R with hκ
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) :=
    IsClosedImmersion.spec_of_surjective _ IsLocalRing.residue_surjective
  set g := Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)) with hg
  set Y := pullback f g with hY
  have hrange_g : Set.range g.base = {IsLocalRing.closedPoint R} := by
    ext z
    simp only [Set.mem_range]
    constructor
    · rintro ⟨x, rfl⟩
      exact IsLocalRing.PrimeSpectrum.comap_residue R x
    · rintro rfl
      exact ⟨⟨⊥, Ideal.isPrime_bot⟩, IsLocalRing.PrimeSpectrum.comap_residue R _⟩
  have hrange_fst : Set.range (pullback.fst f g).base = f.base ⁻¹' {IsLocalRing.closedPoint R} := by
    rw [Scheme.Pullback.range_fst, hrange_g]
  have : PreconnectedSpace Y := by
    have hpre : _root_.IsPreconnected (f.base ⁻¹' {IsLocalRing.closedPoint R}) :=
      AlgebraicGeometry.isPreconnected_preimage_closedPoint_of_isProper_of_bijective_appTop f hΓ
    rw [← hrange_fst, ← Set.image_univ] at hpre
    exact ⟨((pullback.fst f g).isClosedEmbedding.isInducing.isPreconnected_image).mp hpre⟩
  have hX : Nonempty X := by
    by_contra hX
    rw [not_nonempty_iff] at hX
    have htop : (⊤ : X.Opens) = ⊥ := by ext x; exact (IsEmpty.false x).elim
    have hsub : Subsingleton (Γ(X, ⊤) : Type u) := by
      rw [htop]
      exact CommRingCat.subsingleton_of_isTerminal (TopCat.Sheaf.isTerminalOfEmpty X.sheaf)
    have hnt : Nontrivial (Γ(Spec (CommRingCat.of R), ⊤) : Type u) :=
      (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.toRingHom.domain_nontrivial
    obtain ⟨a, b, hab⟩ := hnt
    exact hab (hΓ.1 (hsub.elim _ _))
  have hY : Nonempty Y := by
    obtain ⟨x⟩ := hX
    have hclosed : IsClosed (Set.range f.base) := by
      rw [← Set.image_univ]; exact f.isClosedMap _ isClosed_univ
    have hmem : IsLocalRing.closedPoint R ∈ Set.range f.base :=
      (IsLocalRing.specializes_closedPoint (f.base x)).mem_closed hclosed ⟨x, rfl⟩
    obtain ⟨x', hx'⟩ := hmem
    have : x' ∈ Set.range (pullback.fst f g).base := by rw [hrange_fst]; exact hx'
    obtain ⟨y, _⟩ := this
    exact ⟨y⟩
  obtain ⟨y⟩ := hY
  have : Nontrivial (Γ(Y, ⊤) : Type u) := (Y.presheaf.germ ⊤ y trivial).hom.domain_nontrivial
  have : _root_.IsReduced (Γ(Y, ⊤) : Type u) := inferInstance
  let ιe : (Γ(Spec (CommRingCat.of κ), ⊤) : Type u) ≃+* κ := (Scheme.ΓSpecIso (CommRingCat.of
    κ)).commRingCatIsoToRingEquiv
  let ψ : κ →+* (Γ(Y, ⊤) : Type u) := (pullback.snd f g).appTop.hom.comp ιe.symm.toRingHom
  have hfinTop : (pullback.snd f g).appTop.hom.Finite :=
    AlgebraicGeometry.finite_appTop_of_isProper_of_isNoetherianRing (A := κ) (pullback.snd f g)
  have hψfin : ψ.Finite :=
    RingHom.Finite.comp hfinTop (RingHom.Finite.of_surjective _ ιe.symm.surjective)
  have hψ : Function.Bijective ψ :=
    HconnAux.bijective_of_finite_of_isReduced_of_idempotent ψ hψfin
      (fun e he => HconnAux.idempotent_eq_zero_or_one Y e he)
  have hfac : ⇑(pullback.snd f g).appTop = ψ ∘ ιe := by
    funext s
    change (pullback.snd f g).appTop.hom s = (pullback.snd f g).appTop.hom (ιe.symm (ιe s))
    rw [ιe.symm_apply_apply]
  rw [hfac]
  exact hψ.comp ιe.bijective
end bijective_appTop_pullback_snd_residue_of_bijective_appTop_of_isReduced
end AlgebraicCurves.Geometry.Schemes.Proofs
end ProofImplementation
