/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelEffCartierDiv_exists_isUniversal_of_isAffine.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDivSum
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDivFunctor
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDiv_exists_split
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDiv_exists_I_eq_prodKerGraph
import Nyll.AlgebraicCurves.Geometry.Schemes.prodKerGraph_comap_mapOnProdOver
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDiv_exists_sameDivisorScheme
import Nyll.AlgebraicCurves.Foundations.CategoryTheory.CategoryTheory_MorphismProperty_widePullback_base
import Nyll.AlgebraicCurves.Geometry.Schemes.Scheme_exists_affine_quotient_of_finiteLocallyFree_equivalenceRelation
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDiv_existsUnique_pullbackAlong_eq_of_isPullback_of_isAffine
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDiv_pullbackAlong_injective

/-!
Existence of a universal relative effective Cartier divisor over an affine scheme.
-/

section ProofImplementation

namespace AlgebraicCurves.RelativeDivisors.Proofs.RelEffCartierDiv_exists_isUniversal_of_isAffine
open _root_.AlgebraicGeometry.Scheme.IdealSheafData.IdealHom in
open _root_.AlgebraicGeometry.Scheme.IdealSheafData.IdealHom in
attribute [-instance]
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub
  instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop
  instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero
attribute [-simp]
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

universe v u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace RelEffCartierDiv
open _root_.AlgebraicGeometry.RelEffCartierDiv
namespace ChartAffine
open _root_.AlgebraicGeometry.RelEffCartierDiv
open _root_.AlgebraicGeometry

theorem prodKerGraph_congr'' {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S) {r : ℕ} {T : Scheme.{u}} {g : T ⟶ S}
    {a a' : Fin r → (T ⟶ 𝒞)} (h : a = a') (ha : ∀ i, a i ≫ f = g) (ha' : ∀ i, a' i ≫ f = g) :
    prodKerGraph f a ha = prodKerGraph f a' ha' := by
  subst h; rfl

lemma pullbackAlong_congr_hom {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} {r : ℕ} {T T' : Scheme.{u}}
    {g : T ⟶ S} {g' : T' ⟶ S} (D : RelEffCartierDiv f r g') {φ₁ φ₂ : T ⟶ T'} (e : φ₁ = φ₂)
    (h₁ : φ₁ ≫ g' = g) (h₂ : φ₂ ≫ g' = g) : D.pullbackAlong φ₁ h₁ = D.pullbackAlong φ₂ h₂ := by
  subst e; rfl

lemma pullbackAlong_congr_base {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} {r : ℕ} {T T' : Scheme.{u}}
    {g₁ g₂ : T ⟶ S} {g' : T' ⟶ S} (D : RelEffCartierDiv f r g') (e : g₁ = g₂)
    {φ ψ : T ⟶ T'} (hφ₁ : φ ≫ g' = g₁) (hψ₁ : ψ ≫ g' = g₁) (hφ₂ : φ ≫ g' = g₂) (hψ₂ : ψ ≫ g' = g₂)
    (h : D.pullbackAlong φ hφ₁ = D.pullbackAlong ψ hψ₁) :
    (D.pullbackAlong φ hφ₂).I = (D.pullbackAlong ψ hψ₂).I := by
  subst e; exact congrArg RelEffCartierDiv.I h

lemma sameDivisor_symm' {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S) {r : ℕ} {T : Scheme.{u}} {g g' : T ⟶ S}
    (e : g = g') {a b : Fin r → (T ⟶ 𝒞)} (ha : ∀ i, a i ≫ f = g) (hb : ∀ i, b i ≫ f = g)
    (hb' : ∀ i, b i ≫ f = g') (ha' : ∀ i, a i ≫ f = g') :
    SameDivisor f a ha b hb → SameDivisor f b hb' a ha' := by
  subst e; exact fun h => h.symm

lemma sameDivisor_trans' {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S) {r : ℕ} {T : Scheme.{u}}
    {g g' g'' : T ⟶ S} (e : g = g') (e' : g = g'') {a b c : Fin r → (T ⟶ 𝒞)}
    (ha : ∀ i, a i ≫ f = g) (hb : ∀ i, b i ≫ f = g)
    (hb' : ∀ i, b i ≫ f = g') (hc' : ∀ i, c i ≫ f = g')
    (ha'' : ∀ i, a i ≫ f = g'') (hc'' : ∀ i, c i ≫ f = g'') :
    SameDivisor f a ha b hb → SameDivisor f b hb' c hc' → SameDivisor f a ha'' c hc'' := by
  subst e; subst e'; exact fun h h' => h.trans h'

variable {𝒞 S : Scheme.{u}} [IsAffine 𝒞] [IsAffine S] (f : 𝒞 ⟶ S)
  [IsSeparated f] [SmoothOfRelativeDimension 1 f] (r : ℕ)

theorem main : ∃ (Y : Scheme.{u}) (_ : IsAffine Y) (y : Y ⟶ S) (Duniv : RelEffCartierDiv f r y),
    Duniv.IsUniversal := by
  have haffHom : IsAffineHom (fibrePowOver.toBase f r) :=
    MorphismProperty.widePullback_base (P := @IsAffineHom) (fun _ : Fin r => 𝒞) (fun _ => f)
      fun _ => inferInstance
  have hXaff : IsAffine (fibrePowOver f r) := isAffine_of_isAffineHom (fibrePowOver.toBase f r)
  obtain ⟨Dt, hDt⟩ := RelEffCartierDiv.exists_I_eq_prodKerGraph (f := f)
    (fibrePowOver.proj f r) (fibrePowOver.proj_comp f r)
  have key : ∀ {T' : Scheme.{u}} (g' : T' ⟶ S) (u : T' ⟶ fibrePowOver f r)
      (hu : u ≫ fibrePowOver.toBase f r = g'),
      (Dt.pullbackAlong u hu).I = prodKerGraph f (fun i => u ≫ fibrePowOver.proj f r i)
        (fun i => by rw [Category.assoc, fibrePowOver.proj_comp, hu]) := by
    intro T' g' u hu
    change Dt.I.comap (mapOnProdOver f u hu) = _
    rw [hDt]
    exact prodKerGraph_comap_mapOnProdOver _ _ u hu
  obtain ⟨R, s, t, hst, hcl, ⟨hsfin, hsflat, hslfp, hssurj, -⟩, ⟨htfin, htflat, htlfp, htsurj,
    -⟩, hR⟩ :=
    RelEffCartierDiv.exists_sameDivisorScheme f r
  have hmono : ∀ {T : Scheme.{u}} (a b : T ⟶ R), a ≫ s = b ≫ s → a ≫ t = b ≫ t → a = b := by
    intro T a b h1 h2
    rw [← cancel_mono (pullback.lift s t hst)]
    apply pullback.hom_ext
    · simpa only [Category.assoc, pullback.lift_fst] using h1
    · simpa only [Category.assoc, pullback.lift_snd] using h2
  have hequiv : ∀ T : Scheme.{u},
      _root_.Equivalence fun x y : T ⟶ fibrePowOver f r => ∃ φ : T ⟶ R, φ ≫ s = x ∧ φ ≫ t = y := by
    intro T
    have hbase : ∀ {x y : T ⟶ fibrePowOver f r}, (∃ φ : T ⟶ R, φ ≫ s = x ∧ φ ≫ t = y) →
        x ≫ fibrePowOver.toBase f r = y ≫ fibrePowOver.toBase f r := by
      rintro x y ⟨φ, rfl, rfl⟩
      rw [Category.assoc, Category.assoc, hst]
    refine ⟨fun x => (hR x x rfl).mpr rfl, fun {x y} hxy => ?_, fun {x y z} hxy hyz => ?_⟩
    · have hb := hbase hxy
      exact (hR y x hb.symm).mpr (sameDivisor_symm' f hb _ _ _ _ ((hR x y hb).mp hxy))
    · have hb₁ := hbase hxy
      have hb₂ := hbase hyz
      exact (hR x z (hb₁.trans hb₂)).mpr
        (sameDivisor_trans' f hb₁ rfl _ _ _ _ _ _ ((hR x y hb₁).mp hxy) ((hR y z hb₂).mp hyz))
  obtain ⟨Y, hYaff, p, w, hpfin, hpflat, hplfp, hpsurj, hsq, ⟨hcoeq⟩⟩ :=
    Scheme.exists_affine_quotient_of_finiteLocallyFree_equivalenceRelation s t hmono hequiv
  have hwb : s ≫ fibrePowOver.toBase f r = t ≫ fibrePowOver.toBase f r := hst
  let y : Y ⟶ S := Cofork.IsColimit.desc hcoeq (fibrePowOver.toBase f r) hwb
  have hp : p ≫ y = fibrePowOver.toBase f r := Cofork.IsColimit.π_desc' hcoeq _ hwb
  have hinv : Dt.pullbackAlong s rfl = Dt.pullbackAlong t hst.symm := by
    apply RelEffCartierDiv.ext
    rw [key _ s rfl, key _ t hst.symm]
    exact (hR s t hst).mp ⟨𝟙 R, Category.id_comp _, Category.id_comp _⟩
  obtain ⟨DY, hDY, -⟩ := RelEffCartierDiv.existsUnique_pullbackAlong_eq_of_isPullback_of_isAffine
    (gR := s ≫ fibrePowOver.toBase f r) p hp s t rfl hst.symm hsq Dt hinv
  refine ⟨Y, hYaff, y, DY, ?_⟩
  intro T g D
  obtain ⟨P, gP, π, hπ, b, hb, hπfin, hπflat, hπlfp, hπsurj, -, hI, -⟩ := D.exists_split
  let u : P ⟶ fibrePowOver f r := WidePullback.lift gP b hb
  have hub : ∀ i, u ≫ fibrePowOver.proj f r i = b i := fun i => WidePullback.lift_π _ _ _ _ _
  have hutb : u ≫ fibrePowOver.toBase f r = gP := WidePullback.lift_base _ _ _ _
  have hDu : Dt.pullbackAlong u hutb = D.pullbackAlong π hπ := by
    apply RelEffCartierDiv.ext
    rw [key _ u hutb, hI]
    exact prodKerGraph_congr'' f (funext hub) _ _
  have hcompat : ∀ {Z : Scheme.{u}} (g₁ g₂ : Z ⟶ P), g₁ ≫ π = g₂ ≫ π →
      g₁ ≫ (u ≫ p) = g₂ ≫ (u ≫ p) := by
    intro Z g₁ g₂ h12
    have hb12 : (g₁ ≫ u) ≫ fibrePowOver.toBase f r = (g₂ ≫ u) ≫ fibrePowOver.toBase f r := by
      rw [Category.assoc, Category.assoc, hutb, ← hπ, reassoc_of% h12]
    have hsd : SameDivisor f (fun i => (g₁ ≫ u) ≫ fibrePowOver.proj f r i)
        (fun i => by rw [Category.assoc, fibrePowOver.proj_comp])
        (fun i => (g₂ ≫ u) ≫ fibrePowOver.proj f r i)
        (fun i => by rw [Category.assoc, fibrePowOver.proj_comp, hb12]) := by
      change prodKerGraph f _ _ = prodKerGraph f _ _
      rw [← key _ (g₁ ≫ u) rfl, ← key _ (g₂ ≫ u) hb12.symm]
      have hg₁ : g₁ ≫ gP = (g₁ ≫ u) ≫ fibrePowOver.toBase f r := by rw [Category.assoc, hutb]
      have hg₂ : g₂ ≫ gP = (g₁ ≫ u) ≫ fibrePowOver.toBase f r := by
        rw [hb12, Category.assoc, hutb]
      have e1 := Dt.pullbackAlong_comp u hutb g₁ hg₁
      have e2 := Dt.pullbackAlong_comp u hutb g₂ hg₂
      rw [hDu, D.pullbackAlong_comp] at e1 e2
      exact congrArg RelEffCartierDiv.I
        (e1.symm.trans ((pullbackAlong_congr_hom D (by rw [h12]) _ _).trans e2))
    obtain ⟨φ, h1, h2⟩ := (hR (g₁ ≫ u) (g₂ ≫ u) hb12).mpr hsd
    calc g₁ ≫ u ≫ p = φ ≫ s ≫ p := by rw [← Category.assoc, ← h1, Category.assoc]
      _ = φ ≫ t ≫ p := by rw [w]
      _ = g₂ ≫ u ≫ p := by rw [← Category.assoc, h2, Category.assoc]
  let φT : T ⟶ Y := EffectiveEpi.desc π (u ≫ p) hcompat
  have hfac : π ≫ φT = u ≫ p := EffectiveEpi.fac π (u ≫ p) hcompat
  have hφy : φT ≫ y = g := by
    rw [← cancel_epi π, reassoc_of% hfac, hp, hutb, hπ]
  have hDφT : DY.pullbackAlong φT hφy = D := by
    apply RelEffCartierDiv.pullbackAlong_injective π hπ
    change (DY.pullbackAlong φT hφy).pullbackAlong π hπ = D.pullbackAlong π hπ
    rw [DY.pullbackAlong_comp, pullbackAlong_congr_hom DY hfac _
      (by rw [Category.assoc, hp, hutb]), ← DY.pullbackAlong_comp p hp u hutb, hDY, hDu]
  refine ⟨⟨φT, hφy⟩, (congrArg RelEffCartierDiv.I hDφT :), ?_⟩
  rintro ⟨φ', hφ'y⟩ hPB'
  have hD' : DY.pullbackAlong φ' hφ'y = D := (PullsBackOver.eq_pullbackAlong hPB').symm
  apply Subtype.ext
  change φ' = φT
  let pr := pullback.fst φ' p
  let v := pullback.snd φ' p
  let q₁ := pullback.fst pr π
  let q₂ := pullback.snd pr π
  let k : pullback pr π ⟶ S := (q₁ ≫ pr) ≫ g
  have hv : (q₁ ≫ v) ≫ fibrePowOver.toBase f r = k := by
    simp only [k, Category.assoc, ← hp, ← hφ'y]
    rw [← pullback.condition_assoc]
  have hu' : (q₂ ≫ u) ≫ fibrePowOver.toBase f r = k := by
    simp only [k, Category.assoc, hutb, ← hπ]
    rw [← pullback.condition_assoc]
  have E : Dt.pullbackAlong (q₁ ≫ v) hv = Dt.pullbackAlong (q₂ ≫ u) hu' := by
    have L : Dt.pullbackAlong (q₁ ≫ v) hv = D.pullbackAlong (q₁ ≫ pr) rfl := by
      rw [← hDY, DY.pullbackAlong_comp, pullbackAlong_congr_hom DY
        (show (q₁ ≫ v) ≫ p = (q₁ ≫ pr) ≫ φ' by rw [Category.assoc, Category.assoc,
          pullback.condition]) _ (by rw [Category.assoc, hφ'y]),
        ← DY.pullbackAlong_comp φ' hφ'y (q₁ ≫ pr) rfl, hD']
    have R' : Dt.pullbackAlong (q₂ ≫ u) hu' = D.pullbackAlong (q₁ ≫ pr) rfl := by
      rw [← hDY, DY.pullbackAlong_comp, pullbackAlong_congr_hom DY
        (show (q₂ ≫ u) ≫ p = (q₂ ≫ π) ≫ φT by rw [Category.assoc, Category.assoc, hfac]) _
          (by rw [Category.assoc, hφy]; change (q₂ ≫ π) ≫ g = (q₁ ≫ pr) ≫ g
              change (pullback.snd pr π ≫ π) ≫ g = (pullback.fst pr π ≫ pr) ≫ g
              rw [pullback.condition]),
        ← DY.pullbackAlong_comp φT hφy (q₂ ≫ π) (show (q₂ ≫ π) ≫ g = k by
          change (pullback.snd pr π ≫ π) ≫ g = (pullback.fst pr π ≫ pr) ≫ g
          rw [pullback.condition]), hDφT]
      exact pullbackAlong_congr_hom D (pullback.condition (f := pr) (g := π)).symm _ _
    exact L.trans R'.symm
  have hsd : SameDivisor f (fun i => (q₁ ≫ v) ≫ fibrePowOver.proj f r i)
      (fun i => by rw [Category.assoc, fibrePowOver.proj_comp])
      (fun i => (q₂ ≫ u) ≫ fibrePowOver.proj f r i)
      (fun i => by rw [Category.assoc, fibrePowOver.proj_comp, hu', hv]) := by
    change prodKerGraph f _ _ = prodKerGraph f _ _
    rw [← key _ (q₁ ≫ v) rfl, ← key _ (q₂ ≫ u) (hu'.trans hv.symm)]
    exact pullbackAlong_congr_base Dt hv.symm _ _ _ _ E
  obtain ⟨ρ, hρs, hρt⟩ := (hR (q₁ ≫ v) (q₂ ≫ u) (hv.trans hu'.symm)).mpr hsd
  have hvp : (q₁ ≫ v) ≫ p = (q₂ ≫ u) ≫ p := by
    rw [← hρs, Category.assoc, w, ← Category.assoc, hρt]
  have : Epi (q₁ ≫ pr) := epi_comp _ _
  rw [← cancel_epi (q₁ ≫ pr)]
  calc (q₁ ≫ pr) ≫ φ' = (q₁ ≫ v) ≫ p := by
        rw [Category.assoc, Category.assoc, pullback.condition]
    _ = (q₂ ≫ u) ≫ p := hvp
    _ = (q₂ ≫ π) ≫ φT := by rw [Category.assoc, Category.assoc, hfac]
    _ = (q₁ ≫ pr) ≫ φT := by
        change (pullback.snd pr π ≫ π) ≫ φT = (pullback.fst pr π ≫ pr) ≫ φT
        rw [pullback.condition]

end AlgebraicGeometry.RelEffCartierDiv.ChartAffine

theorem _root_.AlgebraicGeometry.RelEffCartierDiv.exists_isUniversal_of_isAffine
    {𝒞 S : Scheme.{u}} [IsAffine 𝒞] [IsAffine S] (f : 𝒞 ⟶ S)
    [IsSeparated f] [SmoothOfRelativeDimension 1 f] (r : ℕ) :
    ∃ (Y : Scheme.{u}) (_ : IsAffine Y) (y : Y ⟶ S) (Duniv : RelEffCartierDiv f r y),
      Duniv.IsUniversal :=
  AlgebraicGeometry.RelEffCartierDiv.ChartAffine.main f r
end AlgebraicCurves.RelativeDivisors.Proofs.RelEffCartierDiv_exists_isUniversal_of_isAffine
end ProofImplementation

open _root_.AlgebraicGeometry.Scheme.IdealSheafData.IdealHom in
open _root_.AlgebraicGeometry.Scheme.IdealSheafData.IdealHom in
attribute [-instance]
  AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero
  AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one
  AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd
  AlgebraicGeometry.isClosedImmersion_graphOver
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub
  instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop
  instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero
attribute [-simp]
  AlgebraicGeometry.prodKerGraph_one
  AlgebraicGeometry.fibrePowOver.proj_comp
  AlgebraicGeometry.prodKerGraph_zero
  AlgebraicGeometry.RelEffCartierDiv.empty_I
  AlgebraicGeometry.fibrePowOver.proj_comp_assoc
  AlgebraicGeometry.graphOver_fst_assoc
  AlgebraicGeometry.RelEffCartierDiv.toPoint_comp
  AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc
  AlgebraicGeometry.graphOver_fst
  AlgebraicGeometry.RelEffCartierDiv.ofPoint_I
  AlgebraicGeometry.graphOver_snd
  AlgebraicGeometry.graphOver_snd_assoc
  AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec
  AlgebraicCurve.SymmetricPowerPackage.mk.injEq
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
