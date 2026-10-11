/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelEffCartierDiv_exists_sameDivisorScheme.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import AlgebraicCurves.RelativeDivisors.RelEffCartierDivSum
import AlgebraicCurves.RelativeDivisors.RelEffCartierDiv_exists_split
import AlgebraicCurves.RelativeDivisors.RelEffCartierDiv_exists_I_eq_prodKerGraph
import AlgebraicCurves.Geometry.Schemes.prodKerGraph_comap_mapOnProdOver
import AlgebraicCurves.Foundations.CategoryTheory.CategoryTheory_MorphismProperty_widePullback_base

/-!
Compare relative effective Cartier divisors with the same divisor scheme.
-/

section ProofImplementation

namespace AlgebraicCurves.RelativeDivisors.Proofs.RelEffCartierDiv_exists_sameDivisorScheme
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
open _root_.AlgebraicGeometry

theorem prodKerGraph_congr' {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S) {r : ℕ} {T : Scheme.{u}} {g : T ⟶ S}
    {a a' : Fin r → (T ⟶ 𝒞)} (h : a = a') (ha : ∀ i, a i ≫ f = g) (ha' : ∀ i, a' i ≫ f = g) :
    prodKerGraph f a ha = prodKerGraph f a' ha' := by
  subst h; rfl

namespace RelEffCartierDiv
open _root_.AlgebraicGeometry.RelEffCartierDiv
namespace SameDivisorScheme
open _root_.AlgebraicGeometry.RelEffCartierDiv

variable {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S) [IsSeparated f] [SmoothOfRelativeDimension 1 f] (r : ℕ)


theorem main :
    ∃ (R : Scheme.{u}) (s t : R ⟶ fibrePowOver f r)
      (hst : s ≫ fibrePowOver.toBase f r = t ≫ fibrePowOver.toBase f r),
      IsClosedImmersion (pullback.lift s t hst) ∧
      (IsFinite s ∧ Flat s ∧ LocallyOfFinitePresentation s ∧ Surjective s ∧
        ∀ x, s.finrank x = r.factorial) ∧
      (IsFinite t ∧ Flat t ∧ LocallyOfFinitePresentation t ∧ Surjective t ∧
        ∀ x, t.finrank x = r.factorial) ∧
      ∀ ⦃T' : Scheme.{u}⦄ (u v : T' ⟶ fibrePowOver f r)
        (huv : u ≫ fibrePowOver.toBase f r = v ≫ fibrePowOver.toBase f r),
        (∃ w : T' ⟶ R, w ≫ s = u ∧ w ≫ t = v) ↔
          SameDivisor f (fun i => u ≫ fibrePowOver.proj f r i)
            (fun i => by rw [Category.assoc, fibrePowOver.proj_comp])
            (fun i => v ≫ fibrePowOver.proj f r i)
            (fun i => by rw [Category.assoc, fibrePowOver.proj_comp, huv]) := by
  have hsep : IsSeparated (fibrePowOver.toBase f r) :=
    MorphismProperty.widePullback_base (P := @IsSeparated) (fun _ : Fin r => 𝒞) (fun _ => f)
      fun _ => inferInstance
  obtain ⟨Dt, hDt⟩ := RelEffCartierDiv.exists_I_eq_prodKerGraph (f := f)
    (fibrePowOver.proj f r) (fibrePowOver.proj_comp f r)
  obtain ⟨R, gR, s, hs, b, hb, hfin, hflat, hlfp, hsurj, hrank, hI, huniv⟩ :=
    RelEffCartierDiv.exists_split Dt
  subst hs
  let t : R ⟶ fibrePowOver f r := WidePullback.lift (s ≫ fibrePowOver.toBase f r) b hb
  have ht_proj : ∀ i, t ≫ fibrePowOver.proj f r i = b i := fun i => WidePullback.lift_π _ _ _ _ _
  have ht_base : t ≫ fibrePowOver.toBase f r = s ≫ fibrePowOver.toBase f r :=
    WidePullback.lift_base _ _ _ _
  have key : ∀ {T' : Scheme.{u}} (g' : T' ⟶ S) (u : T' ⟶ fibrePowOver f r)
      (hu : u ≫ fibrePowOver.toBase f r = g'),
      (Dt.pullbackAlong u hu).I = prodKerGraph f (fun i => u ≫ fibrePowOver.proj f r i)
        (fun i => by rw [Category.assoc, fibrePowOver.proj_comp, hu]) := by
    intro T' g' u hu
    change Dt.I.comap (mapOnProdOver f u hu) = _
    rw [hDt]
    exact prodKerGraph_comap_mapOnProdOver _ _ u hu
  have hsplit : ∀ {T' : Scheme.{u}} (w : T' ⟶ R),
      (Dt.pullbackAlong (w ≫ s) rfl).I = prodKerGraph f (fun i => w ≫ b i)
        (fun i => by rw [Category.assoc, hb, Category.assoc]) := by
    intro T' w
    have hw : w ≫ s ≫ fibrePowOver.toBase f r = (w ≫ s) ≫ fibrePowOver.toBase f r :=
      (Category.assoc _ _ _).symm
    rw [← congrArg RelEffCartierDiv.I (Dt.pullbackAlong_comp s rfl w hw)]
    change (Dt.pullbackAlong s rfl).I.comap (mapOnProdOver f w hw) = _
    rw [hI, prodKerGraph_comap_mapOnProdOver]
  have hR : ∀ ⦃T' : Scheme.{u}⦄ (u v : T' ⟶ fibrePowOver f r)
      (huv : u ≫ fibrePowOver.toBase f r = v ≫ fibrePowOver.toBase f r),
      (∃ w : T' ⟶ R, w ≫ s = u ∧ w ≫ t = v) ↔
        SameDivisor f (fun i => u ≫ fibrePowOver.proj f r i)
          (fun i => by rw [Category.assoc, fibrePowOver.proj_comp])
          (fun i => v ≫ fibrePowOver.proj f r i)
          (fun i => by rw [Category.assoc, fibrePowOver.proj_comp, huv]) := by
    intro T' u v huv
    constructor
    · rintro ⟨w, rfl, rfl⟩
      change prodKerGraph f _ _ = prodKerGraph f _ _
      rw [← key ((w ≫ s) ≫ fibrePowOver.toBase f r) (w ≫ s) rfl, hsplit w]
      exact prodKerGraph_congr' f (funext fun i => by rw [Category.assoc, ht_proj]) _ _
    · intro hSD
      obtain ⟨w, ⟨hws, hwb⟩, -⟩ := huniv (u ≫ fibrePowOver.toBase f r) u rfl
        (fun i => v ≫ fibrePowOver.proj f r i)
        (fun i => by rw [Category.assoc, fibrePowOver.proj_comp, huv])
        ((key _ u rfl).trans hSD)
      refine ⟨w, hws, ?_⟩
      apply WidePullback.hom_ext
      · intro i; rw [Category.assoc, ht_proj, hwb]
      · rw [Category.assoc, ht_base, ← Category.assoc, hws, huv]
  have hst : s ≫ fibrePowOver.toBase f r = t ≫ fibrePowOver.toBase f r := ht_base.symm
  have hmono : Mono (pullback.lift s t hst) := ⟨fun {Z} w₁ w₂ h => by
    have h1 : w₁ ≫ s = w₂ ≫ s := by
      simpa only [Category.assoc, pullback.lift_fst] using congrArg (· ≫ pullback.fst _ _) h
    have h2 : w₁ ≫ t = w₂ ≫ t := by
      simpa only [Category.assoc, pullback.lift_snd] using congrArg (· ≫ pullback.snd _ _) h
    obtain ⟨w, -, hwuniq⟩ := huniv ((w₂ ≫ s) ≫ fibrePowOver.toBase f r) (w₂ ≫ s) rfl
      (fun i => w₂ ≫ b i) (fun i => by rw [Category.assoc, hb, Category.assoc]) (hsplit w₂)
    refine (hwuniq w₁ ⟨h1, fun i => ?_⟩).trans (hwuniq w₂ ⟨rfl, fun i => rfl⟩).symm
    rw [← ht_proj, ← Category.assoc, h2, Category.assoc]⟩
  have hfin_st : IsFinite (pullback.lift s t hst) := by
    have : IsFinite (pullback.lift s t hst ≫ pullback.fst _ _) := by
      rw [pullback.lift_fst]; exact hfin
    exact IsFinite.of_comp _ (pullback.fst _ _)
  have hcl : IsClosedImmersion (pullback.lift s t hst) :=
    (IsClosedImmersion.iff_isFinite_and_mono _).mpr ⟨hfin_st, hmono⟩
  have hmem := (hR s t hst).mp ⟨𝟙 R, Category.id_comp _, Category.id_comp _⟩
  have hmem' : ∀ (g : R ⟶ S) (e : s ≫ fibrePowOver.toBase f r = g)
      (h₁ : ∀ i, (t ≫ fibrePowOver.proj f r i) ≫ f = g)
      (h₂ : ∀ i, (s ≫ fibrePowOver.proj f r i) ≫ f = g),
      SameDivisor f (fun i => t ≫ fibrePowOver.proj f r i) h₁
        (fun i => s ≫ fibrePowOver.proj f r i) h₂ := by
    intro g e h₁ h₂; subst e; exact hmem.symm
  obtain ⟨ι, hιs, hιt⟩ := (hR t s hst.symm).mpr (hmem' _ hst _ _)
  have hιι : ι ≫ ι = 𝟙 R := by
    rw [← cancel_mono (pullback.lift s t hst)]
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, Category.id_comp]; rw [hιs, hιt]
    · simp only [Category.assoc, pullback.lift_snd, Category.id_comp]; rw [hιt, hιs]
  have : IsIso ι := ⟨⟨ι, hιι, hιι⟩⟩
  have htι : t = ι ≫ s := hιs.symm
  refine ⟨R, s, t, hst, hcl, ⟨hfin, hflat, hlfp, hsurj, hrank⟩, ?_, hR⟩
  rw [htι]
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance,
    fun x => by rw [Scheme.Hom.finrank_comp_left_of_isIso]; exact hrank x⟩

end RelEffCartierDiv.SameDivisorScheme

end AlgebraicGeometry

theorem _root_.AlgebraicGeometry.RelEffCartierDiv.exists_sameDivisorScheme
    {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S) [IsSeparated f] [SmoothOfRelativeDimension 1 f] (r : ℕ) :
    ∃ (R : Scheme.{u}) (s t : R ⟶ fibrePowOver f r)
      (hst : s ≫ fibrePowOver.toBase f r = t ≫ fibrePowOver.toBase f r),
      IsClosedImmersion (pullback.lift s t hst) ∧
      (IsFinite s ∧ Flat s ∧ LocallyOfFinitePresentation s ∧ Surjective s ∧
        ∀ x, s.finrank x = r.factorial) ∧
      (IsFinite t ∧ Flat t ∧ LocallyOfFinitePresentation t ∧ Surjective t ∧
        ∀ x, t.finrank x = r.factorial) ∧
      ∀ ⦃T' : Scheme.{u}⦄ (u v : T' ⟶ fibrePowOver f r)
        (huv : u ≫ fibrePowOver.toBase f r = v ≫ fibrePowOver.toBase f r),
        (∃ w : T' ⟶ R, w ≫ s = u ∧ w ≫ t = v) ↔
          SameDivisor f (fun i => u ≫ fibrePowOver.proj f r i)
            (fun i => by rw [Category.assoc, fibrePowOver.proj_comp])
            (fun i => v ≫ fibrePowOver.proj f r i)
            (fun i => by rw [Category.assoc, fibrePowOver.proj_comp, huv]) :=
  AlgebraicGeometry.RelEffCartierDiv.SameDivisorScheme.main f r
end AlgebraicCurves.RelativeDivisors.Proofs.RelEffCartierDiv_exists_sameDivisorScheme
end ProofImplementation
