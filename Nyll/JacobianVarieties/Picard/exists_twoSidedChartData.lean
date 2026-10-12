/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_exists_twoSidedChartData.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDiv
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDivSupportedIn
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDivSum
import Nyll.JacobianVarieties.Picard.ThetaBundle
import Nyll.AlgebraicCurves.Geometry.Picard.ChartSections
import Nyll.AlgebraicCurves.Geometry.Sheaves.IdealSheafModule
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDivOfPoint
import Nyll.AlgebraicCurves.RelativeDivisors.Cartier
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurveBase
import Nyll.SchemeTheory.Modules.Monoidal
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurve_exists_sections_injective_comp_fst_eq_comp_of_tensorProduct_algEquiv_pi
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDiv_exists_I_eq_prodKerGraph_and_supportedIn
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDiv_exists_supportedIn_I_eq_mul_of_supportedIn

/-!
# Divisor charts formed from two families of split sections

Split finite algebras give injective families of sections in the smooth locus.
Choose subsets on each side, add their effective Cartier divisors, and transport
the total degree to obtain finite two-sided chart data with the required support.
-/

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.TwoSidedChartData

universe u


open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.RelPicard
open _root_.AlgebraicGeometry.RelPicard
open _root_.NeronModelInfra
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry.SmoothProperCurve
open _root_.TensorProduct


noncomputable section

namespace AlgebraicGeometry

export _root_.AlgebraicGeometry (
  SmoothOfRelativeDimension
  Scheme.Hom
  Spec
  Spec.map
  Scheme
  pullbackRestrictIsoRestrict_inv_fst_assoc
  Scheme.Hom.comp_base
  IsClosedImmersion
  IsSeparated
  smoothOfRelativeDimension_isStableUnderBaseChange
  pullbackRestrictIsoRestrict
  RelEffCartierDiv
  prodKerGraph
  SmoothProperCurve.exists_sections_injective_comp_fst_eq_comp_of_tensorProduct_algEquiv_pi
  RelEffCartierDiv.exists_I_eq_prodKerGraph_and_supportedIn
  RelEffCartierDiv.exists_supportedIn_I_eq_mul_of_supportedIn)

namespace RelPicard
namespace N14ChartData

open _root_.AlgebraicGeometry.RelPicard
open _root_.AlgebraicGeometry


theorem smoothOfRelativeDimension_one_preimage_ι_comp_snd {R : Type u} [CommRing R] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of R)) (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)]
    {Y : Scheme.{u}} (s : Y ⟶ Spec (CommRingCat.of R)) :
    SmoothOfRelativeDimension 1 ((pullback.fst c s ⁻¹ᵁ U).ι ≫ pullback.snd c s) := by
  have h : (pullback.fst c s ⁻¹ᵁ U).ι ≫ pullback.snd c s =
      (pullbackRestrictIsoRestrict (pullback.fst c s) U).inv ≫
        (pullbackSymmetry (pullback.fst c s) U.ι).hom ≫
        (pullbackRightPullbackFstIso c s U.ι).hom ≫ pullback.snd (U.ι ≫ c) s := by
    rw [pullbackRightPullbackFstIso_hom_snd, pullbackSymmetry_hom_comp_snd_assoc,
      pullbackRestrictIsoRestrict_inv_fst_assoc]
  have hpb : SmoothOfRelativeDimension 1 (pullback.snd (U.ι ≫ c) s) :=
    SmoothOfRelativeDimension.pullback_snd 1 (U.ι ≫ c) s
  have hright : SmoothOfRelativeDimension 1
      ((pullbackRightPullbackFstIso c s U.ι).hom ≫ pullback.snd (U.ι ≫ c) s) :=
    smoothOfRelativeDimension_comp 0 1 _ _
  have hmiddle : SmoothOfRelativeDimension 1
      ((pullbackSymmetry (pullback.fst c s) U.ι).hom ≫
        (pullbackRightPullbackFstIso c s U.ι).hom ≫ pullback.snd (U.ι ≫ c) s) :=
    smoothOfRelativeDimension_comp 0 1 _ _
  rw [h]
  exact smoothOfRelativeDimension_comp 0 1 _ _

/-- Regard the same relative effective Cartier divisor at an equal degree. -/
def castDeg {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} {T : Scheme.{u}} {g : T ⟶ S} {r s : ℕ} (h : r = s)
    (D : RelEffCartierDiv f r g) : RelEffCartierDiv f s g :=
  ⟨D.I, D.isFinite, D.flat, D.locallyOfFinitePresentation, fun t => (D.finrank_eq t).trans h⟩

@[scoped simp] theorem castDeg_I {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} {T : Scheme.{u}} {g : T ⟶ S}
    {r s : ℕ} (h : r = s)
    (D : RelEffCartierDiv f r g) : (castDeg h D).I = D.I := rfl

theorem castDeg_supportedIn {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} {T : Scheme.{u}} {g : T ⟶ S} {r s : ℕ}
    (h : r = s)
    (D : RelEffCartierDiv f r g) {U : 𝒞.Opens} (hD : D.SupportedIn U) :
        (castDeg h D).SupportedIn U := hD

/-- Choices of disjoint-side section indices and a root in every split algebra. -/
abbrev ChartIdx (e M M' : ℕ) (deg : Fin M → ℕ) (deg' : Fin M' → ℕ) : Type :=
  Σ p : {p : Fin (e + 1) × Fin (e + 1) // (p.1 : ℕ) + p.2 = e},
    {a : Fin p.1.1 → Fin M // Function.Injective a} ×
    {a' : Fin p.1.2 → Fin M' // Function.Injective a'} ×
      (∀ i, Fin (deg i)) × (∀ i, Fin (deg' i))

scoped instance (e M M' : ℕ) (deg : Fin M → ℕ) (deg' : Fin M' → ℕ) :
    Finite (ULift.{u} (ChartIdx e M M' deg deg')) := by
  classical
  infer_instance

theorem range_subset_preimage_of_comp_eq {X C T Y : Scheme.{u}} (s : T ⟶ X) (p : X ⟶ C) (y : T ⟶ Y)
    (z : Y ⟶ C)
    (h : s ≫ p = y ≫ z) (U : C.Opens) (hzU : Set.range z.base ⊆ (U : Set C)) :
    Set.range s.base ⊆ ((p ⁻¹ᵁ U : X.Opens) : Set X) := by
  rintro _ ⟨t, rfl⟩
  change p.base (s.base t) ∈ U
  have e := congrArg (fun k : T ⟶ C => k.base t) h
  simp only [Scheme.Hom.comp_base, TopCat.comp_app] at e
  rw [e]
  exact hzU ⟨_, rfl⟩

end AlgebraicGeometry.RelPicard.N14ChartData

open scoped _root_.JacobianVarieties.Picard.Proofs.TwoSidedChartData.AlgebraicGeometry
open scoped _root_.JacobianVarieties.Picard.Proofs.TwoSidedChartData.AlgebraicGeometry.RelPicard
open scoped
  _root_.JacobianVarieties.Picard.Proofs.TwoSidedChartData.AlgebraicGeometry.RelPicard.N14ChartData


open scoped _root_.JacobianVarieties.Picard.Proofs.TwoSidedChartData.AlgebraicGeometry
open scoped _root_.JacobianVarieties.Picard.Proofs.TwoSidedChartData.AlgebraicGeometry.RelPicard


open scoped _root_.JacobianVarieties.Picard.Proofs.TwoSidedChartData.AlgebraicGeometry


open AlgebraicGeometry.RelPicard.N14ChartData in
theorem _root_.AlgebraicGeometry.RelPicard.exists_twoSidedChartData
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsSeparated c]
    (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)]
    (A : Type u) [CommRing A] [Algebra R A] [Nontrivial A]
    {M M' : ℕ} (B : Fin M → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)]
    (B' : Fin M' → Type u) [∀ i, CommRing (B' i)] [∀ i, Algebra R (B' i)]
    (deg : Fin M → ℕ) (φ : ∀ i, TensorProduct R A (B i) ≃ₐ[A] (Fin (deg i) → A))
    (deg' : Fin M' → ℕ) (φ' : ∀ i, TensorProduct R A (B' i) ≃ₐ[A] (Fin (deg' i) → A))
    (z : ∀ i, Spec (CommRingCat.of (B i)) ⟶ C) [∀ i, IsClosedImmersion (z i)]
    (z' : ∀ i, Spec (CommRingCat.of (B' i)) ⟶ C) [∀ i, IsClosedImmersion (z' i)]
    (hz : ∀ i, z i ≫ c = Spec.map (CommRingCat.ofHom (algebraMap R (B i))))
    (hz' : ∀ i, z' i ≫ c = Spec.map (CommRingCat.ofHom (algebraMap R (B' i))))
    (hzU : ∀ i, Set.range (z i).base ⊆ (U : Set C))
    (hz'U : ∀ i, Set.range (z' i).base ⊆ (U : Set C))
    (e : ℕ) :
    ∃ (σ : ∀ i, Fin (deg i) → SchemeHomOver (𝟙 (Spec (CommRingCat.of A))) (baseChange R c A))
      (σ' : ∀ i, Fin (deg' i) → SchemeHomOver (𝟙 (Spec (CommRingCat.of A))) (baseChange R c A))
      (_ : ∀ i, Function.Injective (σ i)) (_ : ∀ i, Function.Injective (σ' i))
      (_ : ∀ i m, ∃ y : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of (B i)),
        (σ i m).1 ≫ pullback.fst c (specMap R A) = y ≫ z i)
      (_ : ∀ i m, ∃ y : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of (B' i)),
        (σ' i m).1 ≫ pullback.fst c (specMap R A) = y ≫ z' i)
      (ι : Type u) (_ : Finite ι)
      (idx : ∀ (e₁ e₂ : ℕ), e₁ + e₂ = e → {a : Fin e₁ → Fin M // Function.Injective a} →
        {a' : Fin e₂ → Fin M' // Function.Injective a'} →
          (∀ i, Fin (deg i)) → (∀ i, Fin (deg' i)) → ι)
      (Dγ : ι → RelEffCartierDiv (baseChange R c A) e (𝟙 (Spec (CommRingCat.of A)))),
      (∀ (e₁ e₂ : ℕ) (he : e₁ + e₂ = e) (a : {a : Fin e₁ → Fin M // Function.Injective a})
        (a' : {a' : Fin e₂ → Fin M' // Function.Injective a'})
        (m : ∀ i, Fin (deg i))
        (m' : ∀ i, Fin (deg' i)),
        (Dγ (idx e₁ e₂ he a a' m m')).I =
          prodKerGraph (baseChange R c A)
            (fun j => (σ (a.1 j) (m (a.1 j))).1) (fun j => (σ (a.1 j) (m (a.1 j))).2) *
          prodKerGraph (baseChange R c A)
            (fun j => (σ' (a'.1 j) (m' (a'.1 j))).1) (fun j => (σ' (a'.1 j) (m' (a'.1 j))).2)) ∧
      (∀ i, (Dγ i).SupportedIn (pullback.fst c (specMap R A) ⁻¹ᵁ U)) := by
  classical
  have : IsSeparated (baseChange R c A) := inferInstance
  have : SmoothOfRelativeDimension 1 ((pullback.fst c (specMap R A) ⁻¹ᵁ U).ι ≫ baseChange R c A) :=
    smoothOfRelativeDimension_one_preimage_ι_comp_snd c U (specMap R A)
  have hsec := fun i => exists_sections_injective_comp_fst_eq_comp_of_tensorProduct_algEquiv_pi
    R c A (B i) (deg i) (φ i) (z i) (hz i)
  have hsec' := fun i => exists_sections_injective_comp_fst_eq_comp_of_tensorProduct_algEquiv_pi
    R c A (B' i) (deg' i) (φ' i) (z' i) (hz' i)
  choose σ hσinj hσfac using hsec
  choose σ' hσ'inj hσ'fac using hsec'
  have hσU : ∀ i m, Set.range (σ i m).1.base ⊆
      ((pullback.fst c (specMap R A) ⁻¹ᵁ U : (pullback c (specMap R A)).Opens) :
        Set ↥(pullback c (specMap R A))) :=
    fun i m => by
      obtain ⟨y, hy⟩ := hσfac i m
      exact range_subset_preimage_of_comp_eq _ _ _ _ hy U (hzU i)
  have hσ'U : ∀ i m, Set.range (σ' i m).1.base ⊆
      ((pullback.fst c (specMap R A) ⁻¹ᵁ U : (pullback c (specMap R A)).Opens) :
        Set ↥(pullback c (specMap R A))) :=
    fun i m => by
      obtain ⟨y, hy⟩ := hσ'fac i m
      exact range_subset_preimage_of_comp_eq _ _ _ _ hy U (hz'U i)
  have hDn : ∀ (k : ℕ) (a : Fin k → Fin M) (m : ∀ i, Fin (deg i)),
      ∃ D : RelEffCartierDiv (baseChange R c A) k (𝟙 (Spec (CommRingCat.of A))),
        D.I = prodKerGraph (baseChange R c A)
          (fun j => (σ (a j) (m (a j))).1) (fun j => (σ (a j) (m (a j))).2) ∧
        D.SupportedIn (pullback.fst c (specMap R A) ⁻¹ᵁ U) := fun k a m =>
    RelEffCartierDiv.exists_I_eq_prodKerGraph_and_supportedIn (pullback.fst c (specMap R A) ⁻¹ᵁ U)
      _ _ (fun j => hσU (a j) (m (a j)))
  have hDf : ∀ (k : ℕ) (a' : Fin k → Fin M') (m' : ∀ i, Fin (deg' i)),
      ∃ D : RelEffCartierDiv (baseChange R c A) k (𝟙 (Spec (CommRingCat.of A))),
        D.I = prodKerGraph (baseChange R c A)
          (fun j => (σ' (a' j) (m' (a' j))).1) (fun j => (σ' (a' j) (m' (a' j))).2) ∧
        D.SupportedIn (pullback.fst c (specMap R A) ⁻¹ᵁ U) := fun k a' m' =>
    RelEffCartierDiv.exists_I_eq_prodKerGraph_and_supportedIn (pullback.fst c (specMap R A) ⁻¹ᵁ U)
      _ _ (fun j => hσ'U (a' j) (m' (a' j)))
  choose Dn hDnI hDnU using hDn
  choose Df hDfI hDfU using hDf
  have hF : ∀ (k₁ k₂ : ℕ) (a : Fin k₁ → Fin M) (a' : Fin k₂ → Fin M')
      (m : ∀ i, Fin (deg i))
      (m' : ∀ i, Fin (deg' i)),
      ∃ F : RelEffCartierDiv (baseChange R c A) (k₁ + k₂) (𝟙 (Spec (CommRingCat.of A))),
        F.I = (Dn k₁ a m).I * (Df k₂ a' m').I ∧
          F.SupportedIn (pullback.fst c (specMap R A) ⁻¹ᵁ U) :=
    fun k₁ k₂ a a' m m' =>
      RelEffCartierDiv.exists_supportedIn_I_eq_mul_of_supportedIn
        (pullback.fst c (specMap R A) ⁻¹ᵁ U)
        (Dn k₁ a m) (Df k₂ a' m') (hDnU k₁ a m) (hDfU k₂ a' m')
  choose F hFI hFU using hF
  refine ⟨σ, σ', hσinj, hσ'inj, hσfac, hσ'fac, ULift.{u} (ChartIdx e M M' deg deg'), inferInstance,
    fun e₁ e₂ he a a' m m' => ⟨⟨(⟨e₁, by omega⟩, ⟨e₂, by omega⟩), he⟩, a, a', m, m'⟩,
    fun i => castDeg i.down.1.2
      (F i.down.1.1.1 i.down.1.1.2 i.down.2.1.1 i.down.2.2.1.1
        i.down.2.2.2.1 i.down.2.2.2.2), ?_, ?_⟩
  · intro e₁ e₂ he a a' m m'
    rw [castDeg_I, hFI, hDnI, hDfI]
  · intro i
    exact castDeg_supportedIn _ _ (hFU _ _ _ _ _ _)
end
end JacobianVarieties.Picard.Proofs.TwoSidedChartData
end ProofImplementation
