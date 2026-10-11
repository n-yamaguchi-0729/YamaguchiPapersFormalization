/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_etale_schemeNsmul_of_isUnit_of_smoothOfRelativeDimension.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.RingTheory.Smooth.StandardSmooth
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import Mathlib.RingTheory.RingHom.StandardSmooth
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.Kernel
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.Theorems.RelativeGroupLaw_formallyUnramified_schemeNsmul_of_isUnit_of_isLocalRing

/-!
# Etaleness from smoothness of equal relative dimension

Formal unramifiedness and smoothness of the two structure maps imply etaleness.
This criterion applies to multiplication maps of a smooth relative group law.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.AbelianSchemes.Theorems.Proofs
namespace RelativeGroupLaw_etale_schemeNsmul_of_isUnit_of_smoothOfRelativeDimension

open _root_.KaehlerDifferential
open _root_.Algebra
open _root_.TensorProduct
open _root_.Algebra.TensorProduct

universe u

namespace R1NeronObjE4

section algebra

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]

theorem subsingleton_kaehler_of_surjective
    (h : Function.Surjective (KaehlerDifferential.mapBaseChange R S T)) :
    Subsingleton Ω[T⁄S] := by
  have hex := KaehlerDifferential.exact_mapBaseChange_map R S T
  have hsurj := KaehlerDifferential.map_surjective R S T
  refine ⟨fun a b => ?_⟩
  obtain ⟨a', rfl⟩ := hsurj a
  obtain ⟨b', rfl⟩ := hsurj b
  have ha : KaehlerDifferential.map R S T T a' = 0 := by
    obtain ⟨x, rfl⟩ := h a'
    exact hex.apply_apply_eq_zero x
  have hb : KaehlerDifferential.map R S T T b' = 0 := by
    obtain ⟨x, rfl⟩ := h b'
    exact hex.apply_apply_eq_zero x
  rw [ha, hb]

theorem formallyEtale_of_formallySmooth_of_bijective [Algebra.FormallySmooth R T]
    (h : Function.Bijective (KaehlerDifferential.mapBaseChange R S T)) :
    Algebra.FormallyEtale S T := by
  have hΩ : Subsingleton Ω[T⁄S] := subsingleton_kaehler_of_surjective h.2
  have : Algebra.FormallyUnramified S T := ⟨hΩ⟩
  have hδ : ∀ x, Algebra.H1Cotangent.δ R S T x = 0 := by
    intro x
    have hex := Algebra.H1Cotangent.exact_δ_mapBaseChange R S T
    have hmem : Algebra.H1Cotangent.δ R S T x ∈
        LinearMap.ker (KaehlerDifferential.mapBaseChange R S T) := by
      rw [LinearMap.mem_ker]
      exact hex.apply_apply_eq_zero x
    rwa [LinearMap.ker_eq_bot.mpr h.1, Submodule.mem_bot] at hmem
  have hH1 : Subsingleton (Algebra.H1Cotangent S T) := by
    refine ⟨fun a b => ?_⟩
    have hex := Algebra.H1Cotangent.exact_map_δ R S T
    have ha : a ∈ Set.range (Algebra.H1Cotangent.map R S T T) := (hex a).mp (hδ a)
    have hb : b ∈ Set.range (Algebra.H1Cotangent.map R S T T) := (hex b).mp (hδ b)
    obtain ⟨a', rfl⟩ := ha
    obtain ⟨b', rfl⟩ := hb
    rw [Subsingleton.elim a' b']
  have : Module.Projective T Ω[T⁄S] := Module.Projective.of_free
  have : Algebra.FormallySmooth S T := ⟨inferInstance, hH1⟩
  exact Algebra.FormallyEtale.of_formallyUnramified_and_formallySmooth

theorem mapBaseChange_surjective_of_formallyUnramified [Algebra.FormallyUnramified S T] :
    Function.Surjective (KaehlerDifferential.mapBaseChange R S T) := by
  intro y
  have hex := KaehlerDifferential.exact_mapBaseChange_map R S T
  have hy : KaehlerDifferential.map R S T T y = 0 := Subsingleton.elim _ _
  exact (hex y).mp hy

theorem bijective_of_surjective_of_finrank_eq {A : Type*} [CommRing A] [Nontrivial A]
    {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    [Module.Free A M] [Module.Finite A M] [Module.Free A N] [Module.Finite A N]
    (f : M →ₗ[A] N) (hf : Function.Surjective f)
    (hrank : Module.finrank A M = Module.finrank A N) : Function.Bijective f := by
  obtain ⟨e⟩ := FiniteDimensional.nonempty_linearEquiv_of_finrank_eq hrank
  exact OrzechProperty.bijective_of_surjective_of_injective e.toLinearMap f e.injective hf

theorem formallyEtale_of_formallyUnramified_of_isStandardSmoothOfRelativeDimension (n : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension n R S]
    [Algebra.IsStandardSmoothOfRelativeDimension n R T]
    [Algebra.FormallyUnramified S T] :
    Algebra.FormallyEtale S T := by
  have : Algebra.IsStandardSmooth R S :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n
  have : Algebra.IsStandardSmooth R T :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n
  refine formallyEtale_of_formallySmooth_of_bijective (R := R) ?_
  have hsurj := mapBaseChange_surjective_of_formallyUnramified (R := R) (S := S) (T := T)
  cases subsingleton_or_nontrivial T with
  | inl hT =>
      exact ⟨fun a b _ => Subsingleton.elim _ _, hsurj⟩
  | inr hT =>
      have : Nontrivial S := (algebraMap S T).domain_nontrivial
      have hS : Module.rank S Ω[S⁄R] = n :=
        Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential n
      have hTr : Module.rank T Ω[T⁄R] = n :=
        Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential n
      have hSf : Module.finrank S Ω[S⁄R] = n := Module.finrank_eq_of_rank_eq hS
      have hTf : Module.finrank T Ω[T⁄R] = n := Module.finrank_eq_of_rank_eq hTr
      exact bijective_of_surjective_of_finrank_eq _ hsurj
        (by rw [Module.finrank_baseChange, hSf, hTf])

theorem etale_of_formallyUnramified_of_isStandardSmoothOfRelativeDimension (n : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension n R S]
    [Algebra.IsStandardSmoothOfRelativeDimension n R T]
    [Algebra.FormallyUnramified S T] :
    Algebra.Etale S T := by
  have := formallyEtale_of_formallyUnramified_of_isStandardSmoothOfRelativeDimension
    (R := R) (S := S) (T := T) n
  have : Algebra.IsStandardSmooth R S :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n
  have : Algebra.IsStandardSmooth R T :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n
  have : Algebra.FinitePresentation S T :=
    Algebra.FinitePresentation.of_restrict_scalars_finitePresentation R S T
  exact Algebra.Etale.mk

end algebra

section ringHom

theorem ringHom_etale_of_formallyUnramified_of_isStandardSmoothOfRelativeDimension
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] (n : ℕ)
    (φ : R →+* S) (ψ : S →+* T)
    (hφ : φ.IsStandardSmoothOfRelativeDimension n)
    (hψφ : (ψ.comp φ).IsStandardSmoothOfRelativeDimension n)
    (hψ : ψ.FormallyUnramified) : ψ.Etale := by
  algebraize [φ, ψ, ψ.comp φ]
  exact R1NeronObjE4.etale_of_formallyUnramified_of_isStandardSmoothOfRelativeDimension
    (R := R) (S := S) (T := T) n

theorem ringHom_etale_of_formallyUnramified_of_locally_isStandardSmoothOfRelativeDimension
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T] (n : ℕ)
    (φ : R →+* S) (ψ : S →+* T)
    (hφ : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n) φ)
    (hψφ : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n) (ψ.comp φ))
    (hψ : ψ.FormallyUnramified) : ψ.Etale := by
  obtain ⟨sS, hsS, hS⟩ := hφ
  obtain ⟨sT, hsT, hT⟩ := hψφ
  let ι : Type u := sT × sS
  let g : ι → T := fun i => (i.1 : T) * ψ (i.2 : S)
  have hspan : Ideal.span (Set.range g) = ⊤ := by
    have h1 : Ideal.span (ψ '' sS) = ⊤ := by
      have := congrArg (Ideal.map ψ) hsS
      rwa [Ideal.map_span, Ideal.map_top] at this
    have h2 : Ideal.span sT * Ideal.span (ψ '' sS) = Ideal.span (Set.range g) := by
      rw [Ideal.span_mul_span]
      congr 1
      ext x
      simp only [Set.mem_mul, Set.mem_image, Set.mem_range, g, ι, Prod.exists, Subtype.exists,
        exists_prop]
      constructor
      · rintro ⟨a, ha, _, ⟨b, hb, rfl⟩, rfl⟩
        exact ⟨a, ha, b, hb, rfl⟩
      · rintro ⟨a, ha, b, hb, rfl⟩
        exact ⟨a, ha, _, ⟨b, hb, rfl⟩, rfl⟩
    rw [← h2, hsT, h1, Ideal.top_mul]
  let Tt : ι → Type u := fun i => Localization.Away (i.1 : T)
  let Tg : ι → Type u := fun i => Localization.Away (algebraMap T (Tt i) (ψ (i.2 : S)))
  have key : ∀ i : ι, RingHom.Etale ((algebraMap T (Tg i)).comp ψ) := by
    intro i
    obtain ⟨⟨t, ht⟩, ⟨s, hs⟩⟩ := i
    let Ss := Localization.Away s
    have hunit : IsUnit ((algebraMap T (Tg (⟨t, ht⟩, ⟨s, hs⟩))).comp ψ s) := by
      simp only [RingHom.coe_comp, Function.comp_apply, Tg]
      rw [IsScalarTower.algebraMap_apply T (Tt (⟨t, ht⟩, ⟨s, hs⟩)) (Tg (⟨t, ht⟩, ⟨s, hs⟩))]
      exact IsLocalization.Away.algebraMap_isUnit _
    let ψ' : Ss →+* Tg (⟨t, ht⟩, ⟨s, hs⟩) :=
      IsLocalization.Away.lift s (g := (algebraMap T (Tg (⟨t, ht⟩, ⟨s, hs⟩))).comp ψ) hunit
    have hψ' : ψ'.comp (algebraMap S Ss) = (algebraMap T (Tg (⟨t, ht⟩, ⟨s, hs⟩))).comp ψ := by
      ext x
      simp [ψ']
    have h1 : ((algebraMap S Ss).comp φ).IsStandardSmoothOfRelativeDimension n := hS s hs
    have h2 : ((algebraMap T (Tg (⟨t, ht⟩, ⟨s, hs⟩))).comp
        (ψ.comp φ)).IsStandardSmoothOfRelativeDimension n := by
      have h2a : ((algebraMap T (Tt (⟨t, ht⟩, ⟨s, hs⟩))).comp
          (ψ.comp φ)).IsStandardSmoothOfRelativeDimension n := hT t ht
      have :=
        RingHom.isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway n
      have h2b := this.2 (Tg (⟨t, ht⟩, ⟨s, hs⟩)) (algebraMap T (Tt (⟨t, ht⟩, ⟨s, hs⟩)) (ψ s)) _ h2a
      rwa [← RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq] at h2b
    have h3 : ψ'.FormallyUnramified := by
      refine RingHom.FormallyUnramified.of_comp (f := algebraMap S Ss) ?_
      rw [hψ']
      exact RingHom.FormallyUnramified.comp hψ
        (RingHom.FormallyUnramified.holdsForLocalizationAway _ (t * ψ s))
    have h2' : (ψ'.comp ((algebraMap S Ss).comp φ)).IsStandardSmoothOfRelativeDimension n := by
      rwa [← RingHom.comp_assoc, hψ', RingHom.comp_assoc]
    have h4 : ψ'.Etale :=
      R1NeronObjE4.ringHom_etale_of_formallyUnramified_of_isStandardSmoothOfRelativeDimension n _ ψ'
        h1 h2' h3
    have h5 : (algebraMap S Ss).Etale := by
      rw [RingHom.etale_algebraMap]
      exact Algebra.Etale.of_isLocalizationAway s
    rw [← hψ']
    exact RingHom.Etale.stableUnderComposition _ _ h5 h4
  have hloc : RingHom.Locally RingHom.Etale ψ :=
    RingHom.locally_of_exists RingHom.Etale.respectsIso ψ g hspan Tg key
  exact (RingHom.locally_iff_of_localizationSpanTarget RingHom.Etale.respectsIso
    RingHom.Etale.ofLocalizationSpanTarget _).mp hloc

end ringHom

section scheme

open AlgebraicGeometry CategoryTheory

theorem scheme_etale_of_formallyUnramified_of_smoothOfRelativeDimension
    {X Y Z : Scheme.{u}} (n : ℕ) {f : X ⟶ Y} {g : Y ⟶ Z}
    (h1 : SmoothOfRelativeDimension n (f ≫ g)) (h2 : SmoothOfRelativeDimension n g)
    (h3 : FormallyUnramified f) : Etale f := by
  have : IsZariskiLocalAtTarget (@Etale : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget (@Etale : MorphismProperty Scheme.{u})
  have : IsZariskiLocalAtSource (@Etale : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  have : IsZariskiLocalAtTarget
      (@SmoothOfRelativeDimension n : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget (@SmoothOfRelativeDimension n)
  have : IsZariskiLocalAtTarget (@FormallyUnramified : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget (@FormallyUnramified)
  wlog hZ : IsAffine Z generalizing X Y Z
  · rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (f := f) (P := @Etale) _
      (g.iSup_preimage_eq_top (iSup_affineOpens_eq_top Z))]
    intro U
    have H1 := IsZariskiLocalAtTarget.restrict h1 U.1
    rw [morphismRestrict_comp] at H1
    have H2 : SmoothOfRelativeDimension n (g ∣_ U.1) := IsZariskiLocalAtTarget.restrict h2 U.1
    have H3 : FormallyUnramified (f ∣_ g ⁻¹ᵁ U.1) := IsZariskiLocalAtTarget.restrict h3 _
    exact this H1 H2 H3 inferInstance
  wlog hY : IsAffine Y generalizing X Y
  · rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (f := f) (P := @Etale) _ (iSup_affineOpens_eq_top
      Y)]
    intro U
    have H1 := HasRingHomProperty.comp_of_isOpenImmersion (@SmoothOfRelativeDimension n)
      (f ⁻¹ᵁ U.1).ι (f ≫ g) h1
    rw [← morphismRestrict_ι_assoc] at H1
    have H2 : SmoothOfRelativeDimension n (U.1.ι ≫ g) :=
      HasRingHomProperty.comp_of_isOpenImmersion (@SmoothOfRelativeDimension n) _ _ h2
    have H3 : FormallyUnramified (f ∣_ U.1) := IsZariskiLocalAtTarget.restrict h3 _
    exact this H1 H2 H3 U.2
  wlog hX : IsAffine X generalizing X
  · rw [IsZariskiLocalAtSource.iff_of_iSup_eq_top (f := f) (P := @Etale) _ (iSup_affineOpens_eq_top
      X)]
    intro U
    have H1 := HasRingHomProperty.comp_of_isOpenImmersion (@SmoothOfRelativeDimension n)
      U.1.ι (f ≫ g) h1
    rw [← Category.assoc] at H1
    have H3 : FormallyUnramified (U.1.ι ≫ f) :=
      MorphismProperty.IsStableUnderComposition.comp_mem (P := @FormallyUnramified) _ _
        (inferInstance : FormallyUnramified U.1.ι) h3
    exact this H1 H3 U.2
  rw [HasRingHomProperty.iff_of_isAffine (P := @Etale)]
  rw [HasRingHomProperty.iff_of_isAffine (P := @SmoothOfRelativeDimension n)] at h1 h2
  rw [HasRingHomProperty.iff_of_isAffine (P := @FormallyUnramified)] at h3
  rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp] at h1
  exact
    R1NeronObjE4.ringHom_etale_of_formallyUnramified_of_locally_isStandardSmoothOfRelativeDimension
    n _ _ h2 h1 h3

end scheme

section groupLaw

open AlgebraicGeometry CategoryTheory NeronModelInfra GoodReductionJacobian

theorem groupLaw_etale_schemeNsmul
    {R : Type u} [CommRing R] [IsLocalRing R] {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      G.mul t x y = G.mul t y x)
    (d : ℕ) [SmoothOfRelativeDimension d f] (n : ℕ) (hn : IsUnit (n : R)) :
    Etale (G.schemeNsmul n) := by
  have hu : FormallyUnramified (G.schemeNsmul n) :=
    GoodReductionJacobian.RelativeGroupLaw.formallyUnramified_schemeNsmul_of_isUnit_of_isLocalRing
      G hcomm n hn
  have h1 : SmoothOfRelativeDimension d (G.schemeNsmul n ≫ f) := by
    rw [G.schemeNsmul_over]; infer_instance
  exact R1NeronObjE4.scheme_etale_of_formallyUnramified_of_smoothOfRelativeDimension d h1 ‹_› hu

end groupLaw

end R1NeronObjE4

end RelativeGroupLaw_etale_schemeNsmul_of_isUnit_of_smoothOfRelativeDimension
end AlgebraicCurves.Geometry.AbelianSchemes.Theorems.Proofs

universe u

open AlgebraicCurves.Geometry.AbelianSchemes.Theorems.Proofs
open RelativeGroupLaw_etale_schemeNsmul_of_isUnit_of_smoothOfRelativeDimension
open R1NeronObjE4

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry

namespace GoodReductionJacobian.RelativeGroupLaw

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem etale_schemeNsmul_of_isUnit_of_smoothOfRelativeDimension
    {R : Type u} [CommRing R] [IsLocalRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (G : RelativeGroupLaw R f)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      G.mul t x y = G.mul t y x)
    (d : ℕ) [SmoothOfRelativeDimension d f]
    (n : ℕ) (hn : IsUnit (n : R)) :
    Etale (G.schemeNsmul n) :=
  groupLaw_etale_schemeNsmul G hcomm d n hn

end GoodReductionJacobian.RelativeGroupLaw
end ProofImplementation
