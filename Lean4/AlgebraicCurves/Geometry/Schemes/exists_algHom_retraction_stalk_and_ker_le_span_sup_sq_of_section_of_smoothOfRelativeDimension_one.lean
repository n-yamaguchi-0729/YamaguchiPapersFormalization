/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_exists_algHom_retraction_stalk_and_ker_le_span_sup_sq_of_section_of_smoothOfRelativeDimension_one.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Algebra.Algebra.Tower
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.EssentialFiniteness
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.RingHom.FinitePresentation
import Mathlib.RingTheory.RingHom.FiniteType
import Mathlib.RingTheory.RingHom.Locally
import Mathlib.RingTheory.RingHom.Smooth
import Mathlib.RingTheory.RingHom.StandardSmooth
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Topology.Sets.Opens
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Push

/-!
# exists alg Hom retraction stalk and ker le span sup sq of section of smooth Of Relative
Dimension one
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs.SmoothSectionStalkRetraction

universe u

open CategoryTheory AlgebraicGeometry

namespace P2Body
namespace CotSec

open TensorProduct

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

theorem kerCotangentToTensor_bijective [Algebra.FormallySmooth R A] (e : A →ₐ[R] R) :
    letI : Algebra A R := e.toRingHom.toAlgebra
    Function.Bijective (KaehlerDifferential.kerCotangentToTensor R A R) := by
  let : Algebra A R := e.toRingHom.toAlgebra
  have : IsScalarTower R A R := IsScalarTower.of_algebraMap_eq' e.comp_algebraMap.symm
  have hsurj : Function.Surjective (algebraMap A R) := fun r => ⟨algebraMap R A r, e.commutes r⟩
  have : Subsingleton Ω[R⁄R] :=
    KaehlerDifferential.subsingleton_of_surjective (R := R) (S := R) Function.surjective_id
  constructor
  · obtain ⟨l, hl⟩ :=
      (Algebra.FormallySmooth.iff_split_injection (R := R) (P := A) (A := R) hsurj).mp inferInstance
    exact Function.LeftInverse.injective (g := l) fun x => LinearMap.congr_fun hl x
  · intro y
    exact (KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange R A R hsurj y).mp
      (Subsingleton.elim _ _)

theorem free_tensor_kaehlerDifferential [IsLocalRing R] (e : A →ₐ[R] R)
    (hloc : RingHom.Locally (fun f => RingHom.IsStandardSmoothOfRelativeDimension 1 f) (algebraMap
      R A)) :
    letI : Algebra A R := e.toRingHom.toAlgebra
    Module.Free R (R ⊗[A] Ω[A⁄R]) ∧ Module.finrank R (R ⊗[A] Ω[A⁄R]) = 1 := by
  let : Algebra A R := e.toRingHom.toAlgebra
  have : IsScalarTower R A R := IsScalarTower.of_algebraMap_eq' e.comp_algebraMap.symm
  obtain ⟨s, hs, hP⟩ := hloc
  have hex : ∃ t ∈ s, IsUnit (e t) := by
    by_contra hcon
    push Not at hcon
    have hle : Ideal.map e.toRingHom (Ideal.span s) ≤ IsLocalRing.maximalIdeal R := by
      rw [Ideal.map_span, Ideal.span_le]
      rintro _ ⟨t, ht, rfl⟩
      exact (IsLocalRing.mem_maximalIdeal _).mpr (hcon t ht)
    rw [hs, Ideal.map_top, top_le_iff] at hle
    exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top hle
  obtain ⟨t, ht, hunit⟩ := hex
  have hstd := hP t ht
  set At := Localization.Away t with hAt
  rw [← IsScalarTower.algebraMap_eq R A At] at hstd
  have hstd' : Algebra.IsStandardSmoothOfRelativeDimension 1 R At :=
    (RingHom.isStandardSmoothOfRelativeDimension_algebraMap 1).mp hstd
  have : Algebra.IsStandardSmooth R At :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth 1
  let e' : At →+* R := IsLocalization.Away.lift t (g := e.toRingHom) hunit
  have : Nontrivial At := e'.domain_nontrivial
  have hrank : Module.rank At Ω[At⁄R] = 1 := by
    simpa using Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential (R := R) (S :=
      At) 1
  have hfin : Module.finrank At Ω[At⁄R] = 1 := Module.finrank_eq_of_rank_eq (by simpa using hrank)
  let : Algebra At R := e'.toAlgebra
  have : IsScalarTower A At R :=
    IsScalarTower.of_algebraMap_eq' (IsLocalization.Away.lift_comp t hunit).symm
  have : IsScalarTower R At R := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    rw [IsScalarTower.algebraMap_eq R A At, ← RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq A
      At R,
      ← IsScalarTower.algebraMap_eq R A R]
  have : Algebra.FormallyEtale A At := Algebra.FormallyEtale.of_isLocalization (Submonoid.powers t)
  let i1 : R ⊗[At] (At ⊗[A] Ω[A⁄R]) ≃ₗ[R] R ⊗[A] Ω[A⁄R] :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange A At R R Ω[A⁄R]
  let i2 : R ⊗[At] (At ⊗[A] Ω[A⁄R]) ≃ₗ[R] R ⊗[At] Ω[At⁄R] :=
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl R R)
      (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R A At)
  let i : R ⊗[A] Ω[A⁄R] ≃ₗ[R] R ⊗[At] Ω[At⁄R] := i1.symm ≪≫ₗ i2
  refine ⟨Module.Free.of_equiv i.symm, ?_⟩
  rw [i.finrank_eq, Module.finrank_baseChange, hfin]

theorem free_cotangent_ker [IsLocalRing R] [Algebra.FormallySmooth R A] (e : A →ₐ[R] R)
    (hloc : RingHom.Locally (fun f => RingHom.IsStandardSmoothOfRelativeDimension 1 f) (algebraMap
      R A)) :
    Module.Free R (RingHom.ker e.toRingHom).Cotangent ∧
      Module.finrank R (RingHom.ker e.toRingHom).Cotangent = 1 := by
  let : Algebra A R := e.toRingHom.toAlgebra
  have : IsScalarTower R A R := IsScalarTower.of_algebraMap_eq' e.comp_algebraMap.symm
  obtain ⟨hfree, hrank⟩ := free_tensor_kaehlerDifferential e hloc
  let f : (RingHom.ker e.toRingHom).Cotangent ≃ₗ[R] R ⊗[A] Ω[A⁄R] :=
    (LinearEquiv.ofBijective (KaehlerDifferential.kerCotangentToTensor R A R)
      (kerCotangentToTensor_bijective e)).restrictScalars R
  exact ⟨Module.Free.of_equiv f.symm, f.finrank_eq.trans hrank⟩

end P2Body.CotSec

namespace P2Body
namespace GenKerAux

theorem exists_generator {R A : Type*} [CommRing R] [Nontrivial R] [CommRing A] [Algebra R A] (e :
  A →ₐ[R] R)
    [Module.Free R (RingHom.ker e.toRingHom).Cotangent]
    (he : Module.finrank R (RingHom.ker e.toRingHom).Cotangent = 1) :
    ∃ t₀ : A, e t₀ = 0 ∧ RingHom.ker e.toRingHom ≤ Ideal.span {t₀} ⊔ RingHom.ker e.toRingHom ^ 2 :=
      by
  set I : Ideal A := RingHom.ker e.toRingHom with hI
  let b := Module.basisUnique Unit he
  obtain ⟨t, ht⟩ := I.toCotangent_surjective (b default)
  refine ⟨t, t.2, fun x hx => ?_⟩
  set r : R := b.repr (I.toCotangent ⟨x, hx⟩) default with hr
  have h1 : I.toCotangent ⟨x, hx⟩ = r • I.toCotangent t := by
    rw [ht]
    simpa using (b.sum_repr (I.toCotangent ⟨x, hx⟩)).symm
  rw [← LinearMap.map_smul_of_tower] at h1
  have h2 := (I.toCotangent_eq).mp h1
  have hx' : x = ((r • t : I) : A) + (x - ((r • t : I) : A)) := by abel
  rw [hx']
  refine Submodule.add_mem_sup ?_ h2
  rw [Submodule.coe_smul_of_tower, Algebra.smul_def]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

end P2Body.GenKerAux

namespace P2Body

open TensorProduct

/-- The algebra on a stalk induced by the structure morphism to the base spectrum. -/
@[reducible] noncomputable def stalkAlgebra {R : Type u} [CommRing R] {X : Scheme.{u}} (c : X ⟶
  Spec (CommRingCat.of R))
    (x : X) : Algebra R (X.presheaf.stalk x) :=
  ((X.presheaf.germ ⊤ x trivial).hom.comp (c.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of
    R)).inv.hom)).toAlgebra

theorem Lpi {R : Type u} [CommRing R] [IsLocalRing R] {X : Scheme.{u}} (c : X ⟶ Spec
  (CommRingCat.of R))
    (σ : Spec (CommRingCat.of R) ⟶ X) (hσ : σ ≫ c = 𝟙 _)
    (s : Spec (CommRingCat.of R)) (hs : IsClosed ({s} : Set (Spec (CommRingCat.of R)))) :
    letI := stalkAlgebra c (σ.base s)
    ∃ π : X.presheaf.stalk (σ.base s) →ₐ[R] R, RingHom.ker (Scheme.Hom.stalkMap σ s).hom ≤
      RingHom.ker π := by
  have hs' : s = IsLocalRing.closedPoint R :=
    PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal ((PrimeSpectrum.isClosed_singleton_iff_isMaximal
      s).mp hs))
  subst hs'
  let := stalkAlgebra c (σ.base (IsLocalRing.closedPoint R))
  have key : (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ c.appTop ≫
      X.presheaf.germ ⊤ (σ.base (IsLocalRing.closedPoint R)) trivial ≫ Scheme.stalkClosedPointTo σ
        = 𝟙 _ := by
    let p : Spec (CommRingCat.of R) := IsLocalRing.closedPoint R
    have hp : σ p ∈ (⊤ : X.Opens) := trivial
    have hmap : X.presheaf.germ ⊤ (σ p) hp ≫ σ.stalkMap p =
        σ.appTop ≫ (Spec (CommRingCat.of R)).presheaf.germ ⊤ p trivial :=
      σ.germ_stalkMap ⊤ p hp
    have hg : X.presheaf.germ ⊤ (σ p) hp ≫ Scheme.stalkClosedPointTo σ =
        σ.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom := by
      exact (Category.assoc (X.presheaf.germ ⊤ (σ p) hp) (σ.stalkMap p)
          (stalkClosedPointIso (CommRingCat.of R)).hom).symm.trans
        ((congrArg (fun k : Γ(X, ⊤) ⟶ (Spec (CommRingCat.of R)).presheaf.stalk p =>
          k ≫ (stalkClosedPointIso (CommRingCat.of R)).hom) hmap).trans
          ((Category.assoc σ.appTop ((Spec (CommRingCat.of R)).presheaf.germ ⊤ p trivial)
            (stalkClosedPointIso (CommRingCat.of R)).hom).trans
            (congrArg (fun k : Γ(Spec (CommRingCat.of R), ⊤) ⟶ CommRingCat.of R => σ.appTop ≫ k)
              (germ_stalkClosedPointIso_hom (CommRingCat.of R)))))
    have h1 : c.appTop ≫ σ.appTop = 𝟙 (Γ(Spec (CommRingCat.of R), ⊤)) :=
      (Scheme.Hom.comp_appTop σ c).symm.trans
        ((congrArg (fun f : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of R) => f.appTop) hσ).trans
          Scheme.Hom.id_appTop)
    rw [hg, ← Category.assoc c.appTop σ.appTop, h1, Category.id_comp, Iso.inv_hom_id]
  refine ⟨{ (Scheme.stalkClosedPointTo σ).hom with
      commutes' := fun r => ?_ }, ?_⟩
  · change (Scheme.stalkClosedPointTo σ).hom
        ((X.presheaf.germ ⊤ (σ.base (IsLocalRing.closedPoint R)) trivial).hom
          (c.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))) = r
    have := congrArg (fun φ => φ.hom r) key
    simpa using this
  · intro x hx
    rw [RingHom.mem_ker] at hx ⊢
    change (Scheme.stalkClosedPointTo σ).hom x = 0
    rw [Scheme.stalkClosedPointTo, CommRingCat.comp_apply]
    erw [hx]
    exact map_zero _

theorem LS' {R : Type u} [CommRing R] [IsLocalRing R] {X : Scheme.{u}} (c : X ⟶ Spec
  (CommRingCat.of R))
    [SmoothOfRelativeDimension 1 c] (V : X.Opens) (hV : IsAffineOpen V) (y : V) :
    letI := stalkAlgebra c (y : X)
    Algebra.FormallySmooth R (X.presheaf.stalk (y : X)) ∧
    Module.Finite (X.presheaf.stalk (y : X)) Ω[(X.presheaf.stalk (y : X))⁄R] ∧
    ∀ π : X.presheaf.stalk (y : X) →ₐ[R] R,
      Module.Free R (RingHom.ker π.toRingHom).Cotangent ∧ Module.finrank R (RingHom.ker
        π.toRingHom).Cotangent = 1 := by
  let instRS := stalkAlgebra c (y : X)
  have hxV : (y : X) ∈ V := y.2
  let algA : Algebra R Γ(X, V) := ((Scheme.ΓSpecIso (.of R)).inv ≫ c.appLE ⊤ V le_top).hom.toAlgebra
  have : Smooth c := SmoothOfRelativeDimension.smooth 1 c
  have hsm : (c.appLE ⊤ V le_top).hom.Smooth :=
    Smooth.smooth_appLE (f := c) (isAffineOpen_top (Spec (.of R))) hV le_top
  have fsA : Algebra.FormallySmooth R Γ(X, V) := by
    have h2 : ((Scheme.ΓSpecIso (.of R)).inv ≫ c.appLE ⊤ V le_top).hom.FormallySmooth := by
      rw [CommRingCat.hom_comp]
      exact (RingHom.FormallySmooth.respectsIso.cancel_left_isIso _ _).mpr hsm.formallySmooth
    exact h2.toAlgebra
  have ftA : Algebra.FiniteType R Γ(X, V) := by
    have h2 : ((Scheme.ΓSpecIso (.of R)).inv ≫ c.appLE ⊤ V le_top).hom.FiniteType := by
      rw [CommRingCat.hom_comp]
      exact (RingHom.finiteType_respectsIso.cancel_left_isIso _ _).mpr
        (RingHom.FiniteType.of_finitePresentation hsm.finitePresentation)
    exact h2
  have hloc : RingHom.Locally (fun f => RingHom.IsStandardSmoothOfRelativeDimension 1 f)
      (algebraMap R Γ(X, V)) := by
    have h1 : RingHom.Locally (fun f => RingHom.IsStandardSmoothOfRelativeDimension 1 f)
        (c.appLE ⊤ V le_top).hom :=
      HasRingHomProperty.appLE (@SmoothOfRelativeDimension 1) c inferInstance ⟨⊤, isAffineOpen_top
        _⟩ ⟨V, hV⟩ le_top
    have h2 : RingHom.Locally (fun f => RingHom.IsStandardSmoothOfRelativeDimension 1 f)
        ((Scheme.ΓSpecIso (.of R)).inv ≫ c.appLE ⊤ V le_top).hom := by
      rw [CommRingCat.hom_comp]
      exact ((RingHom.locally_respectsIso
        RingHom.isStandardSmoothOfRelativeDimension_respectsIso).cancel_left_isIso
        _ _).mpr h1
    exact h2
  have hIL : IsLocalization.AtPrime (X.presheaf.stalk (y : X)) (hV.primeIdealOf y).asIdeal :=
    hV.isLocalization_stalk y
  have hST : IsScalarTower R Γ(X, V) (X.presheaf.stalk (y : X)) := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    have key : ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ c.appTop) ≫ X.presheaf.germ ⊤ (y : X)
      trivial =
        ((Scheme.ΓSpecIso (.of R)).inv ≫ c.appLE ⊤ V le_top) ≫ X.presheaf.germ V (y : X) hxV := by
      simp only [Scheme.Hom.appLE, Category.assoc, TopCat.Presheaf.germ_res]
      rfl
    change (X.presheaf.germ ⊤ (y : X) trivial).hom.comp (c.appTop.hom.comp (Scheme.ΓSpecIso
      (CommRingCat.of R)).inv.hom) =
      (X.presheaf.germ V (y : X) hxV).hom.comp (((Scheme.ΓSpecIso (.of R)).inv ≫ c.appLE ⊤ V
        le_top).hom)
    rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp, ← CommRingCat.hom_comp, key]
  have fsAS : Algebra.FormallySmooth Γ(X, V) (X.presheaf.stalk (y : X)) :=
    Algebra.FormallySmooth.of_isLocalization (hV.primeIdealOf y).asIdeal.primeCompl
  have fsS : Algebra.FormallySmooth R (X.presheaf.stalk (y : X)) :=
    Algebra.FormallySmooth.comp R Γ(X, V) (X.presheaf.stalk (y : X))
  have : Algebra.EssFiniteType Γ(X, V) (X.presheaf.stalk (y : X)) :=
    Algebra.EssFiniteType.of_isLocalization _ (hV.primeIdealOf y).asIdeal.primeCompl
  have : Algebra.EssFiniteType R (X.presheaf.stalk (y : X)) :=
    Algebra.EssFiniteType.comp R Γ(X, V) (X.presheaf.stalk (y : X))
  refine ⟨fsS, inferInstance, fun π => ?_⟩
  let eA : Γ(X, V) →ₐ[R] R := π.comp (IsScalarTower.toAlgHom R Γ(X, V) (X.presheaf.stalk (y : X)))
  obtain ⟨hfreeA, hrankA⟩ := CotSec.free_tensor_kaehlerDifferential eA hloc
  let : Algebra Γ(X, V) R := eA.toRingHom.toAlgebra
  let : Algebra (X.presheaf.stalk (y : X)) R := π.toRingHom.toAlgebra
  have : IsScalarTower R Γ(X, V) R := IsScalarTower.of_algebraMap_eq' eA.comp_algebraMap.symm
  have : IsScalarTower R (X.presheaf.stalk (y : X)) R := IsScalarTower.of_algebraMap_eq'
    π.comp_algebraMap.symm
  have : IsScalarTower Γ(X, V) (X.presheaf.stalk (y : X)) R := IsScalarTower.of_algebraMap_eq'
    (by rfl)
  have : Algebra.FormallyEtale Γ(X, V) (X.presheaf.stalk (y : X)) :=
    Algebra.FormallyEtale.of_isLocalization (hV.primeIdealOf y).asIdeal.primeCompl
  let S := X.presheaf.stalk (y : X)
  let i1 : R ⊗[S] (S ⊗[Γ(X, V)] Ω[Γ(X, V)⁄R]) ≃ₗ[R] R ⊗[Γ(X, V)] Ω[Γ(X, V)⁄R] :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange Γ(X, V) S R R Ω[Γ(X, V)⁄R]
  let i2 : R ⊗[S] (S ⊗[Γ(X, V)] Ω[Γ(X, V)⁄R]) ≃ₗ[R] R ⊗[S] Ω[S⁄R] :=
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl R R)
      (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R Γ(X, V) S)
  let i : R ⊗[Γ(X, V)] Ω[Γ(X, V)⁄R] ≃ₗ[R] R ⊗[S] Ω[S⁄R] := i1.symm ≪≫ₗ i2
  have hfreeS : Module.Free R (R ⊗[S] Ω[S⁄R]) := Module.Free.of_equiv i
  have hrankS : Module.finrank R (R ⊗[S] Ω[S⁄R]) = 1 := by rw [← i.finrank_eq, hrankA]
  let f : (RingHom.ker π.toRingHom).Cotangent ≃ₗ[R] R ⊗[S] Ω[S⁄R] :=
    (LinearEquiv.ofBijective (KaehlerDifferential.kerCotangentToTensor R S R)
      (CotSec.kerCotangentToTensor_bijective π)).restrictScalars R
  exact ⟨Module.Free.of_equiv f.symm, f.finrank_eq.trans hrankS⟩

theorem LS {R : Type u} [CommRing R] [IsLocalRing R] {X : Scheme.{u}} (c : X ⟶ Spec (CommRingCat.of
  R))
    [SmoothOfRelativeDimension 1 c] (x : X) :
    letI := stalkAlgebra c x
    Algebra.FormallySmooth R (X.presheaf.stalk x) ∧
    Module.Finite (X.presheaf.stalk x) Ω[(X.presheaf.stalk x)⁄R] ∧
    ∀ π : X.presheaf.stalk x →ₐ[R] R,
      Module.Free R (RingHom.ker π.toRingHom).Cotangent ∧ Module.finrank R (RingHom.ker
        π.toRingHom).Cotangent = 1 := by
  obtain ⟨V, hVmem, hxV, -⟩ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens)
      (TopologicalSpace.Opens.mem_top x)
  exact LS' c V hVmem ⟨x, hxV⟩

end P2Body
end AlgebraicCurves.Geometry.Schemes.Proofs.SmoothSectionStalkRetraction

namespace AlgebraicGeometry

open _root_.AlgebraicCurves.Geometry.Schemes.Proofs.SmoothSectionStalkRetraction
universe u
open _root_.CategoryTheory _root_.AlgebraicGeometry


open _root_.AlgebraicCurves.Geometry.Schemes.Proofs.SmoothSectionStalkRetraction.P2Body in
theorem
 exists_algHom_retraction_stalk_and_ker_le_span_sup_sq_of_section_of_smoothOfRelativeDimension_one
    {R : Type u} [CommRing R] [IsLocalRing R] {X : Scheme.{u}} (c : X ⟶ Spec (CommRingCat.of R))
    [SmoothOfRelativeDimension 1 c]
    (σ : Spec (CommRingCat.of R) ⟶ X) (hσ : σ ≫ c = 𝟙 _)
    (s : Spec (CommRingCat.of R)) (hs : IsClosed ({s} : Set (Spec (CommRingCat.of R)))) :
    letI : Algebra R (X.presheaf.stalk (σ.base s)) := ((X.presheaf.germ ⊤ (σ.base s)
      trivial).hom.comp
        (c.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)).toAlgebra
    ∃ (π : X.presheaf.stalk (σ.base s) →ₐ[R] R) (t : X.presheaf.stalk (σ.base s)),
      RingHom.ker (Scheme.Hom.stalkMap σ s).hom ≤ RingHom.ker π ∧
      π t = 0 ∧ (RingHom.ker π ≤ Ideal.span {t} ⊔ RingHom.ker π ^ 2) ∧
      Module.Finite (X.presheaf.stalk (σ.base s)) Ω[(X.presheaf.stalk (σ.base s))⁄R] := by
  let := P2Body.stalkAlgebra c (σ.base s)
  obtain ⟨π, hker⟩ := P2Body.Lpi c σ hσ s hs
  obtain ⟨hfs, hfin, hcot⟩ := P2Body.LS c (σ.base s)
  obtain ⟨hfree, hrk⟩ := hcot π
  have := hfree
  obtain ⟨t, ht, hgen⟩ := P2Body.GenKerAux.exists_generator π hrk
  refine ⟨π, t, hker, ht, ?_, hfin⟩
  simpa only [AlgHom.toRingHom_eq_coe, RingHom.ker_coe_toRingHom] using hgen
end AlgebraicGeometry
end ProofImplementation
