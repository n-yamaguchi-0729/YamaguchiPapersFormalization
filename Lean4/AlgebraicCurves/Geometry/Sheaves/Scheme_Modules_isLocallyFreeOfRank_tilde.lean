/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_isLocallyFreeOfRank_tilde.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Geometry.Sheaves.ModulesLocallyFreeOfRank
import AlgebraicCurves.Geometry.Sheaves.ModulesTildePullback
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Localization.Free
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Local freeness of the sheaf associated to a module

Local finite free descriptions of a module over an affine ring give local
trivializations of its associated module sheaf.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_isLocallyFreeOfRank_tilde

universe u

open _root_.CategoryTheory
open _root_.AlgebraicGeometry
open _root_.Opposite
open _root_.TensorProduct

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry

theorem free_finite_finrank_of_algebra_eq {A S : Type u} [CommRing A] [CommRing S]
    (M : Type u) [AddCommGroup M] [Module A M] (n : ℕ) (i₁ i₂ : Algebra A S) (h : i₁ = i₂)
    (H : letI := i₁;
      Module.Free S (S ⊗[A] M) ∧ Module.Finite S (S ⊗[A] M) ∧ Module.finrank S (S ⊗[A] M) = n) :
    letI := i₂;
      Module.Free S (S ⊗[A] M) ∧ Module.Finite S (S ⊗[A] M) ∧ Module.finrank S (S ⊗[A] M) = n := by
  subst h; exact H

theorem free_finite_finrank_baseChange_away {R : Type u} [CommRing R] (P : Type u)
    [AddCommGroup P] [Module R P] [Module.Finite R P] [Module.Projective R P] (n : ℕ)
    (hrk : ∀ (K : Type u) [Field K] [Algebra R K], Module.finrank K (K ⊗[R] P) = n)
    (r : R) (p : PrimeSpectrum R) (hr : r ∈ p.asIdeal.primeCompl)
    (hfree : Module.Free (Localization (.powers r)) (LocalizedModule (.powers r) P)) :
    Module.Free (Localization.Away r) (Localization.Away r ⊗[R] P) ∧
      Module.Finite (Localization.Away r) (Localization.Away r ⊗[R] P) ∧
      Module.finrank (Localization.Away r) (Localization.Away r ⊗[R] P) = n := by
  have hF : Module.Free (Localization.Away r) (Localization.Away r ⊗[R] P) :=
    Module.Free.of_equiv (LocalizedModule.equivTensorProduct (.powers r) P)
  refine ⟨hF, inferInstance, ?_⟩
  have hp : p ∈ (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R)) :=
    show r ∉ p.asIdeal from hr
  rw [← PrimeSpectrum.localization_away_comap_range (Localization.Away r) r] at hp
  obtain ⟨q, hq⟩ := hp
  have h1 : Module.rankAtStalk (Localization.Away r ⊗[R] P) q =
      Module.finrank (Localization.Away r) (Localization.Away r ⊗[R] P) := by
    exact congrFun (Module.rankAtStalk_eq_finrank_of_free
      (R := Localization.Away r) (M := Localization.Away r ⊗[R] P)) q
  rw [← h1, Module.rankAtStalk_baseChange, hq, Module.rankAtStalk_eq]
  exact hrk _

/-- Identify the sheaf associated to a finite free module with the finite free sheaf of its rank. -/
noncomputable def tildeIsoFreeOfFinrankEq {S : CommRingCat.{u}} [Nontrivial S] (N : ModuleCat.{u} S)
    [Module.Free S N] [Module.Finite S N] {n : ℕ} (hn : Module.finrank S N = n) :
    tilde N ≅ SheafOfModules.free.{u} (ULift.{u} (Fin n)) :=
  (tilde.functor S).mapIso
      (((Module.finBasisOfFinrankEq S N hn).reindex Equiv.ulift.{u, 0}.symm).repr.toModuleIso) ≪≫
    tildeFinsupp (ULift.{u} (Fin n))

namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace Modules
open _root_.AlgebraicGeometry.Scheme.Modules
end Scheme.Modules
open scoped _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.Modules in
theorem Scheme.Modules.opensMap_final'' {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (TopologicalSpace.Opens.map f.base).Final :=
  CategoryTheory.final_of_representablyFlat _

open scoped _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.Modules in
/-- Pullback preserves the free module sheaf on the given index type. -/
noncomputable def Scheme.Modules.pullbackObjFreeIso' {X Y : Scheme.{u}} (f : X ⟶ Y) (I : Type u) :
    (Scheme.Modules.pullback f).obj (SheafOfModules.free.{u} I) ≅ SheafOfModules.free.{u} I :=
  haveI := Scheme.Modules.opensMap_final'' f
  haveI : (SheafOfModules.pushforward.{u} f.toRingCatSheafHom).IsRightAdjoint :=
    (Scheme.Modules.pullbackPushforwardAdjunction f).isRightAdjoint
  SheafOfModules.pullbackObjFreeIso f.toRingCatSheafHom I

open scoped _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.Modules in
/-- Identify a module sheaf with a free sheaf when its pullback along an isomorphism is free. -/
noncomputable def Scheme.Modules.isoFreeOfIsoPullback {U Y : Scheme.{u}} (e : Y ≅ U) (M : U.Modules)
    (I : Type u) (h : (Scheme.Modules.pullback e.hom).obj M ≅ SheafOfModules.free.{u} I) :
    M ≅ SheafOfModules.free.{u} I :=
  (Scheme.Modules.pullbackId U).symm.app M ≪≫
    (Scheme.Modules.pullbackCongr (show 𝟙 U = e.inv ≫ e.hom by simp)).app M ≪≫
    (Scheme.Modules.pullbackComp e.inv e.hom).symm.app M ≪≫
    (Scheme.Modules.pullback e.inv).mapIso h ≪≫
    Scheme.Modules.pullbackObjFreeIso' e.inv I


theorem _root_.AlgebraicGeometry.Scheme.Modules.isLocallyFreeOfRank_tilde {R : CommRingCat.{u}} (P :
  ModuleCat.{u} R)
    [Module.Finite R P] [Module.Projective R P] (n : ℕ)
    (hrk : ∀ (K : Type u) [Field K] [Algebra R K], Module.finrank K (K ⊗[R] P) = n) :
    Scheme.Modules.IsLocallyFreeOfRank n (tilde P) := by
  classical
  have : Module.FinitePresentation R P := Module.finitePresentation_of_projective R P
  refine ⟨fun (p : PrimeSpectrum R) => ?_⟩
  have : Module.Free (Localization.AtPrime p.asIdeal)
      (LocalizedModule p.asIdeal.primeCompl P) := Module.free_of_flat_of_isLocalRing
  obtain ⟨r, hr, hfree, -⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    p.asIdeal.primeCompl (LocalizedModule.mkLinearMap p.asIdeal.primeCompl P)
    (Localization.AtPrime p.asIdeal)
  have : Nontrivial (Localization.Away (r : R)) :=
    (IsLocalization.map (M := .powers r) (T := p.asIdeal.primeCompl) (Localization.AtPrime
        p.asIdeal)
      (RingHom.id _) (Submonoid.powers_le.mpr hr)).domain_nontrivial
  obtain ⟨hF, hFin, hrank⟩ := free_finite_finrank_baseChange_away P n hrk r p hr hfree
  let S : CommRingCat.{u} := .of (Localization.Away (r : R))
  let φ : R ⟶ S := CommRingCat.ofHom (algebraMap R (Localization.Away (r : R)))
  obtain ⟨hF', hFin', hrank'⟩ := free_finite_finrank_of_algebra_eq (A := R) (S := Localization.Away
      (r : R))
    P n inferInstance φ.hom.toAlgebra (Algebra.algebra_ext _ _ fun _ => rfl) ⟨hF, hFin, hrank⟩
  have : Module.Free S ((ModuleCat.extendScalars φ.hom).obj P) := hF'
  have : Module.Finite S ((ModuleCat.extendScalars φ.hom).obj P) := hFin'
  have hn : Module.finrank S ((ModuleCat.extendScalars φ.hom).obj P) = n := hrank'
  have : Nontrivial S := inferInstanceAs (Nontrivial (Localization.Away (r : R)))
  refine ⟨PrimeSpectrum.basicOpen r, (show r ∉ p.asIdeal from hr), ⟨?_⟩⟩
  let U : (Spec R).Opens := PrimeSpectrum.basicOpen r
  let e : (U : Scheme.{u}) ≅ Spec S := basicOpenIsoSpecAway (R := R) r
  have he : e.inv ≫ U.ι = Spec.map φ := by
    calc
      e.inv ≫ U.ι = e.inv ≫ (e.hom ≫ Spec.map φ) :=
        congrArg (fun k : U.toScheme ⟶ Spec R => e.inv ≫ k)
          (basicOpenIsoSpecAway_hom_SpecMap (R := R) (r : R)).symm
      _ = Spec.map φ := by rw [← Category.assoc, e.inv_hom_id, Category.id_comp]
  refine Scheme.Modules.isoFreeOfIsoPullback e.symm _ _ ?_
  exact (Scheme.Modules.pullbackComp e.inv U.ι).app (tilde P) ≪≫
    (Scheme.Modules.pullbackCongr he).app (tilde P) ≪≫
    tilde.pullbackSpecIso φ P ≪≫
    tildeIsoFreeOfFinrankEq ((ModuleCat.extendScalars φ.hom).obj P) hn


end AlgebraicGeometry
end AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_isLocallyFreeOfRank_tilde
end ProofImplementation

attribute [-simp] AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app
