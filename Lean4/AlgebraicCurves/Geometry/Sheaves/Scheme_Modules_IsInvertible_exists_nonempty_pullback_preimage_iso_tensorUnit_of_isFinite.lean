/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_nonempty_pullback_preimage_iso_tensorUnit_of_isFinite.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Ideal.GoingUp
import AlgebraicCurves.Geometry.Sheaves.ModulesLocallyFreeOfRank
import AlgebraicCurves.Geometry.Picard.Functor
import SchemeTheory.Modules.Monoidal
import SchemeTheory.Modules.TensorSections
import SchemeTheory.Cohomology.Cech.TwoAffineOpenCover
import AlgebraicCurves.Cohomology.Cech.TwoChartCechSectionsOf
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsFrameOn_nonempty_pullback_iso_unit
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_exists_isFrameOn
import SchemeTheory.Modules.LocallyTrivialSectionsLocalization
import AlgebraicCurves.Geometry.Projective.Scheme_TwoAffineOpenCover_sectionsOf_isInvertible_projective_finite_finrank
import AlgebraicCurves.Foundations.Algebra.Module_Invertible_of_projective_of_forall_finrank_eq_one

/-!
# Scheme Modules Is Invertible exists nonempty pullback preimage iso tensor Unit of is
Finite
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace InvertibleFinitePreimage

universe u

open TensorProduct

namespace Module
open _root_.Module
namespace Invertible
open _root_.Module.Invertible
open _root_.Module.Invertible
open _root_.Module

theorem finite_maximalSpectrum_of_isLocalRing_of_moduleFinite
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [IsLocalRing R] [Module.Finite R S] :
    Finite (MaximalSpectrum S) := by
  classical
  let 𝔪 := IsLocalRing.maximalIdeal R
  let I : Ideal S := 𝔪.map (algebraMap R S)
  have : Module.Finite (R ⧸ 𝔪) (S ⧸ I) := Module.Finite.of_restrictScalars_finite R (R ⧸ 𝔪) (S ⧸ I)
  let : Field (R ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  have : IsArtinianRing (S ⧸ I) := IsArtinianRing.of_finite (R ⧸ 𝔪) (S ⧸ I)
  have : Algebra.IsIntegral R S := Algebra.IsIntegral.of_finite R S
  have hle : ∀ M : MaximalSpectrum S, I ≤ M.asIdeal := fun M => by
    have := M.isMaximal
    have h1 : (M.asIdeal.comap (algebraMap R S)).IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal
        (algebraMap R S) Algebra.IsIntegral.isIntegral M.asIdeal
    have h2 : M.asIdeal.comap (algebraMap R S) = 𝔪 := IsLocalRing.eq_maximalIdeal h1
    exact Ideal.map_le_iff_le_comap.mpr h2.ge
  have hsurj : Function.Surjective (Ideal.Quotient.mk I) := Ideal.Quotient.mk_surjective
  let φ : MaximalSpectrum S → MaximalSpectrum (S ⧸ I) := fun M =>
    ⟨M.asIdeal.map (Ideal.Quotient.mk I), by
      have := M.isMaximal
      refine (Ideal.map_eq_top_or_isMaximal_of_surjective _ hsurj M.isMaximal).resolve_left ?_
      intro htop
      apply M.isMaximal.ne_top
      have := congrArg (Ideal.comap (Ideal.Quotient.mk I)) htop
      rwa [Ideal.comap_map_of_surjective _ hsurj, Ideal.comap_top, ← RingHom.ker_eq_comap_bot,
        Ideal.mk_ker, sup_eq_left.mpr (hle M)] at this⟩
  refine _root_.Finite.of_injective φ fun M M' h => ?_
  have h' : M.asIdeal.map (Ideal.Quotient.mk I) = M'.asIdeal.map (Ideal.Quotient.mk I) := congrArg
    MaximalSpectrum.asIdeal h
  have key : ∀ M : MaximalSpectrum S, (M.asIdeal.map (Ideal.Quotient.mk I)).comap
    (Ideal.Quotient.mk I) = M.asIdeal :=
    fun M => by
      rw [Ideal.comap_map_of_surjective _ hsurj, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker,
        sup_eq_left.mpr (hle M)]
  ext1
  rw [← key M, ← key M', h']

theorem exists_notMem_linearEquiv_localizedModule_away_of_module_finite
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [Module.Finite A B] (P : Type u)
      [AddCommGroup P]
    [Module B P] [Module.Finite B P] [Module.Invertible B P] (𝔭 : Ideal A) [𝔭.IsPrime] :
    ∃ a : A, a ∉ 𝔭 ∧ Nonempty (LocalizedModule (Submonoid.powers (algebraMap A B a)) P
      ≃ₗ[Localization.Away (algebraMap A B a)]
      Localization.Away (algebraMap A B a)) := by
  classical
  let S : Submonoid B := Algebra.algebraMapSubmonoid B 𝔭.primeCompl
  rcases subsingleton_or_nontrivial (Localization S) with hS | hS
  · have h0 : (0 : Localization S) = 1 := Subsingleton.elim _ _
    have : ∃ s : S, (s : B) * 1 = (s : B) * 0 := by
      have := (IsLocalization.eq_iff_exists S (Localization S)).mp
        (show algebraMap B (Localization S) 1 = algebraMap B (Localization S) 0 from
          Subsingleton.elim _ _)
      simpa using this
    obtain ⟨⟨s, hs⟩, hs0⟩ := this
    simp only [mul_one, mul_zero] at hs0
    obtain ⟨a, ha, rfl⟩ := hs
    refine ⟨a, ha, ?_⟩
    have : Subsingleton (Localization.Away (algebraMap A B a)) :=
      IsLocalization.subsingleton (M := Submonoid.powers (algebraMap A B a)) (S :=
        Localization.Away (algebraMap A B a))
        ((Submonoid.mem_powers_iff _ _).mpr ⟨1, by rw [pow_one, hs0]⟩)
    have : Subsingleton (LocalizedModule (Submonoid.powers (algebraMap A B a)) P) :=
      Module.subsingleton (Localization.Away (algebraMap A B a)) _
    exact ⟨LinearEquiv.ofSubsingleton _ _⟩
  · have : Module.Finite (Localization.AtPrime 𝔭) (Localization S) :=
      Module.Finite.of_isLocalization A B 𝔭.primeCompl
    have : Finite (MaximalSpectrum (Localization S)) :=
      finite_maximalSpectrum_of_isLocalRing_of_moduleFinite (Localization.AtPrime 𝔭) (Localization
        S)
    have : Module.Free (Localization S) (LocalizedModule S P) :=
      CommRing.Pic.mk_eq_one_iff_free.mp (Subsingleton.elim _ _)
    have : Module.FinitePresentation B P := Module.finitePresentation_of_projective B P
    obtain ⟨r, hrS, hfree, -⟩ := Module.FinitePresentation.exists_free_localizedModule_powers S
      (LocalizedModule.mkLinearMap S P) (Localization S)
    obtain ⟨a, ha, rfl⟩ := hrS
    refine ⟨a, ha, ?_⟩
    have := hfree
    exact Module.Invertible.free_iff_linearEquiv.mp hfree

end Module.Invertible

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open _root_.TopologicalSpace
open _root_.Opposite

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace Modules
open _root_.AlgebraicGeometry.Scheme.Modules
namespace B1Glue
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry

/-- The algebraic local triviality assertion for an invertible module over a finite algebra
after inverting a base element outside a given prime. -/
def ALGStatement : Prop :=
  ∀ {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [Module.Finite A B]
    (P : Type u) [AddCommGroup P] [Module B P] [Module.Finite B P] [Module.Invertible B P]
    (𝔭 : Ideal A) [𝔭.IsPrime],
    ∃ a : A, a ∉ 𝔭 ∧ Nonempty (LocalizedModule (Submonoid.powers (algebraMap A B a)) P
      ≃ₗ[Localization.Away (algebraMap A B a)] Localization.Away (algebraMap A B a))

variable {Y : Scheme.{u}}

/-- Restrict a section of `M` along the open inclusion `h`. -/
noncomputable abbrev res (M : Y.Modules) {U W : Y.Opens} (h : W ≤ U) (s : Γ(M, U)) : Γ(M, W) :=
  M.presheaf.map (homOfLE h).op s

lemma res_res (M : Y.Modules) {U W W' : Y.Opens} (h : W ≤ U) (h' : W' ≤ W) (s : Γ(M, U)) :
    res M h' (res M h s) = res M (h'.trans h) s := by
  change (M.presheaf.map (homOfLE h).op ≫ M.presheaf.map (homOfLE h').op) s = _
  rw [← Functor.map_comp]
  rfl

lemma res_smul (M : Y.Modules) {U W : Y.Opens} (h : W ≤ U) (g : Γ(Y, U)) (s : Γ(M, U)) :
    res M h (g • s) = Y.presheaf.map (homOfLE h).op g • res M h s :=
  Scheme.Modules.map_smul M (homOfLE h) g s

lemma presheaf_map_map (M : Y.Modules) {A B C : Y.Opens} (f : B ⟶ A) (g : C ⟶ B) (k : C ⟶ A) (x :
  Γ(M, A)) :
    M.presheaf.map g.op (M.presheaf.map f.op x) = M.presheaf.map k.op x := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, Subsingleton.elim (g ≫ f) k]

lemma ringCat_presheaf_map_map {A B C : Y.Opens} (f : B ⟶ A) (g : C ⟶ B) (k : C ⟶ A) (x : Γ(Y, A)) :
    Y.presheaf.map g.op (Y.presheaf.map f.op x) = Y.presheaf.map k.op x := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, Subsingleton.elim (g ≫ f) k]

theorem isFrameOn_of_forall_exists {M : Y.Modules} {U : Y.Opens} {s : Γ(M, U)} {V : Y.Opens} (_hVU
  : V ≤ U)
    (h : ∀ x ∈ V, ∃ W : Y.Opens, x ∈ W ∧ W ≤ V ∧ Scheme.Modules.IsFrameOn s W) :
    Scheme.Modules.IsFrameOn s V := by
  classical
  choose Wx hxWx hWxV hfr using h
  intro W hWU hWV
  let Uc : W → Y.Opens := fun x => W ⊓ Wx x.1 (hWV x.2)
  have hUcW : ∀ i, Uc i ≤ W := fun i => inf_le_left
  have hUcU : ∀ i, Uc i ≤ U := fun i => (hUcW i).trans hWU
  have hUcWx : ∀ i : W, Uc i ≤ Wx i.1 (hWV i.2) := fun i => inf_le_right
  let iUV : ∀ i, Uc i ⟶ W := fun i => homOfLE (hUcW i)
  have hcover : W ≤ iSup Uc := fun y hy =>
    Opens.mem_iSup.mpr ⟨⟨y, hy⟩, ⟨hy, hxWx y (hWV hy)⟩⟩
  have hbij : ∀ i, Function.Bijective fun g : Γ(Y, Uc i) =>
      g • (M.presheaf.map (homOfLE (hUcU i)).op s : Γ(M, Uc i)) :=
    fun i => hfr i.1 (hWV i.2) (hUcU i) (hUcWx i)
  have hbij2 : ∀ i j, Function.Bijective fun g : Γ(Y, Uc i ⊓ Uc j) =>
      g • (M.presheaf.map (homOfLE (inf_le_left.trans (hUcU i))).op s : Γ(M, Uc i ⊓ Uc j)) :=
    fun i j => hfr i.1 (hWV i.2) (inf_le_left.trans (hUcU i)) (inf_le_left.trans (hUcWx i))
  let 𝒪 : TopCat.Sheaf CommRingCat Y.toTopCat := Y.sheaf
  let ℳ : TopCat.Sheaf Ab Y.toTopCat := ⟨M.presheaf, Scheme.Modules.isSheaf M⟩
  have hres : ∀ (i : W) (g : Γ(Y, W)),
      M.presheaf.map (iUV i).op (g • M.presheaf.map (homOfLE hWU).op s) =
        Y.presheaf.map (iUV i).op g • M.presheaf.map (homOfLE (hUcU i)).op s := fun i g => by
    rw [Scheme.Modules.map_smul, presheaf_map_map M (homOfLE hWU) (iUV i) (homOfLE (hUcU i))]
  refine ⟨fun g g' hgg' => ?_, fun m => ?_⟩
  · apply TopCat.Sheaf.eq_of_locally_eq' 𝒪 Uc W iUV hcover
    intro i
    have hi := congrArg (M.presheaf.map (iUV i).op) hgg'
    change M.presheaf.map (iUV i).op (g • _) = M.presheaf.map (iUV i).op (g' • _) at hi
    rw [hres, hres] at hi
    exact (hbij i).1 hi
  · have hloc : ∀ i, ∃ g : Γ(Y, Uc i),
        g • M.presheaf.map (homOfLE (hUcU i)).op s = M.presheaf.map (iUV i).op m := fun i => (hbij
          i).2 _
    choose gi hgi using hloc
    have hcompat : TopCat.Presheaf.IsCompatible 𝒪.obj Uc gi := by
      intro i j
      apply (hbij2 i j).1
      change Y.presheaf.map _ (gi i) • _ = Y.presheaf.map _ (gi j) • _
      have hi := congrArg (M.presheaf.map (homOfLE (inf_le_left : Uc i ⊓ Uc j ≤ Uc i)).op) (hgi i)
      have hj := congrArg (M.presheaf.map (homOfLE (inf_le_right : Uc i ⊓ Uc j ≤ Uc j)).op) (hgi j)
      rw [Scheme.Modules.map_smul, presheaf_map_map M _ _ (homOfLE (inf_le_left.trans (hUcU i))),
        presheaf_map_map M _ _ (homOfLE (inf_le_left.trans (hUcW i)))] at hi
      rw [Scheme.Modules.map_smul, presheaf_map_map M _ _ (homOfLE (inf_le_left.trans (hUcU i))),
        presheaf_map_map M _ _ (homOfLE (inf_le_left.trans (hUcW i)))] at hj
      exact hi.trans hj.symm
    obtain ⟨g, hg, -⟩ := TopCat.Sheaf.existsUnique_gluing' 𝒪 Uc W iUV hcover gi hcompat
    change Γ(Y, W) at g
    refine ⟨g, ?_⟩
    apply TopCat.Sheaf.eq_of_locally_eq' ℳ Uc W iUV hcover
    intro i
    change M.presheaf.map (iUV i).op (g • _) = M.presheaf.map (iUV i).op m
    rw [hres, ← hgi i]
    exact congrArg (fun c : Γ(Y, Uc i) => c • M.presheaf.map (homOfLE (hUcU i)).op s) (hg i)

lemma res_rfl (M : Y.Modules) {U : Y.Opens} (s : Γ(M, U)) : res M (le_refl U) s = s := by
  change (M.presheaf.map (𝟙 (op U))) s = s
  rw [M.presheaf.map_id]
  rfl

theorem isFrameOn_of_res_eq_smul {M : Y.Modules} {U₁ U₂ W : Y.Opens} {s : Γ(M, U₁)} {p : Γ(M, U₂)}
    (h₁ : W ≤ U₁) (h₂ : W ≤ U₂) (hs : Scheme.Modules.IsFrameOn s W) (u : Γ(Y, W))
    (hu : res M h₁ s = u • res M h₂ p) :
    Scheme.Modules.IsFrameOn p W := by
  obtain ⟨h, hh⟩ := (hs h₁ le_rfl).2 (res M h₂ p)
  have hh' : h • res M h₁ s = res M h₂ p := hh
  have huh : u * h = 1 := by
    apply (hs h₁ le_rfl).1
    change (u * h) • res M h₁ s = (1 : Γ(Y, W)) • res M h₁ s
    rw [one_smul, mul_smul, hh', ← hu]
  have hunit : IsUnit h := isUnit_iff_exists_inv.mpr ⟨u, (mul_comm h u).trans huh⟩
  intro W' hW'U hW'W
  have hres : res M hW'U p = Y.presheaf.map (homOfLE hW'W).op h • res M (hW'W.trans h₁) s := by
    have := congrArg (res M hW'W) hh'
    rw [res_smul, res_res, res_res] at this
    exact this.symm
  have hunit' : IsUnit (Y.presheaf.map (homOfLE hW'W).op h) := hunit.map _
  have hbij := hs (hW'W.trans h₁) hW'W
  have key : (fun g : Γ(Y, W') => g • res M hW'U p) =
      (fun g : Γ(Y, W') => g • res M (hW'W.trans h₁) s) ∘
        (fun g : Γ(Y, W') => g * Y.presheaf.map (homOfLE hW'W).op h) := by
    funext g
    simp only [Function.comp_apply, hres, mul_smul]
  change Function.Bijective (fun g : Γ(Y, W') => g • res M hW'U p)
  rw [key]
  have hmul : Function.Bijective (fun g : Γ(Y, W') => g * Y.presheaf.map (homOfLE hW'W).op h) := by
    have heq : (fun g : Γ(Y, W') => g * Y.presheaf.map (homOfLE hW'W).op h) = ⇑(Units.mulRight
      hunit'.unit) := by
      funext g
      simp [IsUnit.unit_spec]
    rw [heq]
    exact (Units.mulRight hunit'.unit).bijective
  exact hbij.comp hmul

theorem exists_forall_exists_pow_smul_eq_of_linearEquiv {B : Type u} [CommRing B] {P : Type u}
  [AddCommGroup P]
    [Module B P] (a : B)
    (e : LocalizedModule (Submonoid.powers a) P ≃ₗ[Localization.Away a] Localization.Away a) :
    ∃ p : P, ∀ y : P, ∃ (n : ℕ) (c : B), (a ^ n) • y = c • p := by
  classical
  obtain ⟨m, s, hms⟩ : ∃ (m : P) (s : Submonoid.powers a), LocalizedModule.mk m s = e.symm 1 := by
    induction e.symm 1 using LocalizedModule.induction_on with
    | h m s => exact ⟨m, s, rfl⟩
  refine ⟨m, fun y => ?_⟩
  obtain ⟨b, t, hbt⟩ : ∃ (b : B) (t : Submonoid.powers a), Localization.mk b t = e
    (LocalizedModule.mk y 1) := by
    induction e (LocalizedModule.mk y 1) using Localization.induction_on with
    | H x => exact ⟨x.1, x.2, rfl⟩
  have h1 : LocalizedModule.mk y 1 = LocalizedModule.mk (b • m) (t * s) := by
    calc LocalizedModule.mk y (1 : Submonoid.powers a) = e.symm (e (LocalizedModule.mk y 1)) :=
          (e.symm_apply_apply _).symm
      _ = e.symm (Localization.mk b t • (1 : Localization.Away a)) :=
        by rw [← hbt, smul_eq_mul, mul_one]
      _ = Localization.mk b t • e.symm 1 := e.symm.map_smul _ _
      _ = Localization.mk b t • LocalizedModule.mk m s := by rw [hms]
      _ = LocalizedModule.mk (b • m) (t * s) := LocalizedModule.mk_smul_mk b m t s
  obtain ⟨u, hu⟩ := LocalizedModule.mk_eq.mp h1
  obtain ⟨i, hi⟩ := (Submonoid.mem_powers_iff _ _).mp u.2
  obtain ⟨j, hj⟩ := (Submonoid.mem_powers_iff _ _).mp t.2
  obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ _).mp s.2
  refine ⟨i + (j + k), a ^ i * b, ?_⟩
  have hu' := hu
  simp only [Submonoid.smul_def, Submonoid.coe_mul, one_smul, smul_smul] at hu'
  rw [← hi, ← hj, ← hk] at hu'
  rw [pow_add, pow_add]
  exact hu'

theorem isFrameOn_basicOpen_of_forall_exists_pow_smul_eq [IsAffine Y] {N : Y.Modules}
    (hN : Scheme.Modules.IsInvertible N) (p : Γ(N, ⊤)) (a : Γ(Y, ⊤))
    (hgen : ∀ y : Γ(N, ⊤), ∃ (n : ℕ) (c : Γ(Y, ⊤)), (a ^ n) • y = c • p) :
    Scheme.Modules.IsFrameOn p (Y.basicOpen a) := by
  refine isFrameOn_of_forall_exists (s := p) le_top fun x hx => ?_
  obtain ⟨U₁, s, hxU₁, hs⟩ := hN.exists_isFrameOn x
  obtain ⟨b, hbU, hxb⟩ := (isAffineOpen_top Y).exists_basicOpen_le ⟨x, (show x ∈ U₁ ⊓ Y.basicOpen a
    from ⟨hxU₁, hx⟩)⟩
    (Set.mem_univ x)
  have hbU₁ : Y.basicOpen b ≤ U₁ := hbU.trans inf_le_left
  have hba : Y.basicOpen b ≤ Y.basicOpen a := hbU.trans inf_le_right
  refine ⟨Y.basicOpen b, hxb, hba, ?_⟩
  have hsb : Scheme.Modules.IsFrameOn (res N hbU₁ s) (Y.basicOpen b) :=
    (hs.mono hbU₁).map (homOfLE hbU₁)
  obtain ⟨n, y, hy⟩ := (Scheme.Modules.isLocalization_basicOpen_of_locallyTrivial N
    hN.exists_trivialization ⟨⊤, isAffineOpen_top Y⟩ b).1
    (res N hbU₁ s)
  obtain ⟨m, c, hc⟩ := hgen y
  have hbunit : IsUnit (Y.presheaf.map (homOfLE (Y.basicOpen_le b)).op b) :=
    RingedSpace.isUnit_res_basicOpen _ b
  have haunit : IsUnit (Y.presheaf.map (homOfLE (Y.basicOpen_le b)).op a) := by
    have h2 := (RingedSpace.isUnit_res_basicOpen Y.toLocallyRingedSpace.toRingedSpace a).map
      (Y.presheaf.map (homOfLE hba).op).hom
    have h3 : (Y.presheaf.map (homOfLE hba).op).hom (Y.presheaf.map (homOfLE (Y.basicOpen_le a)).op
      a) =
        Y.presheaf.map (homOfLE (Y.basicOpen_le b)).op a :=
      ringCat_presheaf_map_map (homOfLE (Y.basicOpen_le a)) (homOfLE hba) (homOfLE (Y.basicOpen_le
        b)) a
    convert h2 using 2
    exact h3.symm
  have key : Y.presheaf.map (homOfLE (Y.basicOpen_le b)).op (a ^ m * b ^ n) • res N hbU₁ s =
      Y.presheaf.map (homOfLE (Y.basicOpen_le b)).op c • res N (Y.basicOpen_le b) p := by
    have h1 : res N (Y.basicOpen_le b) ((a ^ m) • y) = res N (Y.basicOpen_le b) (c • p) :=
      by rw [hc]
    rw [res_smul, res_smul] at h1
    rw [map_mul, mul_smul]
    change _ • (Y.presheaf.map (homOfLE (Y.basicOpen_le b)).op (b ^ n) • res N hbU₁ s) = _
    rw [← hy]
    exact h1
  have hunit : IsUnit (Y.presheaf.map (homOfLE (Y.basicOpen_le b)).op (a ^ m * b ^ n)) := by
    rw [map_mul, map_pow, map_pow]
    exact (haunit.pow m).mul (hbunit.pow n)
  refine isFrameOn_of_res_eq_smul (s := res N hbU₁ s) (p := p) le_rfl (Y.basicOpen_le b) hsb
    (↑(hunit.unit⁻¹) * Y.presheaf.map (homOfLE (Y.basicOpen_le b)).op c) ?_
  rw [res_rfl, mul_smul, ← key, ← mul_smul, IsUnit.val_inv_mul, one_smul]

/-- The two-affine-open cover of an affine scheme consisting of two copies of the whole scheme. -/
noncomputable def trivialTwoAffineOpenCover (Y : Scheme.{u}) [IsAffine Y] : Y.TwoAffineOpenCover
  where
  U0 := ⊤
  U1 := ⊤
  isAffineOpen_U0 := isAffineOpen_top Y
  isAffineOpen_U1 := isAffineOpen_top Y
  sup_eq_top := sup_idem _
  isAffineOpen_inf := by rw [inf_idem]; exact isAffineOpen_top Y

theorem moduleInvertible_sections_top [IsAffine Y] {N : Y.Modules} (hN :
  Scheme.Modules.IsInvertible N) :
    Module.Invertible Γ(Y, ⊤) Γ(N, ⊤) := by
  obtain ⟨hproj, hfin, hrk, -⟩ :=
    Scheme.TwoAffineOpenCover.sectionsOf_isInvertible_projective_finite_finrank
      (trivialTwoAffineOpenCover Y) Y.toSpecΓ N hN
  have : Module.Projective Γ(Y, ⊤) Γ(N, ⊤) := hproj
  have : Module.Finite Γ(Y, ⊤) Γ(N, ⊤) := hfin
  exact Module.Invertible.of_projective_of_forall_finrank_eq_one (A := Γ(Y, ⊤)) Γ(N, ⊤) hrk

theorem exists_mem_opens_nonempty_pullback_preimage_iso_tensorUnit_of_isFinite (hALG :
  ALGStatement.{u})
    {Z T : Scheme.{u}} (q : Z ⟶ T) [IsFinite q] {N : Z.Modules} (hN : Scheme.Modules.IsInvertible
      N) (t : T) :
    ∃ W : T.Opens, t ∈ W ∧
      Nonempty ((Scheme.Modules.pullback (q ⁻¹ᵁ W).ι).obj N ≅ 𝟙_ (↑(q ⁻¹ᵁ W) : Scheme.{u}).Modules)
        := by
  obtain ⟨U, haU, htU⟩ : ∃ U : T.Opens, IsAffineOpen U ∧ t ∈ U := by
    obtain ⟨_, ⟨U, hU, rfl⟩, ht, -⟩ := T.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ t) isOpen_univ
    exact ⟨U, hU, ht⟩
  have : IsAffine (U : Scheme.{u}) := haU
  let ι := (q ⁻¹ᵁ U).ι
  have : IsAffine (↑(q ⁻¹ᵁ U) : Scheme.{u}) := haU.preimage q
  let qU : (↑(q ⁻¹ᵁ U) : Scheme.{u}) ⟶ ↑U := q ∣_ U
  let A : Type u := Γ(↑U, ⊤)
  let B : Type u := Γ(↑(q ⁻¹ᵁ U), ⊤)
  let : Algebra A B := qU.appTop.hom.toAlgebra
  have : Module.Finite A B := Scheme.Hom.finite_appTop qU
  let NY : (↑(q ⁻¹ᵁ U) : Scheme.{u}).Modules := (Scheme.Modules.pullback ι).obj N
  have hNY : Scheme.Modules.IsInvertible NY := hN.pullback ι
  have : Module.Invertible B Γ(NY, ⊤) := moduleInvertible_sections_top hNY
  let t' : (↑U : Scheme.{u}) := ⟨t, htU⟩
  let 𝔭 : Ideal A := ((↑U : Scheme.{u}).toSpecΓ.base t').asIdeal
  have : 𝔭.IsPrime := ((↑U : Scheme.{u}).toSpecΓ.base t').isPrime
  obtain ⟨a, ha𝔭, ⟨e⟩⟩ := hALG (A := A) (B := B) Γ(NY, ⊤) 𝔭
  obtain ⟨p, hgen⟩ := exists_forall_exists_pow_smul_eq_of_linearEquiv (algebraMap A B a) e
  have hframe := isFrameOn_basicOpen_of_forall_exists_pow_smul_eq hNY p (algebraMap A B a)
    (fun y => by
      obtain ⟨n, c, h⟩ := hgen y
      exact ⟨n, c, h⟩)
  obtain ⟨eD⟩ := hframe.nonempty_pullback_iso_unit ((↑(q ⁻¹ᵁ U) : Scheme.{u}).basicOpen (algebraMap
    A B a))
    le_top le_rfl
  let W₀ : (↑U : Scheme.{u}).Opens := (↑U : Scheme.{u}).basicOpen a
  refine ⟨U.ι ''ᵁ W₀, ⟨t', ?_, rfl⟩, ?_⟩
  · change t' ∈ (↑U : Scheme.{u}).basicOpen a
    rw [← Scheme.toSpecΓ_preimage_basicOpen]
    exact (PrimeSpectrum.mem_basicOpen a _).mpr ha𝔭
  · let D : (↑(q ⁻¹ᵁ U) : Scheme.{u}).Opens := (↑(q ⁻¹ᵁ U) : Scheme.{u}).basicOpen (algebraMap A B
      a)
    have hE : q ⁻¹ᵁ (U.ι ''ᵁ W₀) = ι ''ᵁ D := by
      rw [← image_morphismRestrict_preimage, Scheme.Hom.preimage_basicOpen_top]
      rfl
    let φ : (↑(q ⁻¹ᵁ (U.ι ''ᵁ W₀)) : Scheme.{u}) ⟶ ↑D := (Z.isoOfEq hE).hom ≫ (ι.isoImage D).inv
    have hφ : (q ⁻¹ᵁ (U.ι ''ᵁ W₀)).ι = φ ≫ D.ι ≫ ι := by
      have h1 := Z.isoOfEq_hom_ι hE
      have h2 : (ι.isoImage D).inv ≫ D.ι ≫ ι = (ι ''ᵁ D).ι := by
        rw [← Scheme.Hom.isoImage_hom_ι, Iso.inv_hom_id_assoc]
      simp only [φ, Category.assoc, h2, h1]
    exact ⟨(Scheme.Modules.pullbackCongr hφ).app N ≪≫ ((Scheme.Modules.pullbackComp φ (D.ι ≫
      ι)).app N).symm ≪≫
      (Scheme.Modules.pullback φ).mapIso (((Scheme.Modules.pullbackComp D.ι ι).app N).symm ≪≫ eD) ≪≫
      Scheme.Modules.pullbackUnitIso φ⟩

end AlgebraicGeometry.Scheme.Modules.B1Glue

end InvertibleFinitePreimage
end AlgebraicCurves.Geometry.Sheaves.Proofs

namespace AlgebraicGeometry.Scheme.Modules.IsInvertible

open _root_.AlgebraicCurves.Geometry.Sheaves.Proofs.InvertibleFinitePreimage
universe u
open _root_.TensorProduct
open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open _root_.TopologicalSpace
open _root_.Opposite

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
  _root_.AlgebraicCurves.Geometry.Sheaves.Proofs.InvertibleFinitePreimage.AlgebraicGeometry
  _root_.CategoryTheory.MonoidalCategory in
open _root_.AlgebraicCurves.Geometry.Sheaves.Proofs in
open InvertibleFinitePreimage.AlgebraicGeometry.Scheme.Modules in
theorem exists_nonempty_pullback_preimage_iso_tensorUnit_of_isFinite
    {Z T : Scheme.{u}} (q : Z ⟶ T) [IsFinite q] {N : Z.Modules} (hN : Scheme.Modules.IsInvertible
      N) (t : T) :
    ∃ W : T.Opens, t ∈ W ∧
      Nonempty ((Scheme.Modules.pullback (q ⁻¹ᵁ W).ι).obj N ≅ 𝟙_ (↑(q ⁻¹ᵁ W) : Scheme.{u}).Modules)
        :=
  B1Glue.exists_mem_opens_nonempty_pullback_preimage_iso_tensorUnit_of_isFinite
    (fun {A B} _ _ _ _ P _ _ _ _ 𝔭 _ =>
      Module.Invertible.exists_notMem_linearEquiv_localizedModule_away_of_module_finite (A := A) (B
        := B) P 𝔭)
    q hN t
end AlgebraicGeometry.Scheme.Modules.IsInvertible
end ProofImplementation

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
attribute [-simp] AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right
  AlgebraicGeometry.Scheme.Modules.map_unitSection
  AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply
  AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left
  AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq
  TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq
  TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec
  TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec
  TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec
  CoherentBaseChange.TwoTermComplex.mk.injEq
