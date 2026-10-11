/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_exists_intermediateField_finiteDimensional_forall_smul_eq_of_descent.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Algebra.Algebra.Hom.Rat
import Nyll.AlgebraicCurves.Divisors.Semilinear
import Nyll.AlgebraicCurves.FunctionFields.CurveOver
import Nyll.AlgebraicCurves.Divisors.Maps
import Nyll.AlgebraicCurves.Places.Place_natCard_setOf_comap_eq_eq_deg_of_linearDisjoint

/-!
# Place exists intermediate Field finite Dimensional forall smul eq of descent
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs
namespace Place_exists_intermediateField_finiteDimensional_forall_smul_eq_of_descent

open _root_.AlgebraicCurve
open scoped Pointwise

namespace AlgebraicCurve
open _root_.AlgebraicCurve
namespace C3Tors
namespace Frame
open _root_.AlgebraicCurve

theorem hfg (F : Type) [Field F] [Algebra ℚ F] [IsCurveOver ℚ F] [Algebra.EssFiniteType ℚ F] :
    ∃ s : Finset F, IntermediateField.adjoin ℚ (s : Set F) = ⊤ :=
  IntermediateField.fg_top ℚ F

theorem hgen (F Fbar : Type) [Field F] [Field Fbar] [Algebra (AlgebraicClosure ℚ) Fbar] [Algebra F
  Fbar]
    (toBar : F →+* Fbar) (halg : ∀ x : F, algebraMap F Fbar x = toBar x)
    (closure_toBar : Subfield.closure
      (Set.range (algebraMap (AlgebraicClosure ℚ) Fbar) ∪ Set.range toBar) = ⊤) :
    IntermediateField.adjoin (AlgebraicClosure ℚ) (Set.range (algebraMap F Fbar)) = ⊤ := by
  have hr : Set.range (algebraMap F Fbar) = Set.range toBar := by
    ext y; constructor
    · rintro ⟨x, rfl⟩; exact ⟨x, (halg x).symm⟩
    · rintro ⟨x, rfl⟩; exact ⟨x, halg x⟩
  rw [eq_top_iff]
  intro x _
  have hx : x ∈ Subfield.closure (Set.range (algebraMap (AlgebraicClosure ℚ) Fbar) ∪ Set.range
    toBar) :=
    closure_toBar.symm ▸ Subfield.mem_top x
  rw [← hr] at hx
  exact hx

theorem hLD (F Fbar : Type) [Field F] [Algebra ℚ F] [Field Fbar] [Algebra (AlgebraicClosure ℚ)
  Fbar] [Algebra F Fbar]
    (toBar : F →+* Fbar) (halg : ∀ x : F, algebraMap F Fbar x = toBar x)
    (linearIndependent_toBar : ∀ s : Finset F,
      LinearIndependent ℚ (fun x : s => (x : F)) →
        LinearIndependent (AlgebraicClosure ℚ) (fun x : s => toBar (x : F))) :
    ∀ (n : ℕ) (f : Fin n → F) (c : Fin n → AlgebraicClosure ℚ), LinearIndependent ℚ f →
      ∑ i, algebraMap (AlgebraicClosure ℚ) Fbar (c i) * algebraMap F Fbar (f i) = 0 → ∀ i, c i = 0
        := by
  classical
  intro n f c hf hsum i
  let s : Finset F := Finset.univ.image f
  have hmem : ∀ j, f j ∈ s := fun j => Finset.mem_image_of_mem f (Finset.mem_univ j)
  have hst : Set.range f = (s : Set F) := by
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
  have hs : LinearIndependent ℚ (fun x : ↥s => (x : F)) := LinearIndependent.linearIndepOn_id' hf
    hst
  have hsbar := linearIndependent_toBar s hs
  let ι : Fin n → ↥s := fun j => ⟨f j, hmem j⟩
  have hι : Function.Injective ι := fun j k h => hf.injective (congrArg Subtype.val h)
  have hli : LinearIndependent (AlgebraicClosure ℚ) (fun j : Fin n => toBar (f j)) := hsbar.comp ι
    hι
  have hsum' : ∑ j, c j • toBar (f j) = 0 := by
    simpa only [Algebra.smul_def, halg] using hsum
  exact linearIndependent_iff'.mp hli Finset.univ c hsum' i (Finset.mem_univ i)

end AlgebraicCurve.C3Tors.Frame

noncomputable section

namespace AlgebraicCurve
open _root_.AlgebraicCurve
namespace C3Tors
namespace Core
open _root_.AlgebraicCurve

section Generic

variable {K F : Type} [Field K] [Field F] [Algebra K F]

theorem smul_mem_nonunits_smul (g : SemilinearAut K F) (P : Place K F) {x : F}
    (hx : x ∈ P.toValuationSubring.nonunits) : g • x ∈ (g • P).toValuationSubring.nonunits := by
  rw [SemilinearAut.smul_toValuationSubring, ValuationSubring.mem_nonunits_iff_or]
  rw [ValuationSubring.mem_nonunits_iff_or] at hx
  rcases hx with h0 | hinv
  · left; rw [h0, smul_zero]
  · right
    rw [← smul_inv'', ValuationSubring.smul_mem_pointwise_smul_iff]
    exact hinv

theorem exists_sub_algebraMap_mem_nonunits [IsAlgClosed K] (P : Place K F) [Module.Finite K
  P.ResidueField]
    (y : F) (hy : y ∈ P.toValuationSubring) :
    ∃ a : K, y - algebraMap K F a ∈ P.toValuationSubring.nonunits := by
  have : Algebra.IsIntegral K P.ResidueField := Algebra.IsIntegral.of_finite K P.ResidueField
  have hbij : Function.Bijective (algebraMap K P.ResidueField) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  obtain ⟨a, ha⟩ := hbij.2 (IsLocalRing.residue P.toValuationSubring ⟨y, hy⟩)
  refine ⟨a, ?_⟩
  have hmem : (⟨y, hy⟩ : P.toValuationSubring) - algebraMap K P.toValuationSubring a ∈
      IsLocalRing.maximalIdeal P.toValuationSubring := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub]
    change IsLocalRing.residue P.toValuationSubring ⟨y, hy⟩ -
      IsLocalRing.residue P.toValuationSubring (algebraMap K P.toValuationSubring a) = 0
    rw [sub_eq_zero, ← ha]
    rfl
  have := (ValuationSubring.coe_mem_nonunits_iff).mpr hmem
  simpa using this

theorem algebraMap_eq_of_sub_mem_nonunits (P : Place K F) {y : F} (_hy : y ∈ P.toValuationSubring)
  {a a' : K}
    (ha : y - algebraMap K F a ∈ P.toValuationSubring.nonunits)
    (ha' : y - algebraMap K F a' ∈ P.toValuationSubring.nonunits) : a = a' := by
  by_contra hne
  have hd : algebraMap K F (a' - a) ∈ P.toValuationSubring.nonunits := by
    have : algebraMap K F (a' - a) = (y - algebraMap K F a) - (y - algebraMap K F a') := by
      rw [map_sub]; ring
    rw [this]
    exact P.toValuationSubring.nonunits.sub_mem ha ha'
  rw [ValuationSubring.mem_nonunits_iff_or] at hd
  rcases hd with h0 | hinv
  · exact hne (sub_eq_zero.mp ((map_eq_zero _).mp h0)).symm
  · apply hinv
    rw [← map_inv₀]
    exact P.algebraMap_mem' _

end Generic

section Frame

variable (F : Type) [Field F] [Algebra ℚ F] [IsCurveOver ℚ F] [Algebra.EssFiniteType ℚ F]
  (Fbar : Type) [Field Fbar] [Algebra (AlgebraicClosure ℚ) Fbar]
  [IsCurveOver (AlgebraicClosure ℚ) Fbar] [Algebra.EssFiniteType (AlgebraicClosure ℚ) Fbar]
  [Algebra F Fbar] [Algebra ℚ Fbar] [IsScalarTower ℚ F Fbar] [IsScalarTower ℚ (AlgebraicClosure ℚ)
    Fbar]

omit [IsCurveOver ℚ F] [Algebra.EssFiniteType ℚ F]
  [IsCurveOver (AlgebraicClosure ℚ) Fbar]
  [Algebra.EssFiniteType (AlgebraicClosure ℚ) Fbar] in
theorem isIntegral_of_closure (toBar : F →+* Fbar) (halg : ∀ x, algebraMap F Fbar x = toBar x)
    (closure_toBar : Subfield.closure
      (Set.range (algebraMap (AlgebraicClosure ℚ) Fbar) ∪ Set.range toBar) = ⊤) :
    Algebra.IsIntegral F Fbar := by
  have hrange : Set.range toBar = Set.range (algebraMap F Fbar) := by
    ext x; constructor <;> rintro ⟨y, rfl⟩ <;> exact ⟨y, by rw [halg]⟩
  have htop : IntermediateField.adjoin F (Set.range (algebraMap (AlgebraicClosure ℚ) Fbar)) = ⊤ :=
    by
    apply IntermediateField.toSubfield_injective
    change Subfield.closure (Set.range (algebraMap F Fbar) ∪ Set.range (algebraMap
      (AlgebraicClosure ℚ) Fbar)) = _
    rw [Set.union_comm, ← hrange, closure_toBar]
    rfl
  have hint : ∀ x ∈ Set.range (algebraMap (AlgebraicClosure ℚ) Fbar), IsIntegral F x := by
    rintro x ⟨a, rfl⟩
    have hAlg : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := by
      convert AlgebraicClosure.isAlgebraic ℚ
    have ha : IsIntegral ℚ a := (hAlg.isAlgebraic a).isIntegral
    have ha' : IsIntegral ℚ (algebraMap (AlgebraicClosure ℚ) Fbar a) :=
      ha.map (IsScalarTower.toAlgHom ℚ (AlgebraicClosure ℚ) Fbar)
    exact ha'.tower_top
  have halgadj : Algebra.IsAlgebraic F (IntermediateField.adjoin F (Set.range (algebraMap
    (AlgebraicClosure ℚ) Fbar))) :=
    IntermediateField.isAlgebraic_adjoin hint
  rw [htop] at halgadj
  have : Algebra.IsAlgebraic F Fbar := (IntermediateField.topEquiv (F := F) (E := Fbar)).isAlgebraic
  exact Algebra.isAlgebraic_iff_isIntegral.mp this

variable [Algebra.IsIntegral F Fbar]

/-- A place over the algebraic closure of the rationals, viewed as a place over the rationals. -/
def overQ (P : Place (AlgebraicClosure ℚ) Fbar) : Place ℚ Fbar where
  toValuationSubring := P.toValuationSubring
  algebraMap_mem' a := by
    rw [IsScalarTower.algebraMap_apply ℚ (AlgebraicClosure ℚ) Fbar]
    exact P.algebraMap_mem' _
  ne_top' := P.ne_top'
  isPrincipalIdealRing' := P.isPrincipalIdealRing'
omit [IsCurveOver (AlgebraicClosure ℚ) Fbar] [Algebra.EssFiniteType (AlgebraicClosure ℚ) Fbar] in
@[scoped simp] theorem overQ_toValuationSubring (P : Place (AlgebraicClosure ℚ) Fbar) :
    (overQ Fbar P).toValuationSubring = P.toValuationSubring := rfl
omit [IsCurveOver ℚ F] [Algebra.EssFiniteType ℚ F]
  [IsCurveOver (AlgebraicClosure ℚ) Fbar]
  [Algebra.EssFiniteType (AlgebraicClosure ℚ) Fbar] in
theorem restrict_smul_eq (g : SemilinearAut (AlgebraicClosure ℚ) Fbar) (hg : ∀ x : F, g •
  algebraMap F Fbar x = algebraMap F Fbar x)
    (P : Place (AlgebraicClosure ℚ) Fbar) :
    (g • P).toValuationSubring.comap (algebraMap F Fbar) = ((overQ Fbar P).restrict
      F).toValuationSubring := by
  rw [Place.restrict_toValuationSubring, overQ_toValuationSubring]
  ext x
  rw [ValuationSubring.mem_comap, ValuationSubring.mem_comap, SemilinearAut.smul_toValuationSubring,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  have : g⁻¹ • algebraMap F Fbar x = algebraMap F Fbar x := by
    rw [inv_smul_eq_iff, hg]
  rw [this]
omit [Algebra.EssFiniteType ℚ F] [Algebra.EssFiniteType (AlgebraicClosure ℚ) Fbar] in
theorem exists_intermediateField_forall_exists_mem (P : Place (AlgebraicClosure ℚ) Fbar) :
    ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ L ∧
      ∀ f : F, f ∈ ((overQ Fbar P).restrict F).toValuationSubring →
        ∃ a : AlgebraicClosure ℚ, a ∈ L ∧
          algebraMap F Fbar f - algebraMap (AlgebraicClosure ℚ) Fbar a ∈
            P.toValuationSubring.nonunits := by
  classical
  set v : Place ℚ F := (overQ Fbar P).restrict F with hv
  have : Module.Finite ℚ v.ResidueField := IsCurveOver.finiteResidue v
  have : Module.Finite (AlgebraicClosure ℚ) P.ResidueField := IsCurveOver.finiteResidue P
  have : Algebra.IsIntegral (AlgebraicClosure ℚ) P.ResidueField := Algebra.IsIntegral.of_finite _ _
  have hbij : Function.Bijective (algebraMap (AlgebraicClosure ℚ) P.ResidueField) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  set e : AlgebraicClosure ℚ ≃+* P.ResidueField := RingEquiv.ofBijective (algebraMap
    (AlgebraicClosure ℚ) P.ResidueField) hbij with he
  set ι : v.toValuationSubring →+* P.toValuationSubring := Place.restrictInclusion F (overQ Fbar P)
    with hι
  have hιloc : IsLocalHom ι := Place.instIsLocalHomRestrictInclusion (F := F) (overQ Fbar P)
  set ρ : v.toValuationSubring →+* AlgebraicClosure ℚ :=
    e.symm.toRingHom.comp ((IsLocalRing.residue P.toValuationSubring).comp ι) with hρ
  have hρ_spec : ∀ f : v.toValuationSubring,
      algebraMap F Fbar (f : F) - algebraMap (AlgebraicClosure ℚ) Fbar (ρ f) ∈
        P.toValuationSubring.nonunits := by
    intro f
    have h1 : IsLocalRing.residue P.toValuationSubring (ι f) =
        IsLocalRing.residue P.toValuationSubring (algebraMap (AlgebraicClosure ℚ)
          P.toValuationSubring (ρ f)) := by
      change _ = algebraMap (AlgebraicClosure ℚ) P.ResidueField (ρ f)
      rw [hρ]
      change _ = algebraMap (AlgebraicClosure ℚ) P.ResidueField (e.symm (IsLocalRing.residue
        P.toValuationSubring (ι f)))
      exact (e.apply_symm_apply _).symm
    have hmem : ι f - algebraMap (AlgebraicClosure ℚ) P.toValuationSubring (ρ f) ∈
        IsLocalRing.maximalIdeal P.toValuationSubring := by
      rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero]
      exact h1
    have := (ValuationSubring.coe_mem_nonunits_iff).mpr hmem
    exact this
  have : IsLocalHom ρ := by
    constructor
    intro f hf
    by_contra hnu
    have hmax : f ∈ IsLocalRing.maximalIdeal v.toValuationSubring := (IsLocalRing.mem_maximalIdeal
      _).mpr hnu
    have hι' : ι f ∈ IsLocalRing.maximalIdeal P.toValuationSubring := by
      by_contra h'
      have hu : IsUnit (ι f) := by
        by_contra hnu'
        exact h' ((IsLocalRing.mem_maximalIdeal _).mpr hnu')
      exact hnu (IsLocalHom.map_nonunit f hu)
    have h0 : ρ f = 0 := by
      rw [hρ, RingHom.comp_apply, RingHom.comp_apply, (IsLocalRing.residue_eq_zero_iff _).mpr hι']
      exact map_zero _
    rw [h0] at hf
    exact not_isUnit_zero hf
  set φ : v.ResidueField →ₐ[ℚ] AlgebraicClosure ℚ := (IsLocalRing.ResidueField.lift ρ).toRatAlgHom
    with hφ
  have hφρ : ∀ f : v.toValuationSubring, φ (IsLocalRing.residue v.toValuationSubring f) = ρ f := by
    intro f
    rw [hφ]
    exact IsLocalRing.ResidueField.lift_residue_apply ρ f
  refine ⟨φ.fieldRange, ?_, ?_⟩
  · let ψ : v.ResidueField →ₗ[ℚ] φ.fieldRange :=
      { toFun := fun x => ⟨φ x, (AlgHom.mem_fieldRange).mpr ⟨x, rfl⟩⟩
        map_add' := fun x y => Subtype.ext (map_add φ x y)
        map_smul' := fun c x => Subtype.ext (by simp) }
    have hψ : Function.Surjective ψ := by
      rintro ⟨y, hy⟩
      obtain ⟨x, rfl⟩ := (AlgHom.mem_fieldRange).mp hy
      exact ⟨x, rfl⟩
    exact Module.Finite.of_surjective ψ hψ
  · intro f hf
    refine ⟨ρ ⟨f, hf⟩, ?_, hρ_spec ⟨f, hf⟩⟩
    rw [← hφρ]
    exact (AlgHom.mem_fieldRange).mpr ⟨_, rfl⟩
omit [Algebra.EssFiniteType ℚ F]
  [Algebra.EssFiniteType (AlgebraicClosure ℚ) Fbar] in
theorem main
    (toBar : F →+* Fbar) (halg : ∀ x, algebraMap F Fbar x = toBar x)
    (gal : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* SemilinearAut (AlgebraicClosure ℚ) Fbar)
    (baseAut_gal : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      SemilinearAut.baseAut (gal σ) = (σ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ))
    (gal_smul_toBar : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : F), gal σ • toBar x
      = toBar x)
    (hfg : ∃ s : Finset F, IntermediateField.adjoin ℚ (s : Set F) = ⊤)
    (hgen : IntermediateField.adjoin (AlgebraicClosure ℚ) (Set.range (algebraMap F Fbar)) = ⊤)
    (hLD : ∀ (n : ℕ) (f : Fin n → F) (c : Fin n → AlgebraicClosure ℚ), LinearIndependent ℚ f →
      ∑ i, algebraMap (AlgebraicClosure ℚ) Fbar (c i) * algebraMap F Fbar (f i) = 0 → ∀ i, c i = 0)
    (P : Place (AlgebraicClosure ℚ) Fbar) :
    ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ L ∧
      ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ y ∈ L, σ y = y) → gal σ • P = P := by
  obtain ⟨L, hL, hchar⟩ := exists_intermediateField_forall_exists_mem F Fbar P
  obtain ⟨-, -, huniq⟩ :=
    AlgebraicCurve.Place.natCard_setOf_comap_eq_eq_deg_of_linearDisjoint (k := ℚ) (K :=
      AlgebraicClosure ℚ)
      (F₀ := F) (F := Fbar) hfg hgen hLD ((overQ Fbar P).restrict F)
  refine ⟨L, hL, fun σ hσ => ?_⟩
  have hfix : ∀ x : F, gal σ • algebraMap F Fbar x = algebraMap F Fbar x := fun x =>
    by rw [halg, gal_smul_toBar]
  symm
  refine huniq P (gal σ • P) rfl (restrict_smul_eq F Fbar (gal σ) hfix P) ?_
  intro f hf a ha
  obtain ⟨a₀, ha₀L, ha₀⟩ := hchar f hf
  have haa₀ : a = a₀ := algebraMap_eq_of_sub_mem_nonunits P ((Place.mem_restrict_iff (overQ Fbar
    P)).mp hf) ha ha₀
  have hσa : σ a = a := by rw [haa₀]; exact hσ a₀ ha₀L
  have ht := smul_mem_nonunits_smul (gal σ) P ha
  rw [smul_sub, hfix, SemilinearAut.smul_algebraMap, baseAut_gal] at ht
  change algebraMap F Fbar f - algebraMap (AlgebraicClosure ℚ) Fbar (σ a) ∈ _ at ht
  rwa [hσa] at ht

end Frame

end AlgebraicCurve.C3Tors.Core

end

theorem
  _root_.AlgebraicCurve.Place.exists_intermediateField_finiteDimensional_forall_smul_eq_of_descent
    (F : Type) [Field F] [Algebra ℚ F] [IsCurveOver ℚ F] [Algebra.EssFiniteType ℚ F]
    (Fbar : Type) [Field Fbar] [Algebra (AlgebraicClosure ℚ) Fbar]
    [IsCurveOver (AlgebraicClosure ℚ) Fbar] [Algebra.EssFiniteType (AlgebraicClosure ℚ) Fbar]
    (toBar : F →+* Fbar)
    (toBar_algebraMap : ∀ r : ℚ,
      toBar (algebraMap ℚ F r) = algebraMap (AlgebraicClosure ℚ) Fbar (algebraMap ℚ
        (AlgebraicClosure ℚ) r))
    (closure_toBar : Subfield.closure
      (Set.range (algebraMap (AlgebraicClosure ℚ) Fbar) ∪ Set.range toBar) = ⊤)
    (linearIndependent_toBar : ∀ s : Finset F,
      LinearIndependent ℚ (fun x : s => (x : F)) →
        LinearIndependent (AlgebraicClosure ℚ) (fun x : s => toBar (x : F)))
    (gal : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* SemilinearAut (AlgebraicClosure ℚ) Fbar)
    (baseAut_gal : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      SemilinearAut.baseAut (gal σ) = (σ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ))
    (gal_smul_toBar : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : F), gal σ • toBar x
      = toBar x)
    (P : Place (AlgebraicClosure ℚ) Fbar) :
    ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ L ∧
      ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ y ∈ L, σ y = y) → gal σ • P = P := by
  let algF : Algebra F Fbar := toBar.toAlgebra
  let algQ : Algebra ℚ Fbar := ((algebraMap (AlgebraicClosure ℚ) Fbar).comp (algebraMap ℚ
    (AlgebraicClosure ℚ))).toAlgebra
  have : IsScalarTower ℚ (AlgebraicClosure ℚ) Fbar := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have halg : ∀ x : F, algebraMap F Fbar x = toBar x := fun _ => rfl
  have : IsScalarTower ℚ F Fbar := IsScalarTower.of_algebraMap_eq (fun r => by
    rw [halg, toBar_algebraMap]; rfl)
  have : Algebra.IsIntegral F Fbar := AlgebraicCurve.C3Tors.Core.isIntegral_of_closure F Fbar toBar
    halg closure_toBar
  exact AlgebraicCurve.C3Tors.Core.main F Fbar toBar halg gal baseAut_gal gal_smul_toBar
    (AlgebraicCurve.C3Tors.Frame.hfg F) (AlgebraicCurve.C3Tors.Frame.hgen F Fbar toBar halg
      closure_toBar)
    (AlgebraicCurve.C3Tors.Frame.hLD F Fbar toBar halg linearIndependent_toBar) P
end Place_exists_intermediateField_finiteDimensional_forall_smul_eq_of_descent
end AlgebraicCurves.Places.Proofs
end ProofImplementation
