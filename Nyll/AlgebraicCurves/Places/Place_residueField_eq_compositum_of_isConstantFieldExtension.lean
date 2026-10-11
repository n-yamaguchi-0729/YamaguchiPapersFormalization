/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_residueField_eq_compositum_of_isConstantFieldExtension.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Divisors.ClassGroup
import Nyll.AlgebraicCurves.Divisors.Maps
import Nyll.AlgebraicCurves.Divisors.ConstantExtension
import Nyll.AlgebraicCurves.Places.OverDVR
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.RingTheory.Discriminant
import Mathlib.RingTheory.PicardGroup

/-!
# Place residue Field eq compositum of is Constant Field Extension
-/

section ProofImplementation


namespace AlgebraicCurves.Places.Proofs.PlaceResidueFieldCompositum

open _root_.AlgebraicCurve
open _root_.IntermediateField

namespace AlgebraicCurve
open _root_.AlgebraicCurve
namespace Place
open _root_.AlgebraicCurve.Place
namespace ResidueCompositumAux
open _root_.AlgebraicCurve.Place
open _root_.AlgebraicCurve

section Constants
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem mem_of_isIntegral (w : Place K F) {y : F} (hy : IsIntegral K y) : y ∈ w.toValuationSubring
  := by
  have hint' : IsIntegral w.toValuationSubring y := hy.tower_top
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint'
  rw [← hz]
  exact z.2

theorem isUnit_of_isIntegral (w : Place K F) {y : F} (hy : IsIntegral K y) (hy0 : y ≠ 0) :
    IsUnit (⟨y, mem_of_isIntegral w hy⟩ : w.toValuationSubring) := by
  have hinv : y⁻¹ ∈ w.toValuationSubring := mem_of_isIntegral w hy.inv
  refine ⟨⟨⟨y, mem_of_isIntegral w hy⟩, ⟨y⁻¹, hinv⟩, ?_, ?_⟩, rfl⟩
  · exact Subtype.ext (mul_inv_cancel₀ hy0)
  · exact Subtype.ext (inv_mul_cancel₀ hy0)

end Constants

section Layer

variable {K F F₁ : Type*} [Field K] [Field F] [Field F₁]
  [Algebra K F] [Algebra K F₁] [Algebra F F₁] [IsScalarTower K F F₁]
  [FiniteDimensional F F₁] [Algebra.IsSeparable F F₁]

theorem mem_adjoin_of_isIntegral_valuationSubring (v : Place K F) {α : F₁} (hαK : IsIntegral K α)
    (hgen : IntermediateField.adjoin F ({α} : Set F₁) = ⊤) {z : F₁}
    (hz : IsIntegral v.toValuationSubring z) :
    z ∈ Algebra.adjoin v.toValuationSubring ({α} : Set F₁) := by
  have : IsScalarTower v.toValuationSubring F F₁ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower K v.toValuationSubring F₁ := IsScalarTower.of_algebraMap_eq fun a => by
    change algebraMap K F₁ a = algebraMap F F₁ (algebraMap v.toValuationSubring F (algebraMap K _
      a))
    rw [← IsScalarTower.algebraMap_apply K v.toValuationSubring F, ←
      IsScalarTower.algebraMap_apply K F F₁]
  have hαF : IsIntegral F α := hαK.tower_top
  let B₀ := IntermediateField.adjoin.powerBasis hαF
  let e : IntermediateField.adjoin F ({α} : Set F₁) ≃ₐ[F] F₁ :=
    (IntermediateField.equivOfEq hgen).trans IntermediateField.topEquiv
  let B : PowerBasis F F₁ := B₀.map e
  have hBgen : B.gen = α := by
    change e B₀.gen = α
    rw [IntermediateField.adjoin.powerBasis_gen]
    rfl
  have hdisc_int : IsIntegral K (Algebra.discr F B.basis) := by
    rw [Algebra.discr_def, Matrix.det_apply]
    refine IsIntegral.sum _ fun σ _ => ?_
    have hprod : IsIntegral K (∏ i, Algebra.traceMatrix F (⇑B.basis) (σ i) i) := by
      refine IsIntegral.prod _ fun i _ => ?_
      rw [Algebra.traceMatrix_apply, PowerBasis.coe_basis, hBgen]
      exact Algebra.isIntegral_trace ((hαK.pow _).mul (hαK.pow _))
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
    · rw [h, one_smul]; exact hprod
    · rw [h, Units.neg_smul, one_smul]; exact hprod.neg
  have hdisc_ne : Algebra.discr F B.basis ≠ 0 := (Algebra.discr_isUnit_of_basis F B.basis).ne_zero
  have hkey : Algebra.discr F B.basis • z ∈ Algebra.adjoin v.toValuationSubring ({B.gen} : Set F₁)
    :=
    Algebra.discr_mul_isIntegral_mem_adjoin F (hBgen ▸ (hαK.tower_top : IsIntegral
      v.toValuationSubring α)) hz
  rw [hBgen] at hkey
  have hu := isUnit_of_isIntegral v hdisc_int hdisc_ne
  set d := Algebra.discr F B.basis with hd
  have hucoe : ((hu.unit : (v.toValuationSubring)ˣ) : v.toValuationSubring) = ⟨d,
    mem_of_isIntegral v hdisc_int⟩ :=
    hu.unit_spec
  have hinv : algebraMap v.toValuationSubring F₁ ((hu.unit⁻¹ : (v.toValuationSubring)ˣ) :
    v.toValuationSubring)
      * algebraMap F F₁ d = 1 := by
    rw [IsScalarTower.algebraMap_apply v.toValuationSubring F F₁, ← map_mul, ← map_one (algebraMap
      F F₁)]
    congr 1
    have h1 : ((hu.unit⁻¹ : (v.toValuationSubring)ˣ) : v.toValuationSubring) * hu.unit = 1 :=
      Units.inv_mul _
    rw [hucoe] at h1
    have h2 := congrArg Subtype.val h1
    simp only [MulMemClass.coe_mul, OneMemClass.coe_one] at h2
    exact h2
  have hz_eq : z = algebraMap v.toValuationSubring F₁ ((hu.unit⁻¹ : (v.toValuationSubring)ˣ) :
    v.toValuationSubring)
      * (d • z) := by
    rw [Algebra.smul_def, ← mul_assoc, hinv, one_mul]
  rw [hz_eq]
  exact mul_mem (Subalgebra.algebraMap_mem _ _) hkey

end Layer

end AlgebraicCurve.Place.ResidueCompositumAux

namespace AlgebraicCurve
open _root_.AlgebraicCurve
namespace Place
open _root_.AlgebraicCurve.Place
namespace ResidueCompositumAux
open _root_.AlgebraicCurve.Place
open _root_.AlgebraicCurve

section LayerThrough

theorem algebraMap_mem_adjoin_of_mem_adjoin {K K' F F' : Type*} [Field K] [Field K'] [Field F]
  [Field F']
    [Algebra K K'] [Algebra K' F'] [Algebra K F'] [IsScalarTower K K' F']
    [Algebra K F] [Algebra F F'] [IsScalarTower K F F'] {α s : K'}
    (hs : s ∈ Algebra.adjoin K ({α} : Set K')) :
    algebraMap K' F' s ∈ IntermediateField.adjoin F ({algebraMap K' F' α} : Set F') := by
  let φ : K' →ₐ[K] F' := IsScalarTower.toAlgHom K K' F'
  have h1 : φ s ∈ (Algebra.adjoin K ({α} : Set K')).map φ := Subalgebra.mem_map.mpr ⟨s, hs, rfl⟩
  rw [AlgHom.map_adjoin, Set.image_singleton] at h1
  have h2 : Algebra.adjoin K ({φ α} : Set F') ≤
      ((IntermediateField.adjoin F ({algebraMap K' F' α} : Set F')).toSubalgebra).restrictScalars
        K := by
    refine Algebra.adjoin_le ?_
    rintro _ rfl
    exact IntermediateField.mem_adjoin_simple_self F (algebraMap K' F' α)
  exact h2 h1

theorem isIntegral_algebraMap_of_isIntegral {K K' F F' : Type*} [Field K] [Field K'] [Field F]
  [Field F']
    [Algebra K K'] [Algebra K' F'] [Algebra K F'] [IsScalarTower K K' F']
    [Algebra K F] [Algebra F F'] [IsScalarTower K F F'] {α : K'} (hα : IsIntegral K α) :
    IsIntegral F (algebraMap K' F' α) := by
  have h : IsIntegral K (algebraMap K' F' α) := hα.map (IsScalarTower.toAlgHom K K' F')
  exact h.tower_top

theorem isSeparable_algebraMap_of_isSeparable {K K' F F' : Type*} [Field K] [Field K'] [Field F]
  [Field F']
    [Algebra K K'] [Algebra K' F'] [Algebra K F'] [IsScalarTower K K' F']
    [Algebra K F] [Algebra F F'] [IsScalarTower K F F'] {α : K'} (hα : IsSeparable K α) :
    IsSeparable F (algebraMap K' F' α) := by
  have h : IsSeparable K (algebraMap K' F' α) :=
    IsSeparable.map (IsScalarTower.toAlgHom K K' F') (algebraMap K' F').injective hα
  exact IsSeparable.tower_top F h

theorem exists_layer {K K' F F' : Type*} [Field K] [Field K'] [Field F] [Field F']
    [Algebra K K'] [Algebra K' F'] [Algebra K F'] [IsScalarTower K K' F']
    [Algebra K F] [Algebra F F'] [IsScalarTower K F F']
    [Algebra.IsAlgebraic K K'] [Algebra.IsSeparable K K']
    (hgen : Algebra.adjoin F (Set.range (algebraMap K' F')) = ⊤) (x : F') :
    ∃ α : K', x ∈ IntermediateField.adjoin F ({algebraMap K' F' α} : Set F') := by
  classical
  have hx : x ∈ IntermediateField.adjoin F (Set.range (algebraMap K' F')) := by
    have : x ∈ Algebra.adjoin F (Set.range (algebraMap K' F')) := by rw [hgen]; trivial
    exact IntermediateField.algebra_adjoin_le_adjoin F _ this
  obtain ⟨T, hT, hxT⟩ := IntermediateField.exists_finset_of_mem_adjoin hx
  have hpre : ∀ t : T, ∃ a : K', algebraMap K' F' a = (t : F') := fun t => hT t.2
  choose a ha using hpre
  let S : Finset K' := Finset.univ.image a
  let E : IntermediateField K K' := IntermediateField.adjoin K (S : Set K')
  have : FiniteDimensional K E :=
    IntermediateField.finiteDimensional_adjoin fun s _ => (Algebra.IsAlgebraic.isAlgebraic (R :=
      K) s).isIntegral
  have : Algebra.IsSeparable K E := Algebra.isSeparable_tower_bot_of_isSeparable K E K'
  obtain ⟨α₀, hα₀⟩ := Field.exists_primitive_element K E
  refine ⟨(α₀ : K'), ?_⟩
  have hE : E = IntermediateField.adjoin K ({(α₀ : K')} : Set K') := by
    have h1 : IntermediateField.lift (⊤ : IntermediateField K E) = E := IntermediateField.lift_top
      K E
    rw [← hα₀, IntermediateField.lift_adjoin_simple] at h1
    exact h1.symm
  have hmem : ∀ t : T, (t : F') ∈ IntermediateField.adjoin F ({algebraMap K' F' (α₀ : K')} : Set
    F') := by
    intro t
    rw [← ha t]
    refine algebraMap_mem_adjoin_of_mem_adjoin (K := K) ?_
    have h1 : a t ∈ E := IntermediateField.subset_adjoin K (S : Set K')
      (by simp only [S, Finset.coe_image, Finset.coe_univ, Set.image_univ]; exact ⟨t, rfl⟩)
    rw [hE] at h1
    have h2 : a t ∈ (IntermediateField.adjoin K ({(α₀ : K')} : Set K')).toSubalgebra := h1
    rwa [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (Algebra.IsAlgebraic.isAlgebraic (α₀ : K'))] at h2
  have hle : IntermediateField.adjoin F (T : Set F') ≤
      IntermediateField.adjoin F ({algebraMap K' F' (α₀ : K')} : Set F') :=
    IntermediateField.adjoin_le_iff.mpr fun t ht => hmem ⟨t, ht⟩
  exact hle hxT

end LayerThrough

section Inside

variable {F F' : Type*} [Field F] [Field F'] [Algebra F F']

theorem adjoin_gen_eq_top (a : F') :
    IntermediateField.adjoin F
        ({(⟨a, IntermediateField.mem_adjoin_simple_self F a⟩ : IntermediateField.adjoin F ({a} :
          Set F'))} :
          Set (IntermediateField.adjoin F ({a} : Set F'))) = ⊤ := by
  apply IntermediateField.lift_injective
  rw [IntermediateField.lift_adjoin_simple, IntermediateField.lift_top]

theorem finiteDimensional_adjoin_simple_of_isIntegral {a : F'} (ha : IsIntegral F a) :
    FiniteDimensional F (IntermediateField.adjoin F ({a} : Set F')) :=
  IntermediateField.adjoin.finiteDimensional ha

theorem isSeparable_adjoin_simple {a : F'} (ha : IsSeparable F a) :
    Algebra.IsSeparable F (IntermediateField.adjoin F ({a} : Set F')) :=
  (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable F F').mpr ha

theorem isIntegral_gen_of_isIntegral {K : Type*} [Field K] [Algebra K F] [Algebra K F']
  [IsScalarTower K F F']
    {a : F'} (ha : IsIntegral K a) :
    IsIntegral K (⟨a, IntermediateField.mem_adjoin_simple_self F a⟩ : IntermediateField.adjoin F
      ({a} : Set F')) := by
  have : IsScalarTower K (IntermediateField.adjoin F ({a} : Set F')) F' :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact (isIntegral_algebraMap_iff (R := K) (A := IntermediateField.adjoin F ({a} : Set F')) (B :=
    F')).mp ha

end Inside

end AlgebraicCurve.Place.ResidueCompositumAux

namespace AlgebraicCurve
open _root_.AlgebraicCurve
namespace Place
open _root_.AlgebraicCurve.Place
namespace ResidueCompositumAux
open _root_.AlgebraicCurve.Place
open _root_.AlgebraicCurve

section ResidueChase

open IsLocalRing

theorem residue_mem_adjoin_of_mem_adjoin {K K' F F' : Type*} [Field K] [Field K'] [Field F] [Field
  F']
    [Algebra K K'] [Algebra K' F'] [Algebra K F'] [IsScalarTower K K' F']
    [Algebra K F] [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral K K']
      [Algebra.IsIntegral F F']
    (W : Place K' F') (F₁ : IntermediateField F F') (α : K') (hα : algebraMap K' F' α ∈ F₁)
    (z : F₁)
    (hz : z ∈ Algebra.adjoin ((W.forgetConstants (K := K)).restrict F).toValuationSubring
      ({⟨algebraMap K' F' α, hα⟩} : Set F₁)) :
    ∃ hzO : ((z : F₁) : F') ∈ W.toValuationSubring,
      IsLocalRing.residue W.toValuationSubring ⟨(z : F'), hzO⟩ ∈
        IntermediateField.adjoin K' (E := W.ResidueField)
          (Set.range ((W.forgetConstants (K := K)).restrictResidueMap (F := F))) := by
  refine Algebra.adjoin_induction (hx := hz) ?_ ?_ ?_ ?_
  · rintro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    refine ⟨W.algebraMap_mem' α, ?_⟩
    have h : IsLocalRing.residue W.toValuationSubring ⟨algebraMap K' F' α, W.algebraMap_mem' α⟩ =
        algebraMap K' W.ResidueField α := rfl
    rw [h]
    exact IntermediateField.algebraMap_mem _ α
  · intro r
    have hr : algebraMap F F' (r : F) ∈ W.toValuationSubring :=
      (mem_restrict_iff (w := W.forgetConstants (K := K))).mp r.2
    refine ⟨hr, ?_⟩
    refine IntermediateField.subset_adjoin K' _ ⟨IsLocalRing.residue _ r, ?_⟩
    rw [restrictResidueMap_residue]
    rfl
  · rintro x y - - ⟨hx, hx'⟩ ⟨hy, hy'⟩
    refine ⟨add_mem hx hy, ?_⟩
    have h : (⟨((x + y : F₁) : F'), add_mem hx hy⟩ : W.toValuationSubring) = ⟨(x : F'), hx⟩ + ⟨(y
      : F'), hy⟩ :=
      Subtype.ext rfl
    rw [h, map_add]
    exact add_mem hx' hy'
  · rintro x y - - ⟨hx, hx'⟩ ⟨hy, hy'⟩
    refine ⟨mul_mem hx hy, ?_⟩
    have h : (⟨((x * y : F₁) : F'), mul_mem hx hy⟩ : W.toValuationSubring) = ⟨(x : F'), hx⟩ * ⟨(y
      : F'), hy⟩ :=
      Subtype.ext rfl
    rw [h, map_mul]
    exact mul_mem hx' hy'

end ResidueChase

end AlgebraicCurve.Place.ResidueCompositumAux

namespace AlgebraicCurve
open _root_.AlgebraicCurve
namespace Place
open _root_.AlgebraicCurve.Place
namespace ResidueCompositumAux
open _root_.AlgebraicCurve.Place
open _root_.AlgebraicCurve

section Tower

variable {K F F₁ F' : Type*} [Field K] [Field F] [Field F₁] [Field F']
  [Algebra K F] [Algebra K F₁] [Algebra K F'] [Algebra F F₁] [Algebra F₁ F'] [Algebra F F']
  [IsScalarTower F F₁ F'] [IsScalarTower K F F'] [IsScalarTower K F₁ F'] [IsScalarTower K F F₁]
  [Algebra.IsIntegral F F'] [Algebra.IsIntegral F₁ F'] [Algebra.IsIntegral F F₁]

theorem restrict_restrict (w : Place K F') : (w.restrict F₁).restrict F = w.restrict F := by
  apply Place.ext
  ext f
  simp only [restrict_toValuationSubring, ValuationSubring.mem_comap]
  rw [← IsScalarTower.algebraMap_apply]

end Tower

section Main

variable {K K' F F' : Type*} [Field K] [Field K'] [Field F] [Field F']
    [Algebra K K'] [Algebra K' F'] [Algebra K F'] [IsScalarTower K K' F']
    [Algebra K F] [Algebra F F'] [IsScalarTower K F F']
    [Algebra.IsAlgebraic K K'] [Algebra.IsSeparable K K'] [Algebra.IsIntegral F F']

theorem main (hgen : Algebra.adjoin F (Set.range (algebraMap K' F')) = ⊤) (W : Place K' F') :
    IntermediateField.adjoin K' (E := W.ResidueField)
        (Set.range ((W.forgetConstants (K := K)).restrictResidueMap (F := F))) = ⊤ := by
  have : Algebra.IsIntegral K K' := Algebra.isAlgebraic_iff_isIntegral.mp inferInstance
  set w : Place K F' := W.forgetConstants (K := K) with hw_def
  rw [eq_top_iff]
  rintro xbar -
  set A := IntermediateField.adjoin K' (E := W.ResidueField) (Set.range (w.restrictResidueMap (F
    := F)))
    with hA
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective xbar
  obtain ⟨α, hxα⟩ := exists_layer (K := K) hgen (x : F')
  set a : F' := algebraMap K' F' α with ha_def
  have hαK : IsIntegral K α := Algebra.IsIntegral.isIntegral α
  have haK : IsIntegral K a := hαK.map (IsScalarTower.toAlgHom K K' F')
  have haF : IsIntegral F a := haK.tower_top
  have hαsep : IsSeparable K α := Algebra.IsSeparable.isSeparable K α
  have hasepK : IsSeparable K a := by
    unfold IsSeparable at hαsep ⊢
    rwa [ha_def, minpoly.algebraMap_eq (algebraMap K' F').injective]
  have hasep : IsSeparable F a := IsSeparable.tower_top F hasepK
  have hfd : FiniteDimensional F (IntermediateField.adjoin F ({a} : Set F')) :=
    IntermediateField.adjoin.finiteDimensional haF
  have hsepI : Algebra.IsSeparable F (IntermediateField.adjoin F ({a} : Set F')) :=
    (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable F F').mpr hasep
  set F₁ : IntermediateField F F' := IntermediateField.adjoin F ({a} : Set F') with hF₁
  have : IsScalarTower K F₁ F' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower K F F₁ := IsScalarTower.of_algebraMap_eq fun k =>
    Subtype.ext (IsScalarTower.algebraMap_apply K F F' k)
  have : Algebra.IsIntegral (↥F₁) F' := Algebra.IsIntegral.tower_top (R := F)
  set v : Place K F := w.restrict F with hv
  set w₁ : Place K F₁ := w.restrict F₁ with hw₁_def
  have hw₁ : w₁.restrict F = v := restrict_restrict (F := F) (F₁ := ↥F₁) w
  set x₁ : F₁ := ⟨(x : F'), hxα⟩ with hx₁
  have hx₁O : x₁ ∈ w₁.toValuationSubring := by
    change algebraMap (↥F₁) F' x₁ ∈ w.toValuationSubring
    exact x.2
  have hx₁O' := hx₁O
  rw [toValuationSubring_eq_of_restrict_eq hw₁] at hx₁O'
  obtain ⟨c, s, hs, hcs⟩ := hx₁O'
  set α₁ : F₁ := ⟨a, IntermediateField.mem_adjoin_simple_self F a⟩ with hα₁
  have hα₁K : IsIntegral K α₁ := isIntegral_algebraMap_iff.mp haK
  have hgen₁ : IntermediateField.adjoin F ({α₁} : Set F₁) = ⊤ := adjoin_gen_eq_top a
  have hcB : (c : F₁) ∈ Algebra.adjoin v.toValuationSubring ({α₁} : Set F₁) :=
    mem_adjoin_of_isIntegral_valuationSubring v hα₁K hgen₁ c.2
  have hsB : (s : F₁) ∈ Algebra.adjoin v.toValuationSubring ({α₁} : Set F₁) :=
    mem_adjoin_of_isIntegral_valuationSubring v hα₁K hgen₁ s.2
  obtain ⟨hcO, hcA⟩ := residue_mem_adjoin_of_mem_adjoin (K := K) W F₁ α
    (IntermediateField.mem_adjoin_simple_self F a) _ hcB
  obtain ⟨hsO, hsA⟩ := residue_mem_adjoin_of_mem_adjoin (K := K) W F₁ α
    (IntermediateField.mem_adjoin_simple_self F a) _ hsB
  have hsunit₁ : IsUnit (⟨(s : F₁), forall_mem_of_restrict_eq hw₁ s⟩ : w₁.toValuationSubring) := by
    by_contra hns
    exact hs ((mem_center_iff w₁ (forall_mem_of_restrict_eq hw₁)).mpr
      ((IsLocalRing.mem_maximalIdeal _).mpr hns))
  have hsunitW : IsUnit (⟨((s : F₁) : F'), hsO⟩ : W.toValuationSubring) :=
    hsunit₁.map (restrictInclusion (↥F₁) w)
  have hsres : IsLocalRing.residue W.toValuationSubring ⟨((s : F₁) : F'), hsO⟩ ≠ 0 := by
    rw [Ne, IsLocalRing.residue_eq_zero_iff]
    exact fun h => ((IsLocalRing.mem_maximalIdeal _).mp h) hsunitW
  have hs0 : (s : F₁) ≠ 0 := fun h0 => hsunit₁.ne_zero (Subtype.ext h0)
  have hxs : (x₁ : F₁) * (s : F₁) = (c : F₁) := by
    rw [hcs]
    exact inv_mul_cancel_right₀ hs0 _
  have hxsW : x * (⟨((s : F₁) : F'), hsO⟩ : W.toValuationSubring) = ⟨((c : F₁) : F'), hcO⟩ := by
    apply Subtype.ext
    change (x : F') * ((s : F₁) : F') = ((c : F₁) : F')
    rw [← hxs]
    rfl
  have hres : IsLocalRing.residue W.toValuationSubring x *
      IsLocalRing.residue W.toValuationSubring ⟨((s : F₁) : F'), hsO⟩ =
      IsLocalRing.residue W.toValuationSubring ⟨((c : F₁) : F'), hcO⟩ := by
    rw [← map_mul, hxsW]
  have hx_eq : IsLocalRing.residue W.toValuationSubring x =
      IsLocalRing.residue W.toValuationSubring ⟨((c : F₁) : F'), hcO⟩ *
        (IsLocalRing.residue W.toValuationSubring ⟨((s : F₁) : F'), hsO⟩)⁻¹ := by
    rw [← hres, mul_inv_cancel_right₀ hsres]
  rw [hx_eq]
  exact mul_mem hcA (inv_mem hsA)

end Main

end AlgebraicCurve.Place.ResidueCompositumAux

open _root_.AlgebraicCurve
  _root_.AlgebraicCurves.Places.Proofs.PlaceResidueFieldCompositum.AlgebraicCurve in
theorem _root_.AlgebraicCurve.Place.residueField_eq_compositum_of_isConstantFieldExtension
    {K K' F F' : Type*} [Field K] [Field K'] [Field F] [Field F']
    [Algebra K K'] [Algebra K' F'] [Algebra K F'] [IsScalarTower K K' F']
    [Algebra K F] [Algebra F F'] [IsScalarTower K F F']
    [Algebra.IsAlgebraic K K'] [Algebra.IsSeparable K K'] [Algebra.IsIntegral F F']
    (hgen : Algebra.adjoin F (Set.range (algebraMap K' F')) = ⊤)
    (W : Place K' F') :
    IntermediateField.adjoin K' (E := W.ResidueField)
        (Set.range ((W.forgetConstants (K := K)).restrictResidueMap (F := F))) = ⊤ :=
  AlgebraicCurve.Place.ResidueCompositumAux.main hgen W
end AlgebraicCurves.Places.Proofs.PlaceResidueFieldCompositum
end ProofImplementation

open _root_.AlgebraicCurve.Place in
attribute [-instance]
  instIsPrimeCenter
  instIsFractionRingIntegralClosureAt
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  instIsDedekindDomainIntegralClosureAt
  instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
attribute [-simp] AlgebraicCurve.Place.placeOfPrime_toValuationSubring
  AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply
  AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal
