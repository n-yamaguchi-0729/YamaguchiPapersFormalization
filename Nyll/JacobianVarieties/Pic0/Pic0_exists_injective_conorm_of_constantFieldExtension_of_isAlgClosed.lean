/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Pic0_exists_injective_conorm_of_constantFieldExtension_of_isAlgClosed.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Divisors.ClassGroup
import Nyll.AlgebraicCurves.FunctionFields.CurveOver
import Nyll.AlgebraicCurves.Cohomology.Adelic.Repartitions
import Nyll.AlgebraicCurves.Cohomology.Adelic.Index
import Nyll.AlgebraicCurves.Places.Place_exists_comap_algebraMap_eq_of_constantFieldExtension_of_isAlgClosed
import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.LSpace_mapDomain_subset_span_image_lSpace_of_constantFieldExtension_of_isAlgClosed
import Nyll.AlgebraicCurves.Valuations.ValuationSubring_isPrincipalIdealRing_of_finiteDimensional_adjoin

/-!
# Injectivity of conorm under algebraically closed constant extension

Lifts places uniquely, extends divisors, and descends principal divisors through the
corresponding spaces of rational functions to obtain an injective map on Picard groups.
-/

section ProofImplementation

namespace JacobianVarieties.Pic0.Proofs.ConormInjectivity
attribute [-instance]
  AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
attribute [-simp]
  AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint

noncomputable section

open _root_.AlgebraicCurve

namespace AlgebraicCurve
open _root_.AlgebraicCurve
namespace ConDesc
open _root_.AlgebraicCurve

variable {K F K' F' : Type*}
  [Field K] [Field F] [Field K'] [Field F'] [Algebra K F] [Algebra K' F']
  [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F']

omit [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F']
  [Field K] [Algebra K F] [Field F] in
theorem ord_eq_zero_of_mem_of_inv_mem {L E : Type*} [Field L] [Field E] [Algebra L E]
    (w : Place L E) {x : E} (hx : x ∈ w.toValuationSubring) (hx' : x⁻¹ ∈ w.toValuationSubring)
    (hx0 : x ≠ 0) : w.ord x = 0 := by
  have h1 := (w.adicValuation_le_one_iff).1 (w.adicValuation_le_one_of_mem hx)
  have h2 := (w.adicValuation_le_one_iff).1 (w.adicValuation_le_one_of_mem hx')
  rcases h1 with h1 | h1
  · exact absurd h1 hx0
  rcases h2 with h2 | h2
  · exact absurd h2 (inv_ne_zero hx0)
  rw [w.ord_inv] at h2
  omega

theorem mem_of_forall_comap_ne
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (v' : Place K' F')
    (hv' : ∀ v : Place K F, v'.toValuationSubring.comap (algebraMap F F') ≠ v.toValuationSubring)
    (f : F) : algebraMap F F' f ∈ v'.toValuationSubring := by
  classical
  obtain ⟨x, -, hxfin⟩ := hfg
  set O : ValuationSubring F := v'.toValuationSubring.comap (algebraMap F F') with hO
  have hK : ∀ a : K, algebraMap K F a ∈ O := by
    intro a
    change algebraMap F F' (algebraMap K F a) ∈ v'.toValuationSubring
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply K K' F']
    exact v'.algebraMap_mem' _
  by_cases htop : O = ⊤
  · have : f ∈ O := by rw [htop]; exact Subring.mem_top f
    exact this
  · have := hxfin
    have hPIR : IsPrincipalIdealRing O :=
      ValuationSubring.isPrincipalIdealRing_of_finiteDimensional_adjoin (K := K) x O hK htop
    exact absurd rfl (hv' ⟨O, hK, htop, hPIR⟩)

theorem ord_eq_zero_of_forall_comap_ne
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (v' : Place K' F')
    (hv' : ∀ v : Place K F, v'.toValuationSubring.comap (algebraMap F F') ≠ v.toValuationSubring)
    {f : F} (hf : f ≠ 0) : v'.ord (algebraMap F F' f) = 0 := by
  refine ord_eq_zero_of_mem_of_inv_mem v' (mem_of_forall_comap_ne hfg v' hv' f) ?_
    ((map_ne_zero _).2 hf)
  rw [← map_inv₀]
  exact mem_of_forall_comap_ne hfg v' hv' f⁻¹

section Lift

variable [IsAlgClosed K] [IsCurveOver K F]
  (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
  (hfg' : ∃ x : F', Transcendental K' x ∧
    FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
  (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤)

/-- The unique place above the given place under this constant-field extension. -/
def lift (P : Place K F) : Place K' F' :=
  Classical.choose
    (Place.exists_comap_algebraMap_eq_of_constantFieldExtension_of_isAlgClosed
      K F K' F' hfg hfg' hgen P)

theorem lift_spec (P : Place K F) :
    (lift hfg hfg' hgen P).toValuationSubring.comap (algebraMap F F') = P.toValuationSubring ∧
      (∀ f : F, (lift hfg hfg' hgen P).ord (algebraMap F F' f) = P.ord f) ∧
      ∀ Q' : Place K' F',
        Q'.toValuationSubring.comap (algebraMap F F') = P.toValuationSubring →
          Q' = lift hfg hfg' hgen P :=
  Classical.choose_spec
    (Place.exists_comap_algebraMap_eq_of_constantFieldExtension_of_isAlgClosed
      K F K' F' hfg hfg' hgen P)

theorem comap_lift (P : Place K F) :
    (lift hfg hfg' hgen P).toValuationSubring.comap (algebraMap F F') = P.toValuationSubring :=
  (lift_spec hfg hfg' hgen P).1

theorem ord_lift (P : Place K F) (f : F) :
    (lift hfg hfg' hgen P).ord (algebraMap F F' f) = P.ord f :=
  (lift_spec hfg hfg' hgen P).2.1 f

theorem eq_lift_of_comap_eq {P : Place K F} {Q' : Place K' F'}
    (h : Q'.toValuationSubring.comap (algebraMap F F') = P.toValuationSubring) :
    Q' = lift hfg hfg' hgen P :=
  (lift_spec hfg hfg' hgen P).2.2 Q' h

theorem lift_injective : Function.Injective (lift (K' := K') (F' := F') hfg hfg' hgen) := by
  intro P Q hPQ
  apply Place.ext
  rw [← comap_lift hfg hfg' hgen P, ← comap_lift hfg hfg' hgen Q, hPQ]

theorem lift_new (v' : Place K' F') (hv' : ∀ v, lift hfg hfg' hgen v ≠ v') (v : Place K F) :
    v'.toValuationSubring.comap (algebraMap F F') ≠ v.toValuationSubring :=
  fun h => hv' v (eq_lift_of_comap_eq hfg hfg' hgen h).symm

theorem exists_lift_eq_of_comap_eq {v' : Place K' F'} {v : Place K F}
    (h : v'.toValuationSubring.comap (algebraMap F F') = v.toValuationSubring) :
    lift hfg hfg' hgen v = v' :=
  (eq_lift_of_comap_eq hfg hfg' hgen h).symm

/-- The divisor obtained by sending each place to its unique lift. -/
def con (D : Divisor K F) : Divisor K' F' := Finsupp.mapDomain (lift hfg hfg' hgen) D

theorem con_apply_lift (D : Divisor K F) (v : Place K F) :
    con hfg hfg' hgen D (lift hfg hfg' hgen v) = D v :=
  Finsupp.mapDomain_apply_of_injective (lift_injective hfg hfg' hgen) D v

theorem con_apply_of_forall_ne (D : Divisor K F) (v' : Place K' F')
    (hv' : ∀ v, lift hfg hfg' hgen v ≠ v') : con hfg hfg' hgen D v' = 0 :=
  Finsupp.mapDomain_of_notMem_range D v' (by rintro ⟨v, hv⟩; exact hv' v hv)

theorem eq_con {D : Divisor K F} {D' : Divisor K' F'}
    (hD'over : ∀ (v' : Place K' F') (v : Place K F),
      v'.toValuationSubring.comap (algebraMap F F') = v.toValuationSubring → D' v' = D v)
    (hD'off : ∀ v' : Place K' F',
      (∀ v : Place K F, v'.toValuationSubring.comap (algebraMap F F') ≠ v.toValuationSubring) →
        D' v' = 0) :
    D' = con hfg hfg' hgen D := by
  ext v'
  by_cases h : ∃ v, lift hfg hfg' hgen v = v'
  · obtain ⟨v, rfl⟩ := h
    rw [con_apply_lift, hD'over _ v (comap_lift hfg hfg' hgen v)]
  · push Not at h
    rw [con_apply_of_forall_ne hfg hfg' hgen D v' h, hD'off v' (lift_new hfg hfg' hgen v' h)]

/-- The additive conorm map induced by the unique lifts of places. -/
def conHom : Divisor K F →+ Divisor K' F' := Finsupp.mapDomain.addMonoidHom (lift hfg hfg' hgen)

theorem conHom_apply (D : Divisor K F) : conHom hfg hfg' hgen D = con hfg hfg' hgen D := rfl

theorem isPrincipal_con {D : Divisor K F} (hD : D.IsPrincipal) :
    (con hfg hfg' hgen D).IsPrincipal := by
  obtain ⟨f, hf, hDf⟩ := hD
  refine ⟨algebraMap F F' f, (map_ne_zero _).2 hf, fun v' => ?_⟩
  by_cases h : ∃ v, lift hfg hfg' hgen v = v'
  · obtain ⟨v, rfl⟩ := h
    rw [con_apply_lift, ord_lift, hDf v]
  · push Not at h
    rw [con_apply_of_forall_ne hfg hfg' hgen D v' h,
      ord_eq_zero_of_forall_comap_ne hfg v' (lift_new hfg hfg' hgen v' h) hf]

variable [IsAlgClosed K'] [IsCurveOver K' F']

omit [IsAlgClosed K] [IsCurveOver K F] in
theorem degree_eq_sum {L E : Type*} [Field L] [Field E] [Algebra L E] [IsAlgClosed L]
    [IsCurveOver L E]
    (D : Divisor L E) : Divisor.degree D = D.sum fun _ n => n := by
  unfold Divisor.degree
  rw [Finsupp.liftAddHom_apply]
  refine Finsupp.sum_congr fun v _ => ?_
  rw [AddMonoidHom.mulRight_apply, IsCurveOver.deg_eq_one_of_isAlgClosed v, Nat.cast_one, mul_one]

theorem degree_con (D : Divisor K F) : Divisor.degree (con hfg hfg' hgen D) = Divisor.degree D := by
  rw [degree_eq_sum, degree_eq_sum, con,
    Finsupp.sum_mapDomain_index_inj (lift_injective hfg hfg' hgen)]

omit [IsAlgClosed K'] [IsAlgClosed K] [IsCurveOver K F] in
theorem degree_eq_zero_of_isPrincipal {L E : Type*} [Field L] [Field E] [Algebra L E]
    [HasPrincipalDivisors L E] {D : Divisor L E} (hD : D.IsPrincipal) : Divisor.degree D = 0 := by
  obtain ⟨f, hf, hDf⟩ := hD
  obtain ⟨E₀, hE₀, hdeg⟩ := HasPrincipalDivisors.exists_divisor (K := L) f hf
  have : D = E₀ := Finsupp.ext fun v => (hDf v).trans (hE₀ v).symm
  rw [this, hdeg]

theorem isPrincipal_of_isPrincipal_con {D : Divisor K F} (hD : (con hfg hfg' hgen D).IsPrincipal) :
    D.IsPrincipal := by
  classical
  obtain ⟨f', hf', hDf'⟩ := hD
  have hg' : f'⁻¹ ∈ LSpace (K := K') (Finsupp.mapDomain (lift hfg hfg' hgen) D) := by
    rw [mem_lSpace_iff_ord]
    refine Or.inr fun v' => ?_
    rw [Place.ord_inv, ← hDf' v']
    rfl
  have hspan := lSpace_mapDomain_subset_span_image_lSpace_of_constantFieldExtension_of_isAlgClosed
    K F K' F' hfg hfg' hgen (lift hfg hfg' hgen) (ord_lift hfg hfg' hgen)
    (lift_injective hfg hfg' hgen) (lift_new hfg hfg' hgen) D hg'
  have hne : ∃ g : F, g ∈ LSpace (K := K) D ∧ g ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hzero : ((algebraMap F F') '' (LSpace (K := K) D : Set F)) ⊆ {0} := by
      rintro _ ⟨g, hg, rfl⟩
      rw [Set.mem_singleton_iff, hcon g hg, map_zero]
    have : f'⁻¹ ∈ Submodule.span K' ({0} : Set F') := Submodule.span_mono hzero hspan
    rw [Submodule.span_zero_singleton, Submodule.mem_bot] at this
    exact inv_ne_zero hf' this
  obtain ⟨g, hg, hg0⟩ := hne
  obtain ⟨Dg, hDg, hDgdeg⟩ := HasPrincipalDivisors.exists_divisor (K := K) g hg0
  have hgord : ∀ v : Place K F, -D v ≤ v.ord g := by
    have := (mem_lSpace_iff_ord (K := K)).1 hg
    exact this.resolve_left hg0
  have hEnonneg : ∀ v, 0 ≤ (D + Dg) v := fun v => by
    rw [Finsupp.add_apply, hDg v]; linarith [hgord v]
  have hDdeg : Divisor.degree D = 0 := by
    rw [← degree_con hfg hfg' hgen D]
    exact degree_eq_zero_of_isPrincipal ⟨f', hf', hDf'⟩
  have hEdeg : Divisor.degree (D + Dg) = 0 := by rw [map_add, hDdeg, hDgdeg, add_zero]
  have hE : D + Dg = 0 := by
    rw [degree_eq_sum] at hEdeg
    ext v
    have hle : (D + Dg) v ≤ (D + Dg).sum fun _ n => n := by
      by_cases hv : v ∈ (D + Dg).support
      · exact Finset.single_le_sum (f := fun w => (D + Dg) w) (fun w _ => hEnonneg w) hv
      · rw [Finsupp.notMem_support_iff.1 hv]
        exact Finset.sum_nonneg fun w _ => hEnonneg w
    rw [hEdeg] at hle
    exact le_antisymm hle (hEnonneg v)
  refine ⟨g⁻¹, inv_ne_zero hg0, fun v => ?_⟩
  have := congrArg (fun E : Divisor K F => E v) hE
  simp only [Finsupp.add_apply, Finsupp.coe_zero, Pi.zero_apply] at this
  rw [Place.ord_inv, ← hDg v]
  linarith

/-- The conorm map restricted to divisors of degree zero. -/
def conDegZero : Divisor.degZero (K := K) (F := F) →+ Divisor.degZero (K := K') (F := F') :=
  ((conHom hfg hfg' hgen).comp (Divisor.degZero (K := K) (F := F)).subtype).codRestrict _
    (fun D => by
      rw [Divisor.mem_degZero, AddMonoidHom.comp_apply, conHom_apply, AddSubgroup.coe_subtype,
        degree_con]
      exact D.2)

theorem coe_conDegZero (D : Divisor.degZero (K := K) (F := F)) :
    (conDegZero hfg hfg' hgen D : Divisor K' F') = con hfg hfg' hgen (D : Divisor K F) := rfl

/-- The conorm homomorphism on degree-zero divisor classes. -/
def conPic0 : Pic0 K F →+ Pic0 K' F' :=
  QuotientAddGroup.map _ _ (conDegZero hfg hfg' hgen) (by
    rintro ⟨D, hD0⟩ hD
    simp only [AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_comap] at hD ⊢
    exact isPrincipal_con hfg hfg' hgen hD)

theorem conPic0_mk (D : Divisor.degZero (K := K) (F := F)) :
    conPic0 hfg hfg' hgen (Pic0.mk D) = Pic0.mk (conDegZero hfg hfg' hgen D) := rfl

theorem conPic0_injective : Function.Injective (conPic0 hfg hfg' hgen) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective x
  rw [conPic0_mk] at hx
  have hprin : (con hfg hfg' hgen (D : Divisor K F)).IsPrincipal := by
    have := (QuotientAddGroup.eq_zero_iff _).mp hx
    rw [AddSubgroup.mem_addSubgroupOf] at this
    exact this
  have hD : (D : Divisor K F).IsPrincipal := isPrincipal_of_isPrincipal_con hfg hfg' hgen hprin
  change (QuotientAddGroup.mk D : Pic0 K F) = 0
  rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
  exact hD

end Lift

end AlgebraicCurve.ConDesc

open _root_.AlgebraicCurve
  _root_.JacobianVarieties.Pic0.Proofs.ConormInjectivity.AlgebraicCurve
  AlgebraicCurve.ConDesc in
theorem _root_.AlgebraicCurve.Pic0.exists_injective_conorm_of_constantFieldExtension_of_isAlgClosed
    (K F K' F' : Type*)
    [Field K] [Field F] [Field K'] [Field F'] [Algebra K F] [Algebra K' F']
    [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F']
    [IsAlgClosed K] [IsAlgClosed K']
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfg' : ∃ x : F', Transcendental K' x ∧
      FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
    [IsCurveOver K F] [IsCurveOver K' F']
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤) :
    ∃ ι : Pic0 K F →+ Pic0 K' F', Function.Injective ι ∧
      ∀ (D : Divisor.degZero (K := K) (F := F)) (D' : Divisor.degZero (K := K') (F := F')),
        (∀ (v' : Place K' F') (v : Place K F),
          v'.toValuationSubring.comap (algebraMap F F') = v.toValuationSubring →
            (D' : Divisor K' F') v' = (D : Divisor K F) v) →
        (∀ v' : Place K' F',
          (∀ v : Place K F, v'.toValuationSubring.comap (algebraMap F F') ≠ v.toValuationSubring) →
            (D' : Divisor K' F') v' = 0) →
        ι (Pic0.mk D) = Pic0.mk D' := by
  refine ⟨conPic0 hfg hfg' hgen, conPic0_injective hfg hfg' hgen, fun D D' hover hoff => ?_⟩
  rw [conPic0_mk]
  congr 1
  apply Subtype.ext
  rw [coe_conDegZero]
  exact (eq_con hfg hfg' hgen hover hoff).symm

end
end JacobianVarieties.Pic0.Proofs.ConormInjectivity
end ProofImplementation

attribute [-simp]
  AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd
  AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply
  AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one
  AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint
