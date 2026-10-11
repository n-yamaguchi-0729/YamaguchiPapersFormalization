/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicCurve_LocalResidue.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Differentials.Uniformizer
import Nyll.AlgebraicCurves.Divisors.Canonical
import Nyll.AlgebraicCurves.Cohomology.Adelic.Index

/-!
# Differentials, residues, and divisor correspondences

Local residue data, traced differential residues, and residue functionals on adeles.
-/

noncomputable section

open IsDedekindDomain WithZero Module IsLocalRing KaehlerDifferential

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

namespace Place

variable (v : Place K F)

/-- A linear local residue map that vanishes on integral functions and computes residues of
simple poles. -/
structure LocalResidueData where
  /-- The local residue map to the residue field. -/
  res : F →ₗ[K] v.ResidueField
  /-- Integral functions have zero local residue. -/
  res_of_mem : ∀ f : F, f ∈ v.toValuationSubring → res f = 0
  /-- For a simple pole, the residue is the reduction of the product with the uniformizer. -/
  res_simplePole : ∀ (f : F) (hf : v.uniformizer * f ∈ v.toValuationSubring),
    res f = IsLocalRing.residue _ ⟨v.uniformizer * f, hf⟩

/-- Local residue data whose higher inverse uniformizer monomials have zero residue. -/
structure CanonicalLocalResidueDataK extends v.LocalResidueData where
  /-- Inverse uniformizer powers of pole order at least two have zero residue. -/
  res_higherPoleMonomial : ∀ (n : ℕ), 1 ≤ n → res (v.uniformizer ^ (n + 1))⁻¹ = 0

end Place

variable (K F) in
/-- Local residue data exists at every place. -/
class HasLocalResidue : Prop where
  /-- Every place admits a local residue map with the prescribed integral and simple-pole
  laws. -/
  exists_data : ∀ v : Place K F, Nonempty v.LocalResidueData

variable (K F) in
/-- Canonical local residue data exists at every place. -/
class HasCanonicalLocalResidueK : Prop where
  /-- Every place admits canonical local residue data. -/
  exists_data : ∀ v : Place K F, Nonempty v.CanonicalLocalResidueDataK

instance (priority := 100) instHasLocalResidue_of_hasCanonicalLocalResidueK
    [HasCanonicalLocalResidueK K F] : HasLocalResidue K F :=
  ⟨fun v => (HasCanonicalLocalResidueK.exists_data v).map (·.toLocalResidueData)⟩

variable (K F) in
/-- A specified family of canonical local residue maps at all places. -/
class HasCanonicalLocalResidueKStar where
  /-- The canonical local residue data chosen for each place. -/
  dataKStar : ∀ v : Place K F, v.CanonicalLocalResidueDataK

instance (priority := 100) instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar
    [HasCanonicalLocalResidueKStar K F] : HasCanonicalLocalResidueK K F :=
  ⟨fun v => ⟨HasCanonicalLocalResidueKStar.dataKStar v⟩⟩

namespace Place

variable (v : Place K F)

private theorem mem_of_ord_nonneg_localResidueAux {f : F} (hf : f ≠ 0) (h : 0 ≤ v.ord f) :
    f ∈ v.toValuationSubring := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  rw [hu, show v.ord f = (((v.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h).symm,
    zpow_natCast]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem (π : v.toValuationSubring).2 _)

/-- The local residue map from the specified canonical residue family. -/
noncomputable def localResidue [HasCanonicalLocalResidueKStar K F] :
    F →ₗ[K] v.ResidueField :=
  (HasCanonicalLocalResidueKStar.dataKStar v).res

theorem localResidue_of_mem [HasCanonicalLocalResidueKStar K F] {f : F}
    (hf : f ∈ v.toValuationSubring) :
    v.localResidue f = 0 :=
  (HasCanonicalLocalResidueKStar.dataKStar v).res_of_mem f hf

theorem localResidue_simplePole [HasCanonicalLocalResidueKStar K F] (f : F)
    (hf : v.uniformizer * f ∈ v.toValuationSubring) :
    v.localResidue f = IsLocalRing.residue _ ⟨v.uniformizer * f, hf⟩ :=
  (HasCanonicalLocalResidueKStar.dataKStar v).res_simplePole f hf

theorem localResidue_higherPoleMonomial [HasCanonicalLocalResidueKStar K F]
    (n : ℕ) (hn : 1 ≤ n) :
    v.localResidue (v.uniformizer ^ (n + 1))⁻¹ = 0 :=
  (HasCanonicalLocalResidueKStar.dataKStar v).res_higherPoleMonomial n hn

theorem localResidue_eq_zero_of_ord_nonneg [HasCanonicalLocalResidueKStar K F] {f : F}
    (hf : f = 0 ∨ 0 ≤ v.ord f) : v.localResidue f = 0 := by
  rcases hf with rfl | hf
  · exact map_zero _
  · rcases eq_or_ne f 0 with rfl | hf0
    · exact map_zero _
    · exact v.localResidue_of_mem (v.mem_of_ord_nonneg_localResidueAux hf0 hf)

theorem gate_localResidue_uniformizer_inv [HasCanonicalLocalResidueKStar K F] :
    v.localResidue v.uniformizer⁻¹ = 1 := by
  have hmem : v.uniformizer * v.uniformizer⁻¹ ∈ v.toValuationSubring := by
    rw [mul_inv_cancel₀ v.uniformizer_ne_zero]; exact one_mem _
  rw [v.localResidue_simplePole _ hmem]
  have h1 : (⟨v.uniformizer * v.uniformizer⁻¹, hmem⟩ : v.toValuationSubring) = 1 :=
    Subtype.ext (mul_inv_cancel₀ v.uniformizer_ne_zero)
  rw [h1, map_one]

end Place

variable [HasCanonicalLocalResidueKStar K F]

/-- The base-field trace of the local residue of the function times the differential
coefficient. -/
def kaehlerResidueTerm (ω : Ω[F⁄K]) (α : Place K F → F) (v : Place K F) : K :=
  Algebra.trace K v.ResidueField (v.localResidue (α v * v.differentialCoeff ω))

theorem kaehlerResidueTerm_eq_zero_of_ord_nonneg {ω : Ω[F⁄K]} {α : Place K F → F}
    {v : Place K F} (h : α v * v.differentialCoeff ω = 0 ∨
      0 ≤ v.ord (α v * v.differentialCoeff ω)) :
    kaehlerResidueTerm ω α v = 0 := by
  unfold kaehlerResidueTerm
  rw [v.localResidue_eq_zero_of_ord_nonneg h, map_zero]

omit [HasCanonicalLocalResidueKStar K F] in
theorem Place.differentialCoeff_ne_zero (v : Place K F) [v.DCoordGenerates]
    {ω : Ω[F⁄K]} (hω : ω ≠ 0) : v.differentialCoeff ω ≠ 0 := fun h =>
  hω (by rw [← v.differentialCoeff_smul_dCoord ω, h, zero_smul])

namespace Place

omit [HasCanonicalLocalResidueKStar K F] in
theorem LocalResidueData.res_eq_zero_of_ord_nonneg {v : Place K F} (R : v.LocalResidueData)
    {f : F} (hf : f = 0 ∨ 0 ≤ v.ord f) : R.res f = 0 := by
  rcases hf with rfl | hf
  · exact map_zero _
  · rcases eq_or_ne f 0 with rfl | hf0
    · exact map_zero _
    · exact R.res_of_mem f (v.mem_of_ord_nonneg_localResidueAux hf0 hf)

omit [HasCanonicalLocalResidueKStar K F] in
theorem CanonicalLocalResidueDataK.res_eq_zero_of_ord_nonneg {v : Place K F}
    (R : v.CanonicalLocalResidueDataK) {f : F} (hf : f = 0 ∨ 0 ≤ v.ord f) : R.res f = 0 :=
  R.toLocalResidueData.res_eq_zero_of_ord_nonneg hf

end Place

section Single

open scoped Classical in
omit [HasCanonicalLocalResidueKStar K F] in
theorem single_mem_adeleBdd (v : Place K F) (g : F) (D : Divisor K F)
    (hg : v.adicValuation g ≤ WithZero.exp (D v)) :
    Pi.single v g ∈ adeleBdd D := by
  intro w
  rcases eq_or_ne w v with rfl | hw
  · simpa only [Pi.single_eq_same] using hg
  · rw [Pi.single_eq_of_ne hw, Valuation.map_zero]; exact zero_le

open scoped Classical in
omit [HasCanonicalLocalResidueKStar K F] in
theorem single_mem_adeleSpace (v : Place K F) (g : F) :
    Pi.single v g ∈ adeleSpace K F := by
  rcases eq_or_ne g 0 with rfl | hg
  · simpa only [Pi.single_zero] using (adeleSpace K F).zero_mem
  · refine adeleBdd_le_adeleSpace
      (single_mem_adeleBdd v g (Finsupp.single v (-v.ord g)) ?_)
    rw [v.adicValuation_eq_exp_neg_ord hg, Finsupp.single_eq_same]

open scoped Classical in
/-- The adele supported at the specified place with the specified function value. -/
def adeleSingle (v : Place K F) (g : F) : adeleSpace K F :=
  ⟨Pi.single v g, single_mem_adeleSpace v g⟩

open scoped Classical in
omit [HasCanonicalLocalResidueKStar K F] in
@[simp]
theorem adeleSingle_coe (v : Place K F) (g : F) :
    (adeleSingle v g : Place K F → F) = Pi.single v g := rfl

end Single

variable (K F) in
/-- The residue-field trace to the base field is nonzero at every place. -/
class HasSeparableResidue : Prop where
  /-- Every residue-field trace is a nonzero linear map. -/
  trace_ne_zero : ∀ v : Place K F, (Algebra.trace K v.ResidueField : _ →ₗ[K] K) ≠ 0

section CanonicalKResidueTerm

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]

/-- The traced residue of a function times the differential coefficient, using explicit
local residue data. -/
def Place.kaehlerResidueTermK (v : Place K F) (R : v.CanonicalLocalResidueDataK)
    (ω : Ω[F⁄K]) (f : F) : K :=
  Algebra.trace K v.ResidueField (R.res (f * v.differentialCoeff ω))

/-- The traced residue term using an explicit family of local residue data. -/
def kaehlerResidueTermKFam (Rfam : ∀ v : Place K F, v.CanonicalLocalResidueDataK)
    (ω : Ω[F⁄K]) (α : Place K F → F) (v : Place K F) : K :=
  v.kaehlerResidueTermK (Rfam v) ω (α v)

omit [HasCanonicalLocalResidueKStar K F] in
@[simp]
theorem kaehlerResidueTermKFam_apply (Rfam : ∀ v : Place K F, v.CanonicalLocalResidueDataK)
    (ω : Ω[F⁄K]) (α : Place K F → F) (v : Place K F) :
    kaehlerResidueTermKFam Rfam ω α v
      = Algebra.trace K v.ResidueField ((Rfam v).res (α v * v.differentialCoeff ω)) := rfl

omit [HasCanonicalLocalResidueKStar K F] in
theorem kaehlerResidueTermKFam_eq_zero_of_ord_nonneg
    (Rfam : ∀ v : Place K F, v.CanonicalLocalResidueDataK) {ω : Ω[F⁄K]}
    {α : Place K F → F} {v : Place K F}
    (h : α v * v.differentialCoeff ω = 0 ∨ 0 ≤ v.ord (α v * v.differentialCoeff ω)) :
    kaehlerResidueTermKFam Rfam ω α v = 0 := by
  rw [kaehlerResidueTermKFam_apply, (Rfam v).res_eq_zero_of_ord_nonneg h, map_zero]

section SupportMachinery

variable [HasCanonicalDivisor (K := K) (F := F)] [∀ v : Place K F, v.DCoordGenerates]

omit [HasCanonicalLocalResidueKStar K F] in
theorem kaehlerResidueTermKFam_eq_zero_of_adeleBdd_canonical
    (Rfam : ∀ v : Place K F, v.CanonicalLocalResidueDataK) {ω : Ω[F⁄K]} (hω : ω ≠ 0)
    {α : Place K F → F} (hα : α ∈ adeleBdd (canonicalDivisorOf hω)) (v : Place K F) :
    kaehlerResidueTermKFam Rfam ω α v = 0 := by
  refine kaehlerResidueTermKFam_eq_zero_of_ord_nonneg Rfam ?_
  rcases eq_or_ne (α v) 0 with h0 | h0
  · exact Or.inl (by rw [h0, zero_mul])
  · refine Or.inr ?_
    have hg := v.differentialCoeff_ne_zero hω
    rw [v.ord_mul h0 hg]
    have hαv : -(canonicalDivisorOf hω v) ≤ v.ord (α v) := by
      have hval := hα v
      rw [v.adicValuation_eq_exp_neg_ord h0] at hval
      exact neg_le_of_neg_le (WithZero.exp_le_exp.mp hval)
    rw [canonicalDivisorOf_apply hω v, Place.ordDifferential] at hαv
    linarith

omit [HasCanonicalLocalResidueKStar K F] in
theorem kaehlerResidueTermKFam_support_subset
    (Rfam : ∀ v : Place K F, v.CanonicalLocalResidueDataK) {ω : Ω[F⁄K]} (hω : ω ≠ 0)
    {D : Divisor K F} {α : Place K F → F} (hα : α ∈ adeleBdd D) :
    Function.support (kaehlerResidueTermKFam Rfam ω α)
      ⊆ ↑(D - canonicalDivisorOf hω).support := by
  intro v hv
  rw [Finset.mem_coe, Finsupp.mem_support_iff, Finsupp.sub_apply, ne_eq, sub_eq_zero]
  intro hDω
  apply hv
  refine kaehlerResidueTermKFam_eq_zero_of_ord_nonneg Rfam ?_
  rcases eq_or_ne (α v) 0 with h0 | h0
  · exact Or.inl (by rw [h0, zero_mul])
  · refine Or.inr ?_
    have hg := v.differentialCoeff_ne_zero hω
    rw [v.ord_mul h0 hg]
    have hαv : -(D v) ≤ v.ord (α v) := by
      have hval := hα v
      rw [v.adicValuation_eq_exp_neg_ord h0] at hval
      exact neg_le_of_neg_le (WithZero.exp_le_exp.mp hval)
    rw [hDω, canonicalDivisorOf_apply hω v, Place.ordDifferential] at hαv
    linarith

omit [HasCanonicalLocalResidueKStar K F] in
theorem kaehlerResidueTermKFam_support_finite
    (Rfam : ∀ v : Place K F, v.CanonicalLocalResidueDataK) {ω : Ω[F⁄K]} (hω : ω ≠ 0)
    {D : Divisor K F} {α : Place K F → F} (hα : α ∈ adeleBdd D) :
    (Function.support (kaehlerResidueTermKFam Rfam ω α)).Finite :=
  Set.Finite.subset (Finset.finite_toSet _)
    (kaehlerResidueTermKFam_support_subset Rfam hω hα)

omit [HasCanonicalLocalResidueKStar K F] in
theorem kaehlerResidueTermKFam_support_finite_of_adeleSpace
    (Rfam : ∀ v : Place K F, v.CanonicalLocalResidueDataK) {ω : Ω[F⁄K]} (hω : ω ≠ 0)
    {α : Place K F → F} (hα : α ∈ adeleSpace K F) :
    (Function.support (kaehlerResidueTermKFam Rfam ω α)).Finite := by
  obtain ⟨D, hD⟩ := mem_adeleSpace_iff.mp hα
  exact kaehlerResidueTermKFam_support_finite Rfam hω hD

/-- The adele linear functional obtained by summing residue terms from an explicit canonical
residue family. -/
def weilOfKaehlerK (Rfam : ∀ v : Place K F, v.CanonicalLocalResidueDataK)
    {ω : Ω[F⁄K]} (hω : ω ≠ 0) : Module.Dual K (adeleSpace K F) where
  toFun α := ∑ᶠ v, kaehlerResidueTermKFam Rfam ω (α : Place K F → F) v
  map_add' α β := by
    have hsupα := kaehlerResidueTermKFam_support_finite_of_adeleSpace Rfam hω α.2
    have hsupβ := kaehlerResidueTermKFam_support_finite_of_adeleSpace Rfam hω β.2
    rw [← finsum_add_distrib hsupα hsupβ]
    refine finsum_congr fun v => ?_
    simp only [kaehlerResidueTermKFam_apply]
    rw [Submodule.coe_add, Pi.add_apply, add_mul, map_add, map_add]
  map_smul' c α := by
    simp only [RingHom.id_apply]
    rw [smul_finsum]
    refine finsum_congr fun v => ?_
    simp only [kaehlerResidueTermKFam_apply]
    rw [Submodule.coe_smul, Pi.smul_apply, Algebra.smul_def, mul_assoc,
      ← Algebra.smul_def, map_smul, map_smul]

omit [HasCanonicalLocalResidueKStar K F] in
theorem weilOfKaehlerK_apply (Rfam : ∀ v : Place K F, v.CanonicalLocalResidueDataK)
    {ω : Ω[F⁄K]} (hω : ω ≠ 0) (α : adeleSpace K F) :
    weilOfKaehlerK Rfam hω α
      = ∑ᶠ v, kaehlerResidueTermKFam Rfam ω (α : Place K F → F) v := rfl

omit [HasCanonicalLocalResidueKStar K F] in
theorem weilOfKaehlerK_vanish_adeleBdd_canonical
    (Rfam : ∀ v : Place K F, v.CanonicalLocalResidueDataK) {ω : Ω[F⁄K]} (hω : ω ≠ 0)
    {α : adeleSpace K F} (hα : (α : Place K F → F) ∈ adeleBdd (canonicalDivisorOf hω)) :
    weilOfKaehlerK Rfam hω α = 0 := by
  rw [weilOfKaehlerK_apply]
  exact finsum_eq_zero_of_forall_eq_zero
    (kaehlerResidueTermKFam_eq_zero_of_adeleBdd_canonical Rfam hω hα)

variable (K F)

/-- Every explicit canonical residue family gives a differential residue functional that
vanishes on diagonal functions. -/
def ResidueTheoremK : Prop :=
  ∀ (Rfam : ∀ v : Place K F, v.CanonicalLocalResidueDataK) [HasPrincipalDivisors K F]
    {ω : Ω[F⁄K]} (hω : ω ≠ 0) (f : F),
    weilOfKaehlerK Rfam hω ⟨diagonalHom K F f, diagonal_mem_adeleSpace f⟩ = 0

end SupportMachinery

end CanonicalKResidueTerm

end AlgebraicCurve

end
