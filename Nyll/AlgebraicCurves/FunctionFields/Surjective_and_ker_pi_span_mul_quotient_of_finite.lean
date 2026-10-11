/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_surjective_and_ker_pi_span_mul_quotient_of_finite.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Models.Basic
import Nyll.AlgebraicCurves.FunctionFields.CurveOver
import Nyll.AlgebraicCurves.Cohomology.Cech.DivisorSections
import Nyll.SchemeTheory.Cohomology.Cech.TwoAffineOpenCover
import Nyll.AlgebraicCurves.Foundations.CommutativeAlgebra.IsLocalization_AtPrime_surjective_and_ker_pi_span_mul_quotient_of_moduleFinite
import Nyll.AlgebraicCurves.Geometry.Schemes.Scheme_Opens_range_algebraMap_functionField_eq_iInf

/-!
# Surjective and ker pi span mul quotient of finite
-/

section ProofImplementation

namespace AlgebraicCurves.FunctionFields.Proofs.Surjective_and_ker_pi_span_mul_quotient_of_finite

universe u

open CategoryTheory AlgebraicGeometry AlgebraicCurve
open scoped Pointwise

theorem _root_.AlgebraicCurve.surjective_and_ker_pi_span_mul_quotient_of_finite
    (k : Type u) [Field k] [IsAlgClosed k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
    [IsIntegral C] [IsProper c]
    (hpts : ∀ z : C, z = genericPoint C ∨ IsClosed ({z} : Set C))
    (U : C.Opens) [Nonempty U] (hUaff : IsAffineOpen U) (hU : genericPoint C ∈ U)
    (B : Subalgebra Γ(C, U) C.functionField) (hB : Module.Finite Γ(C, U) B) :
    letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
    let Bz : C → Submodule k C.functionField := fun z =>
      Submodule.span k ((B : Set C.functionField) * Set.range (algebraMap (C.presheaf.stalk z)
        C.functionField))
    let Q : C → Type u := fun z =>
      ↥(Bz z) ⧸ (Submodule.span k (Set.range (algebraMap (C.presheaf.stalk z)
        C.functionField))).comap (Bz z).subtype
    let φ : ↥(Submodule.span k (B : Set C.functionField)) →ₗ[k]
        ((z : {z : C // z ∈ U ∧ IsClosed ({z} : Set C)}) → Q z.1) :=
      LinearMap.pi fun z =>
        (Submodule.mkQ ((Submodule.span k
          (Set.range (algebraMap (C.presheaf.stalk z.1) C.functionField))).comap
          (Bz z.1).subtype)).comp (Submodule.inclusion (Submodule.span_mono
        (fun b hb => Set.mem_mul.mpr ⟨b, hb, 1, ⟨1, map_one _⟩, mul_one b⟩)))
    Function.Surjective φ ∧
      LinearMap.ker φ = (Submodule.span k (Set.range (C.presheaf.germ U (genericPoint C)
        hU).hom)).comap
        (Submodule.span k (B : Set C.functionField)).subtype ∧
      {z : {z : C // z ∈ U ∧ IsClosed ({z} : Set C)} | Nontrivial (Q z.1)}.Finite ∧
      ∀ z : {z : C // z ∈ U ∧ IsClosed ({z} : Set C)}, FiniteDimensional k (Q z.1) := by
  classical
  let hkK : Algebra k C.functionField := (AlgebraicCurve.baseToFunctionField c).toAlgebra
  intro Bz Q φ
  have hη : genericPoint C ∈ (⊤ : C.Opens) := trivial
  let hkA : Algebra k Γ(C, U) := ((c.appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (.of
    k)).inv.hom).toAlgebra
  have hst : IsScalarTower k Γ(C, U) C.functionField :=
    IsScalarTower.of_algebraMap_eq fun a => by
      change (C.presheaf.germ ⊤ (genericPoint C) hη).hom (c.appTop.hom ((Scheme.ΓSpecIso (.of
        k)).inv.hom a)) =
        (C.presheaf.germ U (genericPoint C) _).hom ((c.appLE ⊤ U le_top).hom ((Scheme.ΓSpecIso
          (.of k)).inv.hom a))
      simp only [Scheme.Hom.appLE, CommRingCat.hom_comp, RingHom.comp_apply,
        TopCat.Presheaf.germ_res_apply, Scheme.Hom.appTop]
      rfl
  have hft : (c.appLE ⊤ U le_top).hom.FiniteType :=
    HasRingHomProperty.appLE @LocallyOfFiniteType c inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨U,
      hUaff⟩ le_top
  have hFT : Algebra.FiniteType k Γ(C, U) := by
    rw [← RingHom.finiteType_algebraMap]
    change ((c.appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom).FiniteType
    exact hft.comp (RingHom.FiniteType.of_surjective _ (Scheme.ΓSpecIso (.of
      k)).commRingCatIsoToRingEquiv.symm.surjective)
  have hnoeth : IsNoetherianRing Γ(C, U) := Algebra.FiniteType.isNoetherianRing k Γ(C, U)
  have hfrac : IsFractionRing Γ(C, U) C.functionField :=
    functionField_isFractionRing_of_isAffineOpen C U hUaff
  have hres : ∀ m : Ideal Γ(C, U), m.IsMaximal → Function.Surjective (algebraMap k (Γ(C, U) ⧸ m))
    := by
    intro m hm
    have hmax := hm
    let hfield : Field (Γ(C, U) ⧸ m) := Ideal.Quotient.field m
    have hfiniteType : Algebra.FiniteType k (Γ(C, U) ⧸ m) :=
      Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k m) (Ideal.Quotient.mkₐ_surjective k m)
    have hfinite : Module.Finite k (Γ(C, U) ⧸ m) := finite_of_finite_type_of_isJacobsonRing k _
    have hintegral : Algebra.IsIntegral k (Γ(C, U) ⧸ m) := Algebra.IsIntegral.of_finite k _
    exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := Γ(C, U) ⧸ m)).2
  have hprime : ∀ (x : C) (hx : x ∈ U), x ≠ genericPoint C → IsClosed ({x} : Set C) := fun x _ hne
    =>
    (hpts x).resolve_left hne
  have hdim : ∀ p : Ideal Γ(C, U), p.IsPrime → p ≠ ⊥ → p.IsMaximal := by
    intro p hp hne
    let y : PrimeSpectrum Γ(C, U) := ⟨p, hp⟩
    have hyU : hUaff.fromSpec.base y ∈ U := by
      have : hUaff.fromSpec.base y ∈ (U : Set C) := by
        rw [← hUaff.range_fromSpec]; exact Set.mem_range_self _
      exact this
    have hprim : hUaff.primeIdealOf ⟨hUaff.fromSpec.base y, hyU⟩ = y := by
      apply hUaff.fromSpec.isOpenEmbedding.injective
      rw [hUaff.fromSpec_primeIdealOf]
    rcases hpts (hUaff.fromSpec.base y) with hgen | hcl
    · exfalso
      apply hne
      have h1 := hUaff.primeIdealOf_genericPoint (X := C)
      rw [genericPoint_eq_bot_of_affine] at h1
      have hsub : (⟨hUaff.fromSpec.base y, hyU⟩ : {x : C // x ∈ U}) = ⟨genericPoint C, hU⟩ :=
        Subtype.ext hgen
      have hy : y = ⊥ := by
        rw [← hprim, hsub]
        exact h1
      have := congrArg PrimeSpectrum.asIdeal hy
      simpa using this
    · have := hUaff.primeIdealOf_isMaximal_of_isClosed ⟨hUaff.fromSpec.base y, hyU⟩ hcl
      rwa [hprim] at this
  let P : C → Prop := fun z => z ∈ U ∧ IsClosed ({z} : Set C)
  let instA : ∀ z : {z : C // P z}, Algebra Γ(C, U) (C.presheaf.stalk z.1) :=
    fun z => C.presheaf.algebra_section_stalk (⟨z.1, z.2.1⟩ : {x : C // x ∈ U})
  have instT : ∀ z : {z : C // P z}, IsScalarTower Γ(C, U) (C.presheaf.stalk z.1) C.functionField :=
    fun z => functionField_isScalarTower C U (⟨z.1, z.2.1⟩ : {x : C // x ∈ U})
  let 𝔪 : {z : C // P z} → Ideal Γ(C, U) := fun z => (hUaff.primeIdealOf (⟨z.1, z.2.1⟩ : {x : C //
    x ∈ U})).asIdeal
  have hmaximal : ∀ z, (𝔪 z).IsMaximal := fun z => hUaff.primeIdealOf_isMaximal_of_isClosed (⟨z.1,
    z.2.1⟩ : {x : C // x ∈ U}) z.2.2
  have h𝔪 : Function.Injective 𝔪 := by
    intro z₁ z₂ h
    have h' : hUaff.primeIdealOf (⟨z₁.1, z₁.2.1⟩ : {x : C // x ∈ U}) = hUaff.primeIdealOf (⟨z₂.1,
      z₂.2.1⟩ : {x : C // x ∈ U}) :=
      PrimeSpectrum.ext h
    have := congrArg (fun q => hUaff.fromSpec.base q) h'
    simp only [hUaff.fromSpec_primeIdealOf] at this
    exact Subtype.ext this
  have instL : ∀ z : {z : C // P z}, IsLocalization.AtPrime (C.presheaf.stalk z.1) (𝔪 z) :=
    fun z => hUaff.isLocalization_stalk (⟨z.1, z.2.1⟩ : {x : C // x ∈ U})
  obtain ⟨hs, hk, hf, hfd⟩ :=
    IsLocalization.AtPrime.surjective_and_ker_pi_span_mul_quotient_of_moduleFinite k
      C.functionField hdim hres
      P (fun z => C.presheaf.stalk z) 𝔪 h𝔪 B hB
  have hkmem : ∀ (z : C) (a : k), algebraMap k C.functionField a ∈ Set.range (algebraMap
    (C.presheaf.stalk z) C.functionField) := by
    intro z a
    refine ⟨(C.presheaf.germ ⊤ z trivial).hom (c.appTop.hom ((Scheme.ΓSpecIso (.of k)).inv.hom
      a)), ?_⟩
    change (C.presheaf.stalkSpecializes ((genericPoint_spec C).specializes trivial)).hom
        ((C.presheaf.germ ⊤ z trivial).hom _) = (C.presheaf.germ ⊤ (genericPoint C) hη).hom _
    exact TopCat.Presheaf.germ_stalkSpecializes_apply C.presheaf
      (U := ⊤) (y := z) (x := genericPoint C) trivial
      ((genericPoint_spec C).specializes trivial) _
  have hspan : ∀ (f : Set C.functionField) (hf1 : ∀ a : k, algebraMap k C.functionField a ∈ f)
      (hfmul : ∀ x ∈ f, ∀ y ∈ f, x * y ∈ f) (hfadd : ∀ x ∈ f, ∀ y ∈ f, x + y ∈ f) (hf0 : (0 :
        C.functionField) ∈ f),
      (Submodule.span k f : Set C.functionField) = f := by
    intro f hf1 hfmul hfadd hf0
    refine Set.Subset.antisymm ?_ Submodule.subset_span
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact hy
    | zero => exact hf0
    | add y z _ _ hy hz => exact hfadd y hy z hz
    | smul a y _ hy => rw [Algebra.smul_def]; exact hfmul _ (hf1 a) y hy
  have hspanRange : ∀ z : C, (Submodule.span k (Set.range (algebraMap (C.presheaf.stalk z)
    C.functionField)) :
      Set C.functionField) = Set.range (algebraMap (C.presheaf.stalk z) C.functionField) := fun z =>
    hspan _ (hkmem z) (fun x ⟨a, ha⟩ y ⟨b, hb⟩ => ⟨a * b, by rw [map_mul, ha, hb]⟩)
      (fun x ⟨a, ha⟩ y ⟨b, hb⟩ => ⟨a + b, by rw [map_add, ha, hb]⟩) ⟨0, map_zero _⟩
  have hgermU : ∀ s, (C.presheaf.germ U (genericPoint C) hU).hom s = algebraMap Γ(C, U)
    C.functionField s := fun _ => rfl
  have hspanU : (Submodule.span k (Set.range (C.presheaf.germ U (genericPoint C) hU).hom) : Set
    C.functionField) =
      Set.range (algebraMap Γ(C, U) C.functionField) := by
    have hrg : Set.range (C.presheaf.germ U (genericPoint C) hU).hom = Set.range (algebraMap Γ(C,
      U) C.functionField) := rfl
    rw [hrg]
    refine hspan _ (fun a => ⟨algebraMap k Γ(C, U) a, (IsScalarTower.algebraMap_apply k Γ(C, U) _
      a).symm⟩)
      (fun x ⟨a, ha⟩ y ⟨b, hb⟩ => ⟨a * b, by rw [map_mul, ha, hb]⟩)
      (fun x ⟨a, ha⟩ y ⟨b, hb⟩ => ⟨a + b, by rw [map_add, ha, hb]⟩) ⟨0, map_zero _⟩
  have hgen : ∀ x : C, x = genericPoint C → ∀ b : C.functionField,
      b ∈ Set.range (algebraMap (C.presheaf.stalk x) C.functionField) := by
    rintro x rfl b
    refine ⟨b, ?_⟩
    change (C.presheaf.stalkSpecializes ((genericPoint_spec C).specializes trivial)).hom b = b
    rw [TopCat.Presheaf.stalkSpecializes_refl]
    rfl
  have hkerSub : (⨅ z : {z : C // P z}, Submodule.span k (Set.range (algebraMap (C.presheaf.stalk
    z.1) C.functionField))) =
      Submodule.span k (Set.range (C.presheaf.germ U (genericPoint C) hU).hom) := by
    apply SetLike.coe_injective
    rw [Submodule.coe_iInf, hspanU]
    have h83 := AlgebraicGeometry.Scheme.Opens.range_algebraMap_functionField_eq_iInf (X := C) U
    have h83' : Set.range (algebraMap Γ(C, U) C.functionField) =
        ⋂ (x : C) (_ : x ∈ U), Set.range (algebraMap (C.presheaf.stalk x) C.functionField) := by
      have := congrArg (fun S : Subring C.functionField => (S : Set C.functionField)) h83
      simpa only [RingHom.coe_range, Subring.coe_iInf] using this
    rw [h83']
    ext b
    simp only [Set.mem_iInter, hspanRange]
    constructor
    · intro h x hx
      by_cases hcl : IsClosed ({x} : Set C)
      · exact h ⟨x, hx, hcl⟩
      · exact hgen x ((hpts x).resolve_right hcl) b
    · intro h z
      exact h z.1 z.2.1
  refine ⟨hs, ?_, hf, hfd⟩
  rw [hk, hkerSub]

end AlgebraicCurves.FunctionFields.Proofs.Surjective_and_ker_pi_span_mul_quotient_of_finite
end ProofImplementation
