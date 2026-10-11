/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_ringKrullDim_stalk_eq_of_isFinite_endomorphism.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Morphisms.Finite

import Nyll.AlgebraicCurves.Foundations.CommutativeAlgebra.Ideal_height_eq_height_under_of_finiteType_of_isIntegral
import Nyll.AlgebraicCurves.Foundations.CommutativeAlgebra.AlgHom_injective_of_finite_of_isFractionRing

/-!
# ring Krull Dim stalk eq of is Finite endomorphism
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs.ringKrullDim_stalk_eq_of_isFinite_endomorphism

universe u

open CategoryTheory AlgebraicGeometry

namespace P2mWs11DimEndo

variable {k : Type u} [Field k] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of k)}

/-- The scalar ring homomorphism into sections on an open of a scheme over the base field. -/
noncomputable def secAlg (f : X ⟶ Spec (CommRingCat.of k)) (U : X.Opens) : k →+* Γ(X, U) :=
  (f.appLE ⊤ U ((le_top : U ≤ ⊤).trans (Scheme.Hom.preimage_top f).ge)).hom.comp (Scheme.ΓSpecIso
    (CommRingCat.of k)).inv.hom

theorem app_comp_secAlg (h : X ⟶ X) (hov : h ≫ f = f) (U : X.Opens) :
    (h.app U).hom.comp (secAlg f U) = secAlg f (h ⁻¹ᵁ U) := by
  unfold secAlg
  rw [← RingHom.comp_assoc]
  congr 1
  have : f.appLE ⊤ U ((le_top : U ≤ ⊤).trans (Scheme.Hom.preimage_top f).ge) ≫ h.app U = f.appLE ⊤
    (h ⁻¹ᵁ U) ((le_top : h ⁻¹ᵁ U ≤ ⊤).trans (Scheme.Hom.preimage_top f).ge) := by
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
    conv_rhs => rw [← hov]
  exact congrArg (fun g => g.hom) this

theorem germ_comp_secAlg (U : X.Opens) (x : X) (hx : x ∈ U) :
    (X.presheaf.germ U x hx).hom.comp (secAlg f U) =
      ((Spec (CommRingCat.of k)).presheaf.germ ⊤ (f.base x) trivial ≫ f.stalkMap x).hom.comp
        (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom := by
  unfold secAlg
  rw [← RingHom.comp_assoc]
  congr 1
  have := Scheme.Hom.germ_stalkMap f ⊤ x trivial
  have h2 : f.appLE ⊤ U ((le_top : U ≤ ⊤).trans (Scheme.Hom.preimage_top f).ge) ≫ X.presheaf.germ U
    x hx =
      (Spec (CommRingCat.of k)).presheaf.germ ⊤ (f.base x) trivial ≫ f.stalkMap x := by
    rw [Scheme.Hom.appLE, Category.assoc, X.presheaf.germ_res, ← this]
  exact congrArg (fun g => g.hom) h2

theorem main [LocallyOfFiniteType f] [IsIntegral X]
    (h : X ⟶ X) (hov : h ≫ f = f) [IsFinite h] (x : X) :
    ringKrullDim (X.presheaf.stalk x) = ringKrullDim (X.presheaf.stalk (h.base x)) := by
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (x := h.base x) (U := ⊤)
    trivial
  have hV : IsAffineOpen (h ⁻¹ᵁ U) := hU.preimage h
  have hxV : x ∈ h ⁻¹ᵁ U := hxU
  have : Nonempty U := ⟨⟨h.base x, hxU⟩⟩
  have : Nonempty (h ⁻¹ᵁ U) := ⟨⟨x, hxV⟩⟩
  let A : Type u := Γ(X, U)
  let B : Type u := Γ(X, h ⁻¹ᵁ U)
  let : Algebra k A := (secAlg f U).toAlgebra
  let : Algebra k B := (secAlg f (h ⁻¹ᵁ U)).toAlgebra
  let : Algebra A B := (h.app U).hom.toAlgebra
  have : IsScalarTower k A B := IsScalarTower.of_algebraMap_eq' (app_comp_secAlg h hov U).symm
  have hftA : (secAlg f U).FiniteType :=
    (f.finiteType_appLE (U := ⊤) (isAffineOpen_top _) hU le_top).comp
      (RingHom.FiniteType.of_surjective _ (Scheme.ΓSpecIso (CommRingCat.of
        k)).commRingCatIsoToRingEquiv.symm.surjective)
  have hftB : (secAlg f (h ⁻¹ᵁ U)).FiniteType :=
    (f.finiteType_appLE (U := ⊤) (isAffineOpen_top _) hV le_top).comp
      (RingHom.FiniteType.of_surjective _ (Scheme.ΓSpecIso (CommRingCat.of
        k)).commRingCatIsoToRingEquiv.symm.surjective)
  have : Algebra.FiniteType k A := hftA
  have : Algebra.FiniteType k B := hftB
  have : Module.Finite A B := IsFinite.finite_app h U hU
  have : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
  let K : Type u := X.functionField
  have : IsFractionRing A K := functionField_isFractionRing_of_isAffineOpen X U hU
  have : IsFractionRing B K := functionField_isFractionRing_of_isAffineOpen X (h ⁻¹ᵁ U) hV
  let : Algebra k K := ((algebraMap A K).comp (secAlg f U)).toAlgebra
  have : IsScalarTower k A K := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower k B K := by
    apply IsScalarTower.of_algebraMap_eq'
    change (algebraMap A K).comp (secAlg f U) = (algebraMap B K).comp (secAlg f (h ⁻¹ᵁ U))
    change (X.presheaf.germ U (genericPoint X) _).hom.comp (secAlg f U) =
      (X.presheaf.germ (h ⁻¹ᵁ U) (genericPoint X) _).hom.comp (secAlg f (h ⁻¹ᵁ U))
    rw [germ_comp_secAlg, germ_comp_secAlg]
  have hcommutes : ∀ r : k, (h.app U).hom (algebraMap k A r) = algebraMap k B r := fun r => by
    change ((h.app U).hom.comp (secAlg f U)) r = secAlg f (h ⁻¹ᵁ U) r
    rw [app_comp_secAlg h hov U]
  have hinj : Function.Injective (algebraMap A B) := by
    let φ : A →ₐ[k] B := { (h.app U).hom with commutes' := hcommutes }
    exact AlgHom.injective_of_finite_of_isFractionRing (K := K) φ (IsFinite.finite_app h U hU)
  have : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).mpr hinj
  let q : Ideal B := (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
  let p : Ideal A := (hU.primeIdealOf ⟨h.base x, hxU⟩).asIdeal
  have hpq : q.under A = p := by
    have hc := IsAffineOpen.comap_primeIdealOf_appLE (f := h) U hU (h ⁻¹ᵁ U) hV le_rfl hxV
    rw [← Scheme.Hom.app_eq_appLE] at hc
    exact congrArg PrimeSpectrum.asIdeal hc
  let xV : (h ⁻¹ᵁ U) := ⟨x, hxV⟩
  let yU : U := ⟨h.base x, hxU⟩
  let : Algebra B (X.presheaf.stalk (xV : X)) := TopCat.Presheaf.algebra_section_stalk X.presheaf xV
  let : Algebra A (X.presheaf.stalk (yU : X)) := TopCat.Presheaf.algebra_section_stalk X.presheaf yU
  have : IsLocalization.AtPrime (X.presheaf.stalk (xV : X)) q := hV.isLocalization_stalk xV
  have : IsLocalization.AtPrime (X.presheaf.stalk (yU : X)) p := hU.isLocalization_stalk yU
  change ringKrullDim (X.presheaf.stalk (xV : X)) = ringKrullDim (X.presheaf.stalk (yU : X))
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height q (X.presheaf.stalk (xV : X)),
    IsLocalization.AtPrime.ringKrullDim_eq_height p (X.presheaf.stalk (yU : X)),
    Ideal.height_eq_height_under_of_finiteType_of_isIntegral k A B q, hpq]

end P2mWs11DimEndo

theorem _root_.AlgebraicGeometry.ringKrullDim_stalk_eq_of_isFinite_endomorphism
    {k : Type u} [Field k] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of k)}
    [LocallyOfFiniteType f] [IsIntegral X]
    (h : X ⟶ X) (hov : h ≫ f = f) [IsFinite h] (x : X) :
    ringKrullDim (X.presheaf.stalk x) = ringKrullDim (X.presheaf.stalk (h.base x)) :=
  P2mWs11DimEndo.main h hov x
end AlgebraicCurves.Geometry.Schemes.Proofs.ringKrullDim_stalk_eq_of_isFinite_endomorphism
end ProofImplementation
