/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.Ramification.NativeAlgebraResidueCoefficient
import Nyll.SchemeTheory.RingTheory.Ramification.NativeMaximalResidue

/-!
# Coefficients of the native residue ring action

Forgetting coefficient linearity is a homomorphism. Transport through the
fixed maximal-quotient equivalence preserves the literal coefficient equation.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

universe u v

/-- The native quotient action, forgetting only coefficient linearity. -/
def nativeAlgebraResidueRingEquivHom
    {A : Type u} [CommRing A] (B : CommAlgCat.{v} A) (Q : Ideal B.carrier) :
    (nativeAlgebraResidueAutomorphisms B Q).carrier →*
      ((B.carrier ⧸ Q) ≃+* (B.carrier ⧸ Q)) where
  toFun := nativeAlgebraResidueAutomorphismRingEquiv B Q
  map_one' := by
    apply RingEquiv.ext
    intro x
    rfl
  map_mul' σ τ := by
    apply RingEquiv.ext
    intro x
    rfl

/-- The SAME quotient action on the canonical localization residue field. -/
def nativeAlgebraResidueRingHom
    {A : Type u} [CommRing A] (B : CommAlgCat.{v} A)
    (Q : Ideal B.carrier) [Q.IsMaximal]
    (ρ : (nativeAlgebraResidueAutomorphisms B Q).carrier) :
    Q.ResidueField →+* Q.ResidueField :=
  ((maximalQuotientResidueEquiv Q).toRingHom.comp
    (nativeAlgebraResidueAutomorphismRingEquiv B Q ρ).toRingHom).comp
    (maximalQuotientResidueEquiv Q).symm.toRingHom

/-- The coefficient formula survives the fixed quotient/residue transport. -/
theorem nativeAlgebraResidueRingHom_coefficient
    {A : Type u} [CommRing A] (B : CommAlgCat.{v} A)
    (Q : Ideal B.carrier) [Q.IsMaximal]
    (ρ : (nativeAlgebraResidueAutomorphisms B Q).carrier)
    (s : B.carrier →+* B.carrier)
    (hs : nativeAlgebraResidueCoefficientMap B Q ρ = (Ideal.Quotient.mk Q).comp s)
    (b : B.carrier) :
    (nativeAlgebraResidueRingHom B Q ρ).toFun ((algebraMap B.carrier Q.ResidueField).toFun b) =
      (algebraMap B.carrier Q.ResidueField).toFun (s.toFun b) := by
  have hc (x : B.carrier) :
      (maximalQuotientResidueEquiv Q).toFun ((Ideal.Quotient.mk Q).toFun x) =
        (algebraMap B.carrier Q.ResidueField).toFun x :=
    congrArg (fun f : B.carrier →+* Q.ResidueField => f.toFun x)
      (maximalQuotientResidueEquiv_comp_quotient Q)
  exact (congrArg (nativeAlgebraResidueRingHom B Q ρ).toFun (hc b).symm).trans
    ((congrArg (fun x : B.carrier ⧸ Q => (maximalQuotientResidueEquiv Q).toFun
      ((nativeAlgebraResidueAutomorphismRingEquiv B Q ρ).toFun x))
      ((maximalQuotientResidueEquiv Q).symm_apply_apply ((Ideal.Quotient.mk Q).toFun b))).trans
      ((congrArg (maximalQuotientResidueEquiv Q).toFun
        (congrArg (fun f : B.carrier →+* (B.carrier ⧸ Q) => f.toFun b) hs)).trans
        (hc (s.toFun b))))

end EtaleFundamentalGroups.Inertia

end
