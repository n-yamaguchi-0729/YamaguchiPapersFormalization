/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Purity.Descent.FaithfullyFlatIntegrallyClosed
import EtaleFundamentalGroups.Kummer.Completions.ChosenFactor.RightDomain

/-!
# Normality descent from an actual chosen tensor factor

The maximal-adic completion used in the one-root construction does not have
a global Noetherian instance in the current library.  Normality can instead
be descended from the concrete normal chosen factor.

If `B / A` is faithfully flat, then its base change
`C -> C tensor[A] B` is faithfully flat.  The chosen-factor coordinate
`B tensor[A] C = D` transports that structure to the literal right map
`C -> D`.  Integral closedness therefore descends first from `D` to `C`,
and then, when `C / A` is faithfully flat (as for the finite-etale residue
lift), from `C` to `A`.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups.Kummer

universe uA uB uC uD

/-- The right-coordinate map of a chosen tensor factor is faithfully flat
when the left coordinate is faithfully flat over the common base.

This is the missing structural input for normality descent.  It is generated
by base change and transported across the actual chosen-factor equivalence;
no flatness or injectivity of the right map is assumed separately. -/
theorem tensorChosenFactorRight_faithfullyFlat
    {A : Type uA} {B : Type uB} {C : Type uC} {D : Type uD}
    [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    [Algebra A B] [Algebra A C] [Algebra B D]
    [Module.FaithfullyFlat A B]
    (e : (B ⊗[A] C) ≃ₐ[B] D) :
    letI : Algebra C D :=
      (e.toRingEquiv.toRingHom.comp
        (Algebra.TensorProduct.includeRight :
          C →ₐ[A] B ⊗[A] C).toRingHom).toAlgebra
    Module.FaithfullyFlat C D := by
  let : Algebra C D :=
    (e.toRingEquiv.toRingHom.comp
      (Algebra.TensorProduct.includeRight :
        C →ₐ[A] B ⊗[A] C).toRingHom).toAlgebra
  let eComm : (C ⊗[A] B) ≃ₐ[C] D := by
    refine
      { toRingEquiv :=
          (Algebra.TensorProduct.comm A C B).toRingEquiv.trans
            e.toRingEquiv
        commutes' := ?_ }
    intro c
    rfl
  let : Module.FaithfullyFlat C (C ⊗[A] B) := inferInstance
  exact
    Module.FaithfullyFlat.of_linearEquiv
      (R := C) (M := C ⊗[A] B) eComm.symm.toLinearEquiv

/-- A normal actual chosen factor makes its right tensor coordinate normal.

In the completion application, `C` is the explicit finite-etale residue
lift.  Its domain structure is obtained from the same tensor coordinate,
and faithful-flat descent then supplies integral closedness without a
Noetherian hypothesis on either `A` or `C`. -/
theorem tensorChosenFactorRight_isIntegrallyClosed
    {A : Type uA} {B : Type uB} {C : Type uC} {D : Type uD}
    [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    [Algebra A B] [Algebra A C] [Algebra B D]
    [Module.FaithfullyFlat A B] [Module.FaithfullyFlat A C]
    [IsDomain D] [IsIntegrallyClosed D]
    (e : (B ⊗[A] C) ≃ₐ[B] D) :
    letI : Algebra C D :=
      (e.toRingEquiv.toRingHom.comp
        (Algebra.TensorProduct.includeRight :
          C →ₐ[A] B ⊗[A] C).toRingHom).toAlgebra
    letI : IsDomain C := tensorChosenFactorRight_isDomain e
    IsIntegrallyClosed C := by
  let : Algebra C D :=
    (e.toRingEquiv.toRingHom.comp
      (Algebra.TensorProduct.includeRight :
        C →ₐ[A] B ⊗[A] C).toRingHom).toAlgebra
  let : IsDomain C := tensorChosenFactorRight_isDomain e
  let : Module.FaithfullyFlat C D :=
    tensorChosenFactorRight_faithfullyFlat e
  exact isIntegrallyClosed_of_faithfullyFlat C D

/-- Application-shaped normality descent for the complete chosen-factor
square.

The hypotheses are precisely the structural data produced in the one-root
completion construction: faithful flatness of the root cover `B / A`,
faithful flatness of the finite-etale residue lift `C / A`, the actual tensor
coordinate, and normality of the retained chosen factor `D`.  The theorem
first proves `C` normal from the same coordinate and then descends once more
to the completed base `A`. -/
theorem tensorChosenFactorBase_isIntegrallyClosed_of_normalFactor
    {A : Type uA} {B : Type uB} {C : Type uC} {D : Type uD}
    [CommRing A] [IsDomain A]
    [CommRing B] [CommRing C] [CommRing D]
    [Algebra A B] [Algebra A C] [Algebra B D]
    [Module.FaithfullyFlat A B] [Module.FaithfullyFlat A C]
    [IsDomain D] [IsIntegrallyClosed D]
    (e : (B ⊗[A] C) ≃ₐ[B] D) :
    IsIntegrallyClosed A := by
  let : Algebra C D :=
    (e.toRingEquiv.toRingHom.comp
      (Algebra.TensorProduct.includeRight :
        C →ₐ[A] B ⊗[A] C).toRingHom).toAlgebra
  let : IsDomain C := tensorChosenFactorRight_isDomain e
  let : IsIntegrallyClosed C :=
    tensorChosenFactorRight_isIntegrallyClosed e
  exact isIntegrallyClosed_of_faithfullyFlat A C

/-- Normality descent in the exact finite-etale local residue-lift shape.

The faithful-flatness of `C / A` is not an input: finiteness makes the map
integral, hence local between the displayed local rings, while etaleness
supplies flatness.  Thus the actual chosen-factor coordinate and normality
of its target are the only data beyond the structures already produced by
the complete residue-lift construction. -/
theorem
    tensorChosenFactorBase_isIntegrallyClosed_of_normalFactor_finiteEtaleLocal
    {A : Type uA} {B : Type uB} {C : Type uC} {D : Type uD}
    [CommRing A] [IsDomain A] [IsLocalRing A]
    [CommRing B] [CommRing C] [IsLocalRing C] [CommRing D]
    [Algebra A B] [Algebra A C] [Algebra B D]
    [Module.FaithfullyFlat A B]
    [Module.Finite A C] [Algebra.Etale A C]
    [IsDomain D] [IsIntegrallyClosed D]
    (e : (B ⊗[A] C) ≃ₐ[B] D) :
    IsIntegrallyClosed A := by
  let : Algebra.IsIntegral A C := Algebra.IsIntegral.of_finite A C
  let : IsLocalHom (algebraMap A C) := by
    apply ((IsLocalRing.local_hom_TFAE (algebraMap A C)).out 5 1).mp
    exact IsLocalRing.eq_maximalIdeal
      (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (algebraMap A C)
        (fun x ↦ Algebra.IsIntegral.isIntegral x) (IsLocalRing.maximalIdeal C))
  let : Module.FaithfullyFlat A C :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact tensorChosenFactorBase_isIntegrallyClosed_of_normalFactor e

end EtaleFundamentalGroups.Kummer

end
