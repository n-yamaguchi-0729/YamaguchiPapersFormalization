/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Purity.PuncturedSpectrum

/-!
# Function field of a punctured local spectrum

The canonical open immersion identifies the function field of a
positive-dimensional local domain with that of its punctured spectrum.  In
particular, the latter is a fraction field of the original local domain.
-/

noncomputable section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.FiniteEtale

universe u

variable (R : Type u) [CommRing R] [IsDomain R] [IsLocalRing R]

private theorem puncturedSpectrum_nonempty_of_positiveDimension
    (hpos : (1 : WithBot ℕ∞) ≤ ringKrullDim R) :
    Nonempty (Scheme.puncturedSpectrum R) :=
  Scheme.puncturedSpectrum_nonempty_of_one_le_ringKrullDim R hpos

/-- The function fields of a positive-dimensional local domain and its
punctured spectrum are canonically equivalent. -/
noncomputable def puncturedSpectrumFunctionFieldRingEquivOfPositiveDimension
    (hpos : (1 : WithBot ℕ∞) ≤ ringKrullDim R) :
    let X := Spec (.of R)
    let U := Scheme.puncturedSpectrum R
    let j : U ⟶ X := Scheme.puncturedSpectrumInclusion R
    letI : Nonempty U :=
      puncturedSpectrum_nonempty_of_positiveDimension R hpos
    letI : IsIntegral X := inferInstance
    letI : IsOpenImmersion j := by
      dsimp only [j, Scheme.puncturedSpectrumInclusion]
      infer_instance
    letI : IsIntegral U := isIntegral_of_isOpenImmersion j
    X.functionField ≃+* U.functionField := by
  dsimp only
  let X := Spec (.of R)
  let U := Scheme.puncturedSpectrum R
  let j : U ⟶ X := Scheme.puncturedSpectrumInclusion R
  letI : Nonempty U :=
    puncturedSpectrum_nonempty_of_positiveDimension R hpos
  letI : IsIntegral X := inferInstance
  letI : IsOpenImmersion j := by
    dsimp only [j, Scheme.puncturedSpectrumInclusion]
    infer_instance
  letI : IsIntegral U := isIntegral_of_isOpenImmersion j
  let h : j (genericPoint U) = genericPoint X :=
    genericPoint_eq_of_isOpenImmersion j
  let e : X.functionField ≅ U.functionField :=
    X.presheaf.stalkCongr (.of_eq h.symm) ≪≫
      asIso (j.stalkMap (genericPoint U))
  exact e.commRingCatIsoToRingEquiv

/-- The algebra structure on the punctured-spectrum function field induced
from the local domain through the canonical open immersion. -/
@[reducible] noncomputable def
    puncturedSpectrumFunctionFieldAlgebraOfPositiveDimension
    (hpos : (1 : WithBot ℕ∞) ≤ ringKrullDim R) :
    let X := Spec (.of R)
    let U := Scheme.puncturedSpectrum R
    letI : Nonempty U :=
      puncturedSpectrum_nonempty_of_positiveDimension R hpos
    letI : IsOpenImmersion (Scheme.puncturedSpectrumInclusion R) := by
      dsimp only [Scheme.puncturedSpectrumInclusion]
      infer_instance
    letI : IsIntegral U :=
      isIntegral_of_isOpenImmersion (Scheme.puncturedSpectrumInclusion R)
    letI : Algebra R X.functionField :=
      AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (.of R)
    Algebra R U.functionField := by
  dsimp only
  let X := Spec (.of R)
  let U := Scheme.puncturedSpectrum R
  letI : Nonempty U :=
    puncturedSpectrum_nonempty_of_positiveDimension R hpos
  letI : IsOpenImmersion (Scheme.puncturedSpectrumInclusion R) := by
    dsimp only [Scheme.puncturedSpectrumInclusion]
    infer_instance
  letI : IsIntegral U :=
    isIntegral_of_isOpenImmersion (Scheme.puncturedSpectrumInclusion R)
  letI : Algebra R X.functionField :=
    AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (.of R)
  exact
    ((puncturedSpectrumFunctionFieldRingEquivOfPositiveDimension R hpos).toRingHom.comp
      (algebraMap R X.functionField)).toAlgebra

private noncomputable def
    puncturedSpectrumFunctionFieldAlgEquivOfPositiveDimension
    (hpos : (1 : WithBot ℕ∞) ≤ ringKrullDim R) :
    let X := Spec (.of R)
    let U := Scheme.puncturedSpectrum R
    letI : Nonempty U :=
      puncturedSpectrum_nonempty_of_positiveDimension R hpos
    letI : IsOpenImmersion (Scheme.puncturedSpectrumInclusion R) := by
      dsimp only [Scheme.puncturedSpectrumInclusion]
      infer_instance
    letI : IsIntegral U :=
      isIntegral_of_isOpenImmersion (Scheme.puncturedSpectrumInclusion R)
    letI : Algebra R X.functionField :=
      AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (.of R)
    letI : Algebra R U.functionField :=
      puncturedSpectrumFunctionFieldAlgebraOfPositiveDimension R hpos
    X.functionField ≃ₐ[R] U.functionField := by
  dsimp only
  let X := Spec (.of R)
  let U := Scheme.puncturedSpectrum R
  letI : Nonempty U :=
    puncturedSpectrum_nonempty_of_positiveDimension R hpos
  letI : IsOpenImmersion (Scheme.puncturedSpectrumInclusion R) := by
    dsimp only [Scheme.puncturedSpectrumInclusion]
    infer_instance
  letI : IsIntegral U :=
    isIntegral_of_isOpenImmersion (Scheme.puncturedSpectrumInclusion R)
  letI : Algebra R X.functionField :=
    AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (.of R)
  letI : Algebra R U.functionField :=
    puncturedSpectrumFunctionFieldAlgebraOfPositiveDimension R hpos
  exact
    { puncturedSpectrumFunctionFieldRingEquivOfPositiveDimension R hpos with
      commutes' := fun _ ↦ rfl }

/-- The function field of the punctured spectrum is a fraction field of the
positive-dimensional local domain. -/
theorem puncturedSpectrumFunctionField_isFractionRing_of_positiveDimension
    (hpos : (1 : WithBot ℕ∞) ≤ ringKrullDim R) :
    let X := Spec (.of R)
    let U := Scheme.puncturedSpectrum R
    letI : Nonempty U :=
      puncturedSpectrum_nonempty_of_positiveDimension R hpos
    letI : IsOpenImmersion (Scheme.puncturedSpectrumInclusion R) := by
      dsimp only [Scheme.puncturedSpectrumInclusion]
      infer_instance
    letI : IsIntegral U :=
      isIntegral_of_isOpenImmersion (Scheme.puncturedSpectrumInclusion R)
    letI : Algebra R X.functionField :=
      AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (.of R)
    letI : Algebra R U.functionField :=
      puncturedSpectrumFunctionFieldAlgebraOfPositiveDimension R hpos
    IsFractionRing R U.functionField := by
  dsimp only
  let X := Spec (.of R)
  let U := Scheme.puncturedSpectrum R
  let : Nonempty U :=
    puncturedSpectrum_nonempty_of_positiveDimension R hpos
  let : IsOpenImmersion (Scheme.puncturedSpectrumInclusion R) := by
    dsimp only [Scheme.puncturedSpectrumInclusion]
    infer_instance
  let : IsIntegral U :=
    isIntegral_of_isOpenImmersion (Scheme.puncturedSpectrumInclusion R)
  let : Algebra R X.functionField :=
    AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (.of R)
  let : Algebra R U.functionField :=
    puncturedSpectrumFunctionFieldAlgebraOfPositiveDimension R hpos
  let : IsFractionRing R X.functionField :=
    AlgebraicGeometry.functionField_isFractionRing_of_affine (.of R)
  exact IsFractionRing.of_algEquiv
    (puncturedSpectrumFunctionFieldAlgEquivOfPositiveDimension R hpos)

end AlgebraicGeometry.FiniteEtale
