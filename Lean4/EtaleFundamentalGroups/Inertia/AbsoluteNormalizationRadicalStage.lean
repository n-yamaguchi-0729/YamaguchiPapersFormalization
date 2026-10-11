/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.AbsoluteFiniteNormalization
import EtaleFundamentalGroups.Inertia.AbsoluteUniformizerAmbient
import EtaleFundamentalGroups.Inertia.NativeNormalizationRadical

/-!
# The actual finite-normalization radical stage of the absolute DVR argument

The ambient radical producer chooses the finite Galois field and uniformizer.
Its literal membership and proved integrality construct the root in the
native finite normalization. The original power equation is retained using
the stored coefficient map, with no finite-field scalar action opened here.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v w

/-- Every invertible exponent occurs as a uniformizer radical in the actual
normalization of a finite Galois subextension of the given separable closure. -/
theorem exists_finiteAbsoluteNormalization_uniformizer_radical
    (A : Type u) (K : Type v) (Ω : Type w)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field Ω] [Algebra A K] [IsFractionRing A K]
    [Algebra K Ω] [Algebra A Ω] [IsScalarTower A K Ω] [IsSepClosure K Ω]
    (n : ℕ) (hn : IsUnit (n : A)) :
    ∃ (E : FiniteGaloisIntermediateField K Ω) (π : A)
      (γ : finiteAbsoluteNormalizationAlgebra A K Ω E),
      Irreducible π ∧ γ ^ n =
        commAlgCoefficientMap (finiteAbsoluteNormalizationAlgebra A K Ω E) π := by
  obtain ⟨E, π, α, hπ, _hαzero, hmem, hint, hpow⟩ :=
    exists_finiteGalois_ambient_uniformizer_radical A K Ω n hn
  have hmemS : α ∈ finiteLevelNormalizationSubalgebra A K Ω E := hmem
  refine ⟨E, π, nativeNormalizationElement
    (finiteLevelNormalizationSubalgebra A K Ω E) α hmemS hint, hπ, ?_⟩
  exact nativeNormalizationElement_pow
    (finiteLevelNormalizationSubalgebra A K Ω E) α hmemS hint n π hpow

end EtaleFundamentalGroups.Inertia

end
