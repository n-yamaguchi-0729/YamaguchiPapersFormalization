/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.Flat.Basic
import Nyll.EtaleFundamentalGroups.Completions.FiniteEtale.ChosenFactorCoordinates

/-!
# Domain structure on the right coordinate of a chosen tensor factor

A chosen-factor equivalence `B tensor[A] C = D` embeds its right coordinate
`C` into `D` whenever `C/A` is flat and `B/A` is faithful.  Consequently a
domain structure on the actual chosen factor pulls back to `C`.  This avoids
using Noetherianity of the complete two-dimensional base merely to prove
that its explicit finite residue lift is a domain.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups.Kummer

universe uA uB uC uD

/-- The transported right-coordinate map of a chosen tensor factor is
injective. -/
theorem tensorChosenFactorRight_algebraMap_injective
    {A : Type uA} {B : Type uB} {C : Type uC} {D : Type uD}
    [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    [Algebra A B] [Algebra A C] [Algebra B D]
    [FaithfulSMul A B] [Module.Flat A C]
    (e : (B ⊗[A] C) ≃ₐ[B] D) :
    letI : Algebra C D :=
      (e.toRingEquiv.toRingHom.comp
        (Algebra.TensorProduct.includeRight : C →ₐ[A] B ⊗[A] C).toRingHom).toAlgebra
    Function.Injective (algebraMap C D) := by
  let : Algebra C D :=
    (e.toRingEquiv.toRingHom.comp
      (Algebra.TensorProduct.includeRight : C →ₐ[A] B ⊗[A] C).toRingHom).toAlgebra
  change Function.Injective
    (e.toRingEquiv.toRingHom.comp
      (Algebra.TensorProduct.includeRight : C →ₐ[A] B ⊗[A] C).toRingHom)
  exact e.injective.comp <|
    Algebra.TensorProduct.includeRight_injective
      (FaithfulSMul.algebraMap_injective A B)

/-- If the chosen factor is a domain, so is the finite residue-lift
coordinate embedded in it. -/
theorem tensorChosenFactorRight_isDomain
    {A : Type uA} {B : Type uB} {C : Type uC} {D : Type uD}
    [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    [Algebra A B] [Algebra A C] [Algebra B D]
    [FaithfulSMul A B] [Module.Flat A C] [IsDomain D]
    (e : (B ⊗[A] C) ≃ₐ[B] D) :
    letI : Algebra C D :=
      (e.toRingEquiv.toRingHom.comp
        (Algebra.TensorProduct.includeRight : C →ₐ[A] B ⊗[A] C).toRingHom).toAlgebra
    IsDomain C := by
  let : Algebra C D :=
    (e.toRingEquiv.toRingHom.comp
      (Algebra.TensorProduct.includeRight : C →ₐ[A] B ⊗[A] C).toRingHom).toAlgebra
  exact Function.Injective.isDomain (algebraMap C D)
    (tensorChosenFactorRight_algebraMap_injective e)

end EtaleFundamentalGroups.Kummer

end
