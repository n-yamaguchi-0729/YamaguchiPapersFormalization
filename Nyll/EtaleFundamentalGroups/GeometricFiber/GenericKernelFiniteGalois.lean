/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.ClosedNormalFiniteGalois
import Nyll.EtaleFundamentalGroups.Normalization.UnramifiedSubfield

/-!
# The generic-point kernel as an intersection of unramified finite kernels

For an arbitrary normal integral scheme, the actual generic absolute Galois
kernel is the intersection of the restriction kernels of its finite Galois
subextensions with etale normalization. The classifier is the existing
finite-etale generic-fiber equivalence, and no local criterion is assumed.

Reference: https://stacks.math.columbia.edu/tag/0BTD
-/

open AlgebraicGeometry AlgebraicGeometry.FiniteEtale

namespace EtaleFundamentalGroups

universe u

/-- Finite Galois extensions with etale normalization determine the
literal kernel of the canonical generic-point surjection. -/
theorem genericAbsoluteGaloisHom_ker_eq_iInf_etale_finiteGalois
    (X : Scheme.{u}) [IsIntegral X] [IsNormalIntegral X] :
    (genericAbsoluteGaloisHom X).toMonoidHom.ker =
      ⨅ (E : FiniteGaloisIntermediateField X.functionField
        (SeparableClosure X.functionField))
        (_ : Etale (X.genericExtensionMorphism E).fromNormalization),
        E.toIntermediateField.fixingSubgroup := by
  let H : ClosedSubgroup Gal(SeparableClosure X.functionField/X.functionField) :=
    ⟨(genericAbsoluteGaloisHom X).toMonoidHom.ker,
      isClosed_eq (genericAbsoluteGaloisHom X).continuous continuous_const⟩
  have : H.toSubgroup.Normal := MonoidHom.normal_ker (genericAbsoluteGaloisHom X).toMonoidHom
  change H.toSubgroup = _
  rw [Inertia.closedNormalSubgroup_eq_iInf_finiteGalois_fixingSubgroup
    X.functionField (SeparableClosure X.functionField) H]
  apply le_antisymm
  · apply le_iInf
    intro E
    apply le_iInf
    intro hE σ hσ
    have hfix : H.toSubgroup ≤ E.toIntermediateField.fixingSubgroup :=
      (etale_normalization_iff_genericKernel_le_fixingSubgroup
        X E.toIntermediateField).mp hE
    exact Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp hσ E) hfix
  · apply le_iInf
    intro E
    apply le_iInf
    intro hfix σ hσ
    have hE : Etale (X.genericExtensionMorphism E).fromNormalization :=
      (etale_normalization_iff_genericKernel_le_fixingSubgroup
        X E.toIntermediateField).mpr hfix
    exact Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp hσ E) hE

end EtaleFundamentalGroups
