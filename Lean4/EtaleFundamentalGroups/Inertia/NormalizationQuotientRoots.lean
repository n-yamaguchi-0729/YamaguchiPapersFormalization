/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.NormalizationResidueDVR
import EtaleFundamentalGroups.Inertia.NormalizationRootsGroup
import Mathlib.RingTheory.RootsOfUnity.Basic

/-!
# The canonical quotient comparison on roots

Restricts the already constructed maximal-quotient residue equivalence to
roots. Both the scalar evaluation and inverse needed for surjectivity use
this same equivalence.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

universe u v

attribute [local instance] Ideal.Quotient.field

/-- The SAME maximal quotient/residue comparison, restricted to roots. -/
def normalizationQuotientRootsEquiv
    (A : Type u) (L : Type v) [CommRing A] [CommRing L] [Algebra A L]
    (Q : Ideal (SchemeTheory.normalizationCommAlgCat A L).carrier) [Q.IsMaximal]
    (n : ℕ) : (normalizationRootsGroup A L Q n).carrier ≃*
      rootsOfUnity n ((SchemeTheory.normalizationCommAlgCat A L).carrier ⧸ Q) :=
  (normalizationMaximalQuotientResidueEquiv A L Q).symm.toMulEquiv.restrictRootsOfUnity n

end EtaleFundamentalGroups.Inertia

end
