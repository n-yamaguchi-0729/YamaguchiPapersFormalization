/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.Yamaguchi26AbfaithfulGalois.GroupTheory.Faithful
import Nyll.GaloisCohomology.Topology.FiniteExtensionGalois
import Nyll.GaloisCohomology.Kummer.Concrete.GaloisClosureConjugation

/-!
# Ab-faithfulness under finite field extension

Ab-faithfulness of the absolute Galois group passes to finite field
extensions, including inseparable extensions.
-/

namespace Yamaguchi26AbfaithfulGalois

open ProCGroups.FiniteStepSolvableQuotients KummerTheory

universe u v

/-- Ab-faithfulness of the absolute Galois group passes to every finite field
extension, including inseparable extensions. -/
theorem isAbFaithful_absoluteGaloisGroup_of_finiteExtension
    {K : Type u} {E : Type v} [Field K] [Field E] [Algebra K E]
    [FiniteDimensional K E]
    (hK : IsAbFaithful Gal(AlgebraicClosure K/K)) :
    IsAbFaithful Gal(AlgebraicClosure E/E) := by
  let U := GaloisCohomology.finiteExtensionGaloisOpenSubgroup K E (AlgebraicClosure E)
  have hΩ : IsAbFaithful Gal(AlgebraicClosure E/K) :=
    isAbFaithful_of_continuousMulEquiv
      (absoluteGaloisClosureEquiv K (AlgebraicClosure E)) hK
  exact isAbFaithful_of_continuousMulEquiv
    (GaloisCohomology.finiteExtensionGaloisOpenSubgroupEquiv K E (AlgebraicClosure E))
    (isAbFaithful_openSubgroup hΩ U)

end Yamaguchi26AbfaithfulGalois
