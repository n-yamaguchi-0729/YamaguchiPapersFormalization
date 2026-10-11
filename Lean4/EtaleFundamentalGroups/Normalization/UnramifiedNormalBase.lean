/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Normalization.EtaleDominantQuotient
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.Unramified.LocalStructure

/-!
# Dominant unramified domains over normal domains

An unramified algebra which is a domain faithful over a normal domain is
étale. The local structure of unramified algebras presents principal opens
as quotients of standard étale algebras. Their dominant domain quotients are
étale, and locality on the target gives the conclusion, including finite
presentation.
-/

noncomputable section

namespace EtaleFundamentalGroups

universe u

/-- An unramified domain faithful over a normal domain is étale.
Finite presentation is obtained from the local standard étale quotient
presentations, rather than assumed. -/
theorem etale_of_unramified_of_domain_of_faithful
    {R B : Type u}
    [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [CommRing B] [IsDomain B] [Algebra R B] [FaithfulSMul R B]
    [Algebra.FiniteType R B] [Algebra.FormallyUnramified R B] :
    Algebra.Etale R B := by
  have hlocal (q : Ideal B) [q.IsPrime] :
      ∃ f ∉ q, Algebra.Etale R (Localization.Away f) := by
    obtain ⟨f, hf, P, φ, hφ⟩ :=
      Algebra.IsUnramifiedAt.exists_hasStandardEtaleSurjectionOn (R := R) q
    have hfzero : f ≠ 0 := by
      intro h
      exact hf (h ▸ q.zero_mem)
    let : IsDomain (Localization.Away f) := Localization.Away.isDomain hfzero
    let : FaithfulSMul R (Localization.Away f) :=
      (faithfulSMul_iff_algebraMap_injective R (Localization.Away f)).mpr <| by
        rw [IsScalarTower.algebraMap_eq R B (Localization.Away f)]
        exact (IsLocalization.injective (Localization.Away f)
          (powers_le_nonZeroDivisors_of_noZeroDivisors hfzero)).comp
            (FaithfulSMul.algebraMap_injective R B)
    exact ⟨f, hf, etale_of_surjective_of_domain_of_faithful φ hφ⟩
  let s : Set B := {f | Algebra.Etale R (Localization.Away f)}
  have hs : Ideal.span s = ⊤ := by
    by_contra h
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal (Ideal.span s) h
    let : m.IsMaximal := hm
    obtain ⟨f, hfm, hf⟩ := hlocal m
    exact hfm (hle (Ideal.subset_span hf))
  apply RingHom.etale_algebraMap.mp
  apply RingHom.Etale.ofLocalizationSpanTarget (algebraMap R B) s hs
  intro f
  rw [← IsScalarTower.algebraMap_eq R B (Localization.Away (f : B))]
  exact RingHom.etale_algebraMap.mpr f.property

end EtaleFundamentalGroups
