/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.InvariantEtaleNeighborhood
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.Algebra.Subalgebra.Operations
import Mathlib.Algebra.Algebra.Tower
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Invariant.Galois
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Integral


/-!
# The finite-Galois normalization neighborhood in Stacks tag 0BSU

For a finite Galois extension of the fraction field of a normal domain, the
canonical Galois action on its actual integral closure has the original
normal domain as its full invariants. The literal invariant-base map is
proved bijective; its algebra equivalence transports the original 0BST
étale neighborhood to that original base.

This supplies the finite-Galois principal-neighborhood prerequisite of 0BSU.
The arbitrary infinite inertia restriction and localized filtered-colimit
comparisons are separate statements.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

universe u v w

private theorem exists_etale_away_of_invariant_base
    (A : Type u) (B : Type v) (G : Type w)
    [CommRing A] [CommRing B] [Algebra A B]
    [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G A B]
    [Algebra.IsInvariant A B G]
    (hinj : Function.Injective (algebraMap A B)) (q : Ideal B) [q.IsPrime] :
    ∃ f : FixedPoints.subalgebra A B (q.inertia G),
      (f : B) ∉ q ∧ Algebra.Etale A (Localization.Away f) := by
  let S := FixedPoints.subring B G
  let ι : A →+* S := (algebraMap A B).codRestrict (FixedPoints.subring B G)
    (fun a g => smul_algebraMap g a)
  let : Algebra A S := ι.toAlgebra
  have : IsScalarTower A S B := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hbij : Function.Bijective ι := by
    constructor
    · intro a b h
      exact hinj (congrArg Subtype.val h)
    · intro b
      obtain ⟨a, ha⟩ := Algebra.IsInvariant.isInvariant (A := A) (G := G) (b : B) b.property
      exact ⟨a, Subtype.ext ha⟩
  have : Algebra.Etale A S :=
    Algebra.Etale.of_equiv (AlgEquiv.ofBijective (Algebra.ofId A S) hbij)
  obtain ⟨f₀, hf₀, hEtale⟩ := inertia_invariants_exists_etale_away B G q
  have : Algebra.Etale S (Localization.Away f₀) := hEtale
  have hfinal : Algebra.Etale A (Localization.Away f₀) :=
    Algebra.Etale.comp A S (Localization.Away f₀)
  let f : FixedPoints.subalgebra A B (q.inertia G) := ⟨(f₀ : B), f₀.property⟩
  exact ⟨f, hf₀, hfinal⟩

/-- In a finite Galois normalization, every inertia-invariant localization
at an original normalization prime has an actual principal neighborhood
étale over the original normal domain. The full-invariant base comparison
is proved from canonical Galois invariance and injectivity. -/
theorem finiteGalois_integralClosure_inertia_exists_etale_away
    (A : Type u) (K : Type v) (L : Type w)
    [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [IsGalois K L]
    (q : Ideal (integralClosure A L)) [q.IsPrime] :
    let : MulSemiringAction Gal(L/K) (integralClosure A L) :=
      IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
    let : SMulCommClass Gal(L/K) A (integralClosure A L) := by
      constructor
      intro σ a b
      change (galRestrict A K L (integralClosure A L) σ) (a • b) =
        a • (galRestrict A K L (integralClosure A L) σ) b
      exact (galRestrict A K L (integralClosure A L) σ).toLinearMap.map_smul a b
    ∃ f : FixedPoints.subalgebra A (integralClosure A L) (q.inertia Gal(L/K)),
      (f : integralClosure A L) ∉ q ∧ Algebra.Etale A (Localization.Away f) := by
  intro actualAction actualComm
  have : IsFractionRing (integralClosure A L) L :=
    integralClosure.isFractionRing_of_finite_extension (A := A) K L
  have : Algebra.IsInvariant A (integralClosure A L) Gal(L/K) :=
    Algebra.isInvariant_of_isGalois A K L (integralClosure A L)
  exact exists_etale_away_of_invariant_base A (integralClosure A L) Gal(L/K)
    (algebraMap_injective_of_field_isFractionRing (R := A) (S := integralClosure A L) K L) q

end EtaleFundamentalGroups.Inertia
