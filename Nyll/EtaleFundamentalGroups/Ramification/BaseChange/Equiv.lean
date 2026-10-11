/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Normalization.Primes.AtLargerPrime

/-!
# Ramification indices under equivalent integral models

Equivalent base and target rings do not change ramification indices.  These
lemmas package the change of local model needed when one divisorial valuation
is represented in different scheme stalks.
-/

noncomputable section

namespace EtaleFundamentalGroups

universe uR uS uT uU

/-- An algebra equivalence of target rings preserves ramification indices. -/
theorem ramificationIdx_map_eq_of_algEquiv
    {R : Type uR} {T : Type uT} {U : Type uU}
    [CommRing R] [CommRing T] [CommRing U]
    [Algebra R T] [Algebra R U]
    (e : T ≃ₐ[R] U) (q : Ideal T) [q.IsPrime] :
    (q.map e.toRingEquiv.toRingHom).ramificationIdx R =
      q.ramificationIdx R := by
  let : Algebra T U := e.toRingEquiv.toRingHom.toAlgebra
  let : IsScalarTower R T U :=
    IsScalarTower.of_algebraMap_eq fun r ↦ (e.commutes r).symm
  let eT : T ≃ₐ[T] U :=
    AlgEquiv.ofRingEquiv (f := e.toRingEquiv) fun _ ↦ rfl
  let : IsLocalization (IsUnit.submonoid T) U :=
    IsLocalization.isLocalization_of_algEquiv (IsUnit.submonoid T) eT
  have hdisj : Disjoint
      ((IsUnit.submonoid T : Submonoid T) : Set T) (q : Set T) := by
    rw [Set.disjoint_left]
    intro x hxUnit hxq
    have hqPrime : q.IsPrime := inferInstance
    exact hqPrime.ne_top (q.eq_top_of_isUnit_mem hxq hxUnit)
  exact ramificationIdx_map_eq_of_isLocalization
    (R := R) (S := T) (R' := R) (S' := U)
    (IsUnit.submonoid R) (IsUnit.submonoid T) q hdisj

/-- Replacing a base ring by an equivalent compatible model preserves the
ramification index of every prime of a fixed target ring. -/
theorem ramificationIdx_eq_of_compatible_baseRingEquiv
    {R : Type uR} {S : Type uS} {U : Type uU}
    [CommRing R] [CommRing S] [CommRing U]
    [Algebra R U] [Algebra S U]
    (e : R ≃+* S)
    (hcompat : (algebraMap S U).comp e.toRingHom = algebraMap R U)
    (q : Ideal U) [q.IsPrime] :
    q.ramificationIdx S = q.ramificationIdx R := by
  let pR : Ideal R := q.under R
  let pS : Ideal S := q.under S
  have hcomap : pS.comap e.toRingHom = pR := by
    change (q.comap (algebraMap S U)).comap e.toRingHom =
      q.comap (algebraMap R U)
    rw [Ideal.comap_comap, hcompat]
  have hpS : pS = pR.map e.toRingHom := by
    calc
      pS = (pS.comap e.toRingHom).map e.toRingHom :=
        (Ideal.map_comap_of_surjective e.toRingHom e.surjective pS).symm
      _ = pR.map e.toRingHom := by rw [hcomap]
  have hmap :
      pS.map (algebraMap S (Localization.AtPrime q)) =
        pR.map (algebraMap R (Localization.AtPrime q)) := by
    rw [hpS, Ideal.map_map]
    apply congrArg (fun f : R →+* Localization.AtPrime q ↦ pR.map f)
    apply RingHom.ext
    intro r
    change algebraMap U (Localization.AtPrime q) (algebraMap S U (e r)) =
      algebraMap U (Localization.AtPrime q) (algebraMap R U r)
    exact congrArg (algebraMap U (Localization.AtPrime q))
      (DFunLike.congr_fun hcompat r)
  rw [Ideal.ramificationIdx_eq pS q,
    Ideal.ramificationIdx_eq pR q, hmap]

/-- Compatible equivalences of both source and target rings preserve the
ramification index at corresponding target primes. -/
theorem ramificationIdx_map_eq_of_compatible_ringEquiv
    {R : Type uR} {S : Type uS} {T : Type uT} {U : Type uU}
    [CommRing R] [CommRing S] [CommRing T] [CommRing U]
    [Algebra R T] [Algebra S U]
    (eBase : R ≃+* S) (eTarget : T ≃+* U)
    (hcompat : eTarget.toRingHom.comp (algebraMap R T) =
      (algebraMap S U).comp eBase.toRingHom)
    (q : Ideal T) [q.IsPrime] :
    (q.map eTarget.toRingHom).ramificationIdx S =
      q.ramificationIdx R := by
  let : Algebra R U :=
    (eTarget.toRingHom.comp (algebraMap R T)).toAlgebra
  let : (q.map eTarget.toRingHom).IsPrime := by
    change (q.map eTarget).IsPrime
    infer_instance
  let eTargetAlg : T ≃ₐ[R] U :=
    AlgEquiv.ofRingEquiv (f := eTarget) fun _ ↦ rfl
  calc
    (q.map eTarget.toRingHom).ramificationIdx S =
        (q.map eTarget.toRingHom).ramificationIdx R :=
      ramificationIdx_eq_of_compatible_baseRingEquiv eBase
        hcompat.symm (q.map eTarget.toRingHom)
    _ = q.ramificationIdx R :=
      ramificationIdx_map_eq_of_algEquiv eTargetAlg q

end EtaleFundamentalGroups

end
