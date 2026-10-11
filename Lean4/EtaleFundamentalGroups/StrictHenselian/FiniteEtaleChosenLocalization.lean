/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.FieldTheory.IsSepClosed
import SchemeTheory.FiniteEtale.Henselian.PointedEtale

/-!
# A chosen closed factor of a finite etale algebra over a strict Henselian base

For a specified prime over the closed point, separable closedness makes the
residue-field map bijective.  The pointed Henselian theorem then identifies
the corresponding localization with the base.  Unlike an existence theorem,
this keeps a prime selected by an independent component construction.
-/

noncomputable section

namespace EtaleFundamentalGroups

open Polynomial

universe u v

private theorem isSepClosed_of_ringEquiv_chosenLocalization
    {k : Type u} {l : Type v} [Field k] [Field l] [IsSepClosed k]
    (e : k ≃+* l) : IsSepClosed l := by
  constructor
  intro p hp
  have hp' : (p.map e.symm.toRingHom).Separable :=
    hp.map (f := e.symm.toRingHom)
  have hsplit : (p.map e.symm.toRingHom).Splits :=
    IsSepClosed.splits_of_separable _ hp'
  simpa only [Polynomial.map_map, RingEquiv.toRingHom_eq_coe,
    RingEquiv.comp_symm, Polynomial.map_id] using
      hsplit.map e.toRingHom

/-- Every specified closed prime of an etale algebra over a strictly
Henselian local ring gives a localization canonically isomorphic to the
base.  The prime is input data, while the residue-field bijection is produced
internally from etaleness and separable closedness. -/
theorem strictHenselian_finiteEtale_localizationAlgEquiv_of_primesOver
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [Algebra R S] [HenselianLocalRing R]
    [IsSepClosed (IsLocalRing.ResidueField R)] [Algebra.Etale R S]
    (q : (IsLocalRing.maximalIdeal R).primesOver S) :
    Nonempty (R ≃ₐ[R] Localization.AtPrime q.1) := by
  let m := IsLocalRing.maximalIdeal R
  let : Algebra (Localization.AtPrime m) (Localization.AtPrime q.1) :=
    Localization.AtPrime.algebraOfLiesOver m q.1
  let eResidue : IsLocalRing.ResidueField R ≃+* m.ResidueField :=
    IsLocalRing.ResidueField.mapEquiv
      (localizationAtMaximalIdealAlgEquiv R).toRingEquiv
  let : IsSepClosed m.ResidueField :=
    isSepClosed_of_ringEquiv_chosenLocalization eResidue
  have hres : Function.Bijective
      (Ideal.ResidueField.mapₐ m q.1 (Algebra.ofId R S)
        (q.1.over_def m)) := by
    change Function.Bijective
      (algebraMap m.ResidueField q.1.ResidueField)
    exact IsSepClosed.algebraMap_bijective _ _
  exact ⟨henselianPointedEtaleLocalizationAlgEquiv q.1 hres⟩

end EtaleFundamentalGroups

end
