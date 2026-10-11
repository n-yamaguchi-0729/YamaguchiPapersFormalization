/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-!
# Descending a literal coefficient square to residue fields

This ring-only lemma uses coefficient surjectivity at a maximal ideal. Its
applications supply the two coefficient formulas and square from actual maps.
-/

namespace EtaleFundamentalGroups.Inertia

universe u v

theorem residueMap_coefficient_naturality
    {B : Type u} {C : Type v} [CommRing B] [CommRing C]
    (P : Ideal B) [P.IsMaximal] (Q : Ideal C) [Q.IsPrime]
    (j : B →+* C) (hj : P = Q.comap j)
    (s : B →+* B) (t : C →+* C)
    (a : P.ResidueField →+* P.ResidueField)
    (b : Q.ResidueField →+* Q.ResidueField)
    (ha : ∀ x : B, a.toFun ((algebraMap B P.ResidueField).toFun x) =
      (algebraMap B P.ResidueField).toFun (s.toFun x))
    (hb : ∀ x : C, b.toFun ((algebraMap C Q.ResidueField).toFun x) =
      (algebraMap C Q.ResidueField).toFun (t.toFun x))
    (hcomm : j.comp s = t.comp j) (x : P.ResidueField) :
    (Ideal.ResidueField.map P Q j hj).toFun (a.toFun x) =
      b.toFun ((Ideal.ResidueField.map P Q j hj).toFun x) := by
  obtain ⟨r, rfl⟩ := P.algebraMap_residueField_surjective x
  exact (congrArg (Ideal.ResidueField.map P Q j hj).toFun (ha r)).trans
    ((Ideal.ResidueField.map_algebraMap P Q j hj (s.toFun r)).trans
      ((congrArg (algebraMap C Q.ResidueField).toFun
        (congrArg (fun f : B →+* C => f.toFun r) hcomm)).trans
        ((hb (j.toFun r)).symm.trans
          (congrArg b.toFun (Ideal.ResidueField.map_algebraMap P Q j hj r).symm))))

end EtaleFundamentalGroups.Inertia
