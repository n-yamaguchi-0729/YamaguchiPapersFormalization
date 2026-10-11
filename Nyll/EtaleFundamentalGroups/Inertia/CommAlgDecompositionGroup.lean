/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.Ramification.NativeResidueAction
import Nyll.SchemeTheory.RingTheory.Ramification.StabilizerLocalizationAction
import Nyll.SchemeTheory.Normalization.NativeAutomorphismRingMaps
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Pointwise

/-!
# Native coefficient decomposition groups

The group is the existing native residue stabilizer, with the existing
coefficient-automorphism action. Ring-only contraction and action comparison
prove the stability and lifting statements used by actual finite restrictions.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory
open scoped Pointwise

universe u v w

/-- The existing coefficient-automorphism stabilizer, owned by its native
coefficient algebra so finite towers do not reopen its action dictionaries. -/
def commAlgIdealDecompositionGroup (A : Type u) [CommRing A]
    (B : CommAlgCat.{v} A) (Q : Ideal B.carrier) : GrpCat.{v} :=
  nativeResidueStabilizer B.carrier (B.carrier ≃ₐ[A] B.carrier) Q

/-- The native coefficient ring map of a stabilizer element fixes the
literal prime under contraction. The action dictionaries stay in this owner. -/
theorem commAlgIdealDecomposition_comap
    (A : Type u) [CommRing A] (B : CommAlgCat.{v} A) (Q : Ideal B.carrier)
    (σ : (commAlgIdealDecompositionGroup A B Q).carrier) :
    Q = Q.comap (commAlgAutomorphismRingHom A B σ.val) :=
  stabilizerCoefficientRingEquiv_comap_eq B.carrier (B.carrier ≃ₐ[A] B.carrier) Q σ

/-- An equivariant literal ring map contracts a fixed ideal to a fixed ideal. -/
theorem ideal_map_comap_eq_of_equivariant
    (B : Type v) (C : Type w) [CommRing B] [CommRing C]
    (j : B →+* C) (s : B ≃+* B) (t : C ≃+* C) (Q : Ideal C)
    (hcomm : j.comp s.toRingHom = t.toRingHom.comp j)
    (hQ : Q = Q.comap t.toRingHom) :
    (Q.comap j).map s.toRingHom = Q.comap j := by
  have hp : Q.comap j = (Q.comap j).comap s.toRingHom := by
    calc
      Q.comap j = (Q.comap t.toRingHom).comap j := congrArg (Ideal.comap j) hQ
      _ = Q.comap (t.toRingHom.comp j) := Ideal.comap_comap j t.toRingHom
      _ = Q.comap (j.comp s.toRingHom) :=
        congrArg (fun f : B →+* C => Q.comap f) hcomm.symm
      _ = (Q.comap j).comap s.toRingHom := (Ideal.comap_comap s.toRingHom j).symm
  exact (congrArg (Ideal.map s.toRingHom) hp).trans
    (Ideal.map_comap_of_surjective s.toRingHom s.surjective (Q.comap j))

/-- Actual coefficient stability constructs a morphism into the existing
native decomposition group. -/
def commAlgDecompositionHomOfStabilizer
    (A : Type u) [CommRing A] (B : CommAlgCat.{v} A) (G : GrpCat.{v})
    (Q : Ideal B.carrier) (f : GrpCat.Hom G (commAlgAutomorphismGroup A B))
    (hf : ∀ g : G.carrier,
      Q.map (commAlgAutomorphismRingHom A B (f.hom'.toFun g)) = Q) :
    GrpCat.Hom G (commAlgIdealDecompositionGroup A B Q) where
  hom' :=
    { toFun := fun g => ⟨f.hom'.toFun g, hf g⟩
      map_one' := Subtype.ext f.hom'.map_one
      map_mul' := fun g h => Subtype.ext (f.hom'.map_mul g h) }

/-- A native stabilizer element is trivial exactly when its coefficient
ring map is the identity. -/
theorem commAlgIdealDecomposition_eq_one_iff_coefficient
    (A : Type u) [CommRing A] (B : CommAlgCat.{v} A) (Q : Ideal B.carrier)
    (σ : (commAlgIdealDecompositionGroup A B Q).carrier) :
    σ = 1 ↔ commAlgAutomorphismRingHom A B σ.val = RingHom.id B.carrier := by
  constructor
  · intro h
    rw [h]
    rfl
  · intro h
    apply Subtype.ext
    apply AlgEquiv.ext
    intro b
    exact congrArg (fun f : B.carrier →+* B.carrier => f.toFun b) h

/-- An actual coefficient-automorphism lift with the same ring action
preserves the literal ideal stabilizer condition. -/
theorem coefficientDecomposition_exists_preimage
    (A : Type u) [CommRing A] (B : CommAlgCat.{v} A) (G : GrpCat.{v})
    (Q : Ideal B.carrier) (a : MulSemiringAction G.carrier B.carrier)
    (f : GrpCat.Hom G (commAlgAutomorphismGroup A B))
    (hsurj : Function.Surjective f.hom'.toFun)
    (hcompare :
      let : MulSemiringAction G.carrier B.carrier := a
      ∀ g : G.carrier, MulSemiringAction.toRingHom G.carrier B.carrier g =
        commAlgAutomorphismRingHom A B (f.hom'.toFun g)) :
    let : MulSemiringAction G.carrier B.carrier := a
    ∀ τ : (commAlgIdealDecompositionGroup A B Q).carrier,
      ∃ g : G.carrier, (MulAction.stabilizer G.carrier Q).carrier g ∧
        f.hom'.toFun g = τ.val := by
  intro ringAction τ
  obtain ⟨g, hg⟩ := hsurj τ.val
  refine ⟨g, ?_, hg⟩
  change Q.map (MulSemiringAction.toRingHom G.carrier B.carrier g) = Q
  rw [hcompare g, hg]
  exact τ.property

end EtaleFundamentalGroups.Inertia
