/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.GenericTensor.FilteredColimit.CategoricalTensor
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.Algebra.Category.Ring.Under.Basic
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Correspondence with the original native algebras

Each tensor product is constructed with its original algebra instances in a
one-tensor scope. The categorical interface is then identified with that
native object. The equivalence below has arbitrary native algebra equivalences
as its inverse input, and proves both round trips.
-/

noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u

namespace EtaleFundamentalGroups.CategoricalTensor

variable {R : Type u} [CommRing R]

/-- The actual native tensor algebra, retaining both stored base actions. -/
def nativeTensorObject (S B : CommAlgCat.{u} R) : CommAlgCat.{u} S.carrier :=
  CommAlgCat.of S.carrier (S.carrier ⊗[R] B.carrier)

/-- Read one coefficient arrow as the actual commutative algebra it defines.
The object stores the ring and that same algebra map exactly once. -/
abbrev nativeCoefficientObject (S : Under (CommRingCat.of R)) : CommAlgCat.{u} R where
  carrier := S.right.carrier
  commRing := inferInstance
  algebra := S.hom.hom.toAlgebra

/-- Reconstructing the original algebra from its native algebra map gives the
original stored owner. No tensor is formed in this normalization. -/
theorem nativeCoefficientObject_mkUnder (S : CommAlgCat.{u} R) :
    nativeCoefficientObject (CommRingCat.mkUnder (CommRingCat.of R) S.carrier) = S := by
  change (let a : Algebra R S.carrier := (algebraMap R S.carrier).toAlgebra
    CommAlgCat.of R S.carrier) = S
  rw [toAlgebra_algebraMap]
  cases S
  rfl

/-- The existing tensor functor forms precisely the native tensor of the two
algebras owned by its inputs. This checks only those constructors, not any
tensor relation, map law, or universal-property proof. -/
theorem tensorFunctor_obj_coefficientObjects (S B : Under (CommRingCat.of R)) :
    (tensorFunctor S).obj B =
      CommRingCat.mkUnder S.right
        (nativeTensorObject (nativeCoefficientObject S) (nativeCoefficientObject B)).carrier := by
  rfl

/-- The categorical tensor constructor reconstructs exactly the original
native tensor algebra. Each input normalization was proved before this scope,
so no raw tensor dictionary is reconstructed alongside the functor interface. -/
theorem tensorFunctor_obj_native (S B : CommAlgCat.{u} R) :
    (tensorFunctor (CommRingCat.mkUnder (CommRingCat.of R) S.carrier)).obj
        (CommRingCat.mkUnder (CommRingCat.of R) B.carrier) =
      CommRingCat.mkUnder (CommRingCat.of S.carrier) (nativeTensorObject S B).carrier := by
  rw [tensorFunctor_obj_coefficientObjects]
  rcases S with @⟨s, sr, sa⟩
  rcases B with @⟨b, br, ba⟩
  change CommRingCat.mkUnder (CommRingCat.of s)
    (nativeTensorObject
      { carrier := s, commRing := sr, algebra := (algebraMap R s).toAlgebra }
      { carrier := b, commRing := br, algebra := (algebraMap R b).toAlgebra }).carrier =
    CommRingCat.mkUnder (CommRingCat.of s)
      (nativeTensorObject
        { carrier := s, commRing := sr, algebra := sa }
        { carrier := b, commRing := br, algebra := ba }).carrier
  rw [toAlgebra_algebraMap, toAlgebra_algebraMap]

/-- Read a morphism under the base into the original native algebra actions.
Its scalar compatibility is the defining Under square. -/
def nativeUnderHom (B D : CommAlgCat.{u} R)
    (f : CommRingCat.mkUnder (CommRingCat.of R) B.carrier ⟶
      CommRingCat.mkUnder (CommRingCat.of R) D.carrier) :
    B.carrier →ₐ[R] D.carrier where
  __ := f.right.hom
  commutes' r := congrArg
    (fun h : CommRingCat.of R ⟶ CommRingCat.of D.carrier ↦ h.hom r) f.w

/-- Arbitrary native algebra homomorphisms are precisely the corresponding
Under morphisms, with both round trips proved using the original actions. -/
def nativeUnderHomEquivAlgHom (B D : CommAlgCat.{u} R) :
    (CommRingCat.mkUnder (CommRingCat.of R) B.carrier ⟶
      CommRingCat.mkUnder (CommRingCat.of R) D.carrier) ≃
        (B.carrier →ₐ[R] D.carrier) where
  toFun := nativeUnderHom B D
  invFun f := f.toUnder
  left_inv f := by
    apply Under.UnderMorphism.ext
    rfl
  right_inv f := by
    apply AlgHom.ext
    intro b
    rfl

/-- Native algebra equivalences and isomorphisms under the base have the same
arbitrary data. Neither direction assumes a comparison equation. -/
def nativeUnderIsoEquivAlgEquiv (B D : CommAlgCat.{u} R) :
    (CommRingCat.mkUnder (CommRingCat.of R) B.carrier ≅
      CommRingCat.mkUnder (CommRingCat.of R) D.carrier) ≃
        (B.carrier ≃ₐ[R] D.carrier) where
  toFun e :=
    { toRingEquiv := ((Under.forget (CommRingCat.of R)).mapIso e).commRingCatIsoToRingEquiv
      commutes' := (nativeUnderHom B D e.hom).commutes' }
  invFun e := e.toUnder
  left_inv e := by
    apply Iso.ext
    apply Under.UnderMorphism.ext
    rfl
  right_inv e := by
    apply AlgEquiv.ext
    intro b
    rfl

/-- Original algebraic finite presentation supplies the native Under model's
ring-hom finite presentation. -/
theorem native_finitePresentation (B : CommAlgCat.{u} R)
    [Algebra.FinitePresentation R B.carrier] :
    (CommRingCat.mkUnder (CommRingCat.of R) B.carrier).hom.hom.FinitePresentation := by
  change (algebraMap R B.carrier).FinitePresentation
  exact RingHom.finitePresentation_algebraMap.mpr inferInstance

end EtaleFundamentalGroups.CategoricalTensor

end
