/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.GenericTensor.FilteredColimit.CategoricalDescent
import EtaleFundamentalGroups.GenericTensor.FilteredColimit.NativeTensorCorrespondence
import EtaleFundamentalGroups.GenericTensor.FilteredColimit.NativeTensorPushout
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.Algebra.Category.Ring.Under.Basic
import Mathlib.CategoryTheory.HomCongr
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Descent comparisons retaining the original native tensor actions

The native tensor product is compared directly with the categorical pushout.
The comparison uses the original algebra instances, never the algebras
reconstructed from an Under object. Its coefficient naturality is proved from
the two tensor coprojections. This keeps action normalization out of the
finite-field descent proofs.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace EtaleFundamentalGroups.NativeTensorDescent

open CategoryTheory.CategoricalTensorDescent
open EtaleFundamentalGroups.CategoricalTensor

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

/-- The original tensor algebra and the chosen pushout model have the same
coefficient arrow. The native algebra actions are retained in this constructor. -/
def modelIso (B : Type u) [CommRing B] [Algebra R B] :
    CommRingCat.mkUnder (CommRingCat.of S) (S ⊗[R] B) ≅
      model (CommRingCat.mkUnder (CommRingCat.of R) S)
        (CommRingCat.mkUnder (CommRingCat.of R) B) :=
  Under.isoMk (nativeTensorPushoutIso R S B) (by
    exact (CommRingCat.isPushout_tensorProduct R S B).flip.inr_isoPushout_hom)

/-- The model projection of the actual named native comparison. -/
theorem nativeIso_inl_hom (B : Type u) [CommRing B] [Algebra R B] :
    CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : B →ₐ[R] S ⊗[R] B).toRingHom ≫
        (nativeTensorPushoutIso R S B).hom =
      pushout.inl (CommRingCat.ofHom (algebraMap R B))
        (CommRingCat.ofHom (algebraMap R S)) :=
  (CommRingCat.isPushout_tensorProduct R S B).flip.inl_isoPushout_hom

/-- The coefficient projection of the same native comparison. -/
theorem nativeIso_inr_hom (B : Type u) [CommRing B] [Algebra R B] :
    CommRingCat.ofHom (algebraMap S (S ⊗[R] B)) ≫
        (nativeTensorPushoutIso R S B).hom =
      pushout.inr (CommRingCat.ofHom (algebraMap R B))
        (CommRingCat.ofHom (algebraMap R S)) :=
  (CommRingCat.isPushout_tensorProduct R S B).flip.inr_isoPushout_hom

/-- Reading the Under comparison keeps the same native ring Iso homomorphism. -/
theorem modelIso_hom_right (B : Type u) [CommRing B] [Algebra R B] :
    (modelIso R S B).hom.right = (nativeTensorPushoutIso R S B).hom :=
  rfl

/-- Reading its inverse likewise keeps the existing native ring Iso. -/
theorem modelIso_inv_right (B : Type u) [CommRing B] [Algebra R B] :
    (modelIso R S B).inv.right = (nativeTensorPushoutIso R S B).inv :=
  rfl

/-- Arbitrary native algebra maps correspond to maps of the actual pushout
models. Both directions share the same constructed comparison. -/
def homEquiv (B D : Type u) [CommRing B] [CommRing D] [Algebra R B] [Algebra R D] :
    ((S ⊗[R] B) →ₐ[S] (S ⊗[R] D)) ≃
      (model (CommRingCat.mkUnder (CommRingCat.of R) S)
          (CommRingCat.mkUnder (CommRingCat.of R) B) ⟶
        model (CommRingCat.mkUnder (CommRingCat.of R) S)
          (CommRingCat.mkUnder (CommRingCat.of R) D)) :=
  (nativeUnderHomEquivAlgHom (CommAlgCat.of S (S ⊗[R] B))
    (CommAlgCat.of S (S ⊗[R] D))).symm.trans
      ((modelIso R S B).homCongr (modelIso R S D))

/-- The ring map of the Hom correspondence uses precisely the two native
comparison maps. This computation is closed before a coefficient square is formed. -/
theorem homEquiv_right (B D : Type u) [CommRing B] [CommRing D]
    [Algebra R B] [Algebra R D] (f : (S ⊗[R] B) →ₐ[S] (S ⊗[R] D)) :
    (homEquiv R S B D f).right =
      (nativeTensorPushoutIso R S B).inv ≫ CommRingCat.ofHom f.toRingHom ≫
        (nativeTensorPushoutIso R S D).hom :=
  rfl

/-- The same comparison transports arbitrary native algebra equivalences. -/
def isoEquiv (B D : Type u) [CommRing B] [CommRing D] [Algebra R B] [Algebra R D] :
    ((S ⊗[R] B) ≃ₐ[S] (S ⊗[R] D)) ≃
      (model (CommRingCat.mkUnder (CommRingCat.of R) S)
          (CommRingCat.mkUnder (CommRingCat.of R) B) ≅
        model (CommRingCat.mkUnder (CommRingCat.of R) S)
          (CommRingCat.mkUnder (CommRingCat.of R) D)) :=
  (nativeUnderIsoEquivAlgEquiv (CommAlgCat.of S (S ⊗[R] B))
    (CommAlgCat.of S (S ⊗[R] D))).symm.trans
      ((modelIso R S B).isoCongr (modelIso R S D))

theorem isoEquiv_hom (B D : Type u) [CommRing B] [CommRing D]
    [Algebra R B] [Algebra R D] (e : (S ⊗[R] B) ≃ₐ[S] (S ⊗[R] D)) :
    (isoEquiv R S B D e).hom = homEquiv R S B D e.toAlgHom :=
  rfl

theorem isoEquiv_inv (B D : Type u) [CommRing B] [CommRing D]
    [Algebra R B] [Algebra R D] (e : (S ⊗[R] B) ≃ₐ[S] (S ⊗[R] D)) :
    (isoEquiv R S B D e).inv = homEquiv R S D B e.symm.toAlgHom :=
  rfl

variable {S}

/-- The direct native comparison commutes with the literal tensor map of a
coefficient homomorphism. Only the two coprojection equations are used. -/
theorem nativeIso_leg (T B : Type u) [CommRing T] [CommRing B]
    [Algebra R T] [Algebra R B] (f : S →ₐ[R] T) :
    (nativeTensorPushoutIso R S B).hom ≫
        leg f.toUnder (CommRingCat.mkUnder (CommRingCat.of R) B) =
      CommRingCat.ofHom (Algebra.TensorProduct.map f (AlgHom.id R B)).toRingHom ≫
        (nativeTensorPushoutIso R T B).hom := by
  let S₀ : Under (CommRingCat.of R) := CommRingCat.mkUnder (CommRingCat.of R) S
  let T₀ : Under (CommRingCat.of R) := CommRingCat.mkUnder (CommRingCat.of R) T
  let B₀ : Under (CommRingCat.of R) := CommRingCat.mkUnder (CommRingCat.of R) B
  let f₀ : S₀ ⟶ T₀ := f.toUnder
  have hmodel :
      pushout.inl (CommRingCat.ofHom (algebraMap R B))
          (CommRingCat.ofHom (algebraMap R S)) ≫ leg f₀ B₀ =
        pushout.inl (CommRingCat.ofHom (algebraMap R B))
          (CommRingCat.ofHom (algebraMap R T)) :=
    leg_inl f₀ B₀
  have hcoeff :
      pushout.inr (CommRingCat.ofHom (algebraMap R B))
          (CommRingCat.ofHom (algebraMap R S)) ≫ leg f₀ B₀ =
        CommRingCat.ofHom f.toRingHom ≫
          pushout.inr (CommRingCat.ofHom (algebraMap R B))
            (CommRingCat.ofHom (algebraMap R T)) :=
    leg_inr f₀ B₀
  have hright :
      CommRingCat.ofHom (Algebra.TensorProduct.includeRight : B →ₐ[R] S ⊗[R] B).toRingHom ≫
          CommRingCat.ofHom (Algebra.TensorProduct.map f (AlgHom.id R B)).toRingHom =
        CommRingCat.ofHom (Algebra.TensorProduct.includeRight : B →ₐ[R] T ⊗[R] B).toRingHom := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro b
    exact congrArg (fun g : B →ₐ[R] T ⊗[R] B ↦ g b)
      (Algebra.TensorProduct.map_comp_includeRight f (AlgHom.id R B))
  have hleft :
      CommRingCat.ofHom (algebraMap S (S ⊗[R] B)) ≫
          CommRingCat.ofHom (Algebra.TensorProduct.map f (AlgHom.id R B)).toRingHom =
        CommRingCat.ofHom f.toRingHom ≫
          CommRingCat.ofHom (algebraMap T (T ⊗[R] B)) := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro s
    change Algebra.TensorProduct.map f (AlgHom.id R B) (s ⊗ₜ[R] (1 : B)) =
      f s ⊗ₜ[R] (1 : B)
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  apply (CommRingCat.isPushout_tensorProduct R S B).flip.hom_ext
  · rw [← Category.assoc, nativeIso_inl_hom, hmodel,
      ← Category.assoc, hright]
    exact (nativeIso_inl_hom R T B).symm
  · change CommRingCat.ofHom (algebraMap S (S ⊗[R] B)) ≫
        ((nativeTensorPushoutIso R S B).hom ≫
          leg f.toUnder (CommRingCat.mkUnder (CommRingCat.of R) B)) =
      CommRingCat.ofHom (algebraMap S (S ⊗[R] B)) ≫
        CommRingCat.ofHom (Algebra.TensorProduct.map f (AlgHom.id R B)).toRingHom ≫
          (nativeTensorPushoutIso R T B).hom
    rw [← Category.assoc, nativeIso_inr_hom, hcoeff,
      ← Category.assoc, hleft, Category.assoc]
    rw [nativeIso_inr_hom]

/-- The underlying Under model square follows from the established native
ring square, without unfolding either pushout universal-property proof. -/
theorem modelIso_leg (T B : Type u) [CommRing T] [CommRing B]
    [Algebra R T] [Algebra R B] (f : S →ₐ[R] T) :
    (modelIso R S B).hom.right ≫
        leg f.toUnder (CommRingCat.mkUnder (CommRingCat.of R) B) =
      CommRingCat.ofHom (Algebra.TensorProduct.map f (AlgHom.id R B)).toRingHom ≫
        (modelIso R T B).hom.right := by
  rw [modelIso_hom_right, modelIso_hom_right]
  exact nativeIso_leg R T B f

private theorem square_of_conjugated_square
    {C : Type u} [Category C]
    {A B A' B' X Y X' Y' : C}
    (a : A ≅ X) (b : B ≅ Y) (a' : A' ≅ X') (b' : B' ≅ Y')
    (l : A ⟶ A') (r : B ⟶ B') (L : X ⟶ X') (M : Y ⟶ Y')
    (f : A ⟶ B) (g : A' ⟶ B')
    (hl : a.hom ≫ L = l ≫ a'.hom) (hr : b.hom ≫ M = r ≫ b'.hom)
    (h : L ≫ (a'.inv ≫ g ≫ b'.hom) = (a.inv ≫ f ≫ b.hom) ≫ M) :
    l ≫ g = f ≫ r := by
  apply (cancel_mono b'.hom).mp
  calc
    (l ≫ g) ≫ b'.hom = a.hom ≫ (L ≫ (a'.inv ≫ g ≫ b'.hom)) := by
      rw [← Category.assoc a.hom L, hl]
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
    _ = a.hom ≫ ((a.inv ≫ f ≫ b.hom) ≫ M) := by rw [h]
    _ = (f ≫ r) ≫ b'.hom := by
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
      rw [hr]

/-- A coefficient square between categorical models gives the original
native algebra-hom square, without reopening reconstructed module actions. -/
theorem hom_square (T B D : Type u) [CommRing T] [CommRing B] [CommRing D]
    [Algebra R T] [Algebra R B] [Algebra R D]
    (q : S →ₐ[R] T)
    (f : (S ⊗[R] B) →ₐ[S] (S ⊗[R] D))
    (g : (T ⊗[R] B) →ₐ[T] (T ⊗[R] D))
    (h : leg q.toUnder (CommRingCat.mkUnder (CommRingCat.of R) B) ≫
        (homEquiv R T B D g).right =
      (homEquiv R S B D f).right ≫
        leg q.toUnder (CommRingCat.mkUnder (CommRingCat.of R) D)) :
    (Algebra.TensorProduct.map q (AlgHom.id R D)).comp (f.restrictScalars R) =
      (g.restrictScalars R).comp (Algebra.TensorProduct.map q (AlgHom.id R B)) := by
  let SB : CommRingCat.{u} := CommRingCat.of (S ⊗[R] B)
  let SD : CommRingCat.{u} := CommRingCat.of (S ⊗[R] D)
  let TB : CommRingCat.{u} := CommRingCat.of (T ⊗[R] B)
  let TD : CommRingCat.{u} := CommRingCat.of (T ⊗[R] D)
  let PSB : CommRingCat.{u} := pushout (CommRingCat.ofHom (algebraMap R B))
    (CommRingCat.ofHom (algebraMap R S))
  let PSD : CommRingCat.{u} := pushout (CommRingCat.ofHom (algebraMap R D))
    (CommRingCat.ofHom (algebraMap R S))
  let PTB : CommRingCat.{u} := pushout (CommRingCat.ofHom (algebraMap R B))
    (CommRingCat.ofHom (algebraMap R T))
  let PTD : CommRingCat.{u} := pushout (CommRingCat.ofHom (algebraMap R D))
    (CommRingCat.ofHom (algebraMap R T))
  let a : SB ≅ PSB := nativeTensorPushoutIso R S B
  let b : SD ≅ PSD := nativeTensorPushoutIso R S D
  let a' : TB ≅ PTB := nativeTensorPushoutIso R T B
  let b' : TD ≅ PTD := nativeTensorPushoutIso R T D
  let l : SB ⟶ TB :=
    CommRingCat.ofHom (Algebra.TensorProduct.map q (AlgHom.id R B)).toRingHom
  let r : SD ⟶ TD :=
    CommRingCat.ofHom (Algebra.TensorProduct.map q (AlgHom.id R D)).toRingHom
  let S₀ : Under (CommRingCat.of R) := CommRingCat.mkUnder (CommRingCat.of R) S
  let T₀ : Under (CommRingCat.of R) := CommRingCat.mkUnder (CommRingCat.of R) T
  let B₀ : Under (CommRingCat.of R) := CommRingCat.mkUnder (CommRingCat.of R) B
  let D₀ : Under (CommRingCat.of R) := CommRingCat.mkUnder (CommRingCat.of R) D
  let q₀ : S₀ ⟶ T₀ := q.toUnder
  let L : PSB ⟶ PTB := leg q₀ B₀
  let M : PSD ⟶ PTD := leg q₀ D₀
  let f₀ : SB ⟶ SD := CommRingCat.ofHom f.toRingHom
  let g₀ : TB ⟶ TD := CommRingCat.ofHom g.toRingHom
  have hl := nativeIso_leg (S := S) R T B q
  have hr := nativeIso_leg (S := S) R T D q
  have hring := h
  rw [homEquiv_right, homEquiv_right] at hring
  have hs : l ≫ g₀ = f₀ ≫ r :=
    square_of_conjugated_square (C := CommRingCat.{u})
      a b a' b' l r L M f₀ g₀ hl hr hring
  apply AlgHom.coe_ringHom_injective
  exact (congrArg (fun p ↦ p.hom) hs).symm

end EtaleFundamentalGroups.NativeTensorDescent

end
