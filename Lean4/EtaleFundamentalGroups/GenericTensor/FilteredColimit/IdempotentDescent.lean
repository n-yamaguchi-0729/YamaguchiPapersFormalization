/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.GenericTensor.FilteredColimit.AlgEquivDescent
import EtaleFundamentalGroups.GenericTensor.FilteredColimit.CoconeLeg
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Algebra.Category.Ring.Under.Basic
import Mathlib.RingTheory.Finiteness.FinitePresentationLocal
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Maps


/-!
# Descent of a finite complete family of tensor idempotents

A complete orthogonal family determines a map from a finite product of the
base ring. The existing finite-presentation descent theorem descends that
map. Its values on the standard idempotents give the required family, with
the original literal cocone images. The other tensor factor is arbitrary.

This is finite idempotent data needed by the external Stacks tag 0BSR. It does
not assert that prime fibers or their residue extensions have descended.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace EtaleFundamentalGroups

universe u

private def completeOrthogonalIdempotentsAlgHom
    {R A ι : Type u} [CommRing R] [CommRing A] [Algebra R A] [Fintype ι]
    {e : ι → A} (he : CompleteOrthogonalIdempotents e) : (ι → R) →ₐ[R] A where
  __ := he.ringEquivOfComm.symm.toRingHom.comp
    (RingHom.pi fun i =>
      ((Pi.evalRingHom (fun j => (he.idem j).Corner) i).comp
        (he.ringEquivOfComm.toRingHom.comp (algebraMap R A))).comp
          (Pi.evalRingHom (fun _ : ι => R) i))
  commutes' r := by
    apply he.ringEquivOfComm.injective
    change he.ringEquivOfComm (he.ringEquivOfComm.symm _) = _
    rw [he.ringEquivOfComm.apply_symm_apply]
    rfl

private theorem completeOrthogonalIdempotentsAlgHom_single
    {R A ι : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [Fintype ι] [DecidableEq ι]
    {e : ι → A} (he : CompleteOrthogonalIdempotents e) (i : ι) :
    completeOrthogonalIdempotentsAlgHom (R := R) he (Pi.single i 1) = e i := by
  apply he.ringEquivOfComm.injective
  change he.ringEquivOfComm (he.ringEquivOfComm.symm _) = _
  rw [he.ringEquivOfComm.apply_symm_apply]
  funext j
  apply Subtype.ext
  change e j * algebraMap R A ((Pi.single i (1 : R) : ι → R) j) * e j = e j * e i * e j
  by_cases h : j = i
  · subst j
    simp only [Pi.single_eq_same, map_one, mul_one, (he.idem i).eq]
  · rw [Pi.single_eq_of_ne h, map_zero, mul_zero, zero_mul, he.ortho h, zero_mul]

/-- A finite complete orthogonal family after base change to a filtered
colimit already occurs at a stage. No finiteness hypothesis is imposed on
the fixed tensor factor, and each idempotent retains its given cocone image. -/
theorem exists_completeOrthogonalIdempotents_stage_of_filteredColimit
    {R : CommRingCat.{u}} {B : Type u} [CommRing B] [Algebra R B]
    {J : Type u} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ Under R) (c : Cocone F) (hc : IsColimit c)
    {ι : Type u} [Fintype ι]
    (e : ι → (c.pt ⊗[R] B)) (he : CompleteOrthogonalIdempotents e) :
    ∃ (i : J) (eᵢ : ι → (F.obj i ⊗[R] B)),
      CompleteOrthogonalIdempotents eᵢ ∧
        ∀ a, filteredTensorToColimitAlgHom c i (eᵢ a) = e a := by
  classical
  let f : (c.pt ⊗[R] (ι → R)) →ₐ[c.pt] (c.pt ⊗[R] B) :=
    AlgHom.liftEquiv R c.pt (ι → R) (c.pt ⊗[R] B)
      (completeOrthogonalIdempotentsAlgHom (R := R) he)
  obtain ⟨i, fᵢ, hcompat⟩ :=
    exists_tensorProduct_algHom_stage_of_filteredColimit
      (R := R) (B := ι → R) (D := B) F c hc f
  let gᵢ : (ι → R) →ₐ[R] (F.obj i ⊗[R] B) :=
    (fᵢ.restrictScalars R).comp Algebra.TensorProduct.includeRight
  refine ⟨i, fun a => gᵢ (Pi.single a 1), ?_, ?_⟩
  · exact (CompleteOrthogonalIdempotents.single (fun _ : ι => R)).map gᵢ.toRingHom
  · intro a
    have h := AlgHom.congr_fun hcompat ((1 : F.obj i) ⊗ₜ[R] Pi.single a 1)
    change filteredTensorToColimitAlgHom c i (gᵢ (Pi.single a 1)) =
      f (filteredTensorToColimitAlgHom c i ((1 : F.obj i) ⊗ₜ[R] Pi.single a 1)) at h
    rw [filteredTensorToColimitAlgHom_tmul, map_one] at h
    change filteredTensorToColimitAlgHom c i (gᵢ (Pi.single a 1)) =
      (AlgHom.liftEquiv R c.pt (ι → R) (c.pt ⊗[R] B)
        (completeOrthogonalIdempotentsAlgHom (R := R) he))
          ((1 : c.pt) ⊗ₜ[R] Pi.single a 1) at h
    rw [AlgHom.liftEquiv_tmul, one_smul, completeOrthogonalIdempotentsAlgHom_single] at h
    exact h

end EtaleFundamentalGroups
