/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Purity.Local.MaximalAdicCompletionMixedHomDescent

/-!
# Bilinear descent for mixed completion/localization data

Bilinear maps are linearized on the tensor product and then descended by the
mixed Hom full-faithfulness theorem.  Thus a compatible completion component
and compatible principal-localization components determine a unique global
bilinear map.
-/

noncomputable section

namespace EtaleFundamentalGroups

open IsLocalRing
open scoped TensorProduct

universe u v w x

/-- Tensor-linearized mixed completion/localization data for a bilinear map. -/
abbrev MaximalAdicCompletionMixedCompatibleBilinearMaps
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (M : Type v) [AddCommGroup M] [Module R M]
    (N : Type w) [AddCommGroup N] [Module R N]
    (P : Type x) [AddCommGroup P] [Module R P] :=
  maximalAdicCompletionMixedCompatibleLinearMaps R (M ⊗[R] N) P

/-- A global bilinear map gives tensor-linearized maps on the completion and
on every distinguished principal localization. -/
def bilinearMapToMaximalAdicCompletionMixedCompatible
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (M : Type v) [AddCommGroup M] [Module R M]
    (N : Type w) [AddCommGroup N] [Module R N]
    (P : Type x) [AddCommGroup P] [Module R P] :
    (M →ₗ[R] N →ₗ[R] P) →ₗ[R]
      MaximalAdicCompletionMixedCompatibleBilinearMaps R M N P :=
  (linearMapToMaximalAdicCompletionMixedCompatible R (M ⊗[R] N) P).comp
    (TensorProduct.lift.equiv (RingHom.id R) M N P).toLinearMap

@[simp]
theorem bilinearMapToMaximalAdicCompletionMixedCompatible_completion
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (M : Type v) [AddCommGroup M] [Module R M]
    (N : Type w) [AddCommGroup N] [Module R N]
    (P : Type x) [AddCommGroup P] [Module R P]
    (f : M →ₗ[R] N →ₗ[R] P) :
    (bilinearMapToMaximalAdicCompletionMixedCompatible R M N P f).1.1 =
      (TensorProduct.lift f).baseChange (MaximalAdicCompletionRing R) :=
  rfl

@[simp]
theorem bilinearMapToMaximalAdicCompletionMixedCompatible_localization
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (M : Type v) [AddCommGroup M] [Module R M]
    (N : Type w) [AddCommGroup N] [Module R N]
    (P : Type x) [AddCommGroup P] [Module R P]
    (f : M →ₗ[R] N →ₗ[R] P)
    (i : MaximalAdicCompletionMixedGeneratorIndex R) :
    (bilinearMapToMaximalAdicCompletionMixedCompatible R M N P f).1.2 i =
      LocalizedModule.map
        (Submonoid.powers (maximalAdicCompletionMixedGenerator R i))
        (TensorProduct.lift f) :=
  rfl

/-- Mixed completion and principal-localization data are fully faithful on
bilinear maps, after the canonical tensor-product linearization. -/
noncomputable def maximalAdicCompletionMixedBilinearMapDescentEquiv
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (M : Type v) [AddCommGroup M] [Module R M]
    (N : Type w) [AddCommGroup N] [Module R N]
    (P : Type x) [AddCommGroup P] [Module R P] :
    (M →ₗ[R] N →ₗ[R] P) ≃ₗ[R]
      MaximalAdicCompletionMixedCompatibleBilinearMaps R M N P :=
  (TensorProduct.lift.equiv (RingHom.id R) M N P).trans
    (maximalAdicCompletionMixedLinearMapDescentEquiv R (M ⊗[R] N) P)

@[simp]
theorem maximalAdicCompletionMixedBilinearMapDescentEquiv_apply
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (M : Type v) [AddCommGroup M] [Module R M]
    (N : Type w) [AddCommGroup N] [Module R N]
    (P : Type x) [AddCommGroup P] [Module R P]
    (f : M →ₗ[R] N →ₗ[R] P) :
    maximalAdicCompletionMixedBilinearMapDescentEquiv R M N P f =
      bilinearMapToMaximalAdicCompletionMixedCompatible R M N P f :=
  rfl

@[simp]
theorem maximalAdicCompletionMixedBilinearMapDescentEquiv_symm_completion
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (M : Type v) [AddCommGroup M] [Module R M]
    (N : Type w) [AddCommGroup N] [Module R N]
    (P : Type x) [AddCommGroup P] [Module R P]
    (F : MaximalAdicCompletionMixedCompatibleBilinearMaps R M N P) :
    (TensorProduct.lift
        ((maximalAdicCompletionMixedBilinearMapDescentEquiv R M N P).symm F)).baseChange
          (MaximalAdicCompletionRing R) =
      F.1.1 := by
  let eTensor := TensorProduct.lift.equiv (RingHom.id R) M N P
  let eMixed := maximalAdicCompletionMixedLinearMapDescentEquiv R (M ⊗[R] N) P
  have huncurry :
      TensorProduct.lift (eTensor.symm (eMixed.symm F)) = eMixed.symm F :=
    eTensor.apply_symm_apply (eMixed.symm F)
  change (TensorProduct.lift (eTensor.symm (eMixed.symm F))).baseChange
      (MaximalAdicCompletionRing R) = F.1.1
  rw [huncurry]
  exact maximalAdicCompletionMixedLinearMapDescentEquiv_symm_completion
    R (M ⊗[R] N) P F

@[simp]
theorem maximalAdicCompletionMixedBilinearMapDescentEquiv_symm_localization
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (M : Type v) [AddCommGroup M] [Module R M]
    (N : Type w) [AddCommGroup N] [Module R N]
    (P : Type x) [AddCommGroup P] [Module R P]
    (F : MaximalAdicCompletionMixedCompatibleBilinearMaps R M N P)
    (i : MaximalAdicCompletionMixedGeneratorIndex R) :
    LocalizedModule.map
        (Submonoid.powers (maximalAdicCompletionMixedGenerator R i))
        (TensorProduct.lift
          ((maximalAdicCompletionMixedBilinearMapDescentEquiv R M N P).symm F)) =
      F.1.2 i := by
  let eTensor := TensorProduct.lift.equiv (RingHom.id R) M N P
  let eMixed := maximalAdicCompletionMixedLinearMapDescentEquiv R (M ⊗[R] N) P
  have huncurry :
      TensorProduct.lift (eTensor.symm (eMixed.symm F)) = eMixed.symm F :=
    eTensor.apply_symm_apply (eMixed.symm F)
  change LocalizedModule.map
      (Submonoid.powers (maximalAdicCompletionMixedGenerator R i))
      (TensorProduct.lift (eTensor.symm (eMixed.symm F))) = F.1.2 i
  rw [huncurry]
  exact maximalAdicCompletionMixedLinearMapDescentEquiv_symm_localization
    R (M ⊗[R] N) P F i

end EtaleFundamentalGroups

end
