/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Purity.Local.MaximalAdicCompletionMixedEqualizer
import SchemeTheory.RingTheory.Descent.ModuleBaseChangeHomExt

/-!
# Hom descent for mixed completion/localization data

The mixed module equalizer upgrades to full faithfulness on morphisms.  A
compatible tuple consists of a map after maximal-adic completion and one map
on every distinguished principal localization.  Compatibility is checked on
the canonical generators, and the mixed equalizer of the target descends
their images uniquely.
-/

noncomputable section

namespace EtaleFundamentalGroups

open IsLocalRing
open scoped TensorProduct

universe u v w

/-- The maximal-adic completion used by mixed formal gluing. -/
abbrev MaximalAdicCompletionRing
    (R : Type u) [CommRing R] [IsLocalRing R] :=
  AdicCompletion (maximalIdeal R) R

/-- The canonical finite generator index for the maximal ideal. -/
abbrev MaximalAdicCompletionMixedGeneratorIndex
    (R : Type u) [CommRing R] [IsLocalRing R] :=
  AlgebraicGeometry.Scheme.puncturedSpectrumGeneratorIndex R

/-- The maximal-ideal generator indexed by
`MaximalAdicCompletionMixedGeneratorIndex`. -/
abbrev maximalAdicCompletionMixedGenerator
    (R : Type u) [CommRing R] [IsLocalRing R]
    (i : MaximalAdicCompletionMixedGeneratorIndex R) : R :=
  AlgebraicGeometry.Scheme.puncturedSpectrumGenerator R i

/-- A completion component and one localized component for every generator
of the maximal ideal. -/
abbrev MaximalAdicCompletionMixedLinearMaps
    (R : Type u) [CommRing R] [IsLocalRing R]
    (M : Type v) [AddCommGroup M] [Module R M]
    (N : Type w) [AddCommGroup N] [Module R N] :=
  ((MaximalAdicCompletionRing R ⊗[R] M) →ₗ[MaximalAdicCompletionRing R]
      (MaximalAdicCompletionRing R ⊗[R] N)) ×
    ((i : MaximalAdicCompletionMixedGeneratorIndex R) →
      LocalizedModule (Submonoid.powers (maximalAdicCompletionMixedGenerator R i)) M →ₗ[
        Localization (Submonoid.powers (maximalAdicCompletionMixedGenerator R i))]
      LocalizedModule (Submonoid.powers (maximalAdicCompletionMixedGenerator R i)) N)

/-- Mixed component maps are compatible when the images of every canonical
generator form an element of the target mixed equalizer. -/
def maximalAdicCompletionMixedCompatibleLinearMaps
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (M : Type v) [AddCommGroup M] [Module R M]
    (N : Type w) [AddCommGroup N] [Module R N] :
    Submodule R (MaximalAdicCompletionMixedLinearMaps R M N) where
  carrier := {F | ∀ m : M,
    maximalAdicCompletionMixedLeft R N
        (F.1 (1 ⊗ₜ[R] m),
          fun i ↦ F.2 i (LocalizedModule.mk m 1)) =
      maximalAdicCompletionMixedRight R N
        (F.1 (1 ⊗ₜ[R] m),
          fun i ↦ F.2 i (LocalizedModule.mk m 1))}
  zero_mem' := by
    intro m
    change maximalAdicCompletionMixedLeft R N
        (0 : MaximalAdicCompletionMixedSource R N) =
      maximalAdicCompletionMixedRight R N 0
    simp
  add_mem' := by
    intro F G hF hG m
    change maximalAdicCompletionMixedLeft R N
        ((F.1 (1 ⊗ₜ[R] m), fun i ↦ F.2 i (LocalizedModule.mk m 1)) +
          (G.1 (1 ⊗ₜ[R] m), fun i ↦ G.2 i (LocalizedModule.mk m 1))) =
      maximalAdicCompletionMixedRight R N
        ((F.1 (1 ⊗ₜ[R] m), fun i ↦ F.2 i (LocalizedModule.mk m 1)) +
          (G.1 (1 ⊗ₜ[R] m), fun i ↦ G.2 i (LocalizedModule.mk m 1)))
    rw [map_add, map_add, hF m, hG m]
  smul_mem' := by
    intro r F hF m
    change maximalAdicCompletionMixedLeft R N
        (r • (F.1 (1 ⊗ₜ[R] m),
          fun i ↦ F.2 i (LocalizedModule.mk m 1))) =
      maximalAdicCompletionMixedRight R N
        (r • (F.1 (1 ⊗ₜ[R] m),
          fun i ↦ F.2 i (LocalizedModule.mk m 1)))
    rw [map_smul, map_smul, hF m]

/-- Base change and localization of a global map give compatible mixed
component maps. -/
def linearMapToMaximalAdicCompletionMixedCompatible
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (M : Type v) [AddCommGroup M] [Module R M]
    (N : Type w) [AddCommGroup N] [Module R N] :
    (M →ₗ[R] N) →ₗ[R]
      maximalAdicCompletionMixedCompatibleLinearMaps R M N where
  toFun f := ⟨
    (f.baseChange (MaximalAdicCompletionRing R),
      fun i ↦ LocalizedModule.map
        (Submonoid.powers (maximalAdicCompletionMixedGenerator R i)) f), by
      intro m
      let y : MaximalAdicCompletionMixedSource R N :=
        (f.baseChange (MaximalAdicCompletionRing R) (1 ⊗ₜ[R] m),
          fun i ↦ LocalizedModule.map
            (Submonoid.powers (maximalAdicCompletionMixedGenerator R i)) f
              (LocalizedModule.mk m 1))
      have hy : y =
          (maximalAdicCompletionMixedEqualizerMap R N (f m)).1 := by
        apply Prod.ext
        · simp [y]
        · funext i
          simp [y]
      change maximalAdicCompletionMixedLeft R N y =
        maximalAdicCompletionMixedRight R N y
      rw [hy]
      exact (maximalAdicCompletionMixedEqualizerMap R N (f m)).2⟩
  map_add' f g := by
    apply Subtype.ext
    apply Prod.ext
    · exact LinearMap.baseChange_add f g
    · funext i
      exact (LocalizedModule.map
        (Submonoid.powers (maximalAdicCompletionMixedGenerator R i))).map_add f g
  map_smul' r f := by
    apply Subtype.ext
    apply Prod.ext
    · exact LinearMap.baseChange_smul r f
    · funext i
      exact (LocalizedModule.map
        (Submonoid.powers (maximalAdicCompletionMixedGenerator R i))).map_smul r f

@[simp]
theorem linearMapToMaximalAdicCompletionMixedCompatible_completion
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (M : Type v) [AddCommGroup M] [Module R M]
    (N : Type w) [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) :
    (linearMapToMaximalAdicCompletionMixedCompatible R M N f).1.1 =
      f.baseChange (MaximalAdicCompletionRing R) :=
  rfl

@[simp]
theorem linearMapToMaximalAdicCompletionMixedCompatible_localization
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (M : Type v) [AddCommGroup M] [Module R M]
    (N : Type w) [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (i : MaximalAdicCompletionMixedGeneratorIndex R) :
    (linearMapToMaximalAdicCompletionMixedCompatible R M N f).1.2 i =
      LocalizedModule.map (Submonoid.powers (maximalAdicCompletionMixedGenerator R i)) f :=
  rfl

/-- Mixed maximal-completion and principal-localization data are fully
faithful on module homomorphisms. -/
noncomputable def maximalAdicCompletionMixedLinearMapDescentEquiv
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (M : Type v) [AddCommGroup M] [Module R M]
    (N : Type w) [AddCommGroup N] [Module R N] :
    (M →ₗ[R] N) ≃ₗ[R]
      maximalAdicCompletionMixedCompatibleLinearMaps R M N :=
  LinearEquiv.ofBijective
    (linearMapToMaximalAdicCompletionMixedCompatible R M N) <| by
    let : Module.FaithfullyFlat R (MaximalAdicCompletionRing R) :=
      maximalAdicCompletion_faithfullyFlat R
    constructor
    · intro f g hfg
      apply LinearMap.ext
      intro m
      apply Module.FaithfullyFlat.tensorProduct_mk_injective
        (A := R) (B := MaximalAdicCompletionRing R) N
      have hcompletion := congrArg (fun F ↦ F.1.1) hfg
      have hm := DFunLike.congr_fun hcompletion (1 ⊗ₜ[R] m)
      simpa using hm
    · rintro ⟨F, hF⟩
      let pairMap : M →ₗ[R] MaximalAdicCompletionMixedSource R N :=
        ((F.1.restrictScalars R).comp
          (TensorProduct.mk R (MaximalAdicCompletionRing R) M 1)).prod <|
          LinearMap.pi fun i ↦
            ((F.2 i).restrictScalars R).comp
              (LocalizedModule.mkLinearMap
                (Submonoid.powers (maximalAdicCompletionMixedGenerator R i)) M)
      let lift : M →ₗ[R] LinearMap.eqLocus
          (maximalAdicCompletionMixedLeft R N)
          (maximalAdicCompletionMixedRight R N) :=
        LinearMap.codRestrict _ pairMap (by
          intro m
          change maximalAdicCompletionMixedLeft R N
              (F.1 (1 ⊗ₜ[R] m),
                fun i ↦ F.2 i (LocalizedModule.mk m 1)) =
            maximalAdicCompletionMixedRight R N
              (F.1 (1 ⊗ₜ[R] m),
                fun i ↦ F.2 i (LocalizedModule.mk m 1))
          exact hF m)
      let e := maximalAdicCompletionMixedEqualizerEquiv R N
      let f : M →ₗ[R] N := e.symm.toLinearMap.comp lift
      have hpair (m : M) :
          (1 ⊗ₜ[R] f m,
              fun i ↦ LocalizedModule.mk (f m) 1) =
            (F.1 (1 ⊗ₜ[R] m),
              fun i ↦ F.2 i (LocalizedModule.mk m 1)) := by
        have he := congrArg Subtype.val (e.apply_symm_apply (lift m))
        have he' :
            (e (e.symm (lift m)) :
                MaximalAdicCompletionMixedSource R N) =
              (lift m).1 := he
        rw [maximalAdicCompletionMixedEqualizerEquiv_apply] at he'
        have hlift :
            ((lift m).1 : MaximalAdicCompletionMixedSource R N) =
              (F.1 (1 ⊗ₜ[R] m),
                fun i ↦ F.2 i (LocalizedModule.mk m 1)) := by
          rfl
        change
          (1 ⊗ₜ[R] e.symm (lift m),
              fun i ↦ LocalizedModule.mk (e.symm (lift m)) 1) =
            (F.1 (1 ⊗ₜ[R] m),
              fun i ↦ F.2 i (LocalizedModule.mk m 1))
        exact he'.trans hlift
      refine ⟨f, ?_⟩
      apply Subtype.ext
      apply Prod.ext
      · apply tensorProduct_linearMap_ext_of_one_tmul
        intro m
        simpa using congrArg Prod.fst (hpair m)
      · funext i
        apply localizedModule_linearMap_ext_of_mk_one
        intro m
        simpa using congrArg (fun p ↦ p.2 i) (hpair m)

@[simp]
theorem maximalAdicCompletionMixedLinearMapDescentEquiv_apply
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (M : Type v) [AddCommGroup M] [Module R M]
    (N : Type w) [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) :
    maximalAdicCompletionMixedLinearMapDescentEquiv R M N f =
      linearMapToMaximalAdicCompletionMixedCompatible R M N f :=
  rfl

@[simp]
theorem maximalAdicCompletionMixedLinearMapDescentEquiv_symm_completion
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (M : Type v) [AddCommGroup M] [Module R M]
    (N : Type w) [AddCommGroup N] [Module R N]
    (F : maximalAdicCompletionMixedCompatibleLinearMaps R M N) :
    ((maximalAdicCompletionMixedLinearMapDescentEquiv R M N).symm F).baseChange
        (MaximalAdicCompletionRing R) =
      F.1.1 := by
  change
    (linearMapToMaximalAdicCompletionMixedCompatible R M N
      ((maximalAdicCompletionMixedLinearMapDescentEquiv R M N).symm F)).1.1 =
        F.1.1
  exact congrArg (fun G ↦ G.1.1)
    ((maximalAdicCompletionMixedLinearMapDescentEquiv R M N).apply_symm_apply F)

@[simp]
theorem maximalAdicCompletionMixedLinearMapDescentEquiv_symm_localization
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (M : Type v) [AddCommGroup M] [Module R M]
    (N : Type w) [AddCommGroup N] [Module R N]
    (F : maximalAdicCompletionMixedCompatibleLinearMaps R M N)
    (i : MaximalAdicCompletionMixedGeneratorIndex R) :
    LocalizedModule.map (Submonoid.powers (maximalAdicCompletionMixedGenerator R i))
        ((maximalAdicCompletionMixedLinearMapDescentEquiv R M N).symm F) =
      F.1.2 i := by
  change
    (linearMapToMaximalAdicCompletionMixedCompatible R M N
      ((maximalAdicCompletionMixedLinearMapDescentEquiv R M N).symm F)).1.2 i =
        F.1.2 i
  exact congrArg (fun G ↦ G.1.2 i)
    ((maximalAdicCompletionMixedLinearMapDescentEquiv R M N).apply_symm_apply F)

end EtaleFundamentalGroups

end
