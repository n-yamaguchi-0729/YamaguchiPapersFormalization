/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.FiniteNormalizationInertiaLift
import EtaleFundamentalGroups.Inertia.CommAlgInertiaRingMaps
import EtaleFundamentalGroups.Inertia.OriginalNormalizationInertiaAction

/-!
# Native finite-field lifts of normalization inertia

Constructs an original finite-field inertia element whose coefficient ring map is the prescribed
intrinsic normalization inertia map.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v w

attribute [local instance] normalizationInertiaImageAction

/-- The proved field extension constructs a native original inertia element
with exactly the given intrinsic coefficient RingHom. -/
theorem finiteNormalization_inertia_exists_native_lift
    (A : Type u) (K : Type v) (F : Type w)
    [CommRing A] [Field K] [Field F]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K F] [Algebra A F] [IsScalarTower A K F]
    [IsGalois K F] [FiniteDimensional K F]
    (Q : Ideal (normalizationCommAlgCat A F))
    (τ : commAlgIdealInertiaGroup A (normalizationCommAlgCat A F) Q) :
    ∃ σ : actualNormalizationInertiaGroup A K F Q,
      normalizationGaloisRingHom A K F (actualNormalizationInertiaElement A K F Q σ) =
        commAlgIdealInertiaRingHom A (normalizationCommAlgCat A F) Q τ := by
  have hτ : ∀ b : integralClosure A F,
      Sub.sub (α := integralClosure A F)
        ((τ.val.toRingHom : integralClosure A F →+* integralClosure A F).toFun b) b ∈ Q :=
    τ.property
  obtain ⟨σ, hσ, hcoeff⟩ :=
    finiteNormalization_inertia_exists_field_lift A K F Q τ.val hτ
  refine ⟨⟨σ, hσ⟩, ?_⟩
  change ((σ.restrictScalars A).mapIntegralClosure).toRingHom = τ.val.toRingHom
  exact congrArg
    (fun f : integralClosure A F ≃ₐ[A] integralClosure A F => f.toRingHom) hcoeff

end EtaleFundamentalGroups.Inertia
