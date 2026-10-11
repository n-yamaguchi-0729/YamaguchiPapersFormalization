/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_ModulesTildePullback.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Affine pullback and associated module sheaves

Compares pullback of an associated module sheaf with extension of scalars.
-/

universe u

open CategoryTheory AlgebraicGeometry Opposite

noncomputable section

namespace AlgebraicGeometry

variable {R S : CommRingCat.{u}} (φ : R ⟶ S)


/-- Global sections of pushforward along Spec.map agree with restriction of scalars. -/
def Scheme.Modules.pushforwardSpecCompΓIso :
    Scheme.Modules.pushforward (Spec.map φ) ⋙ moduleSpecΓFunctor (R := R) ≅
      moduleSpecΓFunctor (R := S) ⋙ ModuleCat.restrictScalars φ.hom :=
  NatIso.ofComponents
    (fun N =>
      have nativeIso {T : Type u} [CommRing T] (L P : ModuleCat.{u} T)
          (e : L ≃ₗ[T] P) : L ≅ P := LinearEquiv.toModuleIso e
      nativeIso
      ((Scheme.Modules.pushforward (Spec.map φ) ⋙ moduleSpecΓFunctor (R := R)).obj N)
      ((moduleSpecΓFunctor (R := S) ⋙ ModuleCat.restrictScalars φ.hom).obj N)
      { __ := AddEquiv.refl _
        map_smul' := fun r m => by
          change (ModuleCat.restrictScalars (StructureSheaf.globalSectionsIso R).hom.hom).obj _ at m
          erw [ModuleCat.restrictScalars.smul_def, ModuleCat.restrictScalars.smul_def]
          erw [ModuleCat.restrictScalars.smul_def, ModuleCat.restrictScalars.smul_def]
          simp only [AddEquiv.toFun_eq_coe, RingHom.id_apply]
          have h1 : (Limits.initialOpOfTerminal Limits.isTerminalTop).to (op ⊤) =
              𝟙 (op (⊤ : (Spec (.of R)).Opens)) :=
            (Limits.initialOpOfTerminal Limits.isTerminalTop).hom_ext _ _
          have h2 : (Limits.initialOpOfTerminal Limits.isTerminalTop).to (op ⊤) =
              𝟙 (op (⊤ : (Spec (.of S)).Opens)) :=
            (Limits.initialOpOfTerminal Limits.isTerminalTop).hom_ext _ _
          simp only [h1, h2, CategoryTheory.Functor.map_id, RingCat.hom_id, RingHom.id_apply]
          have key := congrArg (fun ψ : R ⟶ Γ(Spec S, ⊤) => ψ.hom r)
            (Scheme.ΓSpecIso_inv_naturality φ)
          have hcoeff : (Spec.map φ).appTop.hom ((Scheme.ΓSpecIso R).inv.hom r) =
              (Scheme.ΓSpecIso S).inv.hom (φ.hom r) := key.symm
          exact congrArg (fun a : Γ(Spec S, ⊤) => a • (show Γ(N, ⊤) from m)) hcoeff })
    (fun f => by ext; rfl)

/-- The natural comparison between pulling back an associated module sheaf and extending scalars. -/
def tilde.functorCompPullbackSpecIso :
    tilde.functor R ⋙ Scheme.Modules.pullback (Spec.map φ) ≅
      ModuleCat.extendScalars φ.hom ⋙ tilde.functor S :=
  Adjunction.leftAdjointUniq
    ((tilde.adjunction (R := R)).comp (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)))
    (((ModuleCat.extendRestrictScalarsAdj φ.hom).comp (tilde.adjunction (R := S))).ofNatIsoRight
      (Scheme.Modules.pushforwardSpecCompΓIso φ).symm)

/-- The comparison between the pullback of an associated module sheaf and the sheaf of the
  scalar extension. -/
def tilde.pullbackSpecIso (M : ModuleCat.{u} R) :
    (Scheme.Modules.pullback (Spec.map φ)).obj (tilde M) ≅
      tilde ((ModuleCat.extendScalars φ.hom).obj M) :=
  (tilde.functorCompPullbackSpecIso φ).app M

@[simp] theorem tilde.functorCompPullbackSpecIso_app (M : ModuleCat.{u} R) :
    (tilde.functorCompPullbackSpecIso φ).app M = tilde.pullbackSpecIso φ M := rfl

theorem tilde.pullbackSpecIso_hom_naturality {M M' : ModuleCat.{u} R} (f : M ⟶ M') :
    (Scheme.Modules.pullback (Spec.map φ)).map ((tilde.functor R).map f) ≫
        (tilde.pullbackSpecIso φ M').hom =
      (tilde.pullbackSpecIso φ M).hom ≫ (tilde.functor S).map ((ModuleCat.extendScalars
        φ.hom).map f) :=
  (tilde.functorCompPullbackSpecIso φ).hom.naturality f

end AlgebraicGeometry

end
