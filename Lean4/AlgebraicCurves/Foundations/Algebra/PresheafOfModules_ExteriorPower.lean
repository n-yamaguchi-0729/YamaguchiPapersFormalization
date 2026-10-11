/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_PresheafOfModules_ExteriorPower.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Algebra.Category.ModuleCat.Presheaf
import Mathlib.LinearAlgebra.ExteriorPower.Basic

/-!
# Exterior powers of module presheaves

Constructs exterior powers of module presheaves and the maps induced by module morphisms.
-/

universe u

open CategoryTheory
namespace PresheafOfModules

variable {C : Type*} [Category C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}

namespace ExteriorPower

variable (n : ℕ) (M : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))

section map
variable {X Y : Cᵒᵖ} (f : X ⟶ Y)

/-- Restrict a module action along the structure-presheaf restriction homomorphism. -/
@[reducible] noncomputable def moduleAlong (R : Cᵒᵖ ⥤ CommRingCat.{u}) {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (N : Type u) [AddCommGroup N] [Module (R.obj Y) N] : Module (R.obj X) N :=
  Module.compHom N (R.map f).hom

/-- The original module restriction map viewed as linear over the source ring. -/
noncomputable def mapAlong :
    letI := moduleAlong R f (M.obj Y)
    M.obj X →ₗ[R.obj X] M.obj Y :=
  letI := moduleAlong R f (M.obj Y)
  { toFun := fun x => (M.map f x : M.obj Y)
    map_add' := fun x y => map_add _ x y
    map_smul' := fun r x => M.map_smul f r x }

/-- The canonical exterior generator map viewed over the source ring by restriction of scalars. -/
noncomputable def ιMultiAlong :
    letI := moduleAlong R f (M.obj Y); letI := moduleAlong R f (⋀[R.obj Y]^n (M.obj Y))
    (M.obj Y) [⋀^Fin n]→ₗ[R.obj X] (⋀[R.obj Y]^n (M.obj Y)) :=
  letI := moduleAlong R f (M.obj Y); letI := moduleAlong R f (⋀[R.obj Y]^n (M.obj Y))
  { toFun := exteriorPower.ιMulti (R.obj Y) n
    map_update_add' := fun v i x y => (exteriorPower.ιMulti (R.obj Y) n).map_update_add v i x y
    map_update_smul' := fun v i r x => by
      change exteriorPower.ιMulti (R.obj Y) n (Function.update v i (R.map f r • x)) =
        R.map f r • exteriorPower.ιMulti (R.obj Y) n (Function.update v i x)
      exact (exteriorPower.ιMulti (R.obj Y) n).map_update_smul v i (R.map f r) x
    map_eq_zero_of_eq' := fun v _ _ h hij => (exteriorPower.ιMulti (R.obj Y)
      n).map_eq_zero_of_eq v h hij }

/-- The linear restriction map on exterior powers induced by the module restriction map. -/
noncomputable def mapₗ :
    letI := moduleAlong R f (⋀[R.obj Y]^n (M.obj Y))
    ⋀[R.obj X]^n (M.obj X) →ₗ[R.obj X] ⋀[R.obj Y]^n (M.obj Y) :=
  letI := moduleAlong R f (M.obj Y); letI := moduleAlong R f (⋀[R.obj Y]^n (M.obj Y))
  exteriorPower.alternatingMapLinearEquiv ((ιMultiAlong n M f).compLinearMap (mapAlong M f))

lemma mapₗ_ιMulti (m : Fin n → M.obj X) :
    mapₗ n M f (exteriorPower.ιMulti (R.obj X) n m) = exteriorPower.ιMulti (R.obj Y) n (M :=
      M.obj Y) (fun i => M.map f (m i)) := by
  let := moduleAlong R f (M.obj Y); let := moduleAlong R f (⋀[R.obj Y]^n (M.obj Y))
  simp only [mapₗ, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
    AlternatingMap.compLinearMap_apply]
  rfl

lemma mapₗ_smul (r : R.obj X) (x : ⋀[R.obj X]^n (M.obj X)) :
    mapₗ n M f (r • x) = R.map f r • mapₗ n M f x := by
  let := moduleAlong R f (⋀[R.obj Y]^n (M.obj Y))
  exact (mapₗ n M f).map_smul r x

end map

lemma addMonoidHom_ext {X : Cᵒᵖ} {N : Type*} [AddCommGroup N] {φ ψ : ⋀[R.obj X]^n (M.obj X) →+ N}
    (hsmul : ∀ (r : R.obj X) x, φ x = ψ x → φ (r • x) = ψ (r • x))
    (h : ∀ m : Fin n → M.obj X, φ (exteriorPower.ιMulti (R.obj X) n m) = ψ (exteriorPower.ιMulti
      (R.obj X) n m)) :
    φ = ψ := by
  ext x
  have hx : x ∈ Submodule.span (R.obj X) (Set.range (exteriorPower.ιMulti (R.obj X) n (M :=
    M.obj X))) := by
    rw [exteriorPower.ιMulti_span]; trivial
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨m, rfl⟩ := hx; exact h m
  | zero => simp only [map_zero]
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul r x _ hx => exact hsmul r x hx

/-- The additive presheaf of pointwise exterior powers. -/
noncomputable def presheafAb : Cᵒᵖ ⥤ Ab.{u} where
  obj X := AddCommGrpCat.of (⋀[R.obj X]^n (M.obj X))
  map {X Y} f := AddCommGrpCat.ofHom (letI := moduleAlong R f (⋀[R.obj Y]^n (M.obj Y)); (mapₗ n
    M f).toAddMonoidHom)
  map_id X := by
    ext1
    refine addMonoidHom_ext n M (fun r x hx => ?_) (fun m => ?_)
    · change mapₗ n M (𝟙 X) (r • x) = r • x
      rw [mapₗ_smul, R.map_id]; exact congrArg (r • ·) hx
    · change mapₗ n M (𝟙 X) _ = exteriorPower.ιMulti (R.obj X) n m
      rw [mapₗ_ιMulti]
      congr 1; funext i
      rw [M.map_id]
      rfl
  map_comp {X Y Z} f g := by
    ext1
    refine addMonoidHom_ext n M (fun r x hx => ?_) (fun m => ?_)
    · change mapₗ n M (f ≫ g) (r • x) = mapₗ n M g (mapₗ n M f (r • x))
      rw [mapₗ_smul, mapₗ_smul, mapₗ_smul, R.map_comp]; exact congrArg (_ • ·) hx
    · change mapₗ n M (f ≫ g) _ = mapₗ n M g (mapₗ n M f _)
      erw [mapₗ_ιMulti, mapₗ_ιMulti, mapₗ_ιMulti]
      congr 1; funext i
      exact M.map_comp_apply f g (m i)

/-- The pointwise exterior-power module action on the additive presheaf. -/
noncomputable instance instModulePresheafAb (X : Cᵒᵖ) :
    Module ((R ⋙ forget₂ CommRingCat RingCat).obj X) ((presheafAb n M).obj X) :=
  inferInstanceAs (Module (R.obj X) (⋀[R.obj X]^n (M.obj X)))

end ExteriorPower

/-- The presheaf of modules obtained by taking exterior powers at each object. -/
noncomputable def exteriorPower (n : ℕ) (M : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat
  RingCat)) :
    PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat) :=
  @ofPresheaf C _ (R ⋙ forget₂ CommRingCat RingCat) (ExteriorPower.presheafAb n M)
    (fun X => ExteriorPower.instModulePresheafAb n M X)
    (fun _ _ f r x => by
      change ExteriorPower.mapₗ n M f (r • x) = R.map f r • ExteriorPower.mapₗ n M f x
      exact ExteriorPower.mapₗ_smul n M f r x)

@[simp] lemma exteriorPower_map_ιMulti (n : ℕ) (M : PresheafOfModules.{u} (R ⋙ forget₂
  CommRingCat RingCat))
    {X Y : Cᵒᵖ} (f : X ⟶ Y) (m : Fin n → M.obj X) :
    ((exteriorPower n M).map f (show (exteriorPower n M).obj X from exteriorPower.ιMulti (R.obj
      X) n m) :
        ⋀[R.obj Y]^n (M.obj Y)) = exteriorPower.ιMulti (R.obj Y) n (M := M.obj Y) (fun i =>
          M.map f (m i)) :=
  ExteriorPower.mapₗ_ιMulti n M f m

end PresheafOfModules

namespace PresheafOfModules

variable {C : Type*} [Category C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}

namespace ExteriorPower

variable (n : ℕ) {M N P : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)}

/-- A component of a module-presheaf morphism viewed over the corresponding commutative ring. -/
noncomputable def appₗ (φ : M ⟶ N) (X : Cᵒᵖ) : M.obj X →ₗ[R.obj X] N.obj X where
  toFun x := φ.app X x
  map_add' x y := map_add (φ.app X).hom x y
  map_smul' r x := (φ.app X).hom.map_smul r x

@[simp] lemma appₗ_apply (φ : M ⟶ N) (X : Cᵒᵖ) (x : M.obj X) : appₗ φ X x = φ.app X x := rfl

lemma appₗ_id (X : Cᵒᵖ) : appₗ (𝟙 M) X = LinearMap.id := rfl

lemma appₗ_comp (φ : M ⟶ N) (ψ : N ⟶ P) (X : Cᵒᵖ) :
    appₗ (φ ≫ ψ) X = appₗ ψ X ∘ₗ appₗ φ X := rfl

/-- The additive-presheaf morphism induced on pointwise exterior powers. -/
noncomputable def mapAb (φ : M ⟶ N) : presheafAb n M ⟶ presheafAb n N where
  app X := AddCommGrpCat.ofHom (exteriorPower.map n (appₗ φ X)).toAddMonoidHom
  naturality {X Y} f := by
    ext1
    refine addMonoidHom_ext n M (fun r x hx => ?_) (fun m => ?_)
    · change exteriorPower.map n (appₗ φ Y) (mapₗ n M f x) =
        mapₗ n N f (exteriorPower.map n (appₗ φ X) x) at hx
      change exteriorPower.map n (appₗ φ Y) (mapₗ n M f (r • x)) =
        mapₗ n N f (exteriorPower.map n (appₗ φ X) (r • x))
      rw [mapₗ_smul, map_smul, map_smul, mapₗ_smul]
      exact congrArg (R.map f r • ·) hx
    · change exteriorPower.map n (appₗ φ Y) (mapₗ n M f (exteriorPower.ιMulti _ n m)) =
        mapₗ n N f (exteriorPower.map n (appₗ φ X) (exteriorPower.ιMulti _ n m))
      have h₁ := mapₗ_ιMulti n M f m
      have h₂ := exteriorPower.map_apply_ιMulti (appₗ φ Y)
        (fun i => (M.map f (m i) : M.obj Y))
      have h₃ := exteriorPower.map_apply_ιMulti (appₗ φ X) m
      have h₄ := mapₗ_ιMulti n N f (fun i => appₗ φ X (m i))
      let onY : (⋀[R.obj Y]^n (M.obj Y)) → (⋀[R.obj Y]^n (N.obj Y)) :=
        fun z => exteriorPower.map n (appₗ φ Y) z
      let onN : (⋀[R.obj X]^n (N.obj X)) → (⋀[R.obj Y]^n (N.obj Y)) :=
        fun z => mapₗ n N f z
      have hm : (fun i => (appₗ φ Y (M.map f (m i) : M.obj Y) : N.obj Y)) =
          (fun i => (N.map f (appₗ φ X (m i)) : N.obj Y)) := by
        funext i
        exact naturality_apply φ f (m i)
      have hgen := congrArg (fun v : Fin n → N.obj Y => exteriorPower.ιMulti (R.obj Y) n v) hm
      have ha := congrArg onY h₁
      have hb := congrArg onN h₃
      exact ha.trans (h₂.trans (hgen.trans (h₄.symm.trans hb.symm)))

end ExteriorPower

/-- The module-presheaf morphism induced by a morphism on exterior powers. -/
noncomputable def exteriorPowerMap (n : ℕ) {M N : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat
  RingCat)}
    (φ : M ⟶ N) : exteriorPower n M ⟶ exteriorPower n N :=
  homMk (ExteriorPower.mapAb n φ) (fun X r m =>
    (exteriorPower.map n (ExteriorPower.appₗ φ X)).map_smul (show R.obj X from r) m)

lemma exteriorPowerMap_app_apply (n : ℕ) {M N : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat
  RingCat)}
    (φ : M ⟶ N) (X : Cᵒᵖ) (x : ⋀[R.obj X]^n (M.obj X)) :
    ((exteriorPowerMap n φ).app X (show (exteriorPower n M).obj X from x) : ⋀[R.obj X]^n (N.obj
      X)) =
      exteriorPower.map n (ExteriorPower.appₗ φ X) x := rfl

lemma exteriorPowerMap_app_ιMulti (n : ℕ) {M N : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat
  RingCat)}
    (φ : M ⟶ N) (X : Cᵒᵖ) (m : Fin n → M.obj X) :
    ((exteriorPowerMap n φ).app X (show (exteriorPower n M).obj X from exteriorPower.ιMulti
      (R.obj X) n m) :
      ⋀[R.obj X]^n (N.obj X)) = exteriorPower.ιMulti (R.obj X) n (fun i => φ.app X (m i)) :=
  exteriorPower.map_apply_ιMulti (R := R.obj X) _ _

variable (R) in
/-- The endofunctor taking each module presheaf and morphism to its exterior power. -/
noncomputable def exteriorPowerFunctor (n : ℕ) :
    PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat) ⥤
      PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat) where
  obj M := exteriorPower n M
  map φ := exteriorPowerMap n φ
  map_id M := by
    ext X : 1
    ext1
    refine LinearMap.ext fun x => ?_
    change exteriorPower.map n (ExteriorPower.appₗ (𝟙 M) X) x = x
    rw [ExteriorPower.appₗ_id, exteriorPower.map_id]
    rfl
  map_comp φ ψ := by
    ext X : 1
    ext1
    refine LinearMap.ext fun x => ?_
    change exteriorPower.map n (ExteriorPower.appₗ (φ ≫ ψ) X) x =
      exteriorPower.map n (ExteriorPower.appₗ ψ X) (exteriorPower.map n (ExteriorPower.appₗ φ X) x)
    rw [ExteriorPower.appₗ_comp, exteriorPower.map_comp]
    rfl

end PresheafOfModules
