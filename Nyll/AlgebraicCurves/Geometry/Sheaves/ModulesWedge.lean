/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_ModulesWedge.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Foundations.Algebra.PresheafOfModules_ExteriorPower
import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesDet
import Nyll.SchemeTheory.Modules.Monoidal

/-!
# Exterior multiplication for module sheaves

Exterior-algebra multiplication by a vector induces natural maps on module presheaves
and module sheaves through sheafification.
-/

universe u

open CategoryTheory MonoidalCategory

namespace exteriorPower

variable (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M] (a b : ℕ)

/-- The exterior-algebra product as a bilinear map between the specified homogeneous degrees. -/
noncomputable def mulₗ : ⋀[R]^a M →ₗ[R] ⋀[R]^b M →ₗ[R] ⋀[R]^(a + b) M :=
  LinearMap.mk₂ R (fun x y => ⟨x.1 * y.1, SetLike.mul_mem_graded x.2 y.2⟩)
    (fun x x' y => Subtype.ext (add_mul x.1 x'.1 y.1))
    (fun r x y => Subtype.ext (smul_mul_assoc r x.1 y.1))
    (fun x y y' => Subtype.ext (mul_add x.1 y.1 y'.1))
    (fun r x y => Subtype.ext (mul_smul_comm r x.1 y.1))

@[simp] lemma mulₗ_apply_coe (x : ⋀[R]^a M) (y : ⋀[R]^b M) :
    ((mulₗ R M a b x y : ⋀[R]^(a + b) M) : ExteriorAlgebra R M) = x.1 * y.1 := rfl

lemma mulₗ_ιMulti_ιMulti (v : Fin a → M) (w : Fin b → M) :
    mulₗ R M a b (ιMulti R a v) (ιMulti R b w) = ιMulti R (a + b) (Fin.append v w) :=
  Subtype.ext (ExteriorAlgebra.ιMulti_mul_ιMulti v w)

variable {R M} in
omit [AddCommGroup M] [Module R M] in
lemma comp_append {N : Type*} (f : M → N) (v : Fin a → M) (w : Fin b → M) :
    f ∘ Fin.append v w = Fin.append (f ∘ v) (f ∘ w) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp [Fin.append_left]
  · simp [Fin.append_right]

variable {R M} in
lemma map_mulₗ {N : Type u} [AddCommGroup N] [Module R N] (f : M →ₗ[R] N)
    (x : ⋀[R]^a M) (y : ⋀[R]^b M) :
    map (a + b) f (mulₗ R M a b x y) = mulₗ R N a b (map a f x) (map b f y) := by
  have hx : x ∈ Submodule.span R (Set.range (ιMulti R a (M := M))) := by
    rw [ιMulti_span]; trivial
  have hy : y ∈ Submodule.span R (Set.range (ιMulti R b (M := M))) := by
    rw [ιMulti_span]; trivial
  induction hx using Submodule.span_induction generalizing y with
  | mem x hx' =>
    obtain ⟨v, rfl⟩ := hx'
    induction hy using Submodule.span_induction with
    | mem y hy' =>
      obtain ⟨w, rfl⟩ := hy'
      rw [mulₗ_ιMulti_ιMulti, map_apply_ιMulti, map_apply_ιMulti, map_apply_ιMulti,
          mulₗ_ιMulti_ιMulti,
        comp_append]
    | zero => simp
    | add y z _ _ hy hz => rw [map_add, map_add, map_add, map_add, hy, hz]
    | smul r y _ hy => rw [map_smul, map_smul, map_smul, map_smul, hy]
  | zero => simp
  | add x x' _ _ hx hx' =>
    simp only [map_add, LinearMap.add_apply, hx y hy, hx' y hy]
  | smul r x _ hx =>
    simp only [map_smul, LinearMap.smul_apply, hx y hy]

/-- Exterior multiplication by a vector, increasing homogeneous degree by one. -/
noncomputable def mulVec (n : ℕ) : ⋀[R]^n M →ₗ[R] M →ₗ[R] ⋀[R]^(n + 1) M :=
  (mulₗ R M n 1).compl₂ (oneEquiv R M).symm.toLinearMap

lemma mulVec_apply (n : ℕ) (x : ⋀[R]^n M) (m : M) :
    mulVec R M n x m = mulₗ R M n 1 x ((oneEquiv R M).symm m) := rfl

lemma mulVec_ιMulti (n : ℕ) (v : Fin n → M) (m : M) :
    mulVec R M n (ιMulti R n v) m = ιMulti R (n + 1) (Fin.append v (fun _ : Fin 1 => m)) := by
  rw [mulVec_apply, oneEquiv_symm_apply, mulₗ_ιMulti_ιMulti]

variable {R M} in
lemma map_mulVec {N : Type u} [AddCommGroup N] [Module R N] (n : ℕ) (f : M →ₗ[R] N)
    (x : ⋀[R]^n M) (m : M) :
    map (n + 1) f (mulVec R M n x m) = mulVec R N n (map n f x) (f m) := by
  rw [mulVec_apply, mulVec_apply, map_mulₗ, oneEquiv_symm_apply, oneEquiv_symm_apply,
      map_apply_ιMulti]
  rfl

end exteriorPower

namespace PresheafOfModules

variable {C : Type*} [Category C] {R : Cᵒᵖ ⥤ CommRingCat.{u}} (n : ℕ)

namespace ExteriorPower

variable (P : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))


lemma mapₗ_mulVec {X Y : Cᵒᵖ} (f : X ⟶ Y) (x : ⋀[R.obj X]^n (P.obj X)) (m : P.obj X) :
    mapₗ (n + 1) P f (exteriorPower.mulVec (R.obj X) (P.obj X) n x m) =
      exteriorPower.mulVec (R.obj Y) (P.obj Y) n (mapₗ n P f x) (P.map f m) := by
  let := moduleAlong R f (⋀[R.obj Y]^(n + 1) (P.obj Y))
  let := moduleAlong R f (⋀[R.obj Y]^n (P.obj Y))
  let fm : P.obj X → P.obj Y := fun z => P.map f z
  change mapₗ (n + 1) P f (exteriorPower.mulVec (R.obj X) (P.obj X) n x m) =
    exteriorPower.mulVec (R.obj Y) (P.obj Y) n (mapₗ n P f x) (fm m)
  have hx : x ∈ Submodule.span (R.obj X) (Set.range (exteriorPower.ιMulti (R.obj X) n (M := P.obj
      X))) := by
    rw [exteriorPower.ιMulti_span]; trivial
  induction hx using Submodule.span_induction with
  | mem x hx' =>
    obtain ⟨v, rfl⟩ := hx'
    have h1 : mapₗ n P f (exteriorPower.ιMulti (R.obj X) n v) =
        exteriorPower.ιMulti (R.obj Y) n (fun i => fm (v i)) := mapₗ_ιMulti n P f v
    have h2 : mapₗ (n + 1) P f
        (exteriorPower.ιMulti (R.obj X) (n + 1) (Fin.append v (fun _ : Fin 1 => m))) =
        exteriorPower.ιMulti (R.obj Y) (n + 1)
          (fun i => fm (Fin.append v (fun _ : Fin 1 => m) i)) :=
      mapₗ_ιMulti (n + 1) P f (Fin.append v (fun _ : Fin 1 => m))
    rw [exteriorPower.mulVec_ιMulti, h2, h1, exteriorPower.mulVec_ιMulti]
    congr 1
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [Fin.append_left]
    · simp [Fin.append_right]
  | zero => simp only [map_zero, LinearMap.zero_apply]
  | add x y _ _ hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
  | smul r x _ hx => rw [LinearMap.map_smul₂, mapₗ_smul, mapₗ_smul, LinearMap.map_smul₂, hx]

end ExteriorPower

variable (P : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))

/-- Exterior multiplication by a vector on the module of sections at an object. -/
noncomputable abbrev ExteriorPower.mulVecObj (X : Cᵒᵖ) :
    (exteriorPower n P).obj X →ₗ[R.obj X]
      (P.obj X →ₗ[R.obj X] (exteriorPower (n + 1) P).obj X) :=
  exteriorPower.mulVec (R.obj X) (P.obj X) n


/-- The morphism of module presheaves induced by exterior multiplication by a vector. -/
noncomputable def wedgeVec : exteriorPower n P ⊗ P ⟶ exteriorPower (n + 1) P where
  app X := ModuleCat.ofHom
    (X := (exteriorPower n P ⊗ P).obj X)
    (Y := (exteriorPower (n + 1) P).obj X)
    (TensorProduct.lift (ExteriorPower.mulVecObj n P X))
  naturality {X Y} f := by
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro x m
    change exteriorPower.mulVec (R.obj Y) (P.obj Y) n
        (ExteriorPower.mapₗ n P f (show ⋀[R.obj X]^n (P.obj X) from x)) (P.map f m) =
      ExteriorPower.mapₗ (n + 1) P f
        (exteriorPower.mulVec (R.obj X) (P.obj X) n (show ⋀[R.obj X]^n (P.obj X) from x) m)
    exact (ExteriorPower.mapₗ_mulVec n P f _ m).symm

lemma wedgeVec_app_tmul (X : Cᵒᵖ) (x : ⋀[R.obj X]^n (P.obj X)) (m : P.obj X) :
    ((wedgeVec n P).app X ((show (exteriorPower n P).obj X from x) ⊗ₜ[R.obj X] m) :
      ⋀[R.obj X]^(n + 1) (P.obj X)) = exteriorPower.mulVec (R.obj X) (P.obj X) n x m := rfl

variable {P} in
lemma wedgeVec_naturality {Q : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)} (φ : P ⟶ Q)
  :
    (exteriorPowerMap n φ ⊗ₘ φ) ≫ wedgeVec n Q = wedgeVec n P ≫ exteriorPowerMap (n + 1) φ := by
  ext X : 1
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro x m
  change exteriorPower.mulVec (R.obj X) (Q.obj X) n
      (exteriorPower.map n (ExteriorPower.appₗ φ X) (show ⋀[R.obj X]^n (P.obj X) from x)) (φ.app X
          m) =
    exteriorPower.map (n + 1) (ExteriorPower.appₗ φ X)
      (exteriorPower.mulVec (R.obj X) (P.obj X) n (show ⋀[R.obj X]^n (P.obj X) from x) m)
  rw [exteriorPower.map_mulVec]
  rfl

end PresheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (n : ℕ)

/-- The canonical sheafification isomorphism for the underlying presheaf of a sheaf of modules. -/
noncomputable def sheafifyValIso (M : X.Modules) : (Scheme.Modules.sheafify X).obj M.val ≅ M :=
  SheafOfModules.sheafifyCounitIso X.sheaf.obj X.ringCatSheaf.property M
@[reassoc]
lemma sheafifyValIso_hom_naturality {M N : X.Modules} (φ : M ⟶ N) :
    (Scheme.Modules.sheafify X).map φ.val ≫ (sheafifyValIso N).hom = (sheafifyValIso M).hom ≫ φ :=
        by
  have h := (SheafOfModules.sheafifyAdj X.sheaf.obj X.ringCatSheaf.property).counit.naturality φ
  exact h
@[reassoc]
lemma sheafifyValIso_inv_naturality {M N : X.Modules} (φ : M ⟶ N) :
    φ ≫ (sheafifyValIso N).inv = (sheafifyValIso M).inv ≫ (Scheme.Modules.sheafify X).map φ.val :=
        by
  rw [Iso.comp_inv_eq, Category.assoc, sheafifyValIso_hom_naturality, Iso.inv_hom_id_assoc]

lemma det_eq (M : X.Modules) :
    Scheme.Modules.det n M = (Scheme.Modules.sheafify X).obj ((presheafExteriorPower X n).obj M.val)
        := rfl

lemma exteriorPower_map_eq {M N : X.Modules} (φ : M ⟶ N) :
    (exteriorPower X n).map φ = (Scheme.Modules.sheafify X).map ((presheafExteriorPower X n).map
        φ.val) := rfl

/-- Exterior multiplication by a local section, transported from presheaves through sheafification.
-/
noncomputable def wedgeVec (M : X.Modules) : Scheme.Modules.det n M ⊗ M ⟶ Scheme.Modules.det (n + 1)
  M :=
  (Scheme.Modules.det n M ◁ (sheafifyValIso M).inv) ≫
    Functor.LaxMonoidal.μ (Scheme.Modules.sheafify X) ((presheafExteriorPower X n).obj M.val) M.val
        ≫
      (Scheme.Modules.sheafify X).map (PresheafOfModules.wedgeVec n M.val)

lemma whiskerRight_exteriorPower_map_comp_wedgeVec {M N : X.Modules} (φ : M ⟶ N) :
    ((exteriorPower X n).map φ ▷ N) ≫ wedgeVec n N =
      (Scheme.Modules.det n M ◁ (sheafifyValIso N).inv) ≫
        Functor.LaxMonoidal.μ (Scheme.Modules.sheafify X) ((presheafExteriorPower X n).obj M.val)
            N.val ≫
          (Scheme.Modules.sheafify X).map
            (((presheafExteriorPower X n).map φ.val ▷ N.val) ≫ PresheafOfModules.wedgeVec n N.val)
                := by
  erw [wedgeVec, ← whisker_exchange_assoc, exteriorPower_map_eq,
      Functor.LaxMonoidal.μ_natural_left_assoc,
    ← Functor.map_comp]
  rfl

lemma wedgeVec_naturality {M N : X.Modules} (φ : M ⟶ N) :
    ((exteriorPower X n).map φ ⊗ₘ φ) ≫ wedgeVec n N = wedgeVec n M ≫ (exteriorPower X (n + 1)).map φ
        := by
  have h1 : ((exteriorPower X n).map φ ⊗ₘ φ) ≫ (Scheme.Modules.det n N ◁ (sheafifyValIso N).inv) =
      (Scheme.Modules.det n M ◁ (sheafifyValIso M).inv) ≫
        ((Scheme.Modules.sheafify X).map ((presheafExteriorPower X n).map φ.val) ⊗ₘ
          (Scheme.Modules.sheafify X).map φ.val) := by
    erw [exteriorPower_map_eq, MonoidalCategory.tensorHom_def, Category.assoc,
      ← MonoidalCategory.whiskerLeft_comp, sheafifyValIso_inv_naturality,
          MonoidalCategory.whiskerLeft_comp,
      ← whisker_exchange_assoc, ← MonoidalCategory.tensorHom_def]
    rfl
  have h2 : ((presheafExteriorPower X n).map φ.val ⊗ₘ φ.val) ≫ PresheafOfModules.wedgeVec n N.val =
      PresheafOfModules.wedgeVec n M.val ≫ (presheafExteriorPower X (n + 1)).map φ.val :=
    PresheafOfModules.wedgeVec_naturality n φ.val
  let F : X.PresheafOfModules ⥤ X.Modules := Scheme.Modules.sheafify X
  let A := (presheafExteriorPower X n).obj M.val
  let B := (presheafExteriorPower X n).obj N.val
  let T := (presheafExteriorPower X (n + 1)).obj N.val
  let f : A ⟶ B := (presheafExteriorPower X n).map φ.val
  let g := (presheafExteriorPower X (n + 1)).map φ.val
  let wM := PresheafOfModules.wedgeVec n M.val
  let wN : B ⊗ N.val ⟶ T := PresheafOfModules.wedgeVec n N.val
  let d : Scheme.Modules.det n M ⊗ M ⟶ Scheme.Modules.det n M ⊗ F.obj M.val :=
    Scheme.Modules.det n M ◁ (sheafifyValIso M).inv
  let μM := Functor.LaxMonoidal.μ F A M.val
  let μN := Functor.LaxMonoidal.μ F B N.val
  have hμ : (F.map f ⊗ₘ F.map φ.val) ≫ μN = μM ≫ F.map (f ⊗ₘ φ.val) :=
    Functor.LaxMonoidal.μ_natural F f φ.val
  have h1' : ((exteriorPower X n).map φ ⊗ₘ φ) ≫
      (Scheme.Modules.det n N ◁ (sheafifyValIso N).inv) =
      d ≫ (F.map f ⊗ₘ F.map φ.val) := h1
  have h2' : (f ⊗ₘ φ.val) ≫ wN = wM ≫ g := h2
  change ((exteriorPower X n).map φ ⊗ₘ φ) ≫
      ((Scheme.Modules.det n N ◁ (sheafifyValIso N).inv) ≫ μN ≫ F.map wN) =
      (d ≫ μM ≫ F.map wM) ≫ F.map g
  calc
    _ = (((exteriorPower X n).map φ ⊗ₘ φ) ≫
          (Scheme.Modules.det n N ◁ (sheafifyValIso N).inv)) ≫ μN ≫ F.map wN :=
      (Category.assoc _ _ _).symm
    _ = (d ≫ (F.map f ⊗ₘ F.map φ.val)) ≫ μN ≫ F.map wN :=
      congrArg (fun k : Scheme.Modules.det n M ⊗ M ⟶
        Scheme.Modules.det n N ⊗ F.obj N.val => k ≫ μN ≫ F.map wN) h1'
    _ = d ≫ ((F.map f ⊗ₘ F.map φ.val) ≫ μN) ≫ F.map wN := by
      simp only [Category.assoc]
    _ = d ≫ (μM ≫ F.map (f ⊗ₘ φ.val)) ≫ F.map wN :=
      congrArg (fun k : F.obj A ⊗ F.obj M.val ⟶ F.obj (B ⊗ N.val) =>
        d ≫ k ≫ F.map wN) hμ
    _ = d ≫ μM ≫ F.map ((f ⊗ₘ φ.val) ≫ wN) :=
      (congrArg (fun k : F.obj A ⊗ F.obj M.val ⟶ F.obj T => d ≫ k)
        (Category.assoc μM (F.map (f ⊗ₘ φ.val)) (F.map wN))).trans
          (congrArg (fun k : F.obj (A ⊗ M.val) ⟶ F.obj T => d ≫ μM ≫ k)
            (F.map_comp (f ⊗ₘ φ.val) wN).symm)
    _ = d ≫ μM ≫ F.map (wM ≫ g) :=
      congrArg (fun k : A ⊗ M.val ⟶ T => d ≫ μM ≫ F.map k) h2'
    _ = (d ≫ μM ≫ F.map wM) ≫ F.map g :=
      (congrArg (fun k : F.obj (A ⊗ M.val) ⟶ F.obj T => d ≫ μM ≫ k)
        (F.map_comp wM g)).trans
          ((congrArg (fun k : F.obj A ⊗ F.obj M.val ⟶ F.obj T => d ≫ k)
            (Category.assoc μM (F.map wM) (F.map g)).symm).trans
              (Category.assoc d (μM ≫ F.map wM) (F.map g)).symm)

end AlgebraicGeometry.Scheme.Modules
