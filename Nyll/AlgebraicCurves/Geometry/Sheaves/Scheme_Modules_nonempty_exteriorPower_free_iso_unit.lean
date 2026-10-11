/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_nonempty_exteriorPower_free_iso_unit.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesDet
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free

/-!
# Top exterior powers of finite free module sheaves

The standard basis determines a top exterior form and an isomorphism from the
top exterior power of a free module sheaf to the tensor unit.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_Modules_nonempty_exteriorPower_free_iso_unit

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits

namespace exteriorPower
open _root_.exteriorPower
open _root_.exteriorPower

variable (A : Type u) [CommRing A] (n : ℕ)

noncomputable scoped instance uniquePowersetCardFin : Unique (Set.powersetCard (Fin n) n) where
  default := Set.powersetCard.ofCard (n := n) (s := (Finset.univ : Finset (Fin n))) (by simp)
  uniq s := Subtype.ext (Finset.eq_univ_of_card _ (by
    rw [Fintype.card_fin]; exact Set.powersetCard.card_eq s))

/-- The top exterior form determined by the standard basis. -/
noncomputable def topForm : ⋀[A]^n (Fin n → A) :=
  ιMulti_family A n (Pi.basisFun A (Fin n)) default

/-- The exterior power basis of the standard basis in top degree. -/
noncomputable abbrev topBasis : Module.Basis (Set.powersetCard (Fin n) n) A (⋀[A]^n (Fin n → A)) :=
  (Pi.basisFun A (Fin n)).exteriorPower n

lemma topBasis_apply (s : Set.powersetCard (Fin n) n) : topBasis A n s = topForm A n := by
  rw [Subsingleton.elim s default, basis_apply]
  rfl

/-- Identify the top exterior power with the coefficient ring using its standard form. -/
noncomputable def topEquiv : ⋀[A]^n (Fin n → A) ≃ₗ[A] A :=
  (topBasis A n).repr ≪≫ₗ Finsupp.uniqueLinearEquiv A A default

@[scoped simp] lemma topEquiv_topForm : topEquiv A n (topForm A n) = 1 := by
  have h := (topBasis A n).repr_self default
  rw [topBasis_apply] at h
  rw [topEquiv, LinearEquiv.trans_apply, h, Finsupp.uniqueLinearEquiv_apply,
    Finsupp.single_eq_same]

lemma topEquiv_symm_apply (a : A) : (topEquiv A n).symm a = a • topForm A n := by
  apply (topEquiv A n).injective
  rw [LinearEquiv.apply_symm_apply, map_smul (topEquiv A n) a (topForm A n), topEquiv_topForm,
    smul_eq_mul, mul_one]

lemma eq_topEquiv_smul_topForm (x : ⋀[A]^n (Fin n → A)) : x = topEquiv A n x • topForm A n := by
  conv_lhs => rw [← (topEquiv A n).symm_apply_apply x]
  rw [topEquiv_symm_apply]

lemma exists_eq_smul_topForm (x : ⋀[A]^n (Fin n → A)) : ∃ a : A, x = a • topForm A n :=
  ⟨_, eq_topEquiv_smul_topForm A n x⟩

end exteriorPower

namespace PresheafOfModules
open _root_.PresheafOfModules
open _root_.PresheafOfModules

variable {C : Type*} [Category C] (R : Cᵒᵖ ⥤ CommRingCat.{u}) (n : ℕ)

/-- The presheaf of tuples of regular functions with pointwise restriction. -/
noncomputable def piPowAb : Cᵒᵖ ⥤ Ab.{u} where
  obj X := AddCommGrpCat.of (Fin n → R.obj X)
  map {X Y} f := AddCommGrpCat.ofHom (AddMonoidHom.compLeft (R.map f).hom.toAddMonoidHom (Fin n))
  map_id X := by ext v i; simp
  map_comp f g := by ext v i; simp

noncomputable scoped instance instModulePiPowAb (X : Cᵒᵖ) :
    Module ((R ⋙ forget₂ CommRingCat RingCat).obj X) ((piPowAb R n).obj X) :=
  inferInstanceAs (Module (R.obj X) (Fin n → R.obj X))

/-- The module presheaf of tuples of regular functions. -/
noncomputable def piPow : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat) :=
  @ofPresheaf C _ (R ⋙ forget₂ CommRingCat RingCat) (piPowAb R n) (fun X => instModulePiPowAb R n X)
    (fun X Y f r v => by
      funext i
      exact map_mul (R.map f).hom (show R.obj X from r) (v i))

lemma piPow_map_apply {X Y : Cᵒᵖ} (f : X ⟶ Y) (v : Fin n → R.obj X) (i : Fin n) :
    ((piPow R n).map f (show (piPow R n).obj X from v) : Fin n → R.obj Y) i = R.map f (v i) := rfl

lemma piPow_map_basisFun {X Y : Cᵒᵖ} (f : X ⟶ Y) (j : Fin n) :
    ((piPow R n).map f (show (piPow R n).obj X from Pi.basisFun (R.obj X) (Fin n) j) :
      Fin n → R.obj Y) = Pi.basisFun (R.obj Y) (Fin n) j := by
  funext i
  rw [piPow_map_apply, Pi.basisFun_apply, Pi.basisFun_apply, Pi.single_apply, Pi.single_apply]
  split_ifs <;> simp

open _root_.AlgebraicCurves.Geometry.Sheaves.Proofs in
open scoped Scheme_Modules_nonempty_exteriorPower_free_iso_unit.exteriorPower in
lemma mapₗ_topForm {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    ExteriorPower.mapₗ n (piPow R n) f (exteriorPower.topForm (R.obj X) n) =
      exteriorPower.topForm (R.obj Y) n := by
  have hmap := ExteriorPower.mapₗ_ιMulti n (piPow R n) f
    (fun i => (show (piPow R n).obj X from
      Pi.basisFun (R.obj X) (Fin n) ((Set.powersetCard.ofFinEmbEquiv.symm (default :
          Set.powersetCard (Fin n) n)) i)))
  exact hmap.trans (congrArg
    (fun v : Fin n → (piPow R n).obj Y =>
      exteriorPower.ιMulti (R.obj Y) n (M := (piPow R n).obj Y) v)
    (funext fun i => piPow_map_basisFun R n f _))

lemma topEquiv_mapₗ {X Y : Cᵒᵖ} (f : X ⟶ Y) (x : ⋀[R.obj X]^n (Fin n → R.obj X)) :
    exteriorPower.topEquiv (R.obj Y) n (ExteriorPower.mapₗ n (piPow R n) f x) =
      R.map f (exteriorPower.topEquiv (R.obj X) n x) := by
  obtain ⟨a, rfl⟩ := exteriorPower.exists_eq_smul_topForm (R.obj X) n x
  have hx : exteriorPower.topEquiv (R.obj X) n (a • exteriorPower.topForm (R.obj X) n) = a :=
    (congrArg (exteriorPower.topEquiv (R.obj X) n)
      (exteriorPower.topEquiv_symm_apply (R.obj X) n a).symm).trans
      ((exteriorPower.topEquiv (R.obj X) n).apply_symm_apply a)
  have hy : exteriorPower.topEquiv (R.obj Y) n
      (R.map f a • exteriorPower.topForm (R.obj Y) n) = R.map f a :=
    (congrArg (exteriorPower.topEquiv (R.obj Y) n)
      (exteriorPower.topEquiv_symm_apply (R.obj Y) n (R.map f a)).symm).trans
      ((exteriorPower.topEquiv (R.obj Y) n).apply_symm_apply (R.map f a))
  exact (congrArg (exteriorPower.topEquiv (R.obj Y) n)
    ((ExteriorPower.mapₗ_smul n (piPow R n) f a (exteriorPower.topForm (R.obj X) n)).trans
      (congrArg (fun z : ⋀[R.obj Y]^n (Fin n → R.obj Y) => R.map f a • z)
        (mapₗ_topForm R n f)))).trans (hy.trans (congrArg (fun a : R.obj X => R.map f a) hx).symm)

lemma unit_map_apply {X Y : Cᵒᵖ} (f : X ⟶ Y) (a : R.obj X) :
    ((unit (R ⋙ forget₂ CommRingCat RingCat)).map f
      (show (unit (R ⋙ forget₂ CommRingCat RingCat)).obj X from a) : R.obj Y) = R.map f a := rfl

/-- The presheaf map from the top exterior power to its coefficient ring. -/
noncomputable def piPowTopHomAb :
    ExteriorPower.presheafAb n (piPow R n) ⟶ (unit (R ⋙ forget₂ CommRingCat RingCat)).presheaf where
  app X := AddCommGrpCat.ofHom (X := ⋀[R.obj X]^n (Fin n → R.obj X)) (Y := R.obj X)
    (exteriorPower.topEquiv (R.obj X) n).toLinearMap.toAddMonoidHom
  naturality {X Y} f := by
    ext x
    exact topEquiv_mapₗ R n f x

/-- The presheaf map sending a coefficient to a multiple of the standard top form. -/
noncomputable def piPowTopInvAb :
    (unit (R ⋙ forget₂ CommRingCat RingCat)).presheaf ⟶ ExteriorPower.presheafAb n (piPow R n) where
  app X := AddCommGrpCat.ofHom (X := R.obj X) (Y := ⋀[R.obj X]^n (Fin n → R.obj X))
    (LinearMap.toSpanSingleton (R.obj X) (⋀[R.obj X]^n (Fin n → R.obj X))
      (exteriorPower.topForm (R.obj X) n)).toAddMonoidHom
  naturality {X Y} f :=
    AddCommGrpCat.ext fun (a : R.obj X) =>
      ((ExteriorPower.mapₗ_smul n (piPow R n) f a
        (exteriorPower.topForm (R.obj X) n)).trans
          (congrArg (fun z : ⋀[R.obj Y]^n (Fin n → R.obj Y) => R.map f a • z)
            (mapₗ_topForm R n f))).symm

/-- The top exterior power of the tuple presheaf is the unit module presheaf. -/
noncomputable def exteriorPowerPiPowIso :
    exteriorPower n (piPow R n) ≅ unit (R ⋙ forget₂ CommRingCat RingCat) where
  hom := homMk (piPowTopHomAb R n) (fun X r m =>
    map_smul (exteriorPower.topEquiv (R.obj X) n) (show R.obj X from r)
      (show ⋀[R.obj X]^n (Fin n → R.obj X) from m))
  inv := homMk (M₁ := unit _) (piPowTopInvAb R n) (fun X r a =>
    mul_smul (show R.obj X from r) (show R.obj X from a) (exteriorPower.topForm (R.obj X) n))
  hom_inv_id := by
    ext X : 1
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    exact (exteriorPower.eq_topEquiv_smul_topForm (R.obj X) n x).symm
  inv_hom_id := by
    ext X : 1
    refine ModuleCat.hom_ext (LinearMap.ext fun (a : R.obj X) => ?_)
    change exteriorPower.topEquiv (R.obj X) n (a • exteriorPower.topForm (R.obj X) n) = a
    rw [← exteriorPower.topEquiv_symm_apply, LinearEquiv.apply_symm_apply]

end PresheafOfModules

namespace PresheafOfModules
open _root_.PresheafOfModules
open _root_.PresheafOfModules

lemma sum_app {C : Type*} [Category C] {R : Cᵒᵖ ⥤ RingCat.{u}} {M N : PresheafOfModules.{u} R}
    {ι : Type*} (s : Finset ι) (f : ι → (M ⟶ N)) (X : Cᵒᵖ) :
    (∑ i ∈ s, f i).app X = ∑ i ∈ s, (f i).app X :=
  Functor.map_sum (evaluation R X) f s

end PresheafOfModules

namespace SheafOfModules
open _root_.SheafOfModules
open _root_.SheafOfModules

lemma sum_val {C : Type*} [Category C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    {M N : SheafOfModules.{u} R} {ι : Type*} (s : Finset ι) (f : ι → (M ⟶ N)) :
    (∑ i ∈ s, f i).val = ∑ i ∈ s, (f i).val :=
  Functor.map_sum (SheafOfModules.forget R) f s

end SheafOfModules

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace Modules
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry

open TopologicalSpace

variable (X : Scheme.{u}) (n : ℕ)

/-- The tuple module presheaf on a scheme. -/
noncomputable abbrev piPowPresheaf : X.PresheafOfModules := PresheafOfModules.piPow X.sheaf.obj n

/-- The structure sheaf viewed as a sheaf of abelian groups. -/
noncomputable abbrev ringCatSheafAb : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  (sheafCompose (Opens.grothendieckTopology X) (forget₂ RingCat.{u} AddCommGrpCat.{u})).obj
      X.ringCatSheaf

/-- The cone expressing tuples as the product of copies of the structure presheaf. -/
noncomputable def piPowCone :
    Cone (Discrete.functor (fun _ : Fin n => ringCatSheafAb X) ⋙ sheafToPresheaf _ _) where
  pt := (piPowPresheaf X n).presheaf
  π := Discrete.natTrans (fun i =>
    { app := fun V => AddCommGrpCat.ofHom (X := Fin n → (X.presheaf.obj V : Type u))
        (Y := (X.presheaf.obj V : Type u))
        (Pi.evalAddMonoidHom (fun _ : Fin n => (X.presheaf.obj V : Type u)) i.as)
      naturality := fun V W g => by ext v; rfl })

/-- The tuple cone is a limit cone. -/
noncomputable def isLimitPiPowCone : IsLimit (piPowCone X n) :=
  evaluationJointlyReflectsLimits _ (fun V =>
    { lift := fun s => AddCommGrpCat.ofHom (X := (s.pt : Type u)) (Y := Fin n → (X.presheaf.obj V :
        Type u))
        (AddMonoidHom.pi (fun i : Fin n =>
          (show (s.pt : Type u) →+ (X.presheaf.obj V : Type u) from (s.π.app ⟨i⟩).hom)))
      fac := fun s j => by
        obtain ⟨i⟩ := j
        ext x
        rfl
      uniq := fun s m h => by
        ext x
        funext i
        exact ConcreteCategory.congr_hom (h ⟨i⟩) x })

lemma isSheaf_piPowPresheaf :
    Presheaf.IsSheaf (Opens.grothendieckTopology X) (piPowPresheaf X n).presheaf :=
  Sheaf.isSheaf_of_isLimit _ (piPowCone X n) (isLimitPiPowCone X n)

private noncomputable def _root_.AlgebraicGeometry.Scheme.Modules.piPow : X.Modules where
  val := piPowPresheaf X n
  isSheaf := isSheaf_piPowPresheaf X n

open _root_.AlgebraicGeometry.Scheme.Modules

/-- Projection from the tuple module to one coordinate. -/
noncomputable def piPowπ (i : Fin n) : piPow X n ⟶ SheafOfModules.unit X.ringCatSheaf :=
  ⟨PresheafOfModules.homMk (M₂ := PresheafOfModules.unit _)
    { app := fun V => AddCommGrpCat.ofHom (X := Fin n → (X.presheaf.obj V : Type u))
        (Y := (X.presheaf.obj V : Type u))
        (Pi.evalAddMonoidHom (fun _ : Fin n => (X.presheaf.obj V : Type u)) i)
      naturality := fun V W g => by ext v; rfl }
    (fun V r v => rfl)⟩

lemma piPowπ_apply (i : Fin n) (V : X.Opensᵒᵖ) (v : Fin n → (X.presheaf.obj V : Type u)) :
    ((piPowπ X n i).val.app V (show (piPow X n).val.obj V from v) : X.presheaf.obj V) = v i := rfl

/-- Inclusion of a single coordinate into the tuple module. -/
noncomputable def piPowι (i : Fin n) : SheafOfModules.unit X.ringCatSheaf ⟶ piPow X n :=
  ⟨PresheafOfModules.homMk (M₁ := PresheafOfModules.unit _)
    { app := fun V => AddCommGrpCat.ofHom (X := (X.presheaf.obj V : Type u))
        (Y := Fin n → (X.presheaf.obj V : Type u))
        (AddMonoidHom.single (fun _ : Fin n => (X.presheaf.obj V : Type u)) i)
      naturality := fun V W g => by
        refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun (a : X.presheaf.obj V) => ?_)
        funext k
        change (Pi.single i (X.presheaf.map g a) : Fin n → X.presheaf.obj W) k =
          X.presheaf.map g ((Pi.single i a : Fin n → X.presheaf.obj V) k)
        simp only [Pi.single_apply]
        split_ifs <;> simp }
    (fun V (r : X.presheaf.obj V) (a : X.presheaf.obj V) => by
      funext k
      change (Pi.single i (r * a) : Fin n → X.presheaf.obj V) k =
        r * (Pi.single i a : Fin n → X.presheaf.obj V) k
      simp only [Pi.single_apply]
      split_ifs <;> simp)⟩

lemma piPowι_apply (i : Fin n) (V : X.Opensᵒᵖ) (a : (X.presheaf.obj V : Type u)) :
    ((piPowι X n i).val.app V (show (SheafOfModules.unit X.ringCatSheaf).val.obj V from a) :
      Fin n → X.presheaf.obj V) = Pi.single i a := rfl

/-- The bicone of coordinate projections and inclusions for the tuple module. -/
noncomputable def piPowBicone :
    Bicone (fun _ : ULift.{u} (Fin n) => SheafOfModules.unit X.ringCatSheaf) where
  pt := piPow X n
  π j := piPowπ X n j.down
  ι j := piPowι X n j.down
  ι_π j j' := by
    refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V => ModuleCat.hom_ext
      (LinearMap.ext fun (a : X.presheaf.obj V) => ?_))
    by_cases h : j = j'
    · subst h
      rw [dite_eq_left rfl]
      change (Pi.single j.down a : Fin n → X.presheaf.obj V) j.down = a
      simp
    · rw [dite_eq_right h]
      have h' : j'.down ≠ j.down := fun e => h (ULift.ext e.symm)
      change (Pi.single j.down a : Fin n → X.presheaf.obj V) j'.down = (0 : X.presheaf.obj V)
      simp [h']

lemma piPowBicone_total :
    ∑ j : ULift.{u} (Fin n), (piPowBicone X n).π j ≫ (piPowBicone X n).ι j = 𝟙 (piPow X n) := by
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V => ModuleCat.hom_ext
    (LinearMap.ext fun (v : Fin n → X.presheaf.obj V) => ?_))
  rw [SheafOfModules.sum_val, PresheafOfModules.sum_app, ModuleCat.hom_sum]
  erw [LinearMap.sum_apply]
  change (∑ j : ULift.{u} (Fin n), (Pi.single j.down (v j.down) : Fin n → X.presheaf.obj V)) = v
  rw [Fintype.sum_equiv Equiv.ulift
    (fun j : ULift.{u} (Fin n) => (Pi.single j.down (v j.down) : Fin n → X.presheaf.obj V))
    (fun i : Fin n => Pi.single i (v i)) (fun _ => rfl)]
  exact Finset.univ_sum_single _

/-- The coordinate bicone is a biproduct. -/
noncomputable def isBilimitPiPowBicone : (piPowBicone X n).IsBilimit :=
  isBilimitOfTotal _ (piPowBicone_total X n)

/-- Identify the finite free module sheaf with tuples of regular functions. -/
noncomputable def freeIsoPiPow : SheafOfModules.free.{u} (ULift.{u} (Fin n)) ≅ piPow X n :=
  IsColimit.coconePointUniqueUpToIso
    (SheafOfModules.isColimitFreeCofan.{u} (R := X.ringCatSheaf) (ULift.{u} (Fin n)))
    (isBilimitPiPowBicone X n).isColimit

/-- Identify the sheafification of the unit presheaf with the unit sheaf. -/
noncomputable def sheafificationUnitIso :
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj (PresheafOfModules.unit _) ≅
      SheafOfModules.unit X.ringCatSheaf :=
  (asIso (PresheafOfModules.sheafificationAdjunction
    (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).counit).app
    (SheafOfModules.unit X.ringCatSheaf)

/-- The top exterior power of the finite free module sheaf is the unit sheaf. -/
noncomputable def exteriorPowerFreeIso :
    (exteriorPower X n).obj (SheafOfModules.free.{u} (ULift.{u} (Fin n))) ≅
      SheafOfModules.unit X.ringCatSheaf :=
  (exteriorPower X n).mapIso (freeIsoPiPow X n) ≪≫
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso
      (PresheafOfModules.exteriorPowerPiPowIso X.sheaf.obj n) ≪≫
    sheafificationUnitIso X

theorem nonempty_exteriorPowerFreeIso :
    Nonempty ((exteriorPower X n).obj (SheafOfModules.free.{u} (ULift.{u} (Fin n))) ≅
      SheafOfModules.unit X.ringCatSheaf) :=
  ⟨exteriorPowerFreeIso X n⟩

end AlgebraicGeometry.Scheme.Modules

open _root_.AlgebraicGeometry AlgebraicGeometry in
theorem _root_.AlgebraicGeometry.Scheme.Modules.nonempty_exteriorPower_free_iso_unit (X :
  Scheme.{u}) (n : ℕ) :
    Nonempty ((Scheme.Modules.exteriorPower X n).obj (SheafOfModules.free.{u} (ULift.{u} (Fin n))) ≅
      SheafOfModules.unit X.ringCatSheaf) :=
  AlgebraicGeometry.Scheme.Modules.nonempty_exteriorPowerFreeIso X n
end AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_nonempty_exteriorPower_free_iso_unit
end ProofImplementation
