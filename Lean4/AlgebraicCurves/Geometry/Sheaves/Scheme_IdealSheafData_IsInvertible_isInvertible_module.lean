/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_module.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Geometry.Sheaves.IdealSheafModule
import AlgebraicCurves.Geometry.Picard.Functor
import AlgebraicCurves.RelativeDivisors.Cartier
import SchemeTheory.Modules.PresheafInternalHom
import SchemeTheory.Modules.SheafificationMonoidal
import SchemeTheory.Modules.Monoidal
import Mathlib.Util.WithWeakNamespace

/-!
# Invertible ideals and invertible module sheaves

Constructs local module trivializations from non-zero-divisor generators of an invertible ideal.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_IdealSheafData_IsInvertible_isInvertible_module

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.TopologicalSpace
open _root_.Opposite

noncomputable section

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace IdealSheafData
open _root_.AlgebraicGeometry.Scheme.IdealSheafData
open _root_.AlgebraicGeometry.Scheme.IdealSheafData
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry

variable {X : Scheme.{u}} (I : X.IdealSheafData)

private def _root_.AlgebraicGeometry.Scheme.IdealSheafData.sectionsIdeal (U : X.Opens) : Ideal
  Γ(X, U) :=
  RingHom.ker (I.subschemeι.app U).hom

open _root_.AlgebraicGeometry.Scheme.IdealSheafData
private lemma _root_.AlgebraicGeometry.Scheme.IdealSheafData.mem_sectionsIdeal_iff {U : X.Opens}
  (s : Γ(X, U)) :
    s ∈ I.sectionsIdeal U ↔ I.subschemeι.app U s = 0 := RingHom.mem_ker

open _root_.AlgebraicGeometry.Scheme.IdealSheafData

private lemma _root_.AlgebraicGeometry.Scheme.IdealSheafData.sectionsIdeal_eq_ideal (U :
  X.affineOpens) : I.sectionsIdeal U = I.ideal U :=
  I.ker_subschemeι_app U

open _root_.AlgebraicGeometry.Scheme.IdealSheafData

private lemma _root_.AlgebraicGeometry.Scheme.IdealSheafData.map_mem_sectionsIdeal {U V :
  X.Opens} (i : V ⟶ U) {s : Γ(X, U)}
    (hs : s ∈ I.sectionsIdeal U) : X.presheaf.map i.op s ∈ I.sectionsIdeal V := by
  rw [mem_sectionsIdeal_iff] at hs ⊢
  have := ConcreteCategory.congr_hom (I.subschemeι.naturality i.op) s
  simp only [CommRingCat.comp_apply] at this
  erw [this, hs, map_zero]

open _root_.AlgebraicGeometry.Scheme.IdealSheafData

/-- The presheaf of additive groups of sections in the ideal sheaf. -/
def sectionsPresheaf : (X.Opens)ᵒᵖ ⥤ Ab.{u} where
  obj U := AddCommGrpCat.of (I.sectionsIdeal U.unop)
  map {U V} i := AddCommGrpCat.ofHom
    { toFun := fun s => ⟨X.presheaf.map i s.1, I.map_mem_sectionsIdeal i.unop s.2⟩
      map_zero' := Subtype.ext (by
        change X.presheaf.map i (0 : Γ(X, U.unop)) = 0
        exact map_zero _)
      map_add' := fun s t => Subtype.ext (by
        change X.presheaf.map i (s.1 + t.1) = X.presheaf.map i s.1 + X.presheaf.map i t.1
        exact map_add _ _ _) }
  map_id U := by
    ext s
    change X.presheaf.map (𝟙 U) s.1 = s.1
    rw [X.presheaf.map_id]
    rfl
  map_comp i j := by
    ext s
    change X.presheaf.map (i ≫ j) s.1 = X.presheaf.map j (X.presheaf.map i s.1)
    rw [X.presheaf.map_comp]
    rfl

scoped instance (U : (X.Opens)ᵒᵖ) : Module ((X.ringCatSheaf.obj).obj U) ((sectionsPresheaf
  I).obj U) :=
  inferInstanceAs (Module Γ(X, U.unop) (I.sectionsIdeal U.unop))

lemma sectionsPresheaf_map_apply_coe {U V : (X.Opens)ᵒᵖ} (i : U ⟶ V)
    (s : (sectionsPresheaf I).obj U) :
    ((sectionsPresheaf I).map i s).1 = X.presheaf.map i s.1 := rfl

/-- The ideal-section presheaf with its natural structure-module action. -/
def toPresheafOfModules : X.PresheafOfModules :=
  PresheafOfModules.ofPresheaf (sectionsPresheaf I) (by
    intro U V i r s
    apply Subtype.ext
    change X.presheaf.map i ((show Γ(X, U.unop) from r) * s.1) =
      (show Γ(X, V.unop) from X.presheaf.map i (show Γ(X, U.unop) from r)) * X.presheaf.map i s.1
    exact map_mul _ _ _)

@[scoped simp] lemma toPresheafOfModules_presheaf : (toPresheafOfModules I).presheaf =
  sectionsPresheaf I :=
  rfl

/-- Ideal sections viewed as a subfunctor of the underlying structure presheaf. -/
def sectionsSubfunctor : Subfunctor (X.presheaf ⋙ CategoryTheory.forget CommRingCat) where
  obj U := {s | s ∈ I.sectionsIdeal U.unop}
  map {_U _V} i _s hs := I.map_mem_sectionsIdeal i.unop hs

/-- The identification of ideal-section groups with the corresponding subfunctor. -/
def sectionsIso : sectionsPresheaf I ⋙ CategoryTheory.forget Ab ≅ (sectionsSubfunctor
  I).toFunctor :=
  NatIso.ofComponents (fun U => Equiv.toIso
    { toFun := fun s => ⟨s.1, s.2⟩
      invFun := fun s => ⟨s.1, s.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }) (by intros; rfl)

lemma mem_sectionsIdeal_of_locally {U : X.Opens} (s : Γ(X, U))
    (h : ∀ x ∈ U, ∃ (V : X.Opens) (_ : V ≤ U), x ∈ V ∧
      X.presheaf.map (homOfLE ‹V ≤ U›).op s ∈ I.sectionsIdeal V) :
    s ∈ I.sectionsIdeal U := by
  rw [mem_sectionsIdeal_iff]
  let ι : Type u := {V : X.Opens // ∃ (_ : V ≤ U), X.presheaf.map (homOfLE ‹V ≤ U›).op s ∈
    I.sectionsIdeal V}
  let W : ι → I.subscheme.Opens := fun V => I.subschemeι ⁻¹ᵁ V.1
  have hcover : I.subschemeι ⁻¹ᵁ U ≤ iSup W := by
    intro z hz
    obtain ⟨V, hVU, hzV, hV⟩ := h _ hz
    exact Opens.mem_iSup.2 ⟨⟨V, hVU, hV⟩, hzV⟩
  refine I.subscheme.sheaf.eq_of_locally_eq' W (I.subschemeι ⁻¹ᵁ U)
    (fun V => homOfLE (fun z hz => V.2.1 hz)) hcover _ _ (fun V => ?_)
  obtain ⟨hVU, hV⟩ := V.2
  rw [mem_sectionsIdeal_iff] at hV
  have nat := ConcreteCategory.congr_hom (I.subschemeι.naturality (homOfLE hVU).op) s
  simp only [CommRingCat.comp_apply] at nat
  change I.subscheme.presheaf.map (((Opens.map I.subschemeι.base).map (homOfLE hVU)).op)
      (I.subschemeι.app U s) =
    I.subscheme.presheaf.map (((Opens.map I.subschemeι.base).map (homOfLE hVU)).op) 0
  exact (nat.symm.trans hV).trans (map_zero _).symm

lemma isSheaf_toPresheafOfModules :
    Presheaf.IsSheaf (Opens.grothendieckTopology X) (toPresheafOfModules I).presheaf := by
  have hO : Presieve.IsSheaf (Opens.grothendieckTopology X)
      (X.presheaf ⋙ CategoryTheory.forget CommRingCat) :=
    (isSheaf_iff_isSheaf_of_type _ _).1
      ((Presheaf.isSheaf_iff_isSheaf_comp _ X.sheaf.obj (CategoryTheory.forget CommRingCat)).1
        X.sheaf.property)
  rw [toPresheafOfModules_presheaf,
    Presheaf.isSheaf_iff_isSheaf_comp (Opens.grothendieckTopology X) (sectionsPresheaf I)
      (CategoryTheory.forget Ab),
    Presheaf.isSheaf_of_iso_iff (sectionsIso I), isSheaf_iff_isSheaf_of_type,
    Subfunctor.isSheaf_iff _ hO]
  intro U s hs
  apply mem_sectionsIdeal_of_locally
  intro x hx
  obtain ⟨V, i, hi, hxV⟩ := hs x hx
  exact ⟨V, i.le, hxV, hi⟩

private def _root_.AlgebraicGeometry.Scheme.IdealSheafData.toModule : SheafOfModules
  X.ringCatSheaf where
  val := toPresheafOfModules I
  isSheaf := isSheaf_toPresheafOfModules I

open _root_.AlgebraicGeometry.Scheme.IdealSheafData

lemma toModule_sections (U : X.Opens) :
    ((toModule I).val.obj (op U) : Type u) = I.sectionsIdeal U := rfl

private def _root_.AlgebraicGeometry.Scheme.IdealSheafData.toModuleι : toModule I ⟶
  SheafOfModules.unit X.ringCatSheaf :=
  ⟨{ app := fun U => ModuleCat.ofHom
      { toFun := fun s => s.1
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
     naturality := fun i => by ext s; rfl }⟩

open _root_.AlgebraicGeometry.Scheme.IdealSheafData
example : (SheafOfModules.unit X.ringCatSheaf : X.Modules) = 𝟙_ X.Modules := rfl

lemma toModuleι_app_apply (U : (X.Opens)ᵒᵖ) (s : (toModule I).val.obj U) :
    (toModuleι I).val.app U s = s.1 := rfl

scoped instance (U : (X.Opens)ᵒᵖ) : Mono ((toModuleι I).val.app U) :=
  (ModuleCat.mono_iff_injective _).2 (fun s t h => by apply Subtype.ext; exact h)

lemma toModuleι_comp_unitToPushforwardUnit :
    (I.toModuleι : (I.toModule : SheafOfModules X.ringCatSheaf) ⟶
        SheafOfModules.unit X.ringCatSheaf) ≫ I.subschemeι.unitToPushforwardUnit = 0 := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext s
  change (I.subschemeι.unitToPushforwardUnit).val.app U ((I.toModuleι).val.app U s) = 0
  erw [SheafOfModules.unitToPushforwardObjUnit_val_app_apply]
  exact (I.mem_sectionsIdeal_iff s.1).1 s.2

/-- The universal kernel fork for inclusion of the ideal-section module. -/
def isLimitKernelFork : IsLimit (KernelFork.ofι
    (I.toModuleι : (I.toModule : SheafOfModules X.ringCatSheaf) ⟶ SheafOfModules.unit
      X.ringCatSheaf)
    (toModuleι_comp_unitToPushforwardUnit I)) :=
  KernelFork.IsLimit.ofι _ _
    (fun {M} φ hφ => ⟨{
      app := fun U => ModuleCat.ofHom
        { toFun := fun m => (⟨φ.val.app U m, by
            refine (I.mem_sectionsIdeal_iff (U := U.unop) (φ.val.app U m)).mpr ?_
            have h := congr_arg (fun k : M ⟶ _ => k.val.app U m) hφ
            change (I.subschemeι.unitToPushforwardUnit).val.app U (φ.val.app U m) = 0 at h
            erw [SheafOfModules.unitToPushforwardObjUnit_val_app_apply] at h
            exact h⟩ : I.sectionsIdeal U.unop)
          map_add' := fun m m' => Subtype.ext (by
            change φ.val.app U (m + m') = φ.val.app U m + φ.val.app U m'
            exact map_add _ _ _)
          map_smul' := fun r m => Subtype.ext (by
            change φ.val.app U (r • m) = r • φ.val.app U m
            exact (φ.val.app U).hom.map_smul r m) }
      naturality := fun {U V} i => by
        apply ModuleCat.hom_ext; apply LinearMap.ext; intro m
        apply Subtype.ext
        exact PresheafOfModules.naturality_apply φ.val i m }⟩)
    (fun {M} φ hφ => by
      apply SheafOfModules.hom_ext; apply PresheafOfModules.hom_ext; intro U; ext m; rfl)
    (fun {M} φ hφ m hm => by
      apply SheafOfModules.hom_ext; apply PresheafOfModules.hom_ext; intro U; ext x
      apply Subtype.ext
      change ((m ≫ I.toModuleι).val.app U) x = φ.val.app U x
      rw [hm])

/-- The comparison between the kernel ideal module and its ideal-section model. -/
def moduleIsoToModule : (I.module : SheafOfModules X.ringCatSheaf) ≅ I.toModule :=
  IsLimit.conePointUniqueUpToIso (kernelIsKernel _) (isLimitKernelFork I)

section restrict

variable (U : X.Opens)

omit I in
/-- The canonical structure-ring map used for restriction to an open subscheme. -/
def restrictRingCatSheafHom : (U : Scheme.{u}).ringCatSheaf ⟶
    (U.ι.opensFunctor.sheafPushforwardContinuous RingCat.{u}
      (Opens.grothendieckTopology (U : Scheme.{u})) (Opens.grothendieckTopology X)).obj
        X.ringCatSheaf :=
  ⟨𝟙 _⟩

omit I in
/-- Restriction of modules to an open subscheme through the canonical ring map. -/
def restrictFunctor' : X.Modules ⥤ (U : Scheme.{u}).Modules :=
  SheafOfModules.pushforward (restrictRingCatSheafHom U)

omit I in
lemma restrictFunctor'_eq : restrictFunctor' U = Modules.restrictFunctor U.ι := by
  dsimp only [restrictFunctor', Modules.restrictFunctor, restrictRingCatSheafHom]
  congr 2
  ext V : 2
  change 𝟙 _ = (forget₂ CommRingCat RingCat).map (U.ι.appIso V.unop).inv
  rw [Scheme.Opens.ι_appIso]
  rfl

omit I in
/-- The comparison of this restriction functor with module pullback. -/
def restrictFunctor'IsoPullback : restrictFunctor' U ≅ Modules.pullback U.ι :=
  eqToIso (restrictFunctor'_eq U) ≪≫ Modules.restrictFunctorIsoPullback U.ι

omit I in
variable {U} in
lemma image_preimage_of_le {V : X.Opens} (h : V ≤ U) : U.ι ''ᵁ (U.ι ⁻¹ᵁ V) = V := by
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
  exact inf_eq_right.mpr h

omit I in
lemma image_le (W : (U : Scheme.{u}).Opens) : U.ι ''ᵁ W ≤ U :=
  (U.ι.image_le_opensRange W).trans_eq U.opensRange_ι

omit I in
/-- A section on an open subscheme viewed as a section on its image. -/
abbrev secX (W : (U : Scheme.{u}).Opens) (a : Γ(U, W)) : Γ(X, U.ι ''ᵁ W) := a

end restrict

section trivialization

variable (B : X.affineOpens) (g : Γ(X, B)) (hg : g ∈ nonZeroDivisors Γ(X, B))
  (hIg : I.ideal B = Ideal.span {g})

omit I in
/-- The restriction of the chosen affine ideal generator to a smaller open. -/
def gOn (W : X.Opens) (h : W ≤ (B : X.Opens)) : Γ(X, W) := X.presheaf.map (homOfLE h).op g

omit I in
lemma gOn_res {W W' : X.Opens} (h : W ≤ (B : X.Opens)) (i : W' ⟶ W) :
    X.presheaf.map i.op (gOn B g W h) = gOn B g W' (i.le.trans h) := by
  change (X.presheaf.map _ ≫ X.presheaf.map _) g = X.presheaf.map _ g
  rw [← X.presheaf.map_comp]
  rfl

include hIg in
lemma gOn_mem (W : X.Opens) (h : W ≤ (B : X.Opens)) : gOn B g W h ∈ I.sectionsIdeal W := by
  apply I.map_mem_sectionsIdeal
  rw [sectionsIdeal_eq_ideal, hIg]
  exact Ideal.subset_span rfl

include hIg in
lemma sectionsIdeal_eq_span (W : X.Opens) (hW : IsAffineOpen W) (h : W ≤ (B : X.Opens)) :
    I.sectionsIdeal W = Ideal.span {gOn B g W h} := by
  rw [I.sectionsIdeal_eq_ideal ⟨W, hW⟩, ← I.map_ideal (U := ⟨W, hW⟩) (V := B) h, hIg,
    Ideal.map_span, Set.image_singleton]
  rfl

omit I in
include hg in
lemma gOn_mem_nonZeroDivisors (h' : Γ(X, B)) (W : X.Opens) (e : W = X.basicOpen h') :
    gOn B g W (e.trans_le (X.basicOpen_le h')) ∈ nonZeroDivisors Γ(X, W) := by
  subst e
  let := B.2.isLocalization_basicOpen h'
  exact IsLocalization.nonZeroDivisors_le_comap (M := .powers h') (S := Γ(X, X.basicOpen h')) hg

/-- Multiplication by the local generator, as a morphism to the ideal-section module. -/
def mulGen : SheafOfModules.unit ((B : X.Opens) : Scheme.{u}).ringCatSheaf ⟶
    (restrictFunctor' (B : X.Opens)).obj I.toModule :=
  ⟨{ app := fun W => by
      let K : ModuleCat (((B : X.Opens) : Scheme.{u}).ringCatSheaf.obj.obj W) :=
        (SheafOfModules.unit ((B : X.Opens) : Scheme.{u}).ringCatSheaf).val.obj W
      let N : ModuleCat (((B : X.Opens) : Scheme.{u}).ringCatSheaf.obj.obj W) :=
        (((restrictFunctor' (B : X.Opens)).obj I.toModule).val.obj W)
      exact (ModuleCat.homEquiv (M := K) (N := N)).symm
        { toFun := fun a => (⟨secX (B : X.Opens) W.unop a * gOn B g _ (image_le _ W.unop),
            Ideal.mul_mem_left _ _ (gOn_mem I B g hIg _ _)⟩ : I.sectionsIdeal _)
          map_add' := fun a b => Subtype.ext
            (add_mul (secX (B : X.Opens) W.unop a) (secX (B : X.Opens) W.unop b) _)
          map_smul' := fun r a => Subtype.ext
            (mul_assoc (secX (B : X.Opens) W.unop r) (secX (B : X.Opens) W.unop a) _) }
     naturality := fun {W W'} i => by
       apply ModuleCat.hom_ext
       apply LinearMap.ext
       intro a
       apply Subtype.ext
       change secX (B : X.Opens) W'.unop
         (X.presheaf.map ((B : X.Opens).ι.opensFunctor.map i.unop).op
           (secX (B : X.Opens) W.unop a)) * gOn B g _ _ =
         X.presheaf.map ((B : X.Opens).ι.opensFunctor.map i.unop).op
           (secX (B : X.Opens) W.unop a * gOn B g _ _)
       rw [map_mul, gOn_res] }⟩

lemma mulGen_app_apply_coe (W : (((B : X.Opens) : Scheme.{u}).Opens)ᵒᵖ)
    (a : Γ((B : X.Opens), W.unop)) :
    ((mulGen I B g hIg).val.app W a).1 =
      secX (B : X.Opens) W.unop a * gOn B g _ (image_le _ W.unop) := rfl

include hg in
lemma isIso_mulGen : IsIso (mulGen I B g hIg) := by
  set ψ := mulGen I B g hIg
  let J := Opens.grothendieckTopology ((B : X.Opens) : Scheme.{u})
  have refine : ∀ (W' : ((B : X.Opens) : Scheme.{u}).Opens) (y : (B : X.Opens)), y ∈ W' →
      ∃ (h' : Γ(X, B)) (W'' : ((B : X.Opens) : Scheme.{u}).Opens) (_ : W'' ⟶ W'), y ∈ W'' ∧
        (B : X.Opens).ι ''ᵁ W'' = X.basicOpen h' := by
    intro W' y hy
    have hy' : (B : X.Opens).ι.base y ∈ (B : X.Opens).ι ''ᵁ W' := ⟨y, hy, rfl⟩
    obtain ⟨h', hle, hh'⟩ := B.2.exists_basicOpen_le ⟨_, hy'⟩ (image_le _ W' hy')
    refine ⟨h', (B : X.Opens).ι ⁻¹ᵁ (X.basicOpen h'), homOfLE ?_, hh', image_preimage_of_le
      (X.basicOpen_le h')⟩
    intro z hz
    obtain ⟨z', hz', hzz'⟩ := hle hz
    rwa [← (B : X.Opens).ι.isOpenEmbedding.injective hzz']
  have hsurj : Presheaf.IsLocallySurjective J ((SheafOfModules.toSheaf _).map ψ).hom := by
    constructor
    rintro W ⟨t, ht⟩
    refine fun y hy => ?_
    obtain ⟨h', W'', i, hyW'', hW''⟩ := refine W y hy
    refine ⟨W'', i, ?_, hyW''⟩
    have haff : IsAffineOpen ((B : X.Opens).ι ''ᵁ W'') := hW'' ▸ (X.affineBasicOpen h').2
    have ht' := I.map_mem_sectionsIdeal ((B : X.Opens).ι.opensFunctor.map i) ht
    rw [sectionsIdeal_eq_span I B g hIg _ haff (image_le _ _), Ideal.mem_span_singleton'] at ht'
    obtain ⟨a, ha⟩ := ht'
    exact ⟨a, Subtype.ext ha⟩
  have hinj : Presheaf.IsLocallyInjective J ((SheafOfModules.toSheaf _).map ψ).hom := by
    constructor
    intro W a b hab
    refine fun y hy => ?_
    obtain ⟨h', W'', i, hyW'', hW''⟩ := refine W.unop y hy
    refine ⟨W'', i, ?_, hyW''⟩
    have hab' : secX (B : X.Opens) W.unop a * gOn B g _ (image_le _ W.unop) =
        secX (B : X.Opens) W.unop b * gOn B g _ (image_le _ W.unop) := congrArg Subtype.val hab
    have := congrArg (X.presheaf.map ((B : X.Opens).ι.opensFunctor.map i).op) hab'
    rw [map_mul, map_mul, gOn_res] at this
    exact (mul_cancel_right_mem_nonZeroDivisors (gOn_mem_nonZeroDivisors B g hg h' _ hW'')).1 this
  have h₁ : IsIso ((SheafOfModules.toSheaf _).map ψ) :=
    (Sheaf.isLocallyBijective_iff_isIso _).1 ⟨hinj, hsurj⟩
  have h₂ : IsIso ((PresheafOfModules.toPresheaf _).map ((SheafOfModules.forget _).map ψ)) := by
    change IsIso ((sheafToPresheaf _ _).map ((SheafOfModules.toSheaf _).map ψ))
    infer_instance
  have := (SheafOfModules.fullyFaithfulForget
    (((B : X.Opens) : Scheme.{u}).ringCatSheaf)).reflectsIsomorphisms
  have h₃ := isIso_of_reflects_iso ((SheafOfModules.forget _).map ψ)
    (PresheafOfModules.toPresheaf _)
  exact isIso_of_reflects_iso ψ (SheafOfModules.forget _)

end trivialization

end AlgebraicGeometry.Scheme.IdealSheafData

end

open _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.IdealSheafData in
with_weak_namespace AlgebraicGeometry.Scheme.IdealSheafData
theorem _root_.AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible.isInvertible_module {X :
  AlgebraicGeometry.Scheme.{u}} {I : X.IdealSheafData} (hI : I.IsInvertible) :
    AlgebraicGeometry.Scheme.Modules.IsInvertible I.module := by
  have h1 : Scheme.Modules.IsInvertible I.toModule := by
    refine ⟨fun x => ?_⟩
    obtain ⟨U, f, hxf, g, hg, hIg⟩ := hI x
    have := isIso_mulGen I (X.affineBasicOpen f) g hg hIg
    exact ⟨X.basicOpen f, hxf, ⟨(restrictFunctor'IsoPullback (X.basicOpen f)).symm.app _ ≪≫
      (asIso (mulGen I (X.affineBasicOpen f) g hIg)).symm⟩⟩
  refine ⟨fun x => ?_⟩
  obtain ⟨U, hxU, ⟨e⟩⟩ := h1.1 x
  exact ⟨U, hxU, ⟨(Scheme.Modules.pullback U.ι).mapIso (moduleIsoToModule I) ≪≫ e⟩⟩
end Scheme_IdealSheafData_IsInvertible_isInvertible_module
end AlgebraicCurves.Geometry.Sheaves.Proofs
end ProofImplementation
