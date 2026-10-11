/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_IsLocallyFreeOfRank_exists_basis.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesLocallyFreeOfRank

/-!
# Local bases of finite locally free module sheaves

Local trivializations yield compatible bases of section modules on smaller opens
contained in a neighborhood of each point.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_IsLocallyFreeOfRank_exists_basis

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.Opposite
open _root_.TopologicalSpace

namespace PresheafOfModules
open _root_.PresheafOfModules
open _root_.PresheafOfModules

variable {C : Type*} [Category C] (R : Cᵒᵖ ⥤ CommRingCat.{u}) (n : ℕ)

/-- The presheaf of finite tuples of ring sections. -/
noncomputable def piPowAb : Cᵒᵖ ⥤ Ab.{u} where
  obj X := AddCommGrpCat.of (Fin n → R.obj X)
  map {X Y} f := AddCommGrpCat.ofHom (AddMonoidHom.compLeft (R.map f).hom.toAddMonoidHom (Fin n))
  map_id X := by ext v i; simp
  map_comp f g := by ext v i; simp

noncomputable scoped instance instModulePiPowAb (X : Cᵒᵖ) :
    Module ((R ⋙ forget₂ CommRingCat RingCat).obj X) ((piPowAb R n).obj X) :=
  inferInstanceAs (Module (R.obj X) (Fin n → R.obj X))

/-- The module presheaf of finite tuples of ring sections. -/
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

/-- The tuple module presheaf over the scheme structure ring. -/
noncomputable abbrev piPowPresheaf : X.PresheafOfModules := PresheafOfModules.piPow X.sheaf.obj n

/-- The additive sheaf underlying the structure ring. -/
noncomputable abbrev ringCatSheafAb : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  (sheafCompose (Opens.grothendieckTopology X) (forget₂ RingCat.{u} AddCommGrpCat.{u})).obj
      X.ringCatSheaf

/-- The product cone whose coordinates are the structure sheaf. -/
noncomputable def piPowCone :
    Cone (Discrete.functor (fun _ : Fin n => ringCatSheafAb X) ⋙ sheafToPresheaf _ _) where
  pt := (piPowPresheaf X n).presheaf
  π := Discrete.natTrans (fun i =>
    { app := fun V => AddCommGrpCat.ofHom (X := Fin n → (X.presheaf.obj V : Type u))
        (Y := (X.presheaf.obj V : Type u))
        (Pi.evalAddMonoidHom (fun _ : Fin n => (X.presheaf.obj V : Type u)) i.as)
      naturality := fun V W g => by ext v; rfl })

/-- The universal property of the finite tuple product cone. -/
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

/-- Projection of the tuple module sheaf onto one coordinate. -/
noncomputable def piPowπ (i : Fin n) : piPow X n ⟶ SheafOfModules.unit X.ringCatSheaf :=
  ⟨PresheafOfModules.homMk (M₂ := PresheafOfModules.unit _)
    { app := fun V => AddCommGrpCat.ofHom (X := Fin n → (X.presheaf.obj V : Type u))
        (Y := (X.presheaf.obj V : Type u))
        (Pi.evalAddMonoidHom (fun _ : Fin n => (X.presheaf.obj V : Type u)) i)
      naturality := fun V W g => by ext v; rfl }
    (fun V r v => rfl)⟩

lemma piPowπ_apply (i : Fin n) (V : X.Opensᵒᵖ) (v : Fin n → (X.presheaf.obj V : Type u)) :
    ((piPowπ X n i).val.app V (show (piPow X n).val.obj V from v) : X.presheaf.obj V) = v i := rfl

/-- Insertion of a structure-sheaf section into one tuple coordinate. -/
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

/-- The finite biproduct bicone of copies of the structure module. -/
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
  refine (LinearMap.sum_apply Finset.univ
    (fun j : ULift.{u} (Fin n) =>
      (((piPowBicone X n).π j ≫ (piPowBicone X n).ι j).val.app V).hom)
    (show (piPow X n).val.obj V from v)).trans ?_
  change (∑ j : ULift.{u} (Fin n), (Pi.single j.down (v j.down) : Fin n → X.presheaf.obj V)) = v
  rw [Fintype.sum_equiv Equiv.ulift
    (fun j : ULift.{u} (Fin n) => (Pi.single j.down (v j.down) : Fin n → X.presheaf.obj V))
    (fun i : Fin n => Pi.single i (v i)) (fun _ => rfl)]
  exact Finset.univ_sum_single _

/-- The bilimit structure on the finite tuple bicone. -/
noncomputable def isBilimitPiPowBicone : (piPowBicone X n).IsBilimit :=
  isBilimitOfTotal _ (piPowBicone_total X n)

/-- The comparison between the finite free module sheaf and its tuple model. -/
noncomputable def freeIsoPiPow : SheafOfModules.free.{u} (ULift.{u} (Fin n)) ≅ piPow X n :=
  IsColimit.coconePointUniqueUpToIso
    (SheafOfModules.isColimitFreeCofan.{u} (R := X.ringCatSheaf) (ULift.{u} (Fin n)))
    (isBilimitPiPowBicone X n).isColimit

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace Modules
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry

variable {X : Scheme.{u}}

section helpers

lemma map_eq_map' {M : X.Modules} {W₁ W₂ : X.Opens} (i j : W₁ ⟶ W₂) (m : Γ(M, W₂)) :
    M.presheaf.map i.op m = M.presheaf.map j.op m := by
  rw [Subsingleton.elim i j]

lemma map_map_of_eq {M : X.Modules} {W₁ W₂ : X.Opens} (h : W₁ = W₂) (m : Γ(M, W₂)) :
    M.presheaf.map (homOfLE h.ge).op (M.presheaf.map (homOfLE h.le).op m) = m := by
  subst h
  rw [← CategoryTheory.comp_apply, ← Functor.map_comp]
  have : ((homOfLE (le_refl W₁)).op ≫ (homOfLE (le_refl W₁)).op) = 𝟙 _ := Subsingleton.elim _ _
  rw [this, CategoryTheory.Functor.map_id]
  rfl

lemma ringMap_ringMap_of_eq {W₁ W₂ : X.Opens} (h : W₁ = W₂) (a : Γ(X, W₂)) :
    X.presheaf.map (homOfLE h.ge).op (X.presheaf.map (homOfLE h.le).op a) = a := by
  subst h
  rw [← CategoryTheory.comp_apply, ← Functor.map_comp]
  have : ((homOfLE (le_refl W₁)).op ≫ (homOfLE (le_refl W₁)).op) = 𝟙 _ := Subsingleton.elim _ _
  rw [this, CategoryTheory.Functor.map_id]
  rfl

lemma image_preimage_eq_of_le {V W : X.Opens} (hW : W ≤ V) : V.ι ''ᵁ (V.ι ⁻¹ᵁ W) = W := by
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_eq_right.2 hW]

lemma restrictFunctor_obj_presheaf_map (M : X.Modules) (V : X.Opens) {W₁ W₂ : (V :
  Scheme.{u}).Opens}
    (i : W₁ ⟶ W₂) (m : Γ((restrictFunctor V.ι).obj M, W₂)) :
    ((restrictFunctor V.ι).obj M).presheaf.map i.op m =
      M.presheaf.map (homOfLE (V.ι.image_mono i.le)).op (m : Γ(M, V.ι ''ᵁ W₂)) := by
  rw [Scheme.Modules.restrict_map]
  exact map_eq_map' _ _ _

end helpers

namespace IsLocallyFreeOfRank
open _root_.AlgebraicGeometry.Scheme.Modules.IsLocallyFreeOfRank
end IsLocallyFreeOfRank
namespace IsLocallyFreeOfRank
open scoped _root_.AlgebraicGeometry.Scheme.Modules.IsLocallyFreeOfRank in
private theorem _root_.AlgebraicGeometry.Scheme.Modules.IsLocallyFreeOfRank.exists_basis_impl {n :
    ℕ} {M : X.Modules} (hM : IsLocallyFreeOfRank n M) (x : X) :
    ∃ (V : X.Opens), x ∈ V ∧ ∃ e : Fin n → Γ(M, V), ∀ (W : X.Opens) (hW : W ≤ V),
      ∃ b : Module.Basis (Fin n) Γ(X, W) Γ(M, W), ∀ i, b i = M.presheaf.map (homOfLE hW).op (e i) :=
          by
  obtain ⟨V, hxV, ⟨e⟩⟩ := hM.exists_trivialization x
  let t : (restrictFunctor V.ι).obj M ≅ piPow (V : Scheme.{u}) n :=
    (restrictFunctorIsoPullback V.ι).app M ≪≫ e ≪≫ freeIsoPiPow (V : Scheme.{u}) n
  have hV : V.ι ''ᵁ ⊤ = V := V.ι_image_top
  let std : ∀ (W' : (V : Scheme.{u}).Opens), Fin n → Γ(piPow (V : Scheme.{u}) n, W') :=
    fun W' i => (Pi.single i 1 : Fin n → ((V : Scheme.{u}).presheaf.obj (op W')))
  let e₀ : Fin n → Γ(M, V.ι ''ᵁ ⊤) := fun i => (t.inv.app ⊤ (std ⊤ i) : Γ(M, V.ι ''ᵁ ⊤))
  refine ⟨V, hxV, fun i => M.presheaf.map (homOfLE hV.ge).op (e₀ i), fun W hW => ?_⟩
  let W' : (V : Scheme.{u}).Opens := V.ι ⁻¹ᵁ W
  have hW' : V.ι ''ᵁ W' = W := image_preimage_eq_of_le hW
  let ρ : Γ(M, W) → Γ(M, V.ι ''ᵁ W') := fun m => M.presheaf.map (homOfLE hW'.le).op m
  let σ : Γ(M, V.ι ''ᵁ W') → Γ(M, W) := fun m => M.presheaf.map (homOfLE hW'.ge).op m
  let ρR : Γ(X, W) → Γ(X, V.ι ''ᵁ W') := fun a => X.presheaf.map (homOfLE hW'.le).op a
  let σR : Γ(X, V.ι ''ᵁ W') → Γ(X, W) := fun a => X.presheaf.map (homOfLE hW'.ge).op a
  have hσρ : ∀ m, σ (ρ m) = m := fun m => map_map_of_eq hW' m
  have hσρR : ∀ a, σR (ρR a) = a := fun a => ringMap_ringMap_of_eq hW' a
  have hρ_smul : ∀ (a : Γ(X, W)) (m : Γ(M, W)), ρ (a • m) = ρR a • ρ m :=
    fun a m => Modules.map_smul M _ a m
  have hσ_smul : ∀ (a : Γ(X, V.ι ''ᵁ W')) (m : Γ(M, V.ι ''ᵁ W')), σ (a • m) = σR a • σ m :=
    fun a m => Modules.map_smul M _ a m
  have hρ0 : ρ 0 = 0 := map_zero (ConcreteCategory.hom (M.presheaf.map (homOfLE hW'.le).op))
  have hσR0 : σR 0 = 0 := map_zero (ConcreteCategory.hom (X.presheaf.map (homOfLE hW'.ge).op))
  have hρsum : ∀ (f : Fin n → Γ(M, W)), ρ (∑ j, f j) = ∑ j, ρ (f j) :=
    fun f => map_sum (ConcreteCategory.hom (M.presheaf.map (homOfLE hW'.le).op)) _ _
  have hσsum : ∀ (f : Fin n → Γ(M, V.ι ''ᵁ W')), σ (∑ j, f j) = ∑ j, σ (f j) :=
    fun f => map_sum (ConcreteCategory.hom (M.presheaf.map (homOfLE hW'.ge).op)) _ _
  have key : ∀ i, ρ (M.presheaf.map (homOfLE hW).op (M.presheaf.map (homOfLE hV.ge).op (e₀ i))) =
      (t.inv.app W' (std W' i) : Γ(M, V.ι ''ᵁ W')) := by
    intro i
    have h1 : ρ (M.presheaf.map (homOfLE hW).op (M.presheaf.map (homOfLE hV.ge).op (e₀ i))) =
        M.presheaf.map (homOfLE (V.ι.image_mono (le_top : W' ≤ ⊤))).op (e₀ i) := by
      change M.presheaf.map _ (M.presheaf.map _ (M.presheaf.map _ (e₀ i))) = _
      rw [← CategoryTheory.comp_apply, ← CategoryTheory.comp_apply, ← Functor.map_comp, ←
          Functor.map_comp]
      exact map_eq_map' _ _ _
    rw [h1]
    have h2 := congr($(t.inv.mapPresheaf.naturality (homOfLE (le_top : W' ≤ ⊤)).op) (std ⊤ i))
    simp only [CategoryTheory.comp_apply, mapPresheaf_app] at h2
    have h3 : (piPow (V : Scheme.{u}) n).presheaf.map (homOfLE (le_top : W' ≤ ⊤)).op (std ⊤ i) = std
        W' i := by
      funext j
      change (V : Scheme.{u}).presheaf.map (homOfLE (le_top : W' ≤ ⊤)).op ((Pi.single i 1 : Fin n →
          _) j) =
        (Pi.single i 1 : Fin n → _) j
      by_cases h : j = i
      · subst h; simp
      · simp [Pi.single_eq_of_ne h]
    rw [h3] at h2
    rw [h2]
    exact (restrictFunctor_obj_presheaf_map M V (homOfLE (le_top : W' ≤ ⊤)) _).symm
  let A : Type u := Γ((V : Scheme.{u}), W')
  let N : Type u := Γ((restrictFunctor V.ι).obj M, W')
  have ht₁ : ∀ m : N, (t.inv.app W') (t.hom.app W' m) = m := fun m => by
    rw [← CategoryTheory.comp_apply, ← Scheme.Modules.Hom.comp_app, t.hom_inv_id,
        Scheme.Modules.Hom.id_app]
    rfl
  have ht₂ : ∀ v : Γ(piPow (V : Scheme.{u}) n, W'), (t.hom.app W') (t.inv.app W' v) = v := fun v =>
      by
    rw [← CategoryTheory.comp_apply, ← Scheme.Modules.Hom.comp_app, t.inv_hom_id,
        Scheme.Modules.Hom.id_app]
    rfl
  let tW : N ≃ₗ[A] (Fin n → A) :=
    { toFun := fun m => (t.hom.app W' m : (Fin n → A))
      invFun := fun v => (t.inv.app W' v : N)
      map_add' := fun m m' => (t.hom.app W').hom.map_add m m'
      map_smul' := fun a m => by
        rw [RingHom.id_apply]
        exact Hom.app_smul t.hom a m
      left_inv := ht₁
      right_inv := ht₂ }
  let b' : Module.Basis (Fin n) A N := (Pi.basisFun A (Fin n)).map tW.symm
  have hb' : ∀ i, b' i = (t.inv.app W' (std W' i) : N) := fun i => by
    simp only [b', Module.Basis.map_apply, Pi.basisFun_apply]
    rfl
  have hXN : ∀ (a : Γ(X, V.ι ''ᵁ W')) (m : Γ(M, V.ι ''ᵁ W')), a • m = @HSMul.hSMul A N N _ a m := by
    intro a m
    change _ = (((V.ι.appIso W').inv a : Γ(X, V.ι ''ᵁ W')) • m : Γ(M, V.ι ''ᵁ W'))
    (simp [Scheme.Opens.ι_appIso]; rfl)
  let v : Fin n → Γ(M, W) := fun i => M.presheaf.map (homOfLE hW).op (M.presheaf.map (homOfLE
      hV.ge).op (e₀ i))
  have hρv : ∀ i, ρ (v i) = (b' i : Γ(M, V.ι ''ᵁ W')) := fun i => (key i).trans (hb' i).symm
  have hli : LinearIndependent Γ(X, W) v := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    have h0 : ∑ j, @HSMul.hSMul A N N _ (ρR (c j)) (b' j) = (0 : N) := by
      have h := congrArg ρ hc
      rw [hρ0, hρsum] at h
      have he : ∑ j, ρ (c j • v j) = ∑ j, @HSMul.hSMul A N N _ (ρR (c j)) (b' j) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        exact (hρ_smul (c j) (v j)).trans
          ((hXN (ρR (c j)) (ρ (v j))).trans
            (congrArg (fun m : N => (show A from ρR (c j)) • m) (hρv j)))
      exact he.symm.trans h
    have h1 : ρR (c i) = 0 :=
      (Fintype.linearIndependent_iff.mp b'.linearIndependent) (fun j => ρR (c j)) h0 i
    rw [← hσρR (c i)]
    change σR (ρR (c i)) = 0
    rw [h1, hσR0]
  have hsp : ⊤ ≤ Submodule.span (X.presheaf.obj (op W)) (Set.range v) := by
    rintro m -
    set r := b'.repr (ρ m) with hr
    have hm : ρ m = ∑ j, @HSMul.hSMul A N N _ (r j) (b' j) := (b'.sum_repr (ρ m)).symm
    have hm' : m = ∑ j, σR (r j) • v j := by
      have hs : σ (∑ j, (show Γ(M, V.ι ''ᵁ W') from (r j) • b' j)) =
          ∑ j, σ (show Γ(M, V.ι ''ᵁ W') from (r j) • b' j) :=
        hσsum (fun j => (show Γ(M, V.ι ''ᵁ W') from (r j) • b' j))
      have ht : ∀ j : Fin n,
          σ (show Γ(M, V.ι ''ᵁ W') from (r j) • b' j) = σR (r j) • v j := by
        intro j
        have hb : σ (show Γ(M, V.ι ''ᵁ W') from b' j) = v j :=
          (congrArg σ (hρv j).symm).trans (hσρ (v j))
        exact ((congrArg σ (hXN (r j) (b' j)).symm).trans
          (hσ_smul (r j) (b' j))).trans
            (congrArg (fun z : Γ(M, W) => σR (r j) • z) hb)
      exact ((hσρ m).symm.trans (congrArg σ hm)).trans
        (hs.trans (Finset.sum_congr rfl (fun j _ => ht j)))
    rw [hm']
    exact Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))
  exact ⟨Module.Basis.mk hli hsp, fun i => by rw [Module.Basis.mk_apply]⟩

end IsLocallyFreeOfRank
open _root_.AlgebraicGeometry.Scheme.Modules
end AlgebraicGeometry.Scheme.Modules

theorem _root_.AlgebraicGeometry.Scheme.Modules.IsLocallyFreeOfRank.exists_basis {X :
  AlgebraicGeometry.Scheme.{u}} {n : ℕ} {M : X.Modules}
    (hM : AlgebraicGeometry.Scheme.Modules.IsLocallyFreeOfRank n M) (x : X) :
    ∃ (V : X.Opens), x ∈ V ∧ ∃ e : Fin n → Γ(M, V), ∀ (W : X.Opens) (hW : W ≤ V),
      ∃ b : Module.Basis (Fin n) Γ(X, W) Γ(M, W), ∀ i, b i = M.presheaf.map (homOfLE hW).op (e i) :=
  hM.exists_basis_impl x
end AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_IsLocallyFreeOfRank_exists_basis
end ProofImplementation
