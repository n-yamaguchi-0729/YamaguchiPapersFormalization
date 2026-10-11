/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_DescentAction.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Geometry.Descent.DescentAction
import Mathlib.CategoryTheory.EffectiveEpi.Basic

/-!
# Points of an effective descent as matching local points

This identifies points of a descended scheme with the compatible elements of the
presheaf represented after base change. The presheaf is not assumed to be a sheaf.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

noncomputable section

namespace AlgebraicGeometry.DescentAction

variable {S S' : Scheme.{u}} (s : S' ⟶ S)
  (G : (Over S)ᵒᵖ ⥤ Type (u + 1))

/-- The descent compatibility condition for a local presheaf element. -/
def Matching (T : Over S)
    (z : G.obj (op ((Over.map s).obj ((Over.pullback s).obj T)))) : Prop :=
  ∀ ⦃W : Over S⦄ (g₁ g₂ : W ⟶ (Over.map s).obj ((Over.pullback s).obj T)),
    g₁ ≫ coverT s T = g₂ ≫ coverT s T → G.map g₁.op z = G.map g₂.op z

variable {X' : Scheme.{u}} (x' : X' ⟶ S')
  (hX' : ((Over.map s).op ⋙ G).RepresentableBy (Over.mk x'))
  {X : Scheme.{u}} (f : X ⟶ S) (e : pullback f s ≅ X')
  (he : e.hom ≫ x' = pullback.snd f s)

/-- The local presheaf element attached to a point of the descended scheme. -/
def localPoint {T : Over S} (m : T ⟶ Over.mk f) :
    G.obj (op ((Over.map s).obj ((Over.pullback s).obj T))) :=
  hX'.homEquiv (bc s x' f e he m)

theorem localPoint_eq_map_univBC {T : Over S} (m : T ⟶ Over.mk f) :
    localPoint s G x' hX' f e he m =
      G.map ((Over.map s).map ((Over.pullback s).map m)).op
        (univBC s G x' hX' f e he) := by
  rw [localPoint, homEquiv_eq_map_univ, bc, Functor.map_comp, op_comp,
    G.map_comp, types_comp_apply, univBC]

theorem localPoint_injective {T : Over S} [Epi (pullback.fst T.hom s)] :
    Function.Injective (localPoint s G x' hX' f e he (T := T)) := by
  intro m₁ m₂ h
  have h' : bc s x' f e he m₁ = bc s x' f e he m₂ := hX'.homEquiv.injective h
  have h'' := congrArg (fun k => k.left) h'
  change (bc s x' f e he m₁).left = (bc s x' f e he m₂).left at h''
  rw [bc_left, bc_left] at h''
  have h₃ := (cancel_mono e.hom).1 h''
  have h₄ := congrArg (fun k => k ≫ pullback.fst f s) h₃
  have h₅ : pullback.fst T.hom s ≫ m₁.left = pullback.fst T.hom s ≫ m₂.left :=
    ((pullback.lift_fst _ _ _).symm.trans h₄).trans (pullback.lift_fst _ _ _)
  ext
  exact (cancel_epi (pullback.fst T.hom s)).1 h₅

variable (hcompat : eRel s x' f e he ≫ repAct s G x' hX' =
  (canonical s f).act ≫ e.hom)

include hcompat in
theorem localPoint_matching {T : Over S} (m : T ⟶ Over.mk f) :
    Matching s G T (localPoint s G x' hX' f e he m) := by
  intro W g₁ g₂ hg
  rw [localPoint_eq_map_univBC]
  let b := (Over.map s).map ((Over.pullback s).map m)
  have hb : b ≫ cover s f = coverT s T ≫ m := (coverT_comp s f m).symm
  have hpair : (g₁ ≫ b) ≫ cover s f = (g₂ ≫ b) ≫ cover s f := by
    rw [Category.assoc, Category.assoc, hb, ← Category.assoc, ← Category.assoc, hg]
  have h := univBC_compatible s G x' hX' f e he hcompat (g₁ ≫ b) (g₂ ≫ b) hpair
  simpa only [op_comp, G.map_comp, types_comp_apply, b] using h

theorem matching_flip {T : Over S}
    (z : G.obj (op ((Over.map s).obj ((Over.pullback s).obj T))))
    (hz : Matching s G T z) :
    flipMap s T.hom ≫ leftHom s x' (hX'.homEquiv.symm z) =
      nRel s x' (hX'.homEquiv.symm z) ≫ repAct s G x' hX' := by
  let n := hX'.homEquiv.symm z
  have hn : hX'.homEquiv n = z := Equiv.apply_symm_apply _ _
  let ET : Over S' := Over.mk (pullback.snd (pullback.snd T.hom s ≫ s) s)
  let flipO : ET ⟶ (Over.pullback s).obj T :=
    Over.homMk (flipMap s T.hom) (flipMap_snd s T.hom)
  let nRelO : ET ⟶ Over.mk (pullback.snd (x' ≫ s) s) :=
    Over.homMk (nRel s x' n) (nRel_snd s x' n)
  let fstTS : (Over.map s).obj ET ⟶ (Over.map s).obj ((Over.pullback s).obj T) :=
    Over.homMk (pullback.fst _ _) pullback.condition
  have h₁ : (Over.map s).map flipO ≫ coverT s T = fstTS ≫ coverT s T := by
    ext
    exact flipMap_fst s T.hom
  have h₂ : (Over.map s).map nRelO ≫ fstOver s x' = fstTS ≫ (Over.map s).map n := by
    ext
    exact nRel_fst s x' n
  have key : flipO ≫ n = nRelO ≫ repActOver s G x' hX' := by
    apply hX'.homEquiv.injective
    rw [hX'.homEquiv_comp, hX'.homEquiv_comp, repActOver]
    simp only [Equiv.apply_symm_apply]
    rw [hn]
    change G.map ((Over.map s).map flipO).op z =
      G.map ((Over.map s).map nRelO).op (G.map (fstOver s x').op (univ s G x' hX'))
    rw [← types_comp_apply (G.map _) (G.map ((Over.map s).map nRelO).op),
      ← G.map_comp, ← op_comp, h₂, op_comp, G.map_comp, types_comp_apply,
      ← homEquiv_eq_map_univ]
    change G.map ((Over.map s).map flipO).op z =
      G.map fstTS.op (hX'.homEquiv (hX'.homEquiv.symm z))
    rw [Equiv.apply_symm_apply]
    exact hz _ _ h₁
  exact congrArg (fun k => k.left) key

theorem matching_desc_condition
    (hcompat : eRel s x' f e he ≫ repAct s G x' hX' = (canonical s f).act ≫ e.hom)
    {T : Over S}
    (z : G.obj (op ((Over.map s).obj ((Over.pullback s).obj T))))
    (hz : Matching s G T z) {W : Scheme.{u}} (g₁ g₂ : W ⟶ pullback T.hom s)
    (hg : g₁ ≫ pullback.fst T.hom s = g₂ ≫ pullback.fst T.hom s) :
    g₁ ≫ (leftHom s x' (hX'.homEquiv.symm z) ≫ e.inv ≫ pullback.fst f s) =
      g₂ ≫ (leftHom s x' (hX'.homEquiv.symm z) ≫ e.inv ≫ pullback.fst f s)
        := by
  set n := hX'.homEquiv.symm z with hn
  have w : g₁ ≫ pullback.snd T.hom s ≫ s = (g₂ ≫ pullback.snd T.hom s) ≫ s := by
    rw [Category.assoc, ← pullback.condition, reassoc_of% hg]
  let ρ : W ⟶ pullback (pullback.snd T.hom s ≫ s) s := pullback.lift g₁ (g₂ ≫ pullback.snd T.hom s)
    w
  have hρ₁ : g₁ = ρ ≫ pullback.fst _ _ := (pullback.lift_fst _ _ _).symm
  have hρ₂ : g₂ = ρ ≫ flipMap s T.hom := by
    apply pullback.hom_ext
    · rw [Category.assoc, flipMap_fst, pullback.lift_fst_assoc]
      exact hg.symm
    · rw [Category.assoc, flipMap_snd]
      exact (pullback.lift_snd _ _ _).symm
  have heinv : e.inv ≫ pullback.snd f s = x' := by rw [← he, Iso.inv_hom_id_assoc]
  let N : pullback T.hom s ⟶ pullback f s := leftHom s x' n ≫ e.inv
  have hN₂ : N ≫ pullback.snd f s = pullback.snd T.hom s := by
    change (leftHom s x' n ≫ e.inv) ≫ pullback.snd f s = _
    rw [Category.assoc, heinv, leftHom_comp]
  let NS : pullback (pullback.snd T.hom s ≫ s) s ⟶ pullback (pullback.snd f s ≫ s) s :=
    pullback.map _ _ _ _ N (𝟙 _) (𝟙 _) (by rw [Category.comp_id, reassoc_of% hN₂])
      (by rw [Category.comp_id, Category.id_comp])
  have hNS₁ : NS ≫ pullback.fst _ _ = pullback.fst _ _ ≫ N := pullback.lift_fst _ _ _
  have hNS₂ : NS ≫ pullback.snd _ _ = pullback.snd _ _ := (pullback.lift_snd _ _ _).trans
    (Category.comp_id _)
  have hN : NS ≫ eRel s x' f e he = nRel s x' n := by
    apply pullback.hom_ext
    · rw [Category.assoc, eRel_fst, nRel_fst, ← Category.assoc, hNS₁, Category.assoc]
      change pullback.fst _ _ ≫ (leftHom s x' n ≫ e.inv) ≫ e.hom = _
      rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    · rw [Category.assoc, eRel_snd, nRel_snd, hNS₂]
  rw [hρ₁, hρ₂, Category.assoc, Category.assoc]
  congr 1
  rw [reassoc_of% matching_flip s G x' hX' z hz, ← hN, Category.assoc,
    reassoc_of% hcompat, Iso.hom_inv_id_assoc]
  change _ = NS ≫ flipMap s f ≫ pullback.fst f s
  rw [flipMap_fst, reassoc_of% hNS₁]
  simp only [N, Category.assoc]

theorem exists_localPoint_of_matching
    (hcompat : eRel s x' f e he ≫ repAct s G x' hX' = (canonical s f).act ≫
  e.hom)
    {T : Over S} [EffectiveEpi (pullback.fst T.hom s)]
    (z : G.obj (op ((Over.map s).obj ((Over.pullback s).obj T))))
    (hmatch : Matching s G T z) :
    ∃ m : T ⟶ Over.mk f, localPoint s G x' hX' f e he m = z := by
  set n := hX'.homEquiv.symm z with hn
  have hz : hX'.homEquiv n = z := Equiv.apply_symm_apply _ _
  have heinv : e.inv ≫ pullback.snd f s = x' := by rw [← he, Iso.inv_hom_id_assoc]
  let N : pullback T.hom s ⟶ pullback f s := leftHom s x' n ≫ e.inv
  have hN₂ : N ≫ pullback.snd f s = pullback.snd T.hom s := by
    change (leftHom s x' n ≫ e.inv) ≫ pullback.snd f s = _
    rw [Category.assoc, heinv, leftHom_comp]
  let a : pullback T.hom s ⟶ X := leftHom s x' n ≫ e.inv ≫ pullback.fst f s
  let ml : T.left ⟶ X := EffectiveEpi.desc (pullback.fst T.hom s) a
    (fun g₁ g₂ hg => matching_desc_condition s G x' hX' f e he hcompat z hmatch g₁ g₂ hg)
  have hml : pullback.fst T.hom s ≫ ml = a := EffectiveEpi.fac _ _ _
  have hmf : ml ≫ f = T.hom := by
    apply (cancel_epi (pullback.fst T.hom s)).1
    rw [← Category.assoc, hml]
    change ((leftHom s x' n ≫ e.inv) ≫ pullback.fst f s) ≫ f = _
    rw [Category.assoc, pullback.condition, ← Category.assoc, hN₂]
    exact pullback.condition.symm
  let m : T ⟶ Over.mk f := Over.homMk ml hmf
  have hlift : pullback.lift (pullback.fst T.hom s ≫ ml) (pullback.snd T.hom s)
      (by rw [Category.assoc, hmf]; exact pullback.condition) = N := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, hml]
      change (leftHom s x' n ≫ e.inv) ≫ pullback.fst f s = N ≫ pullback.fst f s
      rfl
    · rw [pullback.lift_snd, hN₂]
  have hbc : bc s x' f e he m = n := by
    ext
    change pullback.lift (pullback.fst T.hom s ≫ ml) (pullback.snd T.hom s) _ ≫ e.hom = leftHom s
      x' n
    rw [hlift]
    change (leftHom s x' n ≫ e.inv) ≫ e.hom = _
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact ⟨m, by rw [localPoint, hbc, hz]⟩

/-- Effective descent identifies scheme points with matching local presheaf elements. -/
def matchingEquiv {T : Over S} [EffectiveEpi (pullback.fst T.hom s)] :
    (T ⟶ Over.mk f) ≃
      {z : G.obj (op ((Over.map s).obj ((Over.pullback s).obj T))) // Matching s G T z} :=
  Equiv.ofBijective
    (fun m => ⟨localPoint s G x' hX' f e he m,
      localPoint_matching s G x' hX' f e he hcompat m⟩)
    ⟨fun _ _ h => localPoint_injective s G x' hX' f e he (congrArg Subtype.val h),
      fun z => by
        obtain ⟨m, hm⟩ := exists_localPoint_of_matching s G x' hX' f e he hcompat z.1 z.2
        exact ⟨m, Subtype.ext hm⟩⟩

end AlgebraicGeometry.DescentAction
