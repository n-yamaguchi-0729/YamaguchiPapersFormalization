/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.EtaleFundamentalGroups.GeometricFiber.ArithmeticSections
import Mathlib.CategoryTheory.Limits.MorphismProperty

/-!
# Arithmetic Section Factorization

Every categorical section after a separable constant extension factors
through the pullback of an actual finite étale constant cover.
-/

noncomputable section
open CategoryTheory Limits
universe u
namespace AlgebraicGeometry.FiniteEtale

/-- Every categorical section after a separable constant extension factors
through the pullback of an actual finite étale constant cover. -/
theorem exists_constantCover_section_factorization
    (k L : Type u) [Field k] [Field L] [Algebra k L] [Algebra.IsSeparable k L]
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (f : X ⟶ Spec (.of k)) (Y : FiniteEtale X)
    (s : ⊤_ (FiniteEtale (Limits.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap k L))) f)) ⟶
      (pullback (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k L))) f)).obj Y) :
    ∃ A : FiniteEtale (Spec (.of k)), ∃ q : (pullback f).obj A ⟶ Y,
      ∃ r : ⊤_ (FiniteEtale (Limits.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap k L))) f)) ⟶
        (pullback (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k L))) f)).obj
          ((pullback f).obj A),
        r ≫ (pullback (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k L))) f)).map q = s
          := by
  let XL := Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L))) f
  let p : XL ⟶ X := pullback.snd _ f
  let : IsFiniteEtale (𝟙 XL) := .mk
  let T : FiniteEtale XL := mk (𝟙 XL)
  let hT : IsTerminal T :=
    MorphismProperty.Over.mkIdTerminal (@IsFiniteEtale : MorphismProperty Scheme.{u}) XL
  let e : T ≅ ⊤_ (FiniteEtale XL) := hT.uniqueUpToIso terminalIsTerminal
  let v : T ⟶ (pullback p).obj Y := e.hom ≫ s
  let l : XL ⟶ Limits.pullback Y.hom p := v.left
  let a : XL ⟶ Y.left := l ≫ pullback.fst Y.hom p
  have hv : l ≫ pullback.snd Y.hom p = 𝟙 XL := v.w
  have ha : a ≫ Y.hom = p := by
    dsimp only [a]
    rw [Category.assoc, pullback.condition, ← Category.assoc, hv, Category.id_comp]
  obtain ⟨A, _, q, b, hb, hbX⟩ := exists_constantCover_factorization k L X f Y a ha
  let N := (pullback f).obj A
  let rleft : XL ⟶ Limits.pullback N.hom p :=
    pullback.lift b (𝟙 XL) (hbX.trans (Category.id_comp p).symm)
  let r₀ : T ⟶ (pullback p).obj N := MorphismProperty.Over.homMk rleft
    (pullback.lift_snd _ _ _)
  let q₀ : N.left ⟶ Y.left := q.left
  let qL : Limits.pullback N.hom p ⟶ Limits.pullback Y.hom p := ((pullback p).map q).left
  have hqfst : qL ≫ pullback.fst Y.hom p =
      pullback.fst N.hom p ≫ q₀ := pullback.lift_fst _ _ _
  have hqsnd : qL ≫ pullback.snd Y.hom p =
      pullback.snd N.hom p := pullback.lift_snd _ _ _
  have hr : r₀ ≫ (pullback p).map q = v := by
    apply MorphismProperty.Over.Hom.ext
    change rleft ≫ qL = l
    apply pullback.hom_ext
    · rw [Category.assoc, hqfst, ← Category.assoc]
      change (pullback.lift b (𝟙 XL) _ ≫ pullback.fst N.hom p) ≫ q₀ = _
      rw [pullback.lift_fst]
      exact hb
    · rw [Category.assoc, hqsnd]
      change pullback.lift b (𝟙 XL) _ ≫ pullback.snd N.hom p = _
      rw [pullback.lift_snd]
      exact hv.symm
  refine ⟨A, q, e.inv ≫ r₀, ?_⟩
  rw [Category.assoc, hr]
  change e.inv ≫ (e.hom ≫ s) = s
  rw [← Category.assoc, e.inv_hom_id, Category.id_comp]

end AlgebraicGeometry.FiniteEtale
