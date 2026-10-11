/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.FiniteEtale.FiniteField.SchemeHomDescent
import Nyll.EtaleFundamentalGroups.FiniteEtale.Connected
import Mathlib.CategoryTheory.Limits.MorphismProperty

/-!
# Arithmetic Sections

A section after a separable algebraic constant extension factors through
an actual finite étale constant cover of the base.
-/

noncomputable section
open CategoryTheory Limits Opposite
open CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.FiniteEtale

universe u

/-- A section after a separable algebraic constant extension factors through
an actual finite étale constant cover of the base. -/
theorem exists_constantCover_factorization
    (k L : Type u) [Field k] [Field L] [Algebra k L] [Algebra.IsSeparable k L]
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (f : X ⟶ Spec (.of k)) (Y : FiniteEtale X)
    (a : Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L))) f ⟶ Y.left)
    (ha : a ≫ Y.hom = pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k L))) f) :
    ∃ A : FiniteEtale (Spec (.of k)), Nonempty A.left ∧
      ∃ q : (pullback f).obj A ⟶ Y,
      ∃ b : Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L))) f ⟶
        ((pullback f).obj A).left,
        b ≫ q.left = a ∧ b ≫ ((pullback f).obj A).hom =
          pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k L))) f := by
  obtain ⟨s, hfin, g, hrec, hg⟩ :=
    EtaleFundamentalGroups.exists_finiteIntermediateField_schemeHom k L X Y.left f Y.hom a ha
  let E := IntermediateField.adjoin k (s : Set L)
  let : FiniteDimensional k E := hfin
  let φE := Spec.map (CommRingCat.ofHom (algebraMap k E))
  let : IsFiniteEtale φE := by
    rw [IsFiniteEtale.SpecMap_iff, CommRingCat.hom_ofHom,
      RingHom.finiteEtale_algebraMap_iff]
    let : Algebra.Etale k E :=
      ⟨Algebra.FormallyEtale.of_isSeparable k E,
        Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩
    constructor
  let A : FiniteEtale (Spec (.of k)) := FiniteEtale.mk φE
  let q : (pullback f).obj A ⟶ Y := MorphismProperty.Over.homMk g hg
  let b := (EtaleFundamentalGroups.constantFieldInverseLimitCone k L X f).π.app (op s)
  refine ⟨A, inferInstanceAs (Nonempty (Spec (.of E))), q, b, hrec, ?_⟩
  exact Over.w ((EtaleFundamentalGroups.constantFieldInverseLimitOverCone k L X f).π.app (op s))

/-- A connected finite étale cover with a section after a separable
constant extension is dominated by a finite étale constant cover. -/
theorem exists_constantCover_epi_of_section
    (k L : Type u) [Field k] [Field L] [Algebra k L] [Algebra.IsSeparable k L]
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X] [ConnectedSpace X]
    (f : X ⟶ Spec (.of k)) (Y : FiniteEtale X) [IsConnected Y]
    (a : Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L))) f ⟶ Y.left)
    (ha : a ≫ Y.hom = pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k L))) f) :
    ∃ A : FiniteEtale (Spec (.of k)), ∃ q : (pullback f).obj A ⟶ Y, Epi q := by
  obtain ⟨A, hA, q, b, hb, hbX⟩ := exists_constantCover_factorization k L X f Y a ha
  let : Nonempty A.left := hA
  let N := (pullback f).obj A
  let : Nonempty N.left := pullback_obj_nonempty f A
  let x : X := Classical.choice (inferInstance : Nonempty X)
  let Ω := AlgebraicClosure (X.residueField x)
  let xi : Spec (.of Ω) ⟶ X :=
    Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) Ω)) ≫
      X.fromSpecResidueField x
  let : Nonempty ((fiber xi).obj N) := pullback_obj_nonempty xi N
  exact ⟨A, q, epi_of_nonempty_of_isConnected (fiber xi) q⟩

/-- A connected cover that acquires a categorical section over the
separable extension is an epimorphic image of a constant cover. -/
theorem exists_constantCover_epi_of_terminal_hom
    (k L : Type u) [Field k] [Field L] [Algebra k L] [Algebra.IsSeparable k L]
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X] [ConnectedSpace X]
    (f : X ⟶ Spec (.of k)) (Y : FiniteEtale X) [IsConnected Y]
    (s : ⊤_ (FiniteEtale (Limits.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap k L))) f)) ⟶
      (pullback (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k L))) f)).obj Y) :
    ∃ A : FiniteEtale (Spec (.of k)), ∃ q : (pullback f).obj A ⟶ Y, Epi q := by
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
  have ha : a ≫ Y.hom = p := by
    have hv : l ≫ pullback.snd Y.hom p = 𝟙 XL := v.w
    dsimp only [a]
    rw [Category.assoc, pullback.condition, ← Category.assoc, hv, Category.id_comp]
  exact exists_constantCover_epi_of_section k L X f Y a ha

end AlgebraicGeometry.FiniteEtale
