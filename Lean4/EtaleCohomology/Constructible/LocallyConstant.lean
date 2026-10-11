/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleCohomology.Sites.ConstantPullback
import EtaleCohomology.Sites.PullbackComposition
import EtaleCohomology.Sites.SheafFunctors
import Mathlib.AlgebraicGeometry.Cover.MorphismProperty
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.Hypercover.Zero
import Mathlib.RingTheory.Finiteness.Basic

/-!
# Locally constant étale sheaves of modules

Local constancy means that an actual étale cover trivializes the sheaf as a
sheafification of a constant presheaf. A predicate on the constant models
allows the same base-change and cover-refinement proofs to treat arbitrary
modules and finitely generated modules. No hypothesis on a base field,
noetherianity, or finiteness of the coefficient ring is imposed here.

See the definitions and inverse-image property in
https://stacks.math.columbia.edu/tag/09Y8 .
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace EtaleCohomology

variable {X Y : Scheme.{u}} (R : Type u) [CommRing R]

/-- Étale locally, the sheaf is constant with a model satisfying `P`.
The model may vary among the members of the cover. -/
def IsEtaleLocallyConstantWith (P : ModuleCat.{u} R → Prop)
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) : Prop :=
  ∃ 𝒰 : X.Cover.{u} (Scheme.precoverage (show MorphismProperty Scheme.{u} from @Etale)),
    ∀ a : 𝒰.I₀, ∃ M : ModuleCat.{u} R, P M ∧
      Nonempty ((etalePullback (𝒰.f a) R).obj G ≅
        (constantSheaf (𝒰.X a).smallEtaleTopology (ModuleCat.{u} R)).obj M)

/-- A sheaf of modules is locally constant if it is constant on an étale cover. -/
def IsEtaleLocallyConstant (G : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) : Prop :=
  IsEtaleLocallyConstantWith R (fun _ => True) G

/-- A finite type locally constant sheaf has finitely generated constant
module models on an étale cover. -/
def IsEtaleFiniteTypeLocallyConstant (G : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) : Prop :=
  IsEtaleLocallyConstantWith R (fun M => Module.Finite R M) G

variable {R} {P : ModuleCat.{u} R → Prop}

/-- Isomorphic sheaves have the same possible local constant models. -/
lemma IsEtaleLocallyConstantWith.of_iso
    {G H : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)}
    (hG : IsEtaleLocallyConstantWith R P G) (e : G ≅ H) :
    IsEtaleLocallyConstantWith R P H := by
  obtain ⟨𝒰, h𝒰⟩ := hG
  refine ⟨𝒰, fun a => ?_⟩
  obtain ⟨M, hM, ⟨eM⟩⟩ := h𝒰 a
  exact ⟨M, hM, ⟨(etalePullback (𝒰.f a) R).mapIso e.symm ≪≫ eM⟩⟩

/-- A constant sheaf is trivialized by the identity cover. -/
lemma IsEtaleLocallyConstantWith.constant (M : ModuleCat.{u} R) (hM : P M) :
    IsEtaleLocallyConstantWith R P
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj M) := by
  refine ⟨Scheme.coverOfIsIso (P := show MorphismProperty Scheme.{u} from @Etale) (𝟙 X), ?_⟩
  intro a
  exact ⟨M, hM, ⟨(etalePullbackConstantIso (𝟙 X) R).app M⟩⟩

/-- Pulling back the trivializing cover preserves its constant models. -/
lemma IsEtaleLocallyConstantWith.pullback (f : X ⟶ Y)
    {G : Sheaf Y.smallEtaleTopology (ModuleCat.{u} R)}
    (hG : IsEtaleLocallyConstantWith R P G) :
    IsEtaleLocallyConstantWith R P ((etalePullback f R).obj G) := by
  obtain ⟨𝒰, h𝒰⟩ := hG
  refine ⟨𝒰.pullback₁ f, fun a => ?_⟩
  obtain ⟨M, hM, ⟨eM⟩⟩ := h𝒰 a
  let ecomp : etalePullback ((𝒰.pullback₁ f).f a ≫ f) R ≅
      etalePullback (𝒰.pullbackHom f a ≫ 𝒰.f a) R :=
    eqToIso (congrArg (fun k => etalePullback k R) (𝒰.pullbackHom_map f a).symm)
  refine ⟨M, hM, ⟨?_⟩⟩
  exact ((etalePullbackCompIso ((𝒰.pullback₁ f).f a) f R).app G).symm ≪≫
    ecomp.app G ≪≫ (etalePullbackCompIso (𝒰.pullbackHom f a) (𝒰.f a) R).app G ≪≫
    (etalePullback (𝒰.pullbackHom f a) R).mapIso eM ≪≫
    (etalePullbackConstantIso (𝒰.pullbackHom f a) R).app M

/-- Local constant models on every member of an étale cover give local
constant models on the original scheme, by composing the covers. -/
lemma IsEtaleLocallyConstantWith.of_cover
    (𝒰 : X.Cover.{u} (Scheme.precoverage (show MorphismProperty Scheme.{u} from @Etale)))
    {G : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)}
    (hG : ∀ a : 𝒰.I₀,
      IsEtaleLocallyConstantWith R P ((etalePullback (𝒰.f a) R).obj G)) :
    IsEtaleLocallyConstantWith R P G := by
  choose 𝒱 h𝒱 using hG
  refine ⟨𝒰.bind 𝒱, ?_⟩
  rintro ⟨a, b⟩
  obtain ⟨M, hM, ⟨eM⟩⟩ := h𝒱 a b
  exact ⟨M, hM, ⟨(etalePullbackCompIso ((𝒱 a).f b) (𝒰.f a) R).app G ≪≫ eM⟩⟩

/-- The definition agrees with being constant in mathlib's sense on an
étale cover. -/
lemma isEtaleLocallyConstant_iff
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) :
    IsEtaleLocallyConstant R G ↔
      ∃ 𝒰 : X.Cover.{u} (Scheme.precoverage (show MorphismProperty Scheme.{u} from @Etale)),
        ∀ a : 𝒰.I₀,
          Sheaf.IsConstant (𝒰.X a).smallEtaleTopology ((etalePullback (𝒰.f a) R).obj G) := by
  constructor
  · rintro ⟨𝒰, h𝒰⟩
    refine ⟨𝒰, fun a => ?_⟩
    obtain ⟨M, _, ⟨eM⟩⟩ := h𝒰 a
    exact Sheaf.isConstant_of_iso (𝒰.X a).smallEtaleTopology eM
  · rintro ⟨𝒰, h𝒰⟩
    refine ⟨𝒰, fun a => ?_⟩
    have := h𝒰 a
    obtain ⟨M, ⟨eM⟩⟩ := ((etalePullback (𝒰.f a) R).obj G).mem_essImage_of_isConstant
    exact ⟨M, trivial, ⟨eM.symm⟩⟩

/-- Forgetting finite generation gives ordinary local constancy. -/
lemma IsEtaleFiniteTypeLocallyConstant.isEtaleLocallyConstant
    {G : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)}
    (hG : IsEtaleFiniteTypeLocallyConstant R G) : IsEtaleLocallyConstant R G := by
  obtain ⟨𝒰, h𝒰⟩ := hG
  refine ⟨𝒰, fun a => ?_⟩
  obtain ⟨M, _, eM⟩ := h𝒰 a
  exact ⟨M, trivial, eM⟩

/-- A constant sheaf in mathlib's sense is étale locally constant. -/
lemma isEtaleLocallyConstant_of_isConstant
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u} R))
    [Sheaf.IsConstant X.smallEtaleTopology G] : IsEtaleLocallyConstant R G := by
  obtain ⟨M, ⟨eM⟩⟩ := G.mem_essImage_of_isConstant
  exact (IsEtaleLocallyConstantWith.constant M (P := fun _ => True) trivial).of_iso eM

end EtaleCohomology
