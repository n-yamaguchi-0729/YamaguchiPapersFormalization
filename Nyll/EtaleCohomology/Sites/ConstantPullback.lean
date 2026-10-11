/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleCohomology.Sites.BaseChange
import Nyll.EtaleCohomology.Sites.SheafFunctors
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.Continuous
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-!
# Inverse image of constant sheaves

For a continuous functor preserving a terminal object, composition of its
left adjoint with the constant-sheaf functor is left adjoint to global
sections on the target site. Uniqueness of left adjoints gives the constant
sheaf comparison. Applying this to étale base change shows that inverse
image along any scheme morphism preserves constant coefficient sheaves.
-/

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

universe uC vC uD vD uA vA u

namespace EtaleCohomology.Sites

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  (F : C ⥤ D) [F.IsContinuous J K]
  (A : Type uA) [Category.{vA} A] [HasWeakSheafify J A] [HasWeakSheafify K A]
  {T : C} (hT : IsTerminal T) (hFT : IsTerminal (F.obj T))
  (L : Sheaf J A ⥤ Sheaf K A) (adj : L ⊣ F.sheafPushforwardContinuous A J K)

/-- The left adjoint to restriction preserves constant sheaves when the site
functor carries the chosen terminal object to a terminal object. -/
def constantSheafCompLeftAdjointIso :
    constantSheaf J A ⋙ L ≅ constantSheaf K A :=
  ((constantSheafAdj J A hT).comp adj).leftAdjointUniq (constantSheafAdj K A hFT)

end EtaleCohomology.Sites

namespace EtaleCohomology

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (R : Type u) [CommRing R]

/-- Inverse image of a constant étale coefficient sheaf has the same constant value. -/
def etalePullbackConstantIso :
    constantSheaf Y.smallEtaleTopology (ModuleCat.{u} R) ⋙ etalePullback f R ≅
      constantSheaf X.smallEtaleTopology (ModuleCat.{u} R) :=
  Sites.constantSheafCompLeftAdjointIso (etaleBaseChange f) (ModuleCat.{u} R)
    terminalIsTerminal (terminalIsTerminal.isTerminalObj (etaleBaseChange f) (⊤_ Y.Etale))
    (etalePullback f R) (etalePullbackPushforwardAdjunction f R)

/-- Inverse image preserves the existing constant-sheaf predicate. -/
lemma etalePullback_isConstant (G : Sheaf Y.smallEtaleTopology (ModuleCat.{u} R))
    [Sheaf.IsConstant Y.smallEtaleTopology G] :
    Sheaf.IsConstant X.smallEtaleTopology ((etalePullback f R).obj G) := by
  obtain ⟨M, ⟨e⟩⟩ := G.mem_essImage_of_isConstant
  exact Sheaf.isConstant_of_iso X.smallEtaleTopology
    ((etalePullback f R).mapIso e.symm ≪≫ (etalePullbackConstantIso f R).app M)

end EtaleCohomology
