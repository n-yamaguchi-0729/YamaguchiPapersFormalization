/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.EtaleCohomology.Sites.ZariskiRestriction
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.CategoryTheory.Opposites

/-!
# Global sections of the actual Zariski restriction

The top open subscheme is identified with the identity object of the small
étale site. The induced identification of sections commutes with restriction
to every open subscheme.
-/

noncomputable section

universe u v w

open AlgebraicGeometry CategoryTheory Opposite

namespace EtaleCohomology

variable (X : Scheme.{u})

/-- The top open, included into the small étale site, is its identity object. -/
def zariskiToEtaleTopIso :
    (zariskiToEtale X).obj ⊤ ≅ Scheme.Etale.mk (𝟙 X) :=
  MorphismProperty.Over.isoMk
    (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤)
    X.topIso (Category.comp_id X.topIso.hom)

variable (A : Type v) [Category.{w} A]

/-- The actual identification of global sections on the two sites. -/
def etaleZariskiGlobalSectionsIso (F : Sheaf X.smallEtaleTopology A) :
    ((etaleZariskiRestriction X A).obj F).obj.obj (op (⊤ : X.Opens)) ≅
      F.obj.obj (op (Scheme.Etale.mk (𝟙 X))) :=
  (F.obj.mapIso (zariskiToEtaleTopIso X).op).symm

/-- Converting a global étale section and restricting to an open is exactly
restriction along that open's structural morphism. -/
theorem etaleZariskiGlobalSectionsIso_inv_restrict
    (F : Sheaf X.smallEtaleTopology A) (U : X.Opens) :
    (etaleZariskiGlobalSectionsIso X A F).inv ≫
        ((etaleZariskiRestriction X A).obj F).obj.map
          (homOfLE (show U ≤ ⊤ from le_top)).op =
      F.obj.map
        (MorphismProperty.Over.homMk
          (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤)
          (A := (zariskiToEtale X).obj U) (B := Scheme.Etale.mk (𝟙 X))
          U.ι (Category.comp_id U.ι)).op := by
  let g : (zariskiToEtale X).obj U ⟶ (zariskiToEtale X).obj ⊤ :=
    (zariskiToEtale X).map (homOfLE (show U ≤ ⊤ from le_top))
  let j : (zariskiToEtale X).obj U ⟶ Scheme.Etale.mk (𝟙 X) :=
    MorphismProperty.Over.homMk
      (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤)
      U.ι (Category.comp_id U.ι)
  have hgj : g ≫ (zariskiToEtaleTopIso X).hom = j := by
    apply MorphismProperty.Over.Hom.ext
    change g.left ≫ (⊤ : X.Opens).ι = U.ι
    exact g.w
  change F.obj.map (zariskiToEtaleTopIso X).hom.op ≫ F.obj.map g.op = F.obj.map j.op
  rw [← F.obj.map_comp, ← op_comp, hgj]

end EtaleCohomology
