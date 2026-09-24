import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModuleSheafStalk
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModuleSheafStalkStmt
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.VarietyLineBundle
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle

/-! # Frames of a line bundle

A frame (local frame) of a line bundle `L` on an open `V`: an isomorphism `O_V ≅ L|_V`; equivalently a
section generating every stalk.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open scoped AlgebraicGeometry

/- A frame of the line bundle `L` on the open `V`: a section `section_` generating every stalk, together with
   the trivialization `O_V ≅ L|_V` it gives. The trivialization is recorded as a data field (its forward
   direction is determined by `section_`: `1 ↦ section_`, see `trivialization_one`); the inverse
   "`L|_V → O_V`, `t ↦ t/section_`" needs the generation of stalks to be written down and cannot be extracted
   from the mere existence of `IsIso`, so it is not constructed separately. -/

structure LineBundle.Frame {k : Type u} [Field k] {X : Variety k}
    (L : LineBundle X) (V : X.toScheme.Opens) where
  section_ : Γ(L.toModules, V)
  generates : ∀ (x : X.toScheme) (hx : x ∈ V),
    Submodule.span (X.toScheme.presheaf.stalk x)
      ({L.toModules.presheaf.germ V x hx section_} : Set (L.toModules.stalk x)) = ⊤
  trivialization : SheafOfModules.unit V.toScheme.ringCatSheaf ≅ L.toModules.restrict V.ι
  trivialization_one :
    (trivialization.hom.val.app (Opposite.op ⊤) (1 : V.toScheme.ringCatSheaf.obj.obj (Opposite.op ⊤)) :
        (L.toModules.val.obj (Opposite.op (V.ι ''ᵁ ⊤)) : Type u)) =
      L.toModules.val.map (CategoryTheory.homOfLE (V.ι.image_le_opensRange ⊤ |>.trans (by simp))).op
        (section_ : (L.toModules.val.obj (Opposite.op V) : Type u))

/-- A frame is equivalent to a trivialization `O_V ≅ L|_V`. -/

noncomputable def LineBundle.Frame.iso {k : Type u} [Field k] {X : Variety k}
    {L : LineBundle X} {V : X.toScheme.Opens} (e : L.Frame V) :
    SheafOfModules.unit V.toScheme.ringCatSheaf ≅ L.toModules.restrict V.ι :=
  e.trivialization

end
