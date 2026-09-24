import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Basic.ModulesExactIffLocallyLift
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.ModuleSheafFrame

/-! # An epimorphism criterion through the adjoint transpose

**Epimorphism criterion through the adjoint transpose** (Stacks 01O9, "the map `f^*E → M` is surjective because
the sections `s_{j,t}` generate `M`"): let `g : X ⟶ S`, `E` an `O_S`-module, `M` an `O_X`-module and
`ψ : g^*E ⟶ M`, with adjoint transpose `φ : E ⟶ g_*M` (`pullbackPushforwardAdjunction`). If every point `x ∈ X`
has an open `V ⊆ S`, a section `e ∈ E(V)` and an open `W ∋ x`, `W ⊆ g⁻¹V`, on which `φ(e) ∈ M(g⁻¹V)` restricts to a
**frame** of `M` (`IsFrame`), then `ψ` is an epimorphism.

Proof. Epimorphisms of `O_X`-modules are the locally surjective maps on
sections (`epi_iff_locally_surjective_sections`). Given `t ∈ M(U)` and `p ∈ U`, take `(V, e, W)` at `p` and put
`W' := W ⊓ U`; `φ(e)|_{W'}` is still a frame, so `t|_{W'} = c • φ(e)|_{W'}` for a unique `c ∈ O(W')`. Let
`η(e) ∈ (g^*E)(g⁻¹V)` be the image of `e` under the unit `E ⟶ g_*g^*E`; by the adjunction formula
`φ = η ≫ g_*ψ` we have `ψ(η(e)) = φ(e)` in `M(g⁻¹V)`, hence by naturality of `ψ` and linearity
`ψ(c • η(e)|_{W'}) = c • φ(e)|_{W'} = t|_{W'}`.

Used for the relative Proj description of quasi-projective immersions (Stacks 07RM, Step 4). -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X S : AlgebraicGeometry.Scheme.{u}}

/-- A section of the pushforward `g_*M` over `V`, read as a section of `M` over `g⁻¹V` (definitionally the same
element; this identity coercion only fixes the expected type). -/
abbrev ofPushforwardSection (g : X ⟶ S) (M : X.Modules) {V : S.Opens}
    (t : Γ((AlgebraicGeometry.Scheme.Modules.pushforward g).obj M, V)) : Γ(M, g ⁻¹ᵁ V) :=
  t

/-- The unit of `pullback ⊣ pushforward` followed by `g_*ψ` is the transpose `φ` of `ψ`; on sections over `V`
this reads `ψ(η(e)) = φ(e)` in `M(g⁻¹V)`. -/
theorem app_unit_app_eq_homEquiv_app (g : X ⟶ S) {E : S.Modules} {M : X.Modules}
    (ψ : (AlgebraicGeometry.Scheme.Modules.pullback g).obj E ⟶ M) (V : S.Opens) (e : Γ(E, V)) :
    ψ.app (g ⁻¹ᵁ V)
        (((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction g).unit.app E).app V e) =
      ofPushforwardSection g M
        (((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv E M ψ).app V e) := by
  rw [Adjunction.homEquiv_unit]
  rfl

/-- **Epimorphism criterion**: if the transpose `φ : E ⟶ g_*M` of `ψ : g^*E ⟶ M` has, near every point, a section
`φ(e)` restricting to a frame of `M`, then `ψ` is an epimorphism. -/
theorem epi_of_transpose_frames (g : X ⟶ S) {E : S.Modules} {M : X.Modules}
    (ψ : (AlgebraicGeometry.Scheme.Modules.pullback g).obj E ⟶ M)
    (h : ∀ x : X, ∃ (V : S.Opens) (e : Γ(E, V)) (W : X.Opens) (hW : W ≤ g ⁻¹ᵁ V), x ∈ W ∧
      IsFrame M W (M.res hW (ofPushforwardSection g M
        (((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv E M ψ).app V e)))) :
    CategoryTheory.Epi ψ := by
  rw [AlgebraicGeometry.Scheme.Modules.epi_iff_locally_surjective_sections]
  intro U t p hp
  obtain ⟨V, e, W, hW, hpW, hfr⟩ := h p
  set φe : Γ(M, g ⁻¹ᵁ V) := ofPushforwardSection g M
    (((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv E M ψ).app V e) with hφe
  let W' : X.Opens := W ⊓ U
  have hW'W : W' ≤ W := inf_le_left
  have hW'U : W' ≤ U := inf_le_right
  have hfr' : IsFrame M W' (M.res (hW'W.trans hW) φe) := by
    have := hfr.restrict hW'W
    rwa [M.res_res] at this
  obtain ⟨c, hc⟩ := (hfr' W' le_rfl).2 (M.res hW'U t)
  rw [M.res_self] at hc
  let ηe : Γ((AlgebraicGeometry.Scheme.Modules.pullback g).obj E, g ⁻¹ᵁ V) :=
    ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction g).unit.app E).app V e
  have hψη : ψ.app (g ⁻¹ᵁ V) ηe = φe := app_unit_app_eq_homEquiv_app g ψ V e
  refine ⟨W', hW'U, ⟨hpW, hp⟩, c • ((AlgebraicGeometry.Scheme.Modules.pullback g).obj E).res (hW'W.trans hW) ηe, ?_⟩
  rw [Hom.app_smul]
  have hnat : ψ.app W' (((AlgebraicGeometry.Scheme.Modules.pullback g).obj E).res (hW'W.trans hW) ηe) =
      M.res (hW'W.trans hW) (ψ.app (g ⁻¹ᵁ V) ηe) := by
    have := congrArg (fun k => k ηe) (ψ.val.naturality (homOfLE (hW'W.trans hW)).op)
    exact this
  rw [hnat, hψη]
  exact hc

end AlgebraicGeometry.Scheme.Modules

end
