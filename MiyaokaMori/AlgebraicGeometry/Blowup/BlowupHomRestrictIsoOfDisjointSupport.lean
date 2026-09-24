import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Blowup.BlowupIsoAwayFromCenterAffineLeaf
import MiyaokaMori.AlgebraicGeometry.Blowup.Stacks01og

/-! # The blowup morphism is an isomorphism away from the centre

The general form of Stacks 0807 / 02OS(1): the blowup morphism `(Scheme.blowup I).hom` restricted to an
open set `U` disjoint from `I.support` is an isomorphism (there `I` is the unit ideal sheaf, the Rees
algebra is the polynomial algebra `𝒪_X[T]`, and its relative Proj is `X` itself).

References: Stacks 0807 (the blowup is an isomorphism over the open set not meeting the centre),
Stacks 02OS(1); Hartshorne II.7.13(a). The same statements also appear in `BlowupIsoAwayFromCenter`;
they are repeated here because that module cannot be imported without creating an import cycle.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry

/-- If `S.projToOpen U : Proj(S(U)) → U` is an isomorphism, then the restriction of the structure morphism
of the relative Proj to `U` is an isomorphism as well (`projChart_isPullback`: `Proj(S(U))` is
`relativeProj S ×_X U`). -/
theorem Scheme.GradedAffineAlgebra.isIso_relativeProj_hom_restrict_of_isIso_projToOpen
    {X : Scheme.{u}} (S : X.GradedAffineAlgebra) (U : X.AffineZariskiSite)
    [IsIso (S.projToOpen U)] :
    IsIso (S.relativeProj.hom ∣_ U.toOpens) := by
  have h₁ := S.projChart_isPullback U
  have h₂ := isPullback_morphismRestrict S.relativeProj.hom U.toOpens
  have he : (h₁.isoIsPullback _ _ h₂).inv ≫ S.projToOpen U = S.relativeProj.hom ∣_ U.toOpens :=
    h₁.isoIsPullback_inv_fst _ _ h₂
  rw [← he]
  infer_instance

/-- Stacks 0807: the blowup morphism restricted to an open set `U` disjoint from `I.support` is an
isomorphism. Proof: being an isomorphism is Zariski-local on the target, so it suffices to check on every
affine open `V ⊆ U`; on `V` one has `I(V) = ⊤` (`ideal_eq_top_of_disjoint_support`), so
`I.reesAlgebra.projToOpen V` is an isomorphism (`isIso_reesAlgebra_projToOpen_of_ideal_eq_top`), and the
previous lemma applies. -/
theorem Scheme.blowup_hom_restrict_isIso_of_disjoint_support {X : Scheme.{u}}
    (I : X.IdealSheafData) (U : X.Opens) (hU : Disjoint (U : Set X) (I.support : Set X)) :
    IsIso ((Scheme.blowup I).hom ∣_ U) := by
  rw [← MorphismProperty.isomorphisms.iff]
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme)
    (fun V : U.toScheme.affineOpens => (V : U.toScheme.Opens)) (iSup_affineOpens_eq_top _) ?_
  intro V
  rw [(MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
    (morphismRestrictRestrict (Scheme.blowup I).hom U V.1), MorphismProperty.isomorphisms.iff]
  have hV : IsAffineOpen (U.ι ''ᵁ V.1) := V.2.image_of_isOpenImmersion U.ι
  have hle : U.ι ''ᵁ V.1 ≤ U :=
    (U.ι.image_le_opensRange V.1).trans (le_of_eq (Scheme.Opens.opensRange_ι U))
  have htop : I.ideal ⟨U.ι ''ᵁ V.1, hV⟩ = ⊤ :=
    I.ideal_eq_top_of_disjoint_support ⟨_, hV⟩ (hU.mono_left (fun _ h => hle h))
  have := I.isIso_reesAlgebra_projToOpen_of_ideal_eq_top ⟨U.ι ''ᵁ V.1, hV⟩ htop
  exact I.reesAlgebra.toGradedAffineAlgebra.isIso_relativeProj_hom_restrict_of_isIso_projToOpen
    ⟨U.ι ''ᵁ V.1, hV⟩

end AlgebraicGeometry

end
