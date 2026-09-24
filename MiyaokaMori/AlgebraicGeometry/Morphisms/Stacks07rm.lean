import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Morphisms.QuasiProjectiveMorphism
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProjectiveMorphism
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjSeparated
import MiyaokaMori.AlgebraicGeometry.Morphisms.Stacks07rm_ImmersionRelativeProj

/-! # Quasi-projective morphisms are open in projective ones (Stacks 07RM)

Stacks Project, Tag 07RM: if `S` is quasi-compact and quasi-separated and `f : X → S` is quasi-projective,
then `f = f' ∘ j` with `j` an open immersion and `f'` projective.

The first five paragraphs of the proof (the immersion `r` into `P(E)`) are the lemma
`IsQuasiProjectiveMorphism.exists_isImmersion_relativeProj` (module `Stacks07rm_ImmersionRelativeProj`).
The last paragraph (Tags 03GI and 01RG: `r` is quasi-compact, take the scheme-theoretic image) uses Mathlib's
`QuasiCompact.of_comp`, `Scheme.Hom.toImage` / `imageι` (`IsOpenImmersion f.toImage` for a quasi-compact
immersion) and `relativeProj_isSeparated` from this library.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- **Stacks 07RM**: over a quasi-compact quasi-separated `S`, a quasi-projective `f : X ⟶ S` factors as an
open immersion `j : X ⟶ X'` followed by a projective morphism `f' : X' ⟶ S`.

Proof. By `exists_isImmersion_relativeProj` (Stacks 07RM, paragraphs 1–5)
there are a graded quasi-coherent algebra `𝒜` on `S` generated in degree one with `𝒜₁` of finite type and an
immersion `r : X ⟶ Proj_S 𝒜` with `r ≫ π = f`. Since `f = r ≫ π` is quasi-compact and `π` is separated
(`relativeProj_isSeparated`, hence quasi-separated), `r` is quasi-compact (Stacks 03GI, Mathlib
`QuasiCompact.of_comp`). Let `X' := r.image` be the scheme-theoretic image of `r` (Stacks 01RG, Mathlib
`Scheme.Hom.image`): `r.toImage : X ⟶ X'` is an open immersion because `r` is a quasi-compact immersion
(Mathlib instance in `Morphisms/Immersion.lean`), `r.imageι : X' ⟶ Proj_S 𝒜` is a closed immersion, and
`r.toImage ≫ r.imageι = r`. Put `j := r.toImage` and `f' := r.imageι ≫ π`; `f'` is projective by definition
(`IsProjectiveMorphism`: closed immersion into `Proj_S 𝒜` over `S`, `𝒜` generated in degree one, `𝒜₁` finite
type), and `j ≫ f' = r ≫ π = f`. -/
theorem AlgebraicGeometry.IsQuasiProjectiveMorphism.exists_isOpenImmersion_isProjectiveMorphism
    {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S) [AlgebraicGeometry.IsQuasiProjectiveMorphism f]
    [CompactSpace S] [QuasiSeparatedSpace S] :
    ∃ (X' : AlgebraicGeometry.Scheme.{u}) (j : X ⟶ X') (f' : X' ⟶ S),
      AlgebraicGeometry.IsOpenImmersion j ∧ AlgebraicGeometry.IsProjectiveMorphism f' ∧ j ≫ f' = f := by
  obtain ⟨𝒜, r, hgen, hft, hr, hrf⟩ :=
    AlgebraicGeometry.IsQuasiProjectiveMorphism.exists_isImmersion_relativeProj f
  -- Stacks 03GI: `r ≫ π = f` is quasi-compact and `π` is (quasi-)separated, so `r` is quasi-compact.
  have hqc : AlgebraicGeometry.QuasiCompact (r ≫ (AlgebraicGeometry.Scheme.relativeProj 𝒜).hom) :=
    hrf ▸ AlgebraicGeometry.IsQuasiProjectiveMorphism.quasiCompact (f := f)
  have hrqc : AlgebraicGeometry.QuasiCompact r :=
    AlgebraicGeometry.QuasiCompact.of_comp r (AlgebraicGeometry.Scheme.relativeProj 𝒜).hom
  -- Stacks 01RG: the scheme-theoretic image of the quasi-compact immersion `r`.
  refine ⟨r.image, r.toImage, r.imageι ≫ (AlgebraicGeometry.Scheme.relativeProj 𝒜).hom,
    inferInstance, ⟨𝒜, r.imageι, hgen, hft, inferInstance, rfl⟩, ?_⟩
  rw [← Category.assoc, AlgebraicGeometry.Scheme.Hom.toImage_imageι, hrf]

end
