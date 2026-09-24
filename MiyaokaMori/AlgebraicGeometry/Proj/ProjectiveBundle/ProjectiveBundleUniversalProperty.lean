import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveBundle.ProjectiveBundle
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveBundle.ProjectiveBundleUniversalPropertyCompat
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveBundle.ProjectiveBundleUniversalPropertyIrrelevant
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveBundle.ProjectiveBundleUniversalPropertyLocalRingHom
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjQC
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.RelativeProjTwistQC
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.Stacks01nq
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjLift
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjLiftDataOfEpi

/-! # The universal property of the projective bundle

The universal property of the projective bundle (the functor-of-points part of Stacks 01O4 together
with 01OA): for `V` locally free, `f : T → X`, a line bundle `M` on `T` and an epimorphism
`ψ : f^*V^∨ ↠ M`, there is an `X`-morphism `T → P(V)` (`P(V) = Proj_X Sym(V^∨)`) which pulls `O(1)` back
to `M` and the universal quotient back to `ψ`.

References: Stacks 01O4 (`Proj` represents `F_1`), 01OA (sections of a projective bundle). The paper
uses this for the sections of `P(O ⊕ L)` (§1) and the projectivization `τ` of the affine lift
(Lemma 3.1).

The construction is the special case `S = Sym(V^∨)` of the general lift `relativeProj.lift` for a
graded quasi-coherent algebra `S` with lift data `relativeProj.LiftData S f M`: `projBundle.liftData V f M ψ`
is `relativeProj.liftDataOfEpi f V^∨ M ψ`, and `projBundle.localRingHom`, `liftLocal`, `lift` are
definitionally equal (`rfl`) to the general constructions at this data. Accordingly,
* `projBundle.liftLocal` and `projBundle.lift` are `abbrev`s of `relativeProj.liftLocal` / `relativeProj.lift`;
* `localRingHom_map_irrelevant`, `liftLocal_compat`, `lift_hom` are one-line wrappers of the general theorems.
The names `projBundle.*` are kept because they appear in the statements and definitions of the
downstream modules (`TotLineAffineOverBase*`, `ProjectiveBundleLineSection` / `OSection`, …), and
rewriting to the general form would require supplying `(V^∨).IsQuasicoherent` at every call site
(`isQuasicoherent_of_isLocallyFree` is a theorem, not an instance). `localRingHom_sectionsUnit` does
not require `[Epi ψ]`, and is therefore more general than the specialization of
`liftLocalRingHom_sectionsUnit`; its own proof is kept. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/- The definitions `monoidalPowMap`, `pullbackMonoidalPow`, `unitPowCollapse` and their compatibilities
   (a)(b)(c) with `monoidalPowCat` are in `ProjectiveBundleUniversalPropertyMonoidalPow.lean`;
   `symPowPullbackDesc` / `symGradedPullbackDesc` and their degree-zero and multiplicativity lemmas in
   `…SymPowDesc.lean`; `localRingHomComponent`, `localRingHom` and their pieces in `…LocalRingHom.lean`;
   the pieces of (3/6) in `…Irrelevant.lean`; the naturality lemmas of `Proj.fromOfGlobalSections` and
   `liftData` in `…Compat.lean`. -/

/-- **(3/6) The image of the irrelevant ideal generates the unit ideal** (the hypothesis of
`Proj.fromOfGlobalSections`) on an **affine** open `V′ ⊆ U ⊓ f⁻¹W`.

Reference: the representability part of Stacks 01O4 (`ψ` surjective in degree one implies that the
morphism to `Proj` is everywhere defined). This is the special case at `liftData` of the general
`relativeProj.liftLocalRingHom_map_irrelevant`: `projBundle.localRingHom V f M ψ U e W` and
`relativeProj.liftLocalRingHom (Sym V^∨) f M (liftData V f M ψ) U e W` are definitionally equal.

Proof sketch. Let `R = Γ(V′, O)` and `I = Ideal.map (res ∘ localRingHom) (irrelevant A(W)) ⊆ R`.
(1) At every point `t′ ∈ V′` the image of some degree-one element is a unit: `W` is affine and
`S₁ = V^∨` is quasi-coherent, so `Γ(W, S₁)` generates every stalk of `S₁|_W`
(`stalk_eq_smul_germ_of_isQuasicoherent`), pullback preserves this
(`modulePullbackStalkTensorMap_bijective`), and `Φ₁ : g^*S₁ ⟶ O_V` is an epimorphism
(`symGradedPullbackDesc_one_epi`), hence surjective on stalks; if all `Φ₁(t)` were non-units at `t′`,
`Submodule.span_induction` would give `germ(1) = c • germ(1)` with `c ∈ 𝔪_{t′}`, a contradiction
(`exists_mem_basicOpen_of_epi`). Such a `t` lies in the irrelevant ideal (`mem_irrelevant_iff`).
(2) On the affine `V′`, an ideal with a unit at every point is `⊤` (`Ideal.exists_le_maximal`,
`map_PrimeSpectrum_basicOpen_of_affine`; `ideal_eq_top_of_forall_exists_mem_basicOpen`).
(3) Affineness of `V′` cannot be dropped: for `T = 𝔸²∖{0}`, `X = Spec k`, `V = k²`, `M = O_T`,
`ψ = (x, y)`, `U = T`, `W = X`, the image of the irrelevant ideal is the ideal `(x, y) ≠ ⊤` of `k[x,y]`,
although `x`, `y` have no common zero on `T`. This is why the definition of `lift` shrinks the local
pieces to affine opens. -/
theorem AlgebraicGeometry.Scheme.projBundle.localRingHom_map_irrelevant {X T : AlgebraicGeometry.Scheme.{u}}
    (V : X.Modules) [V.IsLocallyFree] [V.IsFiniteType] (f : T ⟶ X) (M : T.Modules) [M.IsLineBundle]
    (ψ : (AlgebraicGeometry.Scheme.Modules.pullback f).obj (AlgebraicGeometry.Scheme.Modules.dual V) ⟶ M)
    [CategoryTheory.Epi ψ]
    (U : T.Opens) (e : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) (W : X.affineOpens)
    (V' : T.Opens) (hV' : AlgebraicGeometry.IsAffineOpen V') (hle : V' ≤ U ⊓ f ⁻¹ᵁ W.1) :
    Ideal.map
        ((T.homOfLE hle).appTop.hom.comp
          (AlgebraicGeometry.Scheme.projBundle.localRingHom V f M ψ U e W.1))
        (HomogeneousIdeal.irrelevant
          ((AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
            (AlgebraicGeometry.Scheme.Modules.dual V)).sectionsGrading W.1)).toIdeal = ⊤ :=
  AlgebraicGeometry.Scheme.relativeProj.liftLocalRingHom_map_irrelevant _ f M
    (AlgebraicGeometry.Scheme.projBundle.liftData V f M ψ) U e W V' hV' hle

/-- **A local piece of the lift**: on an affine open `V′ ⊆ U ⊓ f⁻¹W`, `localRingHom` restricted to
`Γ(V′, O)` gives `V′ → Proj A(W)` via `Proj.fromOfGlobalSections`, which is placed into `P(V)` through
`π⁻¹W ≅ Proj A(W)` (`relativeProj.affineIso`, Stacks 01NQ). This is an `abbrev` of the general
`relativeProj.liftLocal` at `liftData V f M ψ`, not a second construction. -/
noncomputable abbrev AlgebraicGeometry.Scheme.projBundle.liftLocal {X T : AlgebraicGeometry.Scheme.{u}}
    (V : X.Modules) [V.IsLocallyFree] [V.IsFiniteType] (f : T ⟶ X) (M : T.Modules) [M.IsLineBundle]
    (ψ : (AlgebraicGeometry.Scheme.Modules.pullback f).obj (AlgebraicGeometry.Scheme.Modules.dual V) ⟶ M)
    [CategoryTheory.Epi ψ]
    (U : T.Opens) (e : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) (W : X.affineOpens)
    (V' : T.Opens) (hV' : AlgebraicGeometry.IsAffineOpen V') (hle : V' ≤ U ⊓ f ⁻¹ᵁ W.1) :
    V'.toScheme ⟶ (AlgebraicGeometry.Scheme.projBundle V).left :=
  AlgebraicGeometry.Scheme.relativeProj.liftLocal _ f M
    (AlgebraicGeometry.Scheme.projBundle.liftData V f M ψ) U e W V' hV' hle

/-- **(4/6) Two local pieces agree on the overlap** (the compatibility hypothesis of
`Cover.glueMorphisms`).

References: Stacks 01O4 ("up to strict equivalence": changing the trivialization or the affine open
changes the local ring map by a global unit, which does not change the morphism to `Proj`); 01NQ (the
gluing data of the relative Proj). This is the special case at `liftData` of the general
`relativeProj.liftLocal_compat`.

Proof sketch: reduce to `V₁ ⊓ V₂` (`isPullback_opens_inf`) and check on its affine open cover
(`hom_ext_of_forall_affine`); at each point take an affine `W₃ ∋ f t`, `W₃ ≤ W₁ ⊓ W₂` and an affine
`V₃ ∋ t`, `V₃ ≤ V₁ ⊓ V₂ ⊓ f⁻¹W₃`; shrink `V′` (`homOfLE_liftLocal`, via `fromOfGlobalSections_precomp`);
shrink `W` (`liftLocalPiece_change_W`, via `affineIso_restrict` (01NQ) and
`fromOfGlobalSections_comp_map`); change the trivialization (`fromOfGlobalSections_unit_scale`: two
trivializations differ by a global unit `u`, the degree-`m` components by `u^m`, and
`fromOfGlobalSections` is determined on each `D₊(r)` by degree-zero fractions, in which the powers of
`u` cancel). -/
theorem AlgebraicGeometry.Scheme.projBundle.liftLocal_compat {X T : AlgebraicGeometry.Scheme.{u}}
    (V : X.Modules) [V.IsLocallyFree] [V.IsFiniteType] (f : T ⟶ X) (M : T.Modules) [M.IsLineBundle]
    (ψ : (AlgebraicGeometry.Scheme.Modules.pullback f).obj (AlgebraicGeometry.Scheme.Modules.dual V) ⟶ M)
    [CategoryTheory.Epi ψ]
    (U₁ : T.Opens) (e₁ : M.restrict U₁.ι ≅ SheafOfModules.unit U₁.toScheme.ringCatSheaf) (W₁ : X.affineOpens)
    (V₁ : T.Opens) (hV₁ : AlgebraicGeometry.IsAffineOpen V₁) (hle₁ : V₁ ≤ U₁ ⊓ f ⁻¹ᵁ W₁.1)
    (U₂ : T.Opens) (e₂ : M.restrict U₂.ι ≅ SheafOfModules.unit U₂.toScheme.ringCatSheaf) (W₂ : X.affineOpens)
    (V₂ : T.Opens) (hV₂ : AlgebraicGeometry.IsAffineOpen V₂) (hle₂ : V₂ ≤ U₂ ⊓ f ⁻¹ᵁ W₂.1) :
    CategoryTheory.Limits.pullback.fst V₁.ι V₂.ι ≫
        AlgebraicGeometry.Scheme.projBundle.liftLocal V f M ψ U₁ e₁ W₁ V₁ hV₁ hle₁ =
      CategoryTheory.Limits.pullback.snd V₁.ι V₂.ι ≫
        AlgebraicGeometry.Scheme.projBundle.liftLocal V f M ψ U₂ e₂ W₂ V₂ hV₂ hle₂ :=
  AlgebraicGeometry.Scheme.relativeProj.liftLocal_compat _ f M
    (AlgebraicGeometry.Scheme.projBundle.liftData V f M ψ) U₁ e₁ W₁ V₁ hV₁ hle₁ U₂ e₂ W₂ V₂ hV₂ hle₂

section LocalRingHomSectionsUnit

set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry.Scheme.projBundle

variable {X T : AlgebraicGeometry.Scheme.{u}}

/-- The value of `localRingHom` on the structure map `sectionsUnit W r` (in the degree-zero block) is
`g^♯ r` restricted to `⊤` (`DirectSum.toSemiring_of` + `localRingHomComponent_zero_apply`). Does not
require `[Epi ψ]`. -/
theorem localRingHom_sectionsUnit (V : X.Modules) [V.IsLocallyFree] [V.IsFiniteType] (f : T ⟶ X)
    (M : T.Modules) [M.IsLineBundle]
    (ψ : (AlgebraicGeometry.Scheme.Modules.pullback f).obj (AlgebraicGeometry.Scheme.Modules.dual V) ⟶ M)
    (U : T.Opens) (e : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) (W : X.Opens)
    (r : Γ(X, W)) :
    localRingHom V f M ψ U e W
        (((AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
          (AlgebraicGeometry.Scheme.Modules.dual V)).sectionsUnit W r).1) =
      (localRingHomBase f U W).appLE W ⊤ (localRingHomBase_top_le f U W) r := by
  show DirectSum.toSemiring _ _ _ (DirectSum.of ((AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
    (AlgebraicGeometry.Scheme.Modules.dual V)).sectionsPiece W) 0
    ((AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual V)).one.app W r)) = _
  exact (DirectSum.toSemiring_of _ _ _ 0 _).trans (localRingHomComponent_zero_apply V f M ψ U e W r)

end AlgebraicGeometry.Scheme.projBundle

end LocalRingHomSectionsUnit

/-- **The morphism given by the universal property of the projective bundle** (the construction
direction of Stacks 01O4): for every point `t` of `T`, take a trivializing open `U_t ∋ t` of `M`, an
affine open `W_t ∋ f(t)`, and an **affine** open `V_t ∋ t`, `V_t ⊆ U_t ⊓ f⁻¹W_t`; take `liftLocal` on
`V_t` and glue along the open cover `{V_t}` (`Scheme.Cover.glueMorphisms`). The local pieces must be
shrunk to affine opens: when `U_t ⊓ f⁻¹W_t` is not affine, "the image of the irrelevant ideal is `⊤`"
fails (counterexample `T = 𝔸²∖{0} → ℙ¹`, see `localRingHom_map_irrelevant`).

This is an `abbrev` of the general `relativeProj.lift` at `liftData V f M ψ`, not a second
construction; all properties of `projBundle.lift` (`lift_hom`, `lift_restrict`, `lift_twist`,
uniqueness) come from the general form. -/
noncomputable abbrev AlgebraicGeometry.Scheme.projBundle.lift {X T : AlgebraicGeometry.Scheme.{u}}
    (V : X.Modules) [V.IsLocallyFree] [V.IsFiniteType] (f : T ⟶ X) (M : T.Modules) [M.IsLineBundle]
    (ψ : (AlgebraicGeometry.Scheme.Modules.pullback f).obj (AlgebraicGeometry.Scheme.Modules.dual V) ⟶ M)
    [CategoryTheory.Epi ψ] : T ⟶ (AlgebraicGeometry.Scheme.projBundle V).left :=
  AlgebraicGeometry.Scheme.relativeProj.lift _ f M (AlgebraicGeometry.Scheme.projBundle.liftData V f M ψ)

/-- **(5/6) `lift` is an `X`-morphism**: `lift ≫ projBundle.hom = f`.

Reference: Stacks 01O4 (`F_1` is a functor on `X`-schemes, so the resulting morphism is over `X`).
This is the special case at `liftData` of the general `relativeProj.lift_hom`, whose proof reduces
via `glueMorphisms_comp_eq_of_forall` to each piece of the cover `{V_t}` and applies `liftLocal_hom`:
`affineIso_inv_ι_hom` turns `liftLocal ≫ π` into
`fromOfGlobalSections ≫ toSpecZero ≫ Spec(unitZero) ≫ isoSpec⁻¹ ≫ W.ι`, Mathlib's
`fromOfGlobalSections_toSpecZero` turns this into `V′.toSpecΓ ≫ Spec.map (Φ ∘ algebraMap) ≫ …`; on the
right, `V′.ι ≫ f = f.resLE W V′ ≫ W.ι` and `toSpecΓ_SpecMap_appLE`; the remaining ring homomorphism
identity is `liftLocalRingHom_sectionsUnit` (`Φ` is `g^♯` in degree zero). -/
theorem AlgebraicGeometry.Scheme.projBundle.lift_hom {X T : AlgebraicGeometry.Scheme.{u}}
    (V : X.Modules) [V.IsLocallyFree] [V.IsFiniteType] (f : T ⟶ X) (M : T.Modules) [M.IsLineBundle]
    (ψ : (AlgebraicGeometry.Scheme.Modules.pullback f).obj (AlgebraicGeometry.Scheme.Modules.dual V) ⟶ M)
    [CategoryTheory.Epi ψ] :
    AlgebraicGeometry.Scheme.projBundle.lift V f M ψ ≫ (AlgebraicGeometry.Scheme.projBundle V).hom = f :=
  AlgebraicGeometry.Scheme.relativeProj.lift_hom _ f M (AlgebraicGeometry.Scheme.projBundle.liftData V f M ψ)

/-! **(6/6) `lift_twist`** (`τ^*O(1) ≅ M`, Stacks 01O4 "up to strict equivalence") lives downstream:
its proof goes through `relativeProj.lift` and `relativeProj.lift_inducedBy`. -/

end
