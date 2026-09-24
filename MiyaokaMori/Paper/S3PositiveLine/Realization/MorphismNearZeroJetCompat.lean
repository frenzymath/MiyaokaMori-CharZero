import MiyaokaMori.Paper.S3PositiveLine.Realization.MorphismNearZeroData
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.ThickeningSectionsTruncated
import MiyaokaMori.Paper.S3PositiveLine.Realization.MorphismNearZeroSectionCompat
import MiyaokaMori.Paper.S3PositiveLine.Realization.MorphismNearZeroJetCompatBridges
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.RestrictSectionAlongThickIso

/-! # Compatibility of the morphism near the zero section with the jet: the main identity

Statement: if `Φ₀ : U → X` is the projectivization of the tuple `P` on an open `U ⊆ Tot(L)`,
`ν : C̃_(κ)(L) → U` is the inclusion of the jet neighbourhood (`ν ≫ U.ι = C̃_(κ)(L) ↪ Tot(L)`),
`ȷ^× : C̃_(κ)(L) → Z^×` is the based jet with values in the punctured cone
(`ȷ^× ≫ Z^×.ι = ȷ.hom`), and the cone coordinates of `ȷ` are the restrictions of `P` to the jet
neighbourhood, then `ν ≫ Φ₀ = ȷ^× ≫ (Z^× → X)`.

Source: proof of Theorem 4.2 of the paper: the morphism `Φ₀` "restricts on the jet neighbourhood to
the projection of `ȷ` to `X`"; the projection `Z^× → X` is `MMSetup.toX`.

The top level `morphism_near_zero_jet_compat` is assembled from library facts and one lemma,
`morphism_near_zero_jet_compat_left`, a purely formal identity between two spellings of
the restriction of a section to the jet neighbourhood. Its proof relies on (i) `restrictToThickening` being an
instance of the regular definition `restrictSectionAlong`, (ii) the variable-level lemma
`restrictSectionAlong_eq_thickIso_apply` (`RestrictSectionAlongThickIso`), and (iii) spelling the
implicit argument `Z` of `thickIso` explicitly as `(totalSpace L.toModules).left` so that the lemma's
left-hand side is *structurally* an instance of that lemma; see its docstring.
Generic helper lemmas are in `MorphismNearZeroJetCompatBridges`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry
open MorphismNearZeroJetCompat
noncomputable section

/-- **Left-hand section computation**.

Let `A := f^*O_X(1)`, `N := ρ^*A` (as a module `(ρ^* f^* O_X(1)).toModules`), `π : Tot(L) → C̃`,
`M := π^*N`, `i : C̃_(κ)(L) ↪ Tot(L)`, `p := jetNeighborhood.proj L κ` (so `i ≫ π = p`), and let
`ν : C̃_(κ)(L) → U` with `ν ≫ U.ι = i`. The canonical isomorphism
`θ₁ : ν^*U.ι^*M ≅ (ν ≫ U.ι)^*M = i^*M = i^*π^*N ≅ p^*N` (`pullbackCompApp`, `pullbackCongr hnu`,
`thickIso`) sends the section `ν^*U.ι^*(P ℓ)` to `restrictToThickening L N κ (P ℓ)`.

Source: Theorem 4.2 of the paper together with the definition of `restrictToThickening`
(: restriction to the thickening is pullback along `i` followed by
`i^*π^*N ≅ (i ≫ π)^*N = p^*N`).

Natural-language proof (self-contained, every step is a library fact):
1. `θ₁.hom` applied to `ν^*U.ι^*s` is `thickIso.hom` applied to `i^*s`
   (`MorphismNearZeroJetCompat.pullbackCompApp_chain_apply`: `pullback_comp` then `pullbackCongr_apply`).
2. `thickIso.hom = ((pullbackComp i π).app N).hom ≫ eqToHom (i ≫ π = p)` (`thickIso_hom`, `rfl`).
3. This is literally the body of `restrictToThickening L N κ (P ℓ)` (`restrictToThickening.eq_1`),
   up to the identification of the source `i^*(π^*N)` with `(π^* ⋙ i^*).obj N`
   (`val_app_top_apply_comp_obj`, `Functor.comp_obj`, `rfl`) and the two spellings
   `rho.source.toScheme` / `rho.source.toVariety.carrier` of the base curve (both `abbrev`s).

Lean proof:
`rw [pullbackCompApp_chain_apply, ← restrictSectionAlong_eq_thickIso_apply]; rfl`. Step 1 is the
`rw` with the chain lemma; steps 2-3 are the right-to-left `rw` with the variable-level lemma
`restrictSectionAlong_eq_thickIso_apply` (module `RestrictSectionAlongThickIso`), which turns the
left-hand side into `restrictSectionAlong i π N (congrArg _ hp) (i^*(P ℓ))`, after which
`restrictToThickening L N κ (P ℓ)` unfolds to it by `rfl` (`restrictToThickening` is an
instance of `restrictSectionAlong`; both heads are regular definitions, so the kernel
compares them argument by argument).

Why other spellings of the statement time out in the kernel, and what the statement has to look like:
the kernel's lazy delta reduction unfolds the *abbreviation*-headed side of an equation first; for
`restrictToThickening … = <section-level term>` (head `DFunLike.coe`) this evaluates the concrete
linear map down to `eqToHom` and then attempts the K-rule check `(pullback (i ≫ π)).obj N ≡
(pullback p).obj N`, which does not terminate in practice (`rfl`, `unfold`,
`restrictToThickening.eq_1`, `Eq.refl` on structurally identical sides are all far too slow, while skipping the
kernel makes every one of them finish quickly). Hence the only kernel-cheap route is a `rw` whose
instantiated pattern is *structurally* the goal (so that `Eq.mpr`'s type check is a syntactic
comparison), followed by a `rfl` between two *regular*-headed terms. For the pattern to be
structural, the left-hand side must spell `(totalSpace L.toModules).left` uniformly: inferred from
the type of `(jetNeighborhood.toTotalSpace L kappa).left` it is
`@Over.left _ rho.source.toScheme (@totalSpace rho.source.toScheme _)`, while from `U.ι` and
`P ℓ` it is `@Over.left _ rho.source.toVariety.carrier (@totalSpace rho.source.toVariety.carrier _)`.
The explicit `(Z := (totalSpace L.toModules).left)` in `thickIso` below (and in `θ₁` of the main
theorem, which must be spelled identically so that the `rw` with this lemma stays structural) selects
the second spelling everywhere. -/
theorem morphism_near_zero_jet_compat_left {k : Type u} [Field k]
    {X : SmoothProjectiveVariety k} {C : SmoothProjectiveCurve k}
    {f : C.toScheme ⟶ X.toScheme} {rho : FiniteCover k C}
    {L : LineBundle rho.source.toVariety} {kappa : ℕ}
    (P : Fin (X.embDim + 1) →
      (((AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
        (LineBundle.pullback (X := rho.source.toVariety) (Y := C.toVariety) rho.hom
          (LineBundle.pullback (X := C.toVariety) (Y := X.toVariety) f (X.OX 1))).toModules).val.obj
          (Opposite.op ⊤) : Type u))
    (U : (AlgebraicGeometry.Scheme.totalSpace L.toModules).left.Opens)
    (nu : (jetNeighborhood L kappa).left ⟶ U.toScheme)
    (hnu : nu ≫ U.ι = (jetNeighborhood.toTotalSpace L kappa).left) (ℓ : Fin (X.embDim + 1)) :
    ((pullbackCompApp nu U.ι ((AlgebraicGeometry.Scheme.Modules.pullback
      (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
      (LineBundle.pullback (X := rho.source.toVariety) (Y := C.toVariety) rho.hom
      (LineBundle.pullback (X := C.toVariety) (Y := X.toVariety) f (X.OX 1))).toModules) ≪≫
        (AlgebraicGeometry.Scheme.Modules.pullbackCongr hnu).app ((AlgebraicGeometry.Scheme.Modules.pullback
      (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
      (LineBundle.pullback (X := rho.source.toVariety) (Y := C.toVariety) rho.hom
      (LineBundle.pullback (X := C.toVariety) (Y := X.toVariety) f (X.OX 1))).toModules) ≪≫
        thickIso (Z := (AlgebraicGeometry.Scheme.totalSpace L.toModules).left)
          (jetNeighborhood.toTotalSpace L kappa).left
          (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom (jetNeighborhood.proj L kappa)
          (jetNeighborhood.toTotalSpace_proj L kappa) (LineBundle.pullback (X := rho.source.toVariety) (Y := C.toVariety) rho.hom
      (LineBundle.pullback (X := C.toVariety) (Y := X.toVariety) f (X.OX 1))).toModules).hom.val.app (Opposite.op ⊤)).hom
        (sectionPullbackAlong nu (sectionPullbackAlong U.ι (P ℓ))) =
      restrictToThickening L (LineBundle.pullback (X := rho.source.toVariety) (Y := C.toVariety)
        rho.hom (LineBundle.pullback (X := C.toVariety) (Y := X.toVariety) f (X.OX 1))) kappa (P ℓ) := by
  rw [pullbackCompApp_chain_apply, ← restrictSectionAlong_eq_thickIso_apply]
  rfl

/-- **`Φ₀` restricted to the jet neighbourhood is the projection of the jet to `X`.**

Natural-language proof (each step names the library fact it uses; the Lean proof below follows it).

Notation: `A := seedLineBundle X.embedding f = f^*O_X(1)` on `C`, `N := ρ^*A` on `C̃` (as a module
this is `(LineBundle.pullback ρ (LineBundle.pullback f (X.OX 1))).toModules` up to the
`eqToHom (OX_toModules 1)` identification), `π : Tot(L) → C̃`, `M := π^*N`,
`p := jetNeighborhood.proj L κ`, `i := (jetNeighborhood.toTotalSpace L κ).left : C̃_(κ)(L) ↪ Tot(L)`
(`i ≫ π = p`, `jetNeighborhood.toTotalSpace_proj`), `t := puncturedConeToProduct.base : Z^× → C`,
`emb := X.embedding.emb : X ↪ P^N` (closed immersion, hence mono).

1. Reduce to `P^N`: `emb` is a mono, so it suffices to prove `ν ≫ Φ₀ ≫ emb = ȷ^× ≫ toX ≫ emb`.
2. Left side. By `hPhi`, `Φ₀ ≫ emb = projectivizationMorphism (U.ι^*M) (U.ι^*P)`; by the pullback
   formula `projectivizationMorphism_pullback` (`ν` is a
   `k`-morphism for the `k`-structure `p ≫ (C̃ ↘ Spec k)` on `C̃_(κ)(L)`, because `ν ≫ U.ι = i`
   and `i ≫ π = p`) `ν ≫ Φ₀ ≫ emb = projectivizationMorphism (ν^*U.ι^*M) (ν^*U.ι^*P)`.
   Transport along the canonical isomorphism
   `θ₁ : ν^*U.ι^*M ≅ (ν ≫ U.ι)^*M = i^*π^*N ≅ (i ≫ π)^*N = p^*N`
   (`pullbackComp ν U.ι`, `pullbackCongr hnu`, `pullbackComp i π`, `eqToIso toTotalSpace_proj`)
   using ; on sections this transport sends
   `ν^*U.ι^*(P ℓ)` to `restrictToThickening L N κ (P ℓ)` — literally the definition of
   `restrictToThickening` after
   `AlgebraicGeometry.Scheme.Modules.ModuleSections.pullback_comp` and `pullbackCongr_apply`.
   By `hjet`, `restrictToThickening L N κ (P ℓ) = BasedJet.coneCoordinate ȷ ℓ`. (This step is the
   lemma `morphism_near_zero_jet_compat_left`.)
3. Right side. `MMSetup.toX f = puncturedConeToProduct ≫ pullback.snd` (definition),
   `puncturedConeToProduct = pullback.lift t toX' _` so `toX f = puncturedConeToProduct.toX`
   (`pullback.lift_snd`), and `puncturedConeToProduct.toX ≫ emb = projectivizationMorphism (t^*A) z`
   with `z ℓ := puncturedConeToProduct.coord ℓ` (`IsClosedImmersion.lift_fac`; the `Over Spec k`
   structure on `Z^×` is the local instance `puncturedConeToProduct.overK`, i.e. `t ≫ (C ↘ Spec k)`).
   By the pullback formula along `ȷ^×` (a `k`-morphism: `ȷ^× ≫ t = ȷ^× ≫ Z^×.ι ≫ Z → C = ȷ.hom ≫ (cone).hom
   = p ≫ ρ` by `ȷ.over`, and `ρ` is over `Spec k`),
   `ȷ^× ≫ toX ≫ emb = projectivizationMorphism ((ȷ^×)^* t^*A) ((ȷ^×)^* z)`.
4. Compare coordinates. `z` is, by definition, the tuple of coordinates of the `C`-morphism
   `W → Z ↪ Tot(A^{⊕(N+1)})` under `totalSpaceHomEquiv` (`puncturedConeToProduct.coord`), and
   `coneCoordinate ȷ ℓ` is the tuple of coordinates of `ȷ.hom ≫ coneι` (definition in
   ) followed by `(pullbackComp p ρ).inv` and the `eqToHom (OX_toModules 1)`
   transport. Since `ȷ^× ≫ (Z^×.ι ≫ coneι) = ȷ.hom ≫ coneι`, the naturality of the coordinates
   (`totalSpaceHomEquiv_naturality_coordinate`, , with
   `j := ȷ^×`, `T := Over.mk t`, `m := puncturedConeToProduct.toTot`) followed by the base change
   `totalSpaceHomEquiv_coordinate_congr_base` along `ȷ^× ≫ t = p ≫ ρ` gives: the composite
   `θ₂ : (ȷ^×)^* t^*A ≅ (ȷ^× ≫ t)^*A = (p ≫ ρ)^*A ≅ p^*ρ^*A ≅ p^*N`
   (`pullbackComp`, `pullbackCongr`, `(pullbackComp p ρ).symm`, `eqToIso (OX_toModules 1).symm`)
   sends `(ȷ^×)^* z ℓ` to `coneCoordinate ȷ ℓ`.
5. Apply  with `θ₂` to identify the right side of step 3
   with `projectivizationMorphism (p^*N) (coneCoordinate ȷ)` from step 2; both sides are equal
   (`projectivizationMorphism_congr_tuple`), so `ν ≫ Φ₀ ≫ emb = ȷ^× ≫ toX ≫ emb`, and step 1 concludes. -/
theorem morphism_near_zero_jet_compat {k : Type u} [Field k]
    {X : SmoothProjectiveVariety k} {C : SmoothProjectiveCurve k}
    {f : C.toScheme ⟶ X.toScheme} [D : MMSetup f] {rho : FiniteCover k C}
    {L : LineBundle rho.source.toVariety} {kappa : ℕ} (jet : BasedJet f rho L kappa)
    (P : Fin (X.embDim + 1) →
      (((AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
        (LineBundle.pullback (X := rho.source.toVariety) (Y := C.toVariety) rho.hom
          (LineBundle.pullback (X := C.toVariety) (Y := X.toVariety) f (X.OX 1))).toModules).val.obj
          (Opposite.op ⊤) : Type u))
    (hjet : ∀ ℓ, BasedJet.coneCoordinate jet ℓ =
      restrictToThickening L (LineBundle.pullback (X := rho.source.toVariety) (Y := C.toVariety)
        rho.hom (LineBundle.pullback (X := C.toVariety) (Y := X.toVariety) f (X.OX 1))) kappa
        (P ℓ))
    (U : (AlgebraicGeometry.Scheme.totalSpace L.toModules).left.Opens)
    (Phi0 : U.toScheme ⟶ X.toScheme)
    (hPhi : IsTupleProjectivization
      ((AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
        (LineBundle.pullback (X := rho.source.toVariety) (Y := C.toVariety) rho.hom
          (LineBundle.pullback (X := C.toVariety) (Y := X.toVariety) f (X.OX 1))).toModules)
      P U Phi0)
    (nu : (jetNeighborhood L kappa).left ⟶ U.toScheme)
    (hnu : nu ≫ U.ι = (jetNeighborhood.toTotalSpace L kappa).left)
    (jetx : (jetNeighborhood L kappa).left ⟶ (MMSetup.punctured f).toScheme)
    (hjetx : jetx ≫ (MMSetup.punctured f).ι = jet.hom) :
    nu ≫ Phi0 = jetx ≫ MMSetup.toX f := by
  obtain ⟨hU, hPhi⟩ := hPhi
  -- Conventions (see the section comment above): every module is spelled
  -- out in full (no `let` abbreviations), all section-level statements use the `.val.app (op ⊤)`
  -- spelling, and the tuples `Ptup`/`Qtup` are fixed once so that later lemma applications match
  -- syntactically; otherwise the unifier unfolds the pullback sheaves and the proof becomes far too slow.
  -- the `k`-structures on the jet neighbourhood and on `Z^×` (the latter is the local instance
  -- used inside `puncturedConeToProduct.toX`, restated with the codomain spelled `MMSetup.punctured f`
  -- so that `rw` (reducible transparency) matches the goal)
  let instJ : (jetNeighborhood L kappa).left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨jetNeighborhood.proj L kappa ≫
      (rho.source.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  let instW : (MMSetup.punctured f).toScheme.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    puncturedConeToProduct.overK X.embedding D.E (seedLineBundle X.embedding f) D.E.deg_pos
  -- `t^*A` and `(ȷ^×)^*t^*A` are line bundles (restated with the same spelling of `Z^×`)
  have instLB : AlgebraicGeometry.Scheme.Modules.IsLineBundle (X := (MMSetup.punctured f).toScheme)
      ((AlgebraicGeometry.Scheme.Modules.pullback
      (puncturedConeToProduct.base X.embedding D.E (seedLineBundle X.embedding f) D.E.deg_pos)).obj (seedLineBundle X.embedding f)) :=
    AlgebraicGeometry.Scheme.Modules.IsLineBundle.pullback
      (puncturedConeToProduct.base X.embedding D.E (seedLineBundle X.embedding f) D.E.deg_pos) (seedLineBundle X.embedding f)
  have instLB' : AlgebraicGeometry.Scheme.Modules.IsLineBundle (X := (jetNeighborhood L kappa).left)
      ((AlgebraicGeometry.Scheme.Modules.pullback jetx).obj ((AlgebraicGeometry.Scheme.Modules.pullback
      (puncturedConeToProduct.base X.embedding D.E (seedLineBundle X.embedding f) D.E.deg_pos)).obj (seedLineBundle X.embedding f))) :=
    AlgebraicGeometry.Scheme.Modules.IsLineBundle.pullback jetx _
  -- the cone `Z ↪ Tot(A^{⊕(N+1)})`
  let coneι : (MMSetup.cone f).left ⟶ (AlgebraicGeometry.Scheme.totalSpace
      (AlgebraicGeometry.Scheme.Modules.pow (seedLineBundle X.embedding f) (X.embDim + 1))).left :=
    (⨆ j, AlgebraicGeometry.Scheme.idealSheafOfSection _
      (homogeneousEquationSection (seedLineBundle X.embedding f) X.embDim (D.E.F j)
        (D.E.homogeneous j))).subschemeι
  -- ν and ȷ^× are k-morphisms
  have hν : nu.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)) := ⟨by
    change nu ≫ (U.ι ≫ ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ≫
      (rho.source.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))) =
      jetNeighborhood.proj L kappa ≫
        (rho.source.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
    rw [← Category.assoc, hnu, ← Category.assoc, jetNeighborhood.toTotalSpace_proj]⟩
  have hjt : jetx ≫ puncturedConeToProduct.base X.embedding D.E (seedLineBundle X.embedding f)
      D.E.deg_pos = jetNeighborhood.proj L kappa ≫ rho.hom := by
    change jetx ≫ ((MMSetup.punctured f).ι ≫ (MMSetup.cone f).hom) = _
    rw [← Category.assoc, hjetx, jet.over]
  have hξ : jetx.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)) := ⟨by
    change jetx ≫ (((MMSetup.punctured f).ι ≫ (MMSetup.cone f).hom) ≫
      (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) =
      jetNeighborhood.proj L kappa ≫
        (rho.source.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
    rw [← Category.assoc, ← Category.assoc, hjetx, jet.over, Category.assoc]
    exact congrArg (fun x => jetNeighborhood.proj L kappa ≫ x) rho.isOver⟩
  -- step 3: `toX ≫ emb` is the projectivization of the tautological coordinates `z`
  have htoX : MMSetup.toX f =
      puncturedConeToProduct.toX X.embedding D.E (seedLineBundle X.embedding f) D.E.deg_pos :=
    CategoryTheory.Limits.pullback.lift_snd _ _ _
  have hfac : MMSetup.toX f ≫ X.embedding.emb =
      projectivizationMorphism (k := k) (V := (MMSetup.punctured f).toScheme)
        ((AlgebraicGeometry.Scheme.Modules.pullback
      (puncturedConeToProduct.base X.embedding D.E (seedLineBundle X.embedding f) D.E.deg_pos)).obj (seedLineBundle X.embedding f))
        (puncturedConeToProduct.coord X.embedding D.E (seedLineBundle X.embedding f) D.E.deg_pos)
        (puncturedConeToProduct.coord_nowhereZero X.embedding D.E (seedLineBundle X.embedding f)
          D.E.deg_pos) := by
    rw [htoX]
    exact AlgebraicGeometry.IsClosedImmersion.lift_fac _ _ _
  have hU' := exists_not_isZeroAt_sectionPullbackAlong nu _ _ hU
  have hz' := exists_not_isZeroAt_sectionPullbackAlong jetx _ _
    (puncturedConeToProduct.coord_nowhereZero X.embedding D.E (seedLineBundle X.embedding f)
      D.E.deg_pos)
  -- steps 1–3: both sides are projectivizations on the jet neighbourhood
  -- (the right-hand side is handled in term mode: `rw` would have to re-check the types of the
  -- proof arguments at reducible transparency, where `MMSetup.punctured f` does not unfold)
  rw [← cancel_mono X.embedding.emb, Category.assoc, hPhi, Category.assoc, hfac,
    projectivizationMorphism_pullback nu _ _ hU hU']
  refine Eq.trans ?_ (projectivizationMorphism_pullback jetx _ _ _ hz').symm
  -- the two tuples, fixed once
  let Ptup : Fin (X.embDim + 1) → ((((AlgebraicGeometry.Scheme.Modules.pullback nu).obj
      ((AlgebraicGeometry.Scheme.Modules.pullback U.ι).obj ((AlgebraicGeometry.Scheme.Modules.pullback
      (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
      (LineBundle.pullback (X := rho.source.toVariety) (Y := C.toVariety) rho.hom
      (LineBundle.pullback (X := C.toVariety) (Y := X.toVariety) f (X.OX 1))).toModules))).val.obj (Opposite.op ⊤)) : Type u) :=
    fun ℓ => sectionPullbackAlong nu (sectionPullbackAlong U.ι (P ℓ))
  let Qtup : Fin (X.embDim + 1) → ((((AlgebraicGeometry.Scheme.Modules.pullback jetx).obj
      ((AlgebraicGeometry.Scheme.Modules.pullback
      (puncturedConeToProduct.base X.embedding D.E (seedLineBundle X.embedding f) D.E.deg_pos)).obj (seedLineBundle X.embedding f))).val.obj (Opposite.op ⊤)) : Type u) :=
    fun ℓ => sectionPullbackAlong jetx (puncturedConeToProduct.coord X.embedding D.E (seedLineBundle X.embedding f) D.E.deg_pos ℓ)
  have hU'' : ∀ v : (jetNeighborhood L kappa).left, ∃ ℓ, ¬ IsZeroAt (Ptup ℓ) v :=
    fun v => (hU' v).imp fun ℓ h => h
  have hz'' : ∀ v : (jetNeighborhood L kappa).left, ∃ ℓ, ¬ IsZeroAt (Qtup ℓ) v :=
    fun v => (hz' v).imp fun ℓ h => h
  -- step 2: the canonical isomorphism ν^*U.ι^*M ≅ p^*N. Its target is spelled with
  -- `rho.source.toVariety.carrier` (the spelling inside `restrictToThickening`), not
  -- `rho.source.toScheme`: the two are definitionally equal, but a mismatch of this implicit argument
  -- under a linear-map application makes the unifier unfold the pullback sheaves (far too slow).
  -- Its source spelling: `Z` of `thickIso` is pinned to `(totalSpace L.toModules).left` (spelled with
  -- `rho.source.toVariety.carrier`), exactly as in the statement of `morphism_near_zero_jet_compat_left`;
  -- the `rw` with that lemma below is then a structural match (see its docstring).
  let θ₁ : (AlgebraicGeometry.Scheme.Modules.pullback nu).obj
      ((AlgebraicGeometry.Scheme.Modules.pullback U.ι).obj ((AlgebraicGeometry.Scheme.Modules.pullback
      (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
      (LineBundle.pullback (X := rho.source.toVariety) (Y := C.toVariety) rho.hom
      (LineBundle.pullback (X := C.toVariety) (Y := X.toVariety) f (X.OX 1))).toModules)) ≅
      (@AlgebraicGeometry.Scheme.Modules.pullback (jetNeighborhood L kappa).left
        rho.source.toVariety.carrier (jetNeighborhood.proj L kappa)).obj
        (LineBundle.pullback (X := rho.source.toVariety) (Y := C.toVariety) rho.hom
      (LineBundle.pullback (X := C.toVariety) (Y := X.toVariety) f (X.OX 1))).toModules :=
    pullbackCompApp nu U.ι ((AlgebraicGeometry.Scheme.Modules.pullback
      (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
      (LineBundle.pullback (X := rho.source.toVariety) (Y := C.toVariety) rho.hom
      (LineBundle.pullback (X := C.toVariety) (Y := X.toVariety) f (X.OX 1))).toModules) ≪≫
    (AlgebraicGeometry.Scheme.Modules.pullbackCongr hnu).app ((AlgebraicGeometry.Scheme.Modules.pullback
      (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
      (LineBundle.pullback (X := rho.source.toVariety) (Y := C.toVariety) rho.hom
      (LineBundle.pullback (X := C.toVariety) (Y := X.toVariety) f (X.OX 1))).toModules) ≪≫
    thickIso (Z := (AlgebraicGeometry.Scheme.totalSpace L.toModules).left)
          (jetNeighborhood.toTotalSpace L kappa).left
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom (jetNeighborhood.proj L kappa)
        (jetNeighborhood.toTotalSpace_proj L kappa) (LineBundle.pullback (X := rho.source.toVariety) (Y := C.toVariety) rho.hom
      (LineBundle.pullback (X := C.toVariety) (Y := X.toVariety) f (X.OX 1))).toModules
  have hL : ∀ ℓ, (θ₁.hom.val.app (Opposite.op ⊤)).hom (Ptup ℓ) = BasedJet.coneCoordinate jet ℓ := by
    intro ℓ
    -- only `rw` with syntactically matching closed patterns (see MorphismNearZeroJetCompatBridges)
    rw [show Ptup ℓ = sectionPullbackAlong nu (sectionPullbackAlong U.ι (P ℓ)) from rfl,
      show θ₁ = pullbackCompApp nu U.ι ((AlgebraicGeometry.Scheme.Modules.pullback
      (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
      (LineBundle.pullback (X := rho.source.toVariety) (Y := C.toVariety) rho.hom
      (LineBundle.pullback (X := C.toVariety) (Y := X.toVariety) f (X.OX 1))).toModules) ≪≫
        (AlgebraicGeometry.Scheme.Modules.pullbackCongr hnu).app ((AlgebraicGeometry.Scheme.Modules.pullback
      (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
      (LineBundle.pullback (X := rho.source.toVariety) (Y := C.toVariety) rho.hom
      (LineBundle.pullback (X := C.toVariety) (Y := X.toVariety) f (X.OX 1))).toModules) ≪≫
        thickIso (Z := (AlgebraicGeometry.Scheme.totalSpace L.toModules).left)
          (jetNeighborhood.toTotalSpace L kappa).left
          (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom (jetNeighborhood.proj L kappa)
          (jetNeighborhood.toTotalSpace_proj L kappa) (LineBundle.pullback (X := rho.source.toVariety) (Y := C.toVariety) rho.hom
      (LineBundle.pullback (X := C.toVariety) (Y := X.toVariety) f (X.OX 1))).toModules from rfl,
      morphism_near_zero_jet_compat_left P U nu hnu ℓ, hjet ℓ]
  -- step 4: the canonical isomorphism (ȷ^×)^*t^*A ≅ p^*N
  let θ₂ : (AlgebraicGeometry.Scheme.Modules.pullback jetx).obj ((AlgebraicGeometry.Scheme.Modules.pullback
      (puncturedConeToProduct.base X.embedding D.E (seedLineBundle X.embedding f) D.E.deg_pos)).obj (seedLineBundle X.embedding f)) ≅
      (AlgebraicGeometry.Scheme.Modules.pullback (jetNeighborhood.proj L kappa)).obj
        (LineBundle.pullback (X := rho.source.toVariety) (Y := C.toVariety) rho.hom
      (LineBundle.pullback (X := C.toVariety) (Y := X.toVariety) f (X.OX 1))).toModules :=
    pullbackCompApp jetx (puncturedConeToProduct.base X.embedding D.E (seedLineBundle X.embedding f) D.E.deg_pos) (seedLineBundle X.embedding f) ≪≫
    (AlgebraicGeometry.Scheme.Modules.pullbackCongr hjt).app (seedLineBundle X.embedding f) ≪≫
    (pullbackCompApp (jetNeighborhood.proj L kappa) rho.hom (seedLineBundle X.embedding f)).symm ≪≫
    (AlgebraicGeometry.Scheme.Modules.pullback (jetNeighborhood.proj L kappa)).mapIso
      ((AlgebraicGeometry.Scheme.Modules.pullback rho.hom).mapIso
        ((AlgebraicGeometry.Scheme.Modules.pullback f).mapIso
          (CategoryTheory.eqToIso (X.OX_toModules 1).symm)))
  have hR : ∀ ℓ, (θ₂.hom.val.app (Opposite.op ⊤)).hom (Qtup ℓ) = BasedJet.coneCoordinate jet ℓ := by
    intro ℓ
    -- coordinate naturality along ȷ^×
    have hR1 : (((pullbackCompApp jetx (puncturedConeToProduct.base X.embedding D.E (seedLineBundle X.embedding f) D.E.deg_pos) (seedLineBundle X.embedding f)).hom.val.app (Opposite.op ⊤)).hom
        (sectionPullbackAlong jetx (puncturedConeToProduct.coord X.embedding D.E (seedLineBundle X.embedding f) D.E.deg_pos ℓ))) = (((AlgebraicGeometry.Scheme.Modules.pullback (jetx ≫
            puncturedConeToProduct.base X.embedding D.E (seedLineBundle X.embedding f)
              D.E.deg_pos)).map
          (biproduct.π (fun _ : Fin (X.embDim + 1) => seedLineBundle X.embedding f) ℓ)).val.app
            (Opposite.op ⊤)).hom
          (AlgebraicGeometry.Scheme.totalSpaceHomEquiv
            (⨁ fun _ : Fin (X.embDim + 1) => seedLineBundle X.embedding f)
            (CategoryTheory.Over.mk (jetx ≫
              puncturedConeToProduct.base X.embedding D.E (seedLineBundle X.embedding f)
                D.E.deg_pos))
            ((CategoryTheory.Over.homMk jetx rfl :
              CategoryTheory.Over.mk (jetx ≫
                puncturedConeToProduct.base X.embedding D.E (seedLineBundle X.embedding f)
                  D.E.deg_pos) ⟶
              CategoryTheory.Over.mk (puncturedConeToProduct.base X.embedding D.E
                (seedLineBundle X.embedding f) D.E.deg_pos)) ≫
              puncturedConeToProduct.toTot X.embedding D.E (seedLineBundle X.embedding f)
                D.E.deg_pos)) :=
      (AlgebraicGeometry.Scheme.totalSpaceHomEquiv_naturality_coordinate
        (fun _ : Fin (X.embDim + 1) => seedLineBundle X.embedding f)
        (CategoryTheory.Over.mk (puncturedConeToProduct.base X.embedding D.E
          (seedLineBundle X.embedding f) D.E.deg_pos))
        jetx
        (puncturedConeToProduct.toTot X.embedding D.E (seedLineBundle X.embedding f) D.E.deg_pos)
        ℓ).symm
    -- base change along ȷ^× ≫ t = p ≫ ρ
    have hR2 := AlgebraicGeometry.Scheme.totalSpaceHomEquiv_coordinate_congr_base
      (fun _ : Fin (X.embDim + 1) => seedLineBundle X.embedding f) hjt
      ((CategoryTheory.Over.homMk jetx rfl :
          CategoryTheory.Over.mk (jetx ≫
            puncturedConeToProduct.base X.embedding D.E (seedLineBundle X.embedding f)
              D.E.deg_pos) ⟶
          CategoryTheory.Over.mk (puncturedConeToProduct.base X.embedding D.E
            (seedLineBundle X.embedding f) D.E.deg_pos)) ≫
        puncturedConeToProduct.toTot X.embedding D.E (seedLineBundle X.embedding f) D.E.deg_pos)
      (CategoryTheory.Over.homMk (jet.hom ≫ coneι)
        ((Category.assoc jet.hom coneι (AlgebraicGeometry.Scheme.totalSpace
          (AlgebraicGeometry.Scheme.Modules.pow (seedLineBundle X.embedding f)
            (X.embDim + 1))).hom).trans jet.over))
      ((Category.assoc jetx (MMSetup.punctured f).ι coneι).symm.trans
        (congrArg (fun x => x ≫ coneι) hjetx))
      ℓ
    show (((pullbackCompApp jetx (puncturedConeToProduct.base X.embedding D.E (seedLineBundle X.embedding f) D.E.deg_pos) (seedLineBundle X.embedding f) ≪≫
        (AlgebraicGeometry.Scheme.Modules.pullbackCongr hjt).app (seedLineBundle X.embedding f) ≪≫
        (pullbackCompApp (jetNeighborhood.proj L kappa) rho.hom (seedLineBundle X.embedding f)).symm ≪≫
        (AlgebraicGeometry.Scheme.Modules.pullback (jetNeighborhood.proj L kappa)).mapIso
          ((AlgebraicGeometry.Scheme.Modules.pullback rho.hom).mapIso
            ((AlgebraicGeometry.Scheme.Modules.pullback f).mapIso
              (CategoryTheory.eqToIso (X.OX_toModules 1).symm)))).hom.val.app (Opposite.op ⊤)).hom
      (sectionPullbackAlong jetx (puncturedConeToProduct.coord X.embedding D.E (seedLineBundle X.embedding f) D.E.deg_pos ℓ))) = _
    rw [trans_hom_val_app_top_apply, trans_hom_val_app_top_apply, trans_hom_val_app_top_apply,
      hR1, hR2]
    rfl
  -- step 5: assemble
  have hUθ₁ := exists_not_isZeroAt_iso_val θ₁ Ptup hU''
  have hzθ₂ := exists_not_isZeroAt_iso_val θ₂ Qtup hz''
  refine Eq.trans (projectivizationMorphism_congr_iso_val _ _ θ₁ Ptup hU'' hUθ₁)
    (Eq.trans ?_ (projectivizationMorphism_congr_iso_val _ _ θ₂ Qtup hz'' hzθ₂).symm)
  exact projectivizationMorphism_congr_tuple _
    (P := fun ℓ => (θ₁.hom.val.app (Opposite.op ⊤)).hom (Ptup ℓ))
    (Q := fun ℓ => (θ₂.hom.val.app (Opposite.op ⊤)).hom (Qtup ℓ))
    (funext fun ℓ => (hL ℓ).trans (hR ℓ).symm) hUθ₁ hzθ₂

end
