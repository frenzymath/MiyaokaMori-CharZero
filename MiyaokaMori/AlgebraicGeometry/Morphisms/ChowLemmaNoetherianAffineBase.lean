import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Morphisms.ChowLemmaProjectiveCompletion
import MiyaokaMori.AlgebraicGeometry.Morphisms.ChowLemmaProjectiveProduct
import MiyaokaMori.AlgebraicGeometry.Morphisms.ChowLemmaGeometricAssembly

/-! # Chow's lemma over a Noetherian affine base

**Chow's lemma over a Noetherian affine base, integral case** (Stacks 0200 with `S = Spec A`; Stacks 0201;
EGA II 5.6.1; Hartshorne Ex. II.4.10). For `A` Noetherian, `Z` integral and `g : Z → Spec A` proper there
are a scheme `Z'` and a morphism `π : Z' → Z` such that `π` and `π ≫ g` are projective and `π` is an
isomorphism over a nonempty open `U ⊆ Z`.

This is step 1 of the construction of a generating sheaf on an integral proper scheme
(`IntegralProperGeneratorSheaf.lean`).

The proof body below is assembled from four modules:
* `ChowLemmaNoetherianAffineBase_Completion.lean` — step 1: affine of finite type over a locally Noetherian
  base ⇒ quasi-projective ⇒ open immersion into a projective `S`-scheme (Stacks 01P9 + 07RM);
* `ChowLemmaNoetherianAffineBase_Product.lean` — step 2: finite fibre products of projective `S`-schemes;
* `ChowLemmaNoetherianAffineBase_Aux.lean` — closed immersion into a projective `S`-scheme is projective, proper
  immersion is a closed immersion, immersions are local on the target;
* `ChowLemmaNoetherianAffineBase_Assembly.lean` — steps 3–9, the geometric assembly `ChowSetup`.

**Route actually formalized (differs from the sketch below in steps 3–9).** Instead of the closure `X''` of `U`
in `P`, the opens `V_i ⊆ X''` and the gluing of `π`, the Assembly takes the scheme-theoretic image
`Z' := γ.image` of the graph `γ = (U.ι, g_U) : U ⟶ Z ×_S P`. Then `π := imageι ≫ pr₁` is a closed immersion
into the base change `Z ×_S P → Z` of the projective `f_P`, hence projective directly (no gluing, no graph
argument); `h := imageι ≫ pr₂ : Z' ⟶ P` is proper and, locally over the opens `O_i := p_i⁻¹(e_i(W_i))`, factors
through the graph `Γ_i = W_i ×_{Z_i} P ≅ O_i`, so it is an immersion (`h⁻¹(O_i) = π⁻¹(u_i(W_i))` by the
"proper open immersion with nonempty source into an irreducible scheme is an isomorphism" trick), hence a
closed immersion, so `π ≫ g = h ≫ f_P` is projective; `π` is an isomorphism over `U` by the same trick applied
to the section `U ⟶ π⁻¹U`. The field-case modules `Stacks0200_ChowAssembly*.lean` follow the original
sketch; `Stacks0200_ChowAssembly_Aux.lean` is shared.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- **Chow's lemma** (Stacks 0200, base `S := Spec A`, `A` Noetherian;
Stacks 0201 for the birationality statement; EGA II 5.6.1). `Z` integral, `g : Z → Spec A` proper. Then
there are `Z'` and `π : Z' → Z` with `π` projective, `π ≫ g` projective (so `Z'` is projective over `A`),
and a nonempty open `U ⊆ Z` over which `π` is an isomorphism (`IsIso (π ∣_ U)`).

**Natural-language proof (complete; all cited facts are in Mathlib or in this library).** Write `S := Spec A`.
`S` is affine, hence `CompactSpace S` and `QuasiSeparatedSpace S`, and locally Noetherian (`A` Noetherian).
`Z` is proper over `S`, hence separated and of finite type over `S`; so `Z` is Noetherian
(`LocallyOfFiniteType.isLocallyNoetherian g`, `QuasiCompact.compactSpace_of_compactSpace g`), and every open
of `Z` is quasi-compact. `Z` is integral, so nonempty and irreducible with generic point `η`
(`IsIntegral → IrreducibleSpace`, `genericPoint`). `Z` is separated as a scheme (`Z → S` separated and `S`
affine, hence separated over `Spec ℤ`; Mathlib `IsSeparated.comp`).

0. *Finite affine cover.* `𝒰 := Z.affineCover.finiteSubcover` (Mathlib): finitely many affine `W_i := 𝒰.X i`
   with open immersions `u_i := 𝒰.f i : W_i → Z`, `⨆ i, (u_i).opensRange = ⊤`. Put `w_i := u_i ≫ g : W_i → S`,
   locally of finite type (`g` is, `u_i` is an open immersion).

1. *Each piece is quasi-projective over `S`, hence has a projective completion* (Stacks 01P9 + 07RM).
   `W_i` is affine of finite type over the locally Noetherian `S`, so `W_i` is Noetherian
   (`LocallyOfFiniteType.isLocallyNoetherian w_i`). `O_{W_i}` is ample (`IsAmple.unit_of_isQuasiAffine`,
   `Stacks0892_QuasiAffineUnitAmple.lean`, Stacks 01P9), and for every affine open `V ⊆ S` the
   preimage `w_i⁻¹V` is quasi-affine (an open of the Noetherian affine `W_i`: `Scheme.IsQuasiAffine.of_isImmersion`),
   so `O|_{w_i⁻¹V}` is ample (`IsAmple.pullback_of_isQuasiAffine`). Hence `IsQuasiProjectiveMorphism w_i`
   (this is `isQuasiProjectiveMorphism_of_isAffine` of `Stacks0200_Pieces.lean` with `Spec k` replaced by `S`;
   its proof uses nothing about the field). Stacks 07RM
   (`IsQuasiProjectiveMorphism.exists_isOpenImmersion_isProjectiveMorphism w_i`, `Stacks07rm.lean`, needs
   `CompactSpace S`, `QuasiSeparatedSpace S`) gives a scheme `Z_i`, an open immersion `e_i : W_i → Z_i` and a
   projective `f_i : Z_i → S` with `e_i ≫ f_i = w_i`.

2. *The product `P` of the `Z_i` over `S`.* By induction on `Fintype.card 𝒰.I₀` (using `Fintype.equivFin`)
   build `P` with `f_P : P → S` projective and `S`-morphisms `p_i : P → Z_i` (`p_i ≫ f_i = f_P`) such that for
   every `S`-scheme `T` and `S`-morphisms `t_i : T → Z_i` there is a unique `t : T → P` with `t ≫ p_i = t_i`
   (`pullback.lift`, `pullback.hom_ext`). Induction step: `P' := pullback f_P f_m` with
   `f_{P'} := pullback.fst ≫ f_P`; `pullback.fst : P' → P` is projective as the base change of `f_m`
   (`IsProjectiveMorphism.baseChange f_m f_P`, up to the symmetry `pullback.symmetry`), and
   `f_{P'} = pullback.fst ≫ f_P` is projective by `IsProjectiveMorphism.comp` (`ProjectiveMorphismComp.lean`;
   `CompactSpace S`, `QuasiSeparatedSpace S`). Base case: `P := Z_1`. (Model: `isProjectiveOver_pullback` in
   `Stacks0200_Pieces.lean`, which is exactly this step over a field.)

3. *(Steps 3–9 below are the original sketch; the formalized route differs, see the module docstring.)*
   *The dense open `U` and the diagonal `g_U : U → P`.* `U := ⨅ i, (u_i).opensRange` (finite infimum; drop the
   empty pieces, which does not change the cover). Each `(u_i).opensRange` is a nonempty open of the
   irreducible `Z`, so it contains `η` (`genericPoint_spec.mem_open_set_iff`); hence `η ∈ U`, `U ≠ ∅`, and `U` is
   dense. For each `i`, `U.ι = s_i ≫ u_i` with `s_i := IsOpenImmersion.lift u_i U.ι` an open immersion; put
   `g_i := s_i ≫ e_i : U → Z_i` (an `S`-morphism: `g_i ≫ f_i = s_i ≫ w_i = U.ι ≫ g`). Let `g_U : U → P` be the
   unique `S`-morphism with `g_U ≫ p_i = g_i`. `g_U` is an immersion (`IsImmersion.of_comp`: `g_U ≫ p_{i₀} = g_{i₀}`
   is an open immersion) and quasi-compact (`U` quasi-compact, `P` quasi-separated). Let `X'' := g_U.image`
   (Mathlib `Scheme.Hom.image`, the scheme-theoretic image), `ι'' := g_U.imageι : X'' → P` a closed immersion and
   `t := g_U.toImage : U → X''` an open immersion (`g_U` a quasi-compact immersion) which is dominant.
   `X'' → S` (`ι'' ≫ f_P`) is projective: composing `ι''` with the closed immersion `P → Proj_S 𝒜` from
   `IsProjectiveMorphism f_P` is a closed immersion over `S` into the same `Proj_S 𝒜` (`IsClosedImmersion.comp`),
   and this is the definition of `IsProjectiveMorphism`. `X''` is integral:
   reduced because `Γ(X'', V) → Γ(U, t⁻¹V)` is injective (`Scheme.Hom.toImage_app_injective`), irreducible
   because it is the closure of the irreducible dense image of `U` (`IsIrreducible.closure`), nonempty.

4. *Projections `q_i`, opens `V_i`, maps `π_i`.* `q_i := ι'' ≫ p_i : X'' → Z_i` is proper: `X'' → S` is proper
   (projective ⇒ proper, `IsProjectiveMorphism.isProper`, Stacks 01WC) and `f_i` is separated
   (`IsProper.of_comp q_i f_i`). `V_i := q_i ⁻¹ᵁ (e_i).opensRange`; `r_i : V_i → W_i` is `q_i ∣_ (e_i).opensRange`
   followed by the inverse of `e_i.isoOpensRange`, proper, with `r_i ≫ e_i = V_i.ι ≫ q_i`. Put
   `π_i := r_i ≫ u_i : V_i → Z`. For `u ∈ U`: `q_i(t u) = e_i(s_i u)`, so `t.opensRange ≤ V_i`, and with
   `t_i : U → V_i` the restriction of `t`, `t_i ≫ r_i = s_i` (`e_i` mono), hence `t_i ≫ π_i = U.ι`.

5. *Gluing `π : Z' → Z`.* `Z' := ⨆ i, V_i` (an open of `X''`, nonempty as `t.opensRange ≤ Z'`). On `V_i ⊓ V_j`
   the morphisms `π_i, π_j` agree on the dense open `t.opensRange` (both are `U.ι` there), `V_i ⊓ V_j` is reduced
   (open in the integral `X''`) and `Z` is separated, so they agree (Mathlib `ext_of_isDominant_of_isSeparated`).
   Glue (`Scheme.OpenCover.glueMorphisms`) to `π : Z' → Z` with `(V_i → Z') ≫ π = π_i`; `π ≫ g = Z' → S`
   (`Scheme.OpenCover.hom_ext`: on `V_i`, `π_i ≫ g = r_i ≫ w_i = r_i ≫ e_i ≫ f_i = V_i.ι ≫ q_i ≫ f_i = V_i.ι ≫ (X'' → S)`).

6. *`π⁻¹((u_i).opensRange) = V_i` and `π` is proper.* `O_i := π ⁻¹ᵁ (u_i).opensRange ⊇ V_i`. The open
   immersion `V_i → O_i` composed with `O_i → (u_i).opensRange ≅ W_i` is the proper `r_i`, and `O_i → W_i` is
   separated (a morphism between schemes separated over `S`), so `V_i → O_i` is proper (`IsProper.of_comp`),
   hence has closed range; `V_i` is a nonempty clopen of the irreducible `O_i` (nonempty open of the irreducible
   `X''`), so `V_i = O_i` (`PreirreducibleSpace.isClopen_iff`). Thus `π ∣_ (u_i).opensRange` is isomorphic to `r_i`,
   proper; `⨆ (u_i).opensRange = ⊤` and `IsProper` is Zariski-local on the target
   (`IsZariskiLocalAtTarget @IsProper`, `IsLocalAtTarget.of_iSup_eq_top`), so `π` is proper.

7. *`π` is an isomorphism over `U`.* `O := π ⁻¹ᵁ U`; `t` lands in `O` (step 4: `π(t u) = u`), giving an open
   immersion `τ : U → O` with `τ ≫ (π ∣_ U) = 𝟙 U`. `π ∣_ U` is separated, so `τ` is proper (`IsProper.of_comp`),
   hence has closed range; `O` is irreducible and `τ` has nonempty open range, so `τ` is surjective, and a
   surjective open immersion is an isomorphism (`IsOpenImmersion.isIso_of_surjective`-type lemma). Hence
   `IsIso (π ∣_ U)`.

8. *`π ≫ g` is projective* (Stacks 01W7-type argument, the model is `isProjectiveOver_of_isImmersion_projectiveSpace`
   in `Stacks0200_Pieces.lean`). `j := Z'.ι ≫ ι'' ≫ (P → Proj_S 𝒜)` is an immersion over `S` (open immersion
   followed by closed immersions; `IsImmersion.comp`). `Z' → S = π ≫ g` is proper (`π` proper by step 6, `g`
   proper; `IsProper.comp`), and `Proj_S 𝒜 → S` is separated, so `j` is proper (`IsProper.of_comp`); a proper
   immersion has closed range and is therefore a closed immersion (Mathlib: `IsImmersion` + closed range ⇒
   `IsClosedImmersion`, `isClosedImmersion_iff_isImmersion_and_isClosed_range`-type lemma). So `π ≫ g` is a closed
   immersion into `Proj_S 𝒜` over `S`, with `𝒜` generated in degree one and `𝒜₁` of finite type (the data of
   `IsProjectiveMorphism f_P`): `IsProjectiveMorphism (π ≫ g)` by definition.

9. *`π` is projective.* Let `P_Z := pullback g f_P` with `pullback.fst : P_Z → Z`, projective as the base
   change of `f_P` along `g` (`IsProjectiveMorphism.baseChange f_P g`, up to `pullback.symmetry`): it comes with a
   closed immersion `c : P_Z → Proj_Z ℬ` over `Z` (`ℬ` generated in degree one, `ℬ₁` finite type). The graph
   `γ := pullback.lift π (Z'.ι ≫ ι'') _ : Z' → P_Z` (compatibility: `π ≫ g = Z'.ι ≫ ι'' ≫ f_P`, step 5) is an
   immersion (`γ ≫ pullback.snd = Z'.ι ≫ ι''` is an immersion, `IsImmersion.of_comp`), and `γ ≫ pullback.fst = π`
   is proper while `pullback.fst` is separated (base change of the separated `f_P`), so `γ` is proper
   (`IsProper.of_comp`) and therefore a closed immersion (as in step 8). Then `γ ≫ c : Z' → Proj_Z ℬ` is a
   closed immersion over `Z` with `(γ ≫ c) ≫ (Proj_Z ℬ → Z) = π`: `IsProjectiveMorphism π` by definition.

Return `⟨Z', π, step 9, step 8, U, step 3, step 7⟩`.

**Edge cases.** `A = 0`: `Spec A = ∅` and there is no integral `Z` (vacuous). `Z` a point (`Z = Spec K`,
`K` finite over `A`): `𝒰` has one affine piece, `Z' = X'' = Z_1`-closure of `Z`, `π` an isomorphism, `U = ⊤`.
`Z` already projective over `A`: the construction still returns some `Z'`; nothing requires `Z' = Z`.
`U = ⊤` is allowed (then `π` is an isomorphism). `Z'` need not be integral for the statement, although the
construction gives an integral `Z'` (a nonempty open of the integral `X''`).

**Why these hypotheses.** Stacks 0200 holds for any `Z` separated of finite type over a Noetherian `S`, with
`U` dense; `IsProper g` and `IsIntegral Z` are what the only user has, and integrality turns "dense" into
"nonempty" and removes the reduction to irreducible components. The only other user of a Chow lemma in the
library is the field case (Stacks 0200 over a field), which is this statement with `A = k` up to the
`IsProjectiveOver`/`IsProjectiveMorphism` bridge.

**Formalization.** Steps 0–2 are formalized as sketched (`_Completion`, `_Product`); steps
3–9 are replaced by the scheme-theoretic-image route described in the module docstring (`_Assembly`,
`ChowSetup`), which needs neither the gluing of step 5 nor the graph argument of step 9. -/
theorem AlgebraicGeometry.exists_projective_birational_of_isProper_over_noetherianRing
    {A : CommRingCat.{u}} [IsNoetherianRing A]
    {Z : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsIntegral Z]
    (g : Z ⟶ AlgebraicGeometry.Spec A) [AlgebraicGeometry.IsProper g] :
    ∃ (Z' : AlgebraicGeometry.Scheme.{u}) (π : Z' ⟶ Z),
      AlgebraicGeometry.IsProjectiveMorphism π ∧ AlgebraicGeometry.IsProjectiveMorphism (π ≫ g) ∧
      ∃ U : Z.Opens, (U : Set Z).Nonempty ∧ CategoryTheory.IsIso (π ∣_ U) := by
  classical
  -- `Z` is Noetherian
  have hZc : CompactSpace Z := AlgebraicGeometry.QuasiCompact.compactSpace_of_compactSpace g
  have hZn : AlgebraicGeometry.IsLocallyNoetherian Z :=
    AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian g
  have hZN : AlgebraicGeometry.IsNoetherian Z := ⟨⟩
  -- step 0: the finite affine cover, restricted to its nonempty pieces
  let 𝒰 := Z.affineCover.finiteSubcover
  let ι := {i : 𝒰.I₀ // Nonempty (𝒰.X i)}
  let W : ι → AlgebraicGeometry.Scheme.{u} := fun i => 𝒰.X i.1
  let u : ∀ i, W i ⟶ Z := fun i => 𝒰.f i.1
  have hW : ∀ i, AlgebraicGeometry.IsAffine (W i) := fun i => by
    show AlgebraicGeometry.IsAffine (Z.affineCover.X _)
    infer_instance
  have hu : ∀ i, AlgebraicGeometry.IsOpenImmersion (u i) := fun i => inferInstance
  have hcover : ⨆ i, (u i).opensRange = ⊤ := by
    refine eq_top_iff.mpr fun z _ => ?_
    obtain ⟨j, y, hy⟩ := 𝒰.exists_eq z
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨j, ⟨y⟩⟩, y, hy⟩
  have hne : Nonempty ι := by
    obtain ⟨j, y, -⟩ := 𝒰.exists_eq (Classical.arbitrary Z)
    exact ⟨⟨j, ⟨y⟩⟩⟩
  -- step 1: projective completions of the pieces (Stacks 01P9 + 07RM; module `_Completion`)
  have hA : ∀ i, ∃ (Zc : AlgebraicGeometry.Scheme.{u}) (e : W i ⟶ Zc) (f : Zc ⟶ AlgebraicGeometry.Spec A),
      AlgebraicGeometry.IsOpenImmersion e ∧ AlgebraicGeometry.IsProjectiveMorphism f ∧ e ≫ f = u i ≫ g :=
    fun i => by
      have := hW i
      exact AlgebraicGeometry.exists_isOpenImmersion_isProjectiveMorphism_of_isAffine_of_isLocallyNoetherian
        (u i ≫ g)
  choose Zc e f he hf hef using hA
  -- step 2: the product of the completions over `Spec A`
  obtain ⟨P, fP, hP, p, hp, hlift⟩ :=
    AlgebraicGeometry.exists_isProjectiveMorphism_product (S := AlgebraicGeometry.Spec A) Zc f
  -- step 3: the dense open `U = ⋂ᵢ uᵢ(Wᵢ)` and the diagonal `gU : U ⟶ P`
  let U : Z.Opens :=
    ⟨⋂ i, Set.range (u i), isOpen_iInter_of_finite fun i => (u i).isOpenEmbedding.isOpen_range⟩
  have hUle : ∀ i, (U : Set Z) ⊆ Set.range (u i) := fun i => Set.iInter_subset _ i
  have hUne : (U : Set Z).Nonempty := by
    refine ⟨genericPoint Z, Set.mem_iInter.mpr fun i => ?_⟩
    rw [(genericPoint_spec Z).mem_open_set_iff (u i).isOpenEmbedding.isOpen_range]
    obtain ⟨y⟩ := i.2
    exact ⟨u i y, trivial, ⟨_, rfl⟩⟩
  have hUc : IsCompact (U : Set Z) := TopologicalSpace.NoetherianSpace.isCompact _
  have hsr : ∀ i, Set.range U.ι ⊆ Set.range (u i) := fun i => by
    rw [AlgebraicGeometry.Scheme.Opens.range_ι]; exact hUle i
  let s : ∀ i, (U : AlgebraicGeometry.Scheme.{u}) ⟶ W i := fun i =>
    AlgebraicGeometry.IsOpenImmersion.lift (u i) U.ι (hsr i)
  have hs : ∀ i, s i ≫ u i = U.ι := fun i => AlgebraicGeometry.IsOpenImmersion.lift_fac _ _ _
  obtain ⟨gU, hgU⟩ := hlift U (U.ι ≫ g) (fun i => s i ≫ e i) fun i => by
    rw [Category.assoc, hef i, ← Category.assoc, hs i]
  have hgUf : gU ≫ fP = U.ι ≫ g := by
    obtain ⟨i⟩ := hne
    rw [← hp i, ← Category.assoc, hgU i, Category.assoc, hef i, ← Category.assoc, hs i]
  -- steps 4–9: the geometric assembly (`ChowLemmaNoetherianAffineBase_Assembly.lean`)
  let D : AlgebraicGeometry.ChowSetup g :=
    { ι := ι, W := W, u := u, hu := hu, hcover := hcover, Zc := Zc, e := e, he := he, f := f, hf := hf,
      hef := hef, P := P, fP := fP, hP := hP, p := p, hp := hp, U := U, hUne := hUne, hUc := hUc, s := s,
      hs := hs, gU := gU, hgU := hgU, hgUf := hgUf }
  exact D.exists_projective_birational

end
