import MiyaokaMori.AlgebraicGeometry.Proj.Twist.RelativeProjTwistPiApp_LimitSections

/-! # The abstract gluing argument for locally glued diagrams (Stacks 01LI on sections)

Setting (`LocallyGluedDiagram`). `Y` a scheme, `J` a preorder, `D : Jᵒᵖ ⥤ Y.Modules` a diagram of `𝒪_Y`-modules
with transition maps `θ_h := D.map (homOfLE h).op : D V ⟶ D W` for `h : W ≤ V`, and a family of opens
`R : J → Y.Opens` ("the image of the `V`-th chart") such that
* (`mono`) `R` is monotone;
* (`supp`) `D V` is supported on `R V`: the restriction `Γ(Ω, D V) → Γ(Ω ⊓ R V, D V)` is bijective for every `Ω`;
* (`loc`) `θ_h` is bijective on sections over every open `Ω ≤ R W` (`h : W ≤ V`);
* (`cover`) two charts meet in charts: `x ∈ R U ⊓ R V` lies in some `R W` with `W ≤ U`, `W ≤ V`.

In the application `D V = (ι_V)_* O_V(m)`, `R V = im ι_V` (the charts of the relative Proj), `θ_h` the transition
map `twistTransition`; the three hypotheses are `RelativeProjTwistLocalIso` (`loc`), the definition of
the pushforward (`supp`) and `RelativeProjChartCover` (`cover`).

Statement (`LocallyGluedDiagram.bijective_π_app`): for every limit cone `c` of `D`, every `U : J` and every
open `Ω ≤ R U`, the section map `(c.π.app (op U)).app Ω : Γ(Ω, c.pt) → Γ(Ω, D U)` is bijective.

Proof. Write `π_V := (c.π.app (op V)).app Ω` and `res` for restriction maps. By part (i)
(`limitCone_sections_ext`, `limitCone_sections_exists`) the sections `Γ(Ω, c.pt)` are the compatible families
`(x_V)_V`, `x_V ∈ Γ(Ω, D V)`, `θ_h.app Ω x_V = x_W`.
0. Locality (`eq_of_transition_eq`): let `Ω₀` be open, `V : J`, `a, b ∈ Γ(Ω₀, D V)`, and `P` a set of indices
   `W ≤ V` such that the `R W` (`W ∈ P`) cover `Ω₀ ⊓ R V`. If `θ_{W≤V}.app (Ω₀ ⊓ R W) (res a) = θ_{W≤V}.app (Ω₀ ⊓ R W) (res b)`
   for all `W ∈ P`, then `a = b`. Indeed by `supp` it suffices that `res a = res b` in `Γ(Ω₀ ⊓ R V, D V)`; the opens
   `Ω₀ ⊓ R W` (`W ∈ P`) cover `Ω₀ ⊓ R V`, so by the locality axiom of the sheaf `D V`
   (`TopCat.Sheaf.eq_of_locally_eq'`) it suffices that `res a = res b` on each `Ω₀ ⊓ R W`, and there `θ_{W≤V}.app`
   is injective (`loc`, as `Ω₀ ⊓ R W ≤ R W`).
1. Injectivity of `π_U`. Let `π_U s = π_U t`. For each `V`, apply step 0 with `Ω₀ = Ω`, `a = π_V s`, `b = π_V t`,
   `P = {W : W ≤ U ∧ W ≤ V}` (a cover of `Ω ⊓ R V ⊆ R U ⊓ R V` by `cover`): for `W ∈ P`,
   `θ_{W≤V}.app (res (π_V s)) = res (θ_{W≤V}.app (π_V s)) = res (π_W s) = res (θ_{W≤U}.app (π_U s))`, and likewise
   for `t`; these agree. So `π_V s = π_V t` for all `V`, hence `s = t` (part (i)).
2. Surjectivity of `π_U`. Let `t ∈ Γ(Ω, D U)`. For `W ≤ U` and `Ω' ≤ Ω` put `τ_W(Ω') := θ_{W≤U}.app Ω' (res t)`;
   then `θ_{W''≤W}.app Ω'' (res τ_W(Ω')) = τ_{W''}(Ω'')` for `W'' ≤ W`, `Ω'' ≤ Ω'` (functoriality of `D` and
   naturality of `Hom.app`).
   For each `V`, define `s_V ∈ Γ(Ω, D V)` as follows. For `W ∈ I_V := {W : W ≤ U ∧ W ≤ V}` let
   `sf_W ∈ Γ(Ω ⊓ R W, D V)` be the unique section with `θ_{W≤V}.app (Ω ⊓ R W) sf_W = τ_W(Ω ⊓ R W)` (`loc`).
   Key identity (`transition_res_sf`): for `W'' ≤ W`, `W ∈ I_V`, `Ω'' ≤ Ω ⊓ R W`:
   `θ_{W''≤V}.app Ω'' (res sf_W) = θ_{W''≤W}.app Ω'' (θ_{W≤V}.app Ω'' (res sf_W)) = θ_{W''≤W}.app Ω'' (res τ_W(Ω ⊓ R W)) = τ_{W''}(Ω'')`.
   The `sf_W` are compatible on overlaps `(Ω ⊓ R W) ⊓ (Ω ⊓ R W')`: apply step 0 with `P = {W'' : W'' ≤ W ∧ W'' ≤ W'}`
   (covers the overlap intersected with `R V` by `cover`), and on `Ω'' := overlap ⊓ R W''` both sides are
   `τ_{W''}(Ω'')` by the key identity. So they glue (`TopCat.Sheaf.existsUnique_gluing'`) to a section of
   `D V` over `Ω ⊓ R V` (the `Ω ⊓ R W`, `W ∈ I_V`, cover `Ω ⊓ R V` by `cover`), which by `supp` is `res s_V` for a
   unique `s_V ∈ Γ(Ω, D V)`; thus `res s_V = sf_W` on each `Ω ⊓ R W`, `W ∈ I_V` (`exists_glued`).
   Consequently (`transition_res_s`): for `W ≤ U`, `W ≤ V`, `Ω'' ≤ Ω ⊓ R W`: `θ_{W≤V}.app Ω'' (res s_V) = τ_W(Ω'')`.
   Compatibility of `(s_V)`: for `V' ≤ V` apply step 0 (`Ω₀ = Ω`, `a = θ_{V'≤V}.app Ω s_V`, `b = s_{V'}`,
   `P = I_{V'}`): on `Ω ⊓ R W`, `θ_{W≤V'}.app (res a) = θ_{W≤V}.app (res s_V) = τ_W(Ω ⊓ R W) = θ_{W≤V'}.app (res s_{V'})`.
   By part (i) there is `s ∈ Γ(Ω, c.pt)` with `π_V s = s_V` for all `V`. Finally `s_U = t`: step 0 with
   `P = {W : W ≤ U}` (which covers `Ω ⊓ R U` since `Ω ≤ R U`): `θ_{W≤U}.app (res s_U) = τ_W(Ω ⊓ R W) = θ_{W≤U}.app (res t)`.
   Hence `π_U s = t`.

Source: Stacks 01LI (proof), 01NP/01NR; Lemma 2.2 of the paper. This is the abstract part of
`RelativeProjTwistPiApp` (steps 3–6 of its proof, abstracted from the twist). Edge cases:
`Ω = ∅` (all section groups zero); `R U = ∅` forces `Ω = ∅`; `J` with one element (`cover` is trivial with `W = U`).
-/

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {Y : Scheme.{u}}

/-- Naturality of `Hom.app` with respect to restriction of sections. -/
theorem Hom.app_map_apply {M N : Y.Modules} (φ : M ⟶ N) {Ω' Ω : Y.Opens} (i : Ω' ⟶ Ω) (x : Γ(M, Ω)) :
    φ.app Ω' (M.presheaf.map i.op x) = N.presheaf.map i.op (φ.app Ω x) :=
  ConcreteCategory.congr_hom (φ.mapPresheaf.naturality i.op) x

/-- Two restriction maps between the same opens agree (`Y.Opens` is thin). -/
theorem presheaf_map_congr (M : Y.Modules) {A C : Y.Opens} (i j : A ⟶ C) (x : Γ(M, C)) :
    M.presheaf.map i.op x = M.presheaf.map j.op x := by
  rw [Subsingleton.elim i j]

/-- Restricting twice is restricting once. -/
theorem presheaf_map_map (M : Y.Modules) {A B C : Y.Opens} (i : A ⟶ B) (j : B ⟶ C) (k : A ⟶ C)
    (x : Γ(M, C)) : M.presheaf.map i.op (M.presheaf.map j.op x) = M.presheaf.map k.op x := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, Subsingleton.elim (i ≫ j) k]

/-- Composition of morphisms of `𝒪_Y`-modules on sections. -/
theorem Hom.comp_app_apply_sections {M N K : Y.Modules} (φ : M ⟶ N) (ψ : N ⟶ K) (Ω : Y.Opens) (x : Γ(M, Ω)) :
    (φ ≫ ψ).app Ω x = ψ.app Ω (φ.app Ω x) := rfl

variable {J : Type u} [Preorder J]

/-- Composition of transition maps of a diagram indexed by `Jᵒᵖ`, on sections. -/
theorem map_homOfLE_op_app_app (D : Jᵒᵖ ⥤ Y.Modules) {W'' W V : J} (h'' : W'' ≤ W) (h : W ≤ V)
    (Ω : Y.Opens) (x : Γ(D.obj (op V), Ω)) :
    (D.map (homOfLE h'').op).app Ω ((D.map (homOfLE h).op).app Ω x) =
      (D.map (homOfLE (h''.trans h)).op).app Ω x := by
  rw [← Hom.comp_app_apply_sections, ← D.map_comp, ← op_comp, homOfLE_comp]

/-- The hypotheses of the gluing argument of Stacks 01LI (see the module docstring): `R V` is the support
of `D V`, the transition maps are bijective on sections over opens inside `R W`, and two charts meet in charts. -/
structure LocallyGluedDiagram (D : Jᵒᵖ ⥤ Y.Modules) (R : J → Y.Opens) : Prop where
  mono : Monotone R
  supp : ∀ (V : J) (Ω : Y.Opens),
    Function.Bijective ((D.obj (op V)).presheaf.map (homOfLE (inf_le_left : Ω ⊓ R V ≤ Ω)).op).hom
  loc : ∀ {W V : J} (h : W ≤ V) (Ω : Y.Opens), Ω ≤ R W →
    Function.Bijective ((D.map (homOfLE h).op).app Ω).hom
  cover : ∀ (U V : J) (x : Y), x ∈ R U → x ∈ R V → ∃ W, W ≤ U ∧ W ≤ V ∧ x ∈ R W

namespace LocallyGluedDiagram

variable {D : Jᵒᵖ ⥤ Y.Modules} {R : J → Y.Opens} (hD : LocallyGluedDiagram D R)

/-- `D V` as an abelian sheaf on `Y`. -/
def sheaf (D : Jᵒᵖ ⥤ Y.Modules) (V : J) : TopCat.Sheaf Ab Y :=
  ⟨(D.obj (op V)).presheaf, (D.obj (op V)).isSheaf⟩

include hD in
/-- Step 0 (locality): two sections `a, b` of `D V` over `Ω₀` agree as soon as, for a family `P` of indices
`W ≤ V` whose `R W` cover `Ω₀ ⊓ R V`, the transition maps `θ_{W≤V}` take the same value on their restrictions
to `Ω₀ ⊓ R W`. -/
theorem eq_of_transition_eq {V : J} (Ω₀ : Y.Opens) (P : J → Prop) (hPV : ∀ W, P W → W ≤ V)
    (hcov : ∀ x : Y, x ∈ Ω₀ ⊓ R V → ∃ W, P W ∧ x ∈ R W) {a b : Γ(D.obj (op V), Ω₀)}
    (h : ∀ W (hW : P W),
      (D.map (homOfLE (hPV W hW)).op).app (Ω₀ ⊓ R W)
          ((D.obj (op V)).presheaf.map (homOfLE (inf_le_left : Ω₀ ⊓ R W ≤ Ω₀)).op a) =
        (D.map (homOfLE (hPV W hW)).op).app (Ω₀ ⊓ R W)
          ((D.obj (op V)).presheaf.map (homOfLE (inf_le_left : Ω₀ ⊓ R W ≤ Ω₀)).op b)) :
    a = b := by
  apply (hD.supp V Ω₀).injective
  let Us : {W : J // P W} → Y.Opens := fun W => Ω₀ ⊓ R W.1
  have iUV : ∀ W : {W : J // P W}, Us W ⟶ Ω₀ ⊓ R V :=
    fun W => homOfLE (inf_le_inf_left _ (hD.mono (hPV W.1 W.2)))
  have hcover : Ω₀ ⊓ R V ≤ iSup Us := by
    intro x hx
    obtain ⟨W, hW, hxW⟩ := hcov x hx
    exact Opens.mem_iSup.mpr ⟨⟨W, hW⟩, ⟨hx.1, hxW⟩⟩
  apply (sheaf D V).eq_of_locally_eq' Us (Ω₀ ⊓ R V) iUV hcover
  intro W
  apply (hD.loc (hPV W.1 W.2) (Us W) inf_le_right).injective
  change (D.map (homOfLE (hPV W.1 W.2)).op).app (Us W)
      ((D.obj (op V)).presheaf.map (iUV W).op
        ((D.obj (op V)).presheaf.map (homOfLE inf_le_left).op a)) =
    (D.map (homOfLE (hPV W.1 W.2)).op).app (Us W)
      ((D.obj (op V)).presheaf.map (iUV W).op
        ((D.obj (op V)).presheaf.map (homOfLE inf_le_left).op b))
  rw [presheaf_map_map _ _ _ (homOfLE inf_le_left), presheaf_map_map _ _ _ (homOfLE inf_le_left)]
  exact h W.1 W.2

section Cone

variable {c : Cone D} (hc : IsLimit c)

/-- Naturality of the cone maps with respect to restriction (`Hom.app_map_apply` with `c.pt` spelled out). -/
theorem cone_π_app_map_apply (c : Cone D) (V : Jᵒᵖ) {Ω' Ω : Y.Opens} (i : Ω' ⟶ Ω) (s : Γ(c.pt, Ω)) :
    (c.π.app V).app Ω' (c.pt.presheaf.map i.op s) = (D.obj V).presheaf.map i.op ((c.π.app V).app Ω s) :=
  Hom.app_map_apply (c.π.app V) i s

/-- Compatibility of the cone maps on sections: `π_W = θ_{W≤V} ∘ π_V`. -/
theorem cone_π_app_apply (c : Cone D) {W V : J} (h : W ≤ V) (Ω : Y.Opens) (s : Γ(c.pt, Ω)) :
    (c.π.app (op W)).app Ω s = (D.map (homOfLE h).op).app Ω ((c.π.app (op V)).app Ω s) := by
  rw [← Hom.comp_app_apply_sections, c.w]

include hD hc in
/-- Injectivity of `π_U` on sections over `Ω ≤ R U` (step 1). -/
theorem injective_π_app (U : J) (Ω : Y.Opens) (hΩ : Ω ≤ R U) :
    Function.Injective ((c.π.app (op U)).app Ω).hom := by
  intro s t hst
  have hst' : (c.π.app (op U)).app Ω s = (c.π.app (op U)).app Ω t := hst
  apply limitCone_sections_ext hc Ω
  intro j
  induction j using Opposite.rec with
  | op V =>
  apply hD.eq_of_transition_eq Ω (fun W => W ≤ U ∧ W ≤ V) (fun W hW => hW.2)
    (fun x hx => by
      obtain ⟨W, hWU, hWV, hxW⟩ := hD.cover U V x (hΩ hx.1) hx.2
      exact ⟨W, ⟨hWU, hWV⟩, hxW⟩)
  intro W hW
  rw [← cone_π_app_map_apply c (op V), ← cone_π_app_map_apply c (op V), ← cone_π_app_apply c hW.2,
    ← cone_π_app_apply c hW.2, cone_π_app_apply c hW.1 (Ω ⊓ R W), cone_π_app_apply c hW.1 (Ω ⊓ R W),
    cone_π_app_map_apply c (op U), cone_π_app_map_apply c (op U), hst']

end Cone

section Surjective

variable (U : J) (Ω : Y.Opens) (t : Γ(D.obj (op U), Ω))

/-- `τ_W(Ω') := θ_{W≤U}.app Ω' (t|_{Ω'})` for `W ≤ U`, `Ω' ≤ Ω`. -/
def tau {W : J} (hW : W ≤ U) {Ω' : Y.Opens} (hΩ' : Ω' ≤ Ω) : Γ(D.obj (op W), Ω') :=
  (D.map (homOfLE hW).op).app Ω' ((D.obj (op U)).presheaf.map (homOfLE hΩ').op t)

/-- `θ_{W''≤W}(τ_W(Ω')|_{Ω''}) = τ_{W''}(Ω'')`. -/
theorem transition_res_tau {W'' W : J} (h'' : W'' ≤ W) (hW : W ≤ U) {Ω'' Ω' : Y.Opens} (hΩ'' : Ω'' ≤ Ω')
    (hΩ' : Ω' ≤ Ω) :
    (D.map (homOfLE h'').op).app Ω''
        ((D.obj (op W)).presheaf.map (homOfLE hΩ'').op (tau U Ω t hW hΩ')) =
      tau U Ω t (h''.trans hW) (hΩ''.trans hΩ') := by
  unfold tau
  rw [← Hom.app_map_apply, map_homOfLE_op_app_app,
    presheaf_map_map _ _ _ (homOfLE (hΩ''.trans hΩ'))]

include hD in
/-- The local section `sf_W ∈ Γ(Ω ⊓ R W, D V)` (`W ≤ U`, `W ≤ V`): the unique preimage of `τ_W(Ω ⊓ R W)` under the
bijection `θ_{W≤V}.app (Ω ⊓ R W)`. -/
def sf (V : J) {W : J} (hW : W ≤ U ∧ W ≤ V) : Γ(D.obj (op V), Ω ⊓ R W) :=
  (Equiv.ofBijective _ (hD.loc hW.2 (Ω ⊓ R W) inf_le_right)).symm (tau U Ω t hW.1 inf_le_left)

include hD in
theorem transition_sf (V : J) {W : J} (hW : W ≤ U ∧ W ≤ V) :
    (D.map (homOfLE hW.2).op).app (Ω ⊓ R W) (hD.sf U Ω t V hW) = tau U Ω t hW.1 inf_le_left :=
  Equiv.ofBijective_apply_symm_apply _ (hD.loc hW.2 (Ω ⊓ R W) inf_le_right) _

include hD in
/-- Key identity: `θ_{W''≤V}(sf_W|_{Ω''}) = τ_{W''}(Ω'')` for `W'' ≤ W`, `Ω'' ≤ Ω ⊓ R W`. -/
theorem transition_res_sf (V : J) {W'' W : J} (h'' : W'' ≤ W) (hW : W ≤ U ∧ W ≤ V) {Ω'' : Y.Opens}
    (hΩ'' : Ω'' ≤ Ω ⊓ R W) :
    (D.map (homOfLE (h''.trans hW.2)).op).app Ω''
        ((D.obj (op V)).presheaf.map (homOfLE hΩ'').op (hD.sf U Ω t V hW)) =
      tau U Ω t (h''.trans hW.1) (hΩ''.trans inf_le_left) := by
  rw [← map_homOfLE_op_app_app D h'' hW.2, Hom.app_map_apply, hD.transition_sf U Ω t V hW,
    transition_res_tau]

include hD in
/-- Step 2, gluing: for every `V` there is `s_V ∈ Γ(Ω, D V)` restricting to `sf_W` on every `Ω ⊓ R W`
(`W ≤ U`, `W ≤ V`). -/
theorem exists_glued (hΩ : Ω ≤ R U) (V : J) :
    ∃ s : Γ(D.obj (op V), Ω), ∀ (W : J) (hW : W ≤ U ∧ W ≤ V),
      (D.obj (op V)).presheaf.map (homOfLE (inf_le_left : Ω ⊓ R W ≤ Ω)).op s = hD.sf U Ω t V hW := by
  let I := {W : J // W ≤ U ∧ W ≤ V}
  let Us : I → Y.Opens := fun W => Ω ⊓ R W.1
  have iUV : ∀ W : I, Us W ⟶ Ω ⊓ R V := fun W => homOfLE (inf_le_inf_left _ (hD.mono W.2.2))
  have hcover : Ω ⊓ R V ≤ iSup Us := by
    intro x hx
    obtain ⟨W, hWU, hWV, hxW⟩ := hD.cover U V x (hΩ hx.1) hx.2
    exact Opens.mem_iSup.mpr ⟨⟨W, hWU, hWV⟩, ⟨hx.1, hxW⟩⟩
  let sf' : ∀ W : I, ((sheaf D V).1.obj (op (Us W))) := fun W => hD.sf U Ω t V W.2
  have compat : TopCat.Presheaf.IsCompatible (sheaf D V).1 Us sf' := by
    intro i j
    apply hD.eq_of_transition_eq (Us i ⊓ Us j) (fun W'' => W'' ≤ i.1 ∧ W'' ≤ j.1)
      (fun W'' h => h.1.trans i.2.2)
      (fun x hx => by
        obtain ⟨W'', h1, h2, hxW⟩ := hD.cover i.1 j.1 x hx.1.1.2 hx.1.2.2
        exact ⟨W'', ⟨h1, h2⟩, hxW⟩)
    intro W'' hW''
    change (D.map (homOfLE _).op).app (Us i ⊓ Us j ⊓ R W'')
        ((D.obj (op V)).presheaf.map (homOfLE inf_le_left).op
          ((D.obj (op V)).presheaf.map (Opens.infLELeft (Us i) (Us j)).op (hD.sf U Ω t V i.2))) =
      (D.map (homOfLE _).op).app (Us i ⊓ Us j ⊓ R W'')
        ((D.obj (op V)).presheaf.map (homOfLE inf_le_left).op
          ((D.obj (op V)).presheaf.map (Opens.infLERight (Us i) (Us j)).op (hD.sf U Ω t V j.2)))
    rw [presheaf_map_map _ _ _ (homOfLE (inf_le_left.trans inf_le_left)),
      presheaf_map_map _ _ _ (homOfLE (inf_le_left.trans inf_le_right)),
      hD.transition_res_sf U Ω t V hW''.1 i.2, hD.transition_res_sf U Ω t V hW''.2 j.2]
  obtain ⟨s', hs', -⟩ := (sheaf D V).existsUnique_gluing' Us (Ω ⊓ R V) iUV hcover sf' compat
  refine ⟨(Equiv.ofBijective _ (hD.supp V Ω)).symm s', fun W hW => ?_⟩
  have e : (D.obj (op V)).presheaf.map (homOfLE (inf_le_left : Ω ⊓ R V ≤ Ω)).op
      ((Equiv.ofBijective _ (hD.supp V Ω)).symm s') = s' :=
    Equiv.ofBijective_apply_symm_apply _ (hD.supp V Ω) s'
  rw [← presheaf_map_map _ (iUV ⟨W, hW⟩) (homOfLE inf_le_left), e]
  exact hs' ⟨W, hW⟩

include hD in
/-- Surjectivity of `π_U` on sections over `Ω ≤ R U` (step 2). -/
theorem surjective_π_app {c : Cone D} (hc : IsLimit c) (hΩ : Ω ≤ R U) :
    Function.Surjective ((c.π.app (op U)).app Ω).hom := by
  intro t
  choose sV hsV using hD.exists_glued U Ω t hΩ
  -- `θ_{W≤V}(s_V|_{Ω''}) = τ_W(Ω'')` for `W ≤ U`, `W ≤ V`, `Ω'' ≤ Ω ⊓ R W`
  have key : ∀ (V W : J) (hW : W ≤ U ∧ W ≤ V) {Ω'' : Y.Opens} (hΩ'' : Ω'' ≤ Ω ⊓ R W),
      (D.map (homOfLE hW.2).op).app Ω''
          ((D.obj (op V)).presheaf.map (homOfLE (hΩ''.trans inf_le_left)).op (sV V)) =
        tau U Ω t hW.1 (hΩ''.trans inf_le_left) := by
    intro V W hW Ω'' hΩ''
    rw [← presheaf_map_map _ (homOfLE hΩ'') (homOfLE inf_le_left), hsV V W hW]
    exact hD.transition_res_sf U Ω t V le_rfl hW hΩ''
  -- the family `(s_V)` is compatible
  have compat : ∀ {i j : Jᵒᵖ} (f : i ⟶ j), (D.map f).app Ω (sV i.unop) = sV j.unop := by
    intro i j f
    induction i using Opposite.rec with
    | op V =>
    induction j using Opposite.rec with
    | op V' =>
    have hf : V' ≤ V := leOfHom f.unop
    have hf' : f = (homOfLE hf).op := by
      rw [← Quiver.Hom.op_unop f]
      congr 1
    rw [hf']
    apply hD.eq_of_transition_eq Ω (fun W => W ≤ U ∧ W ≤ V') (fun W hW => hW.2)
      (fun x hx => by
        obtain ⟨W, hWU, hWV, hxW⟩ := hD.cover U V' x (hΩ hx.1) hx.2
        exact ⟨W, ⟨hWU, hWV⟩, hxW⟩)
    intro W hW
    rw [← Hom.app_map_apply, map_homOfLE_op_app_app, key V W ⟨hW.1, hW.2.trans hf⟩ le_rfl,
      key V' W hW le_rfl]
  obtain ⟨s, hs⟩ := limitCone_sections_exists hc Ω (fun j => sV j.unop) compat
  refine ⟨s, ?_⟩
  change (c.π.app (op U)).app Ω s = t
  rw [hs (op U)]
  apply hD.eq_of_transition_eq Ω (fun W => W ≤ U) (fun W hW => hW)
    (fun x hx => ⟨U, le_rfl, hx.2⟩)
  intro W hW
  rw [key U W ⟨hW, hW⟩ le_rfl]
  rfl

end Surjective

include hD in
/-- **Stacks 01LI on sections**: the limit projection `π_U` is bijective on sections over every open
`Ω ≤ R U`. -/
theorem bijective_π_app {c : Cone D} (hc : IsLimit c) (U : J) (Ω : Y.Opens) (hΩ : Ω ≤ R U) :
    Function.Bijective ((c.π.app (op U)).app Ω).hom :=
  ⟨hD.injective_π_app hc U Ω hΩ, hD.surjective_π_app U Ω hc hΩ⟩

end LocallyGluedDiagram

end AlgebraicGeometry.Scheme.Modules

end
