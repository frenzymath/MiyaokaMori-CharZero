import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Glue.ModulesOverlapSectionMap

/-! # A sectionwise equalizer of gluing data restricts to the pieces

Let `X` be a scheme, `{U_i}` a family of opens, `F_i` sheaves of modules on `U_i`, and
`θ_ij : F_i|_{U_i ⊓ U_j} ⟶ F_j|_{U_i ⊓ U_j}` morphisms. Let `M` be a sheaf of modules on `X` with
`p_i : M ⟶ ι_{i*}F_i` such that `(M, p)` is sectionwise an equalizer of `(F, θ)`
(`IsSectionwiseGlue`):
* (compat) for `V ≤ U_i ⊓ U_j`, `p_i(V)` followed by the section map of `θ_ij` on `V`
  (`overlapSectionMap`) equals `p_j(V)`;
* (inj) for every open `V`, a section `s ∈ Γ(M, V)` is determined by the `p_i(V)(s)`;
* (glue) for every open `V`, a family `t_i ∈ Γ(F_i, ι_i⁻¹V)` with
  `θ_ij(t_i|_{V ⊓ U_i ⊓ U_j}) = t_j|_{V ⊓ U_i ⊓ U_j}` comes from some `s ∈ Γ(M, V)`.

Assume moreover the cocycle condition on sections: `θ_ii` is the identity on `V ≤ U_i`, and
`θ_jl ∘ θ_ij = θ_il` for `V ≤ U_i ⊓ U_j ⊓ U_l`. Then (`IsSectionwiseGlue.exists_iso`) the
adjoint `M|_{U_i} ⟶ F_i` of `p_i` under `restrict ⊣ pushforward` is an isomorphism `e_i`, and
`θ_ij ∘ e_i = e_j` on every open `A` of `U_i ⊓ U_j` (as an identity of section maps, aligned via
the restriction maps of `M`).

Proof sketch. For `V ≤ U_i`, `p_i(V)` is bijective: injectivity follows from (compat), (inj) and
the fact that restriction `Γ(F_j, ι_j⁻¹V) → Γ(F_j, ι_j⁻¹(V ⊓ U_i ⊓ U_j))` is an isomorphism
(`isIso_map_of_preimage_eq`); surjectivity by transporting `t ∈ Γ(F_i, ι_i⁻¹V)` to the other
pieces via `θ_ij`, checking the gluing condition with the cocycle identity, and applying (glue).
The section map of the adjoint on `B ⊆ U_i` is `p_i(ι_i ''ᵁ B)` composed with a restriction
isomorphism (`adjunct_app`), so the adjoint is an isomorphism (`Hom.isIso_iff_isIso_app`);
compatibility is (compat) rewritten with `app_eq_overlapSectionMap`.

Reference: Stacks 00AL (the part proving `F|_{U_i} ≅ F_i`).
-/

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

variable {X : AlgebraicGeometry.Scheme.{u}}

theorem glueAux_cat9 {C : Type*} [Category C] {M M' Pi Pi' Pj Pj' : C}
    (m : M ⟶ M') (pi : M ⟶ Pi) (pi' : M' ⟶ Pi') (ri : Pi ⟶ Pi') (pj : M ⟶ Pj) (pj' : M' ⟶ Pj')
    (rj : Pj ⟶ Pj') (o : Pi' ⟶ Pj') (nj : m ≫ pj' = pj ≫ rj) (ni : m ≫ pi' = pi ≫ ri)
    (c : pi' ≫ o = pj') : pj ≫ rj = pi ≫ ri ≫ o := by
  rw [← nj, ← c, reassoc_of% ni]

theorem glueAux_cat10 {C : Type*} [Category C] {A A1 A' B B1 B' : C}
    (r : A ⟶ A1) (o : A1 ⟶ B1) (res : B ⟶ B1) [IsIso res] (f : B ⟶ B') (g : B1 ⟶ B') (r' : A1 ⟶ A')
    (a : A ⟶ A') (o' : A' ⟶ B') (h1 : res ≫ g = f) (nat : r' ≫ o' = o ≫ g) (h2 : r ≫ r' = a) :
    (r ≫ o ≫ inv res) ≫ f = a ≫ o' := by
  subst h1 h2
  simp [nat]

theorem glueAux_map3_endo' {T : Type*} [Preorder T] {C : Type*} [Category C] (F : Tᵒᵖ ⥤ C) {a b c : Tᵒᵖ}
    (f : a ⟶ b) (g : b ⟶ c) (k : c ⟶ a) : F.map f ≫ F.map g ≫ F.map k = 𝟙 _ := by
  rw [← F.map_comp, ← F.map_comp]; exact glueAux_map_endo F _

theorem glueAux_cat11 {C : Type*} [Category C] {M1 M2 M0 P1 P0 Q0 Q2 F1 G1 : C}
    (m1 : M0 ⟶ M1) (pi' : M1 ⟶ P1) (ci : P1 ⟶ F1) (θ : F1 ⟶ G1)
    (m2 : M0 ⟶ M2) (pj' : M2 ⟶ Q2) (cj : Q2 ⟶ G1)
    (pi : M0 ⟶ P0) (n1 : P0 ⟶ P1) (pj : M0 ⟶ Q0) (n2 : Q0 ⟶ Q2) (o : P0 ⟶ Q0) (a : F1 ⟶ P0) (b : Q0 ⟶ G1)
    (ni : m1 ≫ pi' = pi ≫ n1) (nj : m2 ≫ pj' = pj ≫ n2) (c : pi ≫ o = pj)
    (hθ : θ = a ≫ o ≫ b) (h1 : n1 ≫ ci ≫ a = 𝟙 _) (h2 : b = n2 ≫ cj) :
    m1 ≫ (pi' ≫ ci) ≫ θ = m2 ≫ (pj' ≫ cj) := by
  subst hθ h2
  simp only [Category.assoc]
  rw [reassoc_of% ni, reassoc_of% nj, reassoc_of% h1, ← c]
  simp

theorem adjunct_app {Y : AlgebraicGeometry.Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f] {M : X.Modules}
    {F : Y.Modules} (p : M ⟶ (pushforward f).obj F) (B : Y.Opens) :
    (((restrictAdjunction f).homEquiv M F).symm p).app B =
      p.app (f ''ᵁ B) ≫ F.presheaf.map (eqToHom (f.preimage_image_eq B).symm).op := by
  rw [Adjunction.homEquiv_counit]
  rfl

variable {ι : Type u} (U : ι → X.Opens) (F : ∀ i, (U i).toScheme.Modules)
  (θ : ∀ i j, (F i).restrict (X.homOfLE (inf_le_left : U i ⊓ U j ≤ U i)) ⟶
    (F j).restrict (X.homOfLE (inf_le_right : U i ⊓ U j ≤ U j)))

/-- `(M, p)` is sectionwise an equalizer of the gluing data `(F, θ)`. -/
structure IsSectionwiseGlue (M : X.Modules) (p : ∀ i, M ⟶ (pushforward (U i).ι).obj (F i)) : Prop where
  compat : ∀ i j (V : X.Opens) (hV : V ≤ U i ⊓ U j),
    (p i).app V ≫ overlapSectionMap inf_le_left inf_le_right (θ i j) V hV = (p j).app V
  inj : ∀ (V : X.Opens) (s s' : Γ(M, V)), (∀ i, (p i).app V s = (p i).app V s') → s = s'
  glue : ∀ (V : X.Opens) (t : ∀ i, Γ(F i, (U i).ι ⁻¹ᵁ V)),
    (∀ i j, overlapSectionMap inf_le_left inf_le_right (θ i j) (V ⊓ (U i ⊓ U j)) inf_le_right
        ((F i).presheaf.map (homOfLE ((U i).ι.preimage_mono (inf_le_left : V ⊓ (U i ⊓ U j) ≤ V))).op (t i)) =
      (F j).presheaf.map (homOfLE ((U j).ι.preimage_mono (inf_le_left : V ⊓ (U i ⊓ U j) ≤ V))).op (t j)) →
    ∃ s : Γ(M, V), ∀ i, (p i).app V s = t i

variable {U F θ} {M : X.Modules} {p : ∀ i, M ⟶ (pushforward (U i).ι).obj (F i)}

theorem IsSectionwiseGlue.compat_restrict (hc : IsSectionwiseGlue U F θ M p) (i j : ι) (V V' : X.Opens)
    (hV' : V' ≤ V) (h : V' ≤ U i ⊓ U j) :
    (p j).app V ≫ (F j).presheaf.map (homOfLE ((U j).ι.preimage_mono hV')).op =
      (p i).app V ≫ (F i).presheaf.map (homOfLE ((U i).ι.preimage_mono hV')).op ≫
        overlapSectionMap inf_le_left inf_le_right (θ i j) V' h := by
  have ni := (p i).mapPresheaf.naturality (homOfLE hV').op
  have nj := (p j).mapPresheaf.naturality (homOfLE hV').op
  simp only [mapPresheaf_app] at ni nj
  have c := hc.compat i j V' h
  exact glueAux_cat9 _ _ _ _ _ _ _ _ nj ni c

/-- For `V ≤ U_i` the section map of `p_i` on `V` is bijective. -/
theorem IsSectionwiseGlue.bijective_app (hc : IsSectionwiseGlue U F θ M p)
    (hrefl : ∀ i (V : X.Opens) (hV : V ≤ U i ⊓ U i),
      overlapSectionMap inf_le_left inf_le_right (θ i i) V hV = 𝟙 _)
    (hcocycle : ∀ i j l (V : X.Opens) (hV : V ≤ U i ⊓ U j ⊓ U l),
      overlapSectionMap inf_le_left inf_le_right (θ i j) V (hV.trans inf_le_left) ≫
        overlapSectionMap inf_le_left inf_le_right (θ j l) V
          (hV.trans (inf_le_inf_right _ inf_le_right)) =
      overlapSectionMap inf_le_left inf_le_right (θ i l) V (hV.trans (inf_le_inf_right _ inf_le_left)))
    (i : ι) (V : X.Opens) (hV : V ≤ U i) : Function.Bijective ((p i).app V) := by
  -- the restriction `Γ(F_j, ι_j⁻¹V) ⟶ Γ(F_j, ι_j⁻¹(V ⊓ (U_i ⊓ U_j)))` is an isomorphism
  have hpre : ∀ j, (U j).ι ⁻¹ᵁ (V ⊓ (U i ⊓ U j)) = (U j).ι ⁻¹ᵁ V := by
    intro j
    ext x
    change (U j).ι x ∈ V ⊓ (U i ⊓ U j) ↔ (U j).ι x ∈ V
    exact ⟨fun h => h.1, fun h => ⟨h, hV h, x.2⟩⟩
  let res : ∀ j, Γ(F j, (U j).ι ⁻¹ᵁ V) ⟶ Γ(F j, (U j).ι ⁻¹ᵁ (V ⊓ (U i ⊓ U j))) := fun j =>
    (F j).presheaf.map (homOfLE ((U j).ι.preimage_mono (inf_le_left : V ⊓ (U i ⊓ U j) ≤ V))).op
  let ri : ∀ j, Γ(F i, (U i).ι ⁻¹ᵁ V) ⟶ Γ(F i, (U i).ι ⁻¹ᵁ (V ⊓ (U i ⊓ U j))) := fun j =>
    (F i).presheaf.map (homOfLE ((U i).ι.preimage_mono (inf_le_left : V ⊓ (U i ⊓ U j) ≤ V))).op
  have hres : ∀ j, IsIso (res j) := fun j => isIso_map_of_preimage_eq (F j) (hpre j) _
  have hresinj : ∀ j, Function.Injective (res j) := fun j =>
    ((ConcreteCategory.isIso_iff_bijective (res j)).mp (hres j)).1
  constructor
  · intro s s' h
    refine hc.inj V s s' (fun j => hresinj j ?_)
    have star := hc.compat_restrict i j V (V ⊓ (U i ⊓ U j)) inf_le_left inf_le_right
    have e1 := ConcreteCategory.congr_hom star s
    have e2 := ConcreteCategory.congr_hom star s'
    exact e1.trans ((congrArg (fun y => (ri j ≫ overlapSectionMap inf_le_left inf_le_right (θ i j)
      (V ⊓ (U i ⊓ U j)) inf_le_right) y) h).trans e2.symm)
  · intro t
    let T : ∀ j, Γ(F i, (U i).ι ⁻¹ᵁ V) ⟶ Γ(F j, (U j).ι ⁻¹ᵁ V) := fun j =>
      ri j ≫ overlapSectionMap inf_le_left inf_le_right (θ i j) (V ⊓ (U i ⊓ U j)) inf_le_right ≫
        inv (res j)
    have T1 : ∀ j (V' : X.Opens) (hV' : V' ≤ V) (h : V' ≤ U i ⊓ U j),
        T j ≫ (F j).presheaf.map (homOfLE ((U j).ι.preimage_mono hV')).op =
          (F i).presheaf.map (homOfLE ((U i).ι.preimage_mono hV')).op ≫
            overlapSectionMap inf_le_left inf_le_right (θ i j) V' h := by
      intro j V' hV' h
      have hle : V' ≤ V ⊓ (U i ⊓ U j) := le_inf hV' h
      exact glueAux_cat10 _ _ _ _ _ _ _ _ (glueAux_map2 (F j).presheaf _ _ _)
        (overlapSectionMap_naturality inf_le_left inf_le_right (θ i j) _ V' inf_le_right hle)
        (glueAux_map2 (F i).presheaf _ _ _)
    have Ti : T i = 𝟙 _ := by
      rw [← cancel_mono (res i)]
      simp only [T, Category.assoc, IsIso.inv_hom_id, Category.comp_id, Category.id_comp, hrefl]
      rfl
    have hglue : ∀ j l, T j ≫
        (F j).presheaf.map (homOfLE ((U j).ι.preimage_mono (inf_le_left : V ⊓ (U j ⊓ U l) ≤ V))).op ≫
          overlapSectionMap inf_le_left inf_le_right (θ j l) (V ⊓ (U j ⊓ U l)) inf_le_right =
        T l ≫
          (F l).presheaf.map (homOfLE ((U l).ι.preimage_mono (inf_le_left : V ⊓ (U j ⊓ U l) ≤ V))).op := by
      intro j l
      have hijl : V ⊓ (U j ⊓ U l) ≤ U i ⊓ U j ⊓ U l :=
        le_inf (le_inf (inf_le_left.trans hV) (inf_le_right.trans inf_le_left))
          (inf_le_right.trans inf_le_right)
      rw [← Category.assoc, T1 j _ inf_le_left (hijl.trans inf_le_left), Category.assoc,
        hcocycle i j l _ hijl, ← T1 l _ inf_le_left]
    obtain ⟨s, hs⟩ := hc.glue V (fun j => T j t) (fun j l => ConcreteCategory.congr_hom (hglue j l) t)
    refine ⟨s, ?_⟩
    rw [hs i, Ti]
    rfl

theorem IsSectionwiseGlue.isIso_adjunct (hc : IsSectionwiseGlue U F θ M p)
    (hrefl : ∀ i (V : X.Opens) (hV : V ≤ U i ⊓ U i),
      overlapSectionMap inf_le_left inf_le_right (θ i i) V hV = 𝟙 _)
    (hcocycle : ∀ i j l (V : X.Opens) (hV : V ≤ U i ⊓ U j ⊓ U l),
      overlapSectionMap inf_le_left inf_le_right (θ i j) V (hV.trans inf_le_left) ≫
        overlapSectionMap inf_le_left inf_le_right (θ j l) V
          (hV.trans (inf_le_inf_right _ inf_le_right)) =
      overlapSectionMap inf_le_left inf_le_right (θ i l) V (hV.trans (inf_le_inf_right _ inf_le_left)))
    (i : ι) : IsIso (((restrictAdjunction (U i).ι).homEquiv M (F i)).symm (p i)) := by
  rw [Hom.isIso_iff_isIso_app]
  intro B
  rw [adjunct_app]
  have hB : (U i).ι ''ᵁ B ≤ U i := by
    conv_rhs => rw [← AlgebraicGeometry.Scheme.Opens.opensRange_ι (U i)]
    exact AlgebraicGeometry.Scheme.Hom.image_le_opensRange _ _
  have : IsIso ((p i).app ((U i).ι ''ᵁ B)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (hc.bijective_app hrefl hcocycle i _ hB)
  let a : Γ(M, (U i).ι ''ᵁ B) ⟶ Γ(F i, (U i).ι ⁻¹ᵁ (U i).ι ''ᵁ B) := (p i).app ((U i).ι ''ᵁ B)
  have ha : IsIso a := this
  change IsIso (a ≫ (F i).presheaf.map (eqToHom ((U i).ι.preimage_image_eq B).symm).op)
  infer_instance

theorem IsSectionwiseGlue.adjunct_compat (hc : IsSectionwiseGlue U F θ M p) (i j : ι)
    (A : (U i ⊓ U j).toScheme.Opens) :
    M.presheaf.map (eqToHom (image_homOfLE_image (inf_le_left : U i ⊓ U j ≤ U i) A)).op ≫
      (((restrictAdjunction (U i).ι).homEquiv M (F i)).symm (p i)).app
        (X.homOfLE (inf_le_left : U i ⊓ U j ≤ U i) ''ᵁ A) ≫ (θ i j).app A =
    M.presheaf.map (eqToHom (image_homOfLE_image (inf_le_right : U i ⊓ U j ≤ U j) A)).op ≫
      (((restrictAdjunction (U j).ι).homEquiv M (F j)).symm (p j)).app
        (X.homOfLE (inf_le_right : U i ⊓ U j ≤ U j) ''ᵁ A) := by
  rw [adjunct_app, adjunct_app]
  have e1 := image_homOfLE_image (inf_le_left : U i ⊓ U j ≤ U i) A
  have e2 := image_homOfLE_image (inf_le_right : U i ⊓ U j ≤ U j) A
  let pi0 : Γ(M, (U i ⊓ U j).ι ''ᵁ A) ⟶ Γ(F i, (U i).ι ⁻¹ᵁ (U i ⊓ U j).ι ''ᵁ A) := (p i).app _
  let pj0 : Γ(M, (U i ⊓ U j).ι ''ᵁ A) ⟶ Γ(F j, (U j).ι ⁻¹ᵁ (U i ⊓ U j).ι ''ᵁ A) := (p j).app _
  let pi1 : Γ(M, (U i).ι ''ᵁ X.homOfLE (inf_le_left : U i ⊓ U j ≤ U i) ''ᵁ A) ⟶
    Γ(F i, (U i).ι ⁻¹ᵁ (U i).ι ''ᵁ X.homOfLE (inf_le_left : U i ⊓ U j ≤ U i) ''ᵁ A) := (p i).app _
  let pj1 : Γ(M, (U j).ι ''ᵁ X.homOfLE (inf_le_right : U i ⊓ U j ≤ U j) ''ᵁ A) ⟶
    Γ(F j, (U j).ι ⁻¹ᵁ (U j).ι ''ᵁ X.homOfLE (inf_le_right : U i ⊓ U j ≤ U j) ''ᵁ A) := (p j).app _
  have ni : M.presheaf.map (eqToHom e1).op ≫ pi1 =
      pi0 ≫ (F i).presheaf.map ((Opens.map (U i).ι.base).map (eqToHom e1)).op :=
    (p i).mapPresheaf.naturality (eqToHom e1).op
  have nj : M.presheaf.map (eqToHom e2).op ≫ pj1 =
      pj0 ≫ (F j).presheaf.map ((Opens.map (U j).ι.base).map (eqToHom e2)).op :=
    (p j).mapPresheaf.naturality (eqToHom e2).op
  have c : pi0 ≫ overlapSectionMap inf_le_left inf_le_right (θ i j) ((U i ⊓ U j).ι ''ᵁ A)
      (le_of_image_eq A rfl) = pj0 := hc.compat i j ((U i ⊓ U j).ι ''ᵁ A) (le_of_image_eq A rfl)
  have hθ := app_eq_overlapSectionMap inf_le_left inf_le_right (θ i j) A rfl
  exact glueAux_cat11 _ pi1 _ _ _ pj1 _ pi0 _ pj0 _ _ _ _ ni nj c hθ
    (glueAux_map3_endo' (F i).presheaf _ _ _) (glueAux_map2 (F j).presheaf _ _ _).symm

/-- Main result: a sectionwise equalizer `(M, p)` gives isomorphisms `M|_{U_i} ≅ F_i` (the adjoints
of the `p_i`) compatible with `θ` (on sections). -/
theorem IsSectionwiseGlue.exists_iso (hc : IsSectionwiseGlue U F θ M p)
    (hrefl : ∀ i (V : X.Opens) (hV : V ≤ U i ⊓ U i),
      overlapSectionMap inf_le_left inf_le_right (θ i i) V hV = 𝟙 _)
    (hcocycle : ∀ i j l (V : X.Opens) (hV : V ≤ U i ⊓ U j ⊓ U l),
      overlapSectionMap inf_le_left inf_le_right (θ i j) V (hV.trans inf_le_left) ≫
        overlapSectionMap inf_le_left inf_le_right (θ j l) V
          (hV.trans (inf_le_inf_right _ inf_le_right)) =
      overlapSectionMap inf_le_left inf_le_right (θ i l) V (hV.trans (inf_le_inf_right _ inf_le_left))) :
    ∃ e : ∀ i, M.restrict (U i).ι ≅ F i, ∀ i j (A : (U i ⊓ U j).toScheme.Opens),
      M.presheaf.map (eqToHom (image_homOfLE_image (inf_le_left : U i ⊓ U j ≤ U i) A)).op ≫
        (e i).hom.app (X.homOfLE (inf_le_left : U i ⊓ U j ≤ U i) ''ᵁ A) ≫ (θ i j).app A =
      M.presheaf.map (eqToHom (image_homOfLE_image (inf_le_right : U i ⊓ U j ≤ U j) A)).op ≫
        (e j).hom.app (X.homOfLE (inf_le_right : U i ⊓ U j ≤ U j) ''ᵁ A) :=
  ⟨fun i => @asIso _ _ _ _ (((restrictAdjunction (U i).ι).homEquiv M (F i)).symm (p i))
      (hc.isIso_adjunct hrefl hcocycle i),
    fun i j A => hc.adjunct_compat i j A⟩

end

end AlgebraicGeometry.Scheme.Modules
