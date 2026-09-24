import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModuleSheafStalk
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesInternalHom
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.FinitePresentationLocalData
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModuleSheafificationStalk

/-! # Stalks of the internal Hom (Stacks 01CP)

Stacks 01CP (finite presentation part): if `F` is an `O_X`-module of finite presentation, the
canonical map `Hom(F, G)_x → Hom_{O_{X,x}}(F_x, G_x)`, `(U, φ) ↦ φ_x`, is an isomorphism of
`O_{X,x}`-modules. The statement `stalk_internalHom_iso` gives an isomorphism `e` whose forward map
satisfies `e([U, φ])([V, m]) = [V, φ_V(m)]` on germs, i.e. `e` is the canonical map; the corollary
`stalk_internalHom_nonempty_iso` records the existence of an abstract isomorphism.

Source: Stacks 01CP (`modules-lemma-stalk-internal-hom`).

Structure of the proof. `internalHom F G` is by definition the sheafification of the internal Hom
**presheaf** `internalHomPresheaf F G`, and sheafification is an isomorphism on stalks
(`AlgebraicGeometry.Scheme.Modules.moduleSheafificationStalkEquiv`); this reduces 01CP to a statement about the stalk of
the presheaf (step 1). The canonical map is the concrete `localHomStalkHom F G x`, obtained from two
`colimit.desc`s, with germ formula `localHomStalkHom_germ_germ` (step 2 (a), (b)). Its bijectivity
(`localHomStalkHom_bijective`) follows the second and third paragraphs of Stacks 01CP, with "finite
presentation" unfolded into concrete local data (`exists_isLocalPresentation`, see
`FinitePresentationLocalData`): injectivity from finite type
(`localHomStalkHom_injective_of_isLocalGenerators`, step 2 (c)) and surjectivity from a local
presentation (`localHomStalkHom_surjective_of_isLocalPresentation`, step 2 (d): the universal
property of the cokernel is realized by hand through the relation `SurjRel` and gluing).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace AlgebraicGeometry.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}}

/-! ### Step 1: sheafification does not change stalks -/

/-- **The stalk of the internal Hom is the stalk of the internal Hom presheaf** (Stacks 007Z: a
presheaf and its sheafification have the same stalks).

`internalHom F G` is by definition (`ModulesInternalHom`)
`(PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj (internalHomPresheaf F G)`, i.e.
`AlgebraicGeometry.Scheme.Modules.moduleSheafification X (internalHomPresheaf F G)`; the linear map induced on stalks by
the sheafification unit is bijective (`AlgebraicGeometry.Scheme.Modules.moduleSheafificationStalkMap_bijective`, from
Mathlib's `TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso`). -/
def internalHomPresheafStalkEquiv (F G : X.Modules) (x : X) :
    ↥(TopCat.Presheaf.stalk
        (AlgebraicGeometry.Scheme.Modules.internalHomPresheaf F G).presheaf x)
      ≃ₗ[X.presheaf.stalk x]
      ((AlgebraicGeometry.Scheme.Modules.internalHom F G).stalk x) :=
  AlgebraicGeometry.Scheme.Modules.moduleSheafificationStalkEquiv X
    (AlgebraicGeometry.Scheme.Modules.internalHomPresheaf F G) x

/-- The previous isomorphism sends the presheaf germ `[U, φ]` to the germ `[U, η_U φ]` of the
sheafification (`η` the sheafification unit). -/
theorem internalHomPresheafStalkEquiv_germ (F G : X.Modules) (x : X) (U : X.Opens) (hxU : x ∈ U)
    (φ : AlgebraicGeometry.Scheme.Modules.localHomSubmodule F G U) :
    AlgebraicGeometry.Scheme.Modules.internalHomPresheafStalkEquiv F G x
        (TopCat.Presheaf.germ
          (AlgebraicGeometry.Scheme.Modules.internalHomPresheaf F G).presheaf U x hxU φ) =
      (AlgebraicGeometry.Scheme.Modules.internalHom F G).presheaf.germ U x hxU
        (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
          (AlgebraicGeometry.Scheme.Modules.internalHomPresheaf F G)).app (Opposite.op U) φ) := by
  exact AlgebraicGeometry.Scheme.Modules.moduleSheafificationStalkEquiv_germ X
    (AlgebraicGeometry.Scheme.Modules.internalHomPresheaf F G) x U hxU φ

/-! ### Step 2 (a): the linear map `φ_x` induced on stalks by a local homomorphism (Stacks 01CP, first paragraph) -/

/-- `V ⊓ U` as an object of `Over U`. -/
abbrev infOver (U V : X.Opens) : CategoryTheory.Over U :=
  CategoryTheory.Over.mk (homOfLE (inf_le_right : V ⊓ U ≤ U))

/-- Two successive restrictions of a presheaf equal one restriction (morphisms in `Opens X` are
unique). -/
theorem presheaf_map_map_of_hom (P : TopCat.Presheaf Ab X) {U V W : X.Opens} (i : W ⟶ V) (j : V ⟶ U)
    (k : W ⟶ U) (m : P.obj (op U)) : P.map i.op (P.map j.op m) = P.map k.op m := by
  rw [Subsingleton.elim k (i ≫ j), op_comp, P.map_comp, ConcreteCategory.comp_apply]

/-- **Congruence on germs**: for `φ ∈ Hom_{O_U}(F|_U, G|_U)`, `V, V' ∈ Over U` containing `x`, and
sections `m, m'` with the same restriction to some open neighbourhood `W ≤ V, V'` of `x`, we have
`[V, φ_V(m)] = [V', φ_{V'}(m')]`. Proof: view `W` as an object of `Over U`; the membership condition
of `localHomSubmodule` gives `φ_V(m)|_W = φ_W(m|_W) = φ_W(m'|_W) = φ_{V'}(m')|_W`. -/
theorem germ_localHom_congr (F G : X.Modules) {U : X.Opens}
    (φ : AlgebraicGeometry.Scheme.Modules.localHomSubmodule F G U) (x : X)
    {V V' : CategoryTheory.Over U} (hxV : x ∈ V.left) (hxV' : x ∈ V'.left)
    {m : Γ(F, V.left)} {m' : Γ(F, V'.left)} (W : X.Opens) (hxW : x ∈ W)
    (hWV : W ≤ V.left) (hWV' : W ≤ V'.left)
    (h : F.presheaf.map (homOfLE hWV).op m = F.presheaf.map (homOfLE hWV').op m') :
    G.presheaf.germ V.left x hxV (φ.1 V m) = G.presheaf.germ V'.left x hxV' (φ.1 V' m') := by
  apply TopCat.Presheaf.germ_ext (C := Ab) G.presheaf W hxW (homOfLE hWV) (homOfLE hWV')
  let W' : CategoryTheory.Over U := CategoryTheory.Over.mk (homOfLE (hWV.trans V.hom.le))
  have h1 := φ.2 W' V (CategoryTheory.Over.homMk (homOfLE hWV) (Subsingleton.elim _ _)) m
  have h2 := φ.2 W' V' (CategoryTheory.Over.homMk (homOfLE hWV') (Subsingleton.elim _ _)) m'
  simp only [CategoryTheory.Over.homMk_left] at h1 h2
  exact h1.symm.trans ((congrArg _ h).trans h2)

/-- Germs commute with scalar multiplication (Mathlib's `PresheafOfModules.germ_smul` spelled out
for `X.Modules`). -/
theorem germ_smul_of_modules (M : X.Modules) {V : X.Opens} {y : X} (hy : y ∈ V) (r : Γ(X, V))
    (m : Γ(M, V)) :
    M.presheaf.germ V y hy (r • m) = X.presheaf.germ V y hy r • M.presheaf.germ V y hy m :=
  PresheafOfModules.germ_smul (R := X.presheaf) M.val y V hy r m

/-- For `V ∋ x`, the additive map `F(V) → G_x`, `m ↦ [V ⊓ U, φ_{V ⊓ U}(m|_{V ⊓ U})]`. -/
def localHomGerm (F G : X.Modules) {U : X.Opens}
    (φ : AlgebraicGeometry.Scheme.Modules.localHomSubmodule F G U) (x : X) (hxU : x ∈ U)
    (V : X.Opens) (hxV : x ∈ V) : Γ(F, V) →+ G.presheaf.stalk x :=
  (G.presheaf.germ (V ⊓ U) x ⟨hxV, hxU⟩).hom.comp
    ((φ.1 (AlgebraicGeometry.Scheme.Modules.infOver U V)).toAddMonoidHom.comp
      (F.presheaf.map (homOfLE (inf_le_left : V ⊓ U ≤ V)).op).hom)

theorem localHomGerm_apply (F G : X.Modules) {U : X.Opens}
    (φ : AlgebraicGeometry.Scheme.Modules.localHomSubmodule F G U) (x : X) (hxU : x ∈ U)
    (V : X.Opens) (hxV : x ∈ V) (m : Γ(F, V)) :
    AlgebraicGeometry.Scheme.Modules.localHomGerm F G φ x hxU V hxV m =
      G.presheaf.germ (V ⊓ U) x ⟨hxV, hxU⟩
        (φ.1 (AlgebraicGeometry.Scheme.Modules.infOver U V)
          (F.presheaf.map (homOfLE (inf_le_left : V ⊓ U ≤ V)).op m)) := rfl

/-- Compatibility with restriction: for `W ≤ V`, `localHomGerm` takes the same value on `m|_W` as on
`m`. -/
theorem localHomGerm_res (F G : X.Modules) {U : X.Opens}
    (φ : AlgebraicGeometry.Scheme.Modules.localHomSubmodule F G U) (x : X) (hxU : x ∈ U)
    {V W : X.Opens} (i : W ⟶ V) (hxW : x ∈ W) (m : Γ(F, V)) :
    AlgebraicGeometry.Scheme.Modules.localHomGerm F G φ x hxU W hxW (F.presheaf.map i.op m) =
      AlgebraicGeometry.Scheme.Modules.localHomGerm F G φ x hxU V (i.le hxW) m := by
  rw [AlgebraicGeometry.Scheme.Modules.localHomGerm_apply,
    AlgebraicGeometry.Scheme.Modules.localHomGerm_apply]
  have key : F.presheaf.map (homOfLE (le_rfl : W ⊓ U ≤ W ⊓ U)).op
      (F.presheaf.map (homOfLE (inf_le_left : W ⊓ U ≤ W)).op (F.presheaf.map i.op m)) =
      F.presheaf.map (homOfLE (inf_le_inf_right U i.le)).op
        (F.presheaf.map (homOfLE (inf_le_left : V ⊓ U ≤ V)).op m) := by
    rw [AlgebraicGeometry.Scheme.Modules.presheaf_map_map_of_hom F.presheaf _ i
      (homOfLE (inf_le_left.trans i.le)),
      AlgebraicGeometry.Scheme.Modules.presheaf_map_map_of_hom F.presheaf _ _
      (homOfLE (inf_le_left.trans i.le)),
      AlgebraicGeometry.Scheme.Modules.presheaf_map_map_of_hom F.presheaf _ _
      (homOfLE (inf_le_left.trans i.le))]
  exact AlgebraicGeometry.Scheme.Modules.germ_localHom_congr F G φ x
    (V := AlgebraicGeometry.Scheme.Modules.infOver U W)
    (V' := AlgebraicGeometry.Scheme.Modules.infOver U V) ⟨hxW, hxU⟩ ⟨i.le hxW, hxU⟩
    (W ⊓ U) ⟨hxW, hxU⟩ le_rfl (inf_le_inf_right U i.le) key

/-- The cocone `V ↦ localHomGerm φ V`. -/
def localHomStalkCocone (F G : X.Modules) {U : X.Opens}
    (φ : AlgebraicGeometry.Scheme.Modules.localHomSubmodule F G U) (x : X) (hxU : x ∈ U) :
    Cocone ((OpenNhds.inclusion x).op ⋙ F.presheaf) where
  pt := G.presheaf.stalk x
  ι.app V := AddCommGrpCat.ofHom
    (AlgebraicGeometry.Scheme.Modules.localHomGerm F G φ x hxU V.unop.1 V.unop.2)
  ι.naturality V W f := by
    ext m
    exact AlgebraicGeometry.Scheme.Modules.localHomGerm_res F G φ x hxU
      ((OpenNhds.inclusion x).map f.unop) W.unop.2 m

/-- `φ_x : F_x → G_x` as an additive homomorphism (universal property of the colimit). -/
def localHomStalkAdd (F G : X.Modules) {U : X.Opens}
    (φ : AlgebraicGeometry.Scheme.Modules.localHomSubmodule F G U) (x : X) (hxU : x ∈ U) :
    F.presheaf.stalk x →+ G.presheaf.stalk x :=
  (colimit.desc _ (AlgebraicGeometry.Scheme.Modules.localHomStalkCocone F G φ x hxU)).hom

theorem localHomStalkAdd_germ (F G : X.Modules) {U : X.Opens}
    (φ : AlgebraicGeometry.Scheme.Modules.localHomSubmodule F G U) (x : X) (hxU : x ∈ U)
    (V : X.Opens) (hxV : x ∈ V) (m : Γ(F, V)) :
    AlgebraicGeometry.Scheme.Modules.localHomStalkAdd F G φ x hxU (F.presheaf.germ V x hxV m) =
      G.presheaf.germ (V ⊓ U) x ⟨hxV, hxU⟩
        (φ.1 (AlgebraicGeometry.Scheme.Modules.infOver U V)
          (F.presheaf.map (homOfLE (inf_le_left : V ⊓ U ≤ V)).op m)) :=
  ConcreteCategory.congr_hom
    (colimit.ι_desc (AlgebraicGeometry.Scheme.Modules.localHomStalkCocone F G φ x hxU)
      (op ⟨V, hxV⟩)) m

/-- **`φ_x : F_x → G_x`**, `O_{X,x}`-linear (the "induced map on stalks" of Stacks 01CP, first
paragraph). -/
def localHomStalk (F G : X.Modules) {U : X.Opens}
    (φ : AlgebraicGeometry.Scheme.Modules.localHomSubmodule F G U) (x : X) (hxU : x ∈ U) :
    F.stalk x →ₗ[X.presheaf.stalk x] G.stalk x where
  toFun := AlgebraicGeometry.Scheme.Modules.localHomStalkAdd F G φ x hxU
  map_add' := map_add _
  map_smul' r m := by
    obtain ⟨W, hxW, a, rfl⟩ := X.presheaf.exists_germ_eq r
    obtain ⟨V, hVW, hxV, b, rfl⟩ := F.presheaf.exists_le_germ_eq m hxW
    rw [← X.presheaf.germ_res_apply (homOfLE hVW) x hxV a]
    erw [← AlgebraicGeometry.Scheme.Modules.germ_smul_of_modules F hxV]
    rw [AlgebraicGeometry.Scheme.Modules.localHomStalkAdd_germ,
      AlgebraicGeometry.Scheme.Modules.localHomStalkAdd_germ,
      AlgebraicGeometry.Scheme.Modules.map_smul, LinearMap.map_smul,
      AlgebraicGeometry.Scheme.Modules.germ_smul_of_modules, X.presheaf.germ_res_apply]
    rfl

theorem localHomStalk_germ (F G : X.Modules) {U : X.Opens}
    (φ : AlgebraicGeometry.Scheme.Modules.localHomSubmodule F G U) (x : X) (hxU : x ∈ U)
    (V : X.Opens) (hxV : x ∈ V) (m : Γ(F, V)) :
    AlgebraicGeometry.Scheme.Modules.localHomStalk F G φ x hxU (F.presheaf.germ V x hxV m) =
      G.presheaf.germ (V ⊓ U) x ⟨hxV, hxU⟩
        (φ.1 (AlgebraicGeometry.Scheme.Modules.infOver U V)
          (F.presheaf.map (homOfLE (inf_le_left : V ⊓ U ≤ V)).op m)) :=
  AlgebraicGeometry.Scheme.Modules.localHomStalkAdd_germ F G φ x hxU V hxV m

/-- **Germ formula**: for `V ∈ Over U` with `x ∈ V`, `φ_x([V, m]) = [V, φ_V(m)]`. -/
theorem localHomStalk_germ_over (F G : X.Modules) {U : X.Opens}
    (φ : AlgebraicGeometry.Scheme.Modules.localHomSubmodule F G U) (x : X) (hxU : x ∈ U)
    (V : CategoryTheory.Over U) (hxV : x ∈ V.left) (m : Γ(F, V.left)) :
    AlgebraicGeometry.Scheme.Modules.localHomStalk F G φ x hxU
        (F.presheaf.germ V.left x hxV m) =
      G.presheaf.germ V.left x hxV (φ.1 V m) := by
  rw [AlgebraicGeometry.Scheme.Modules.localHomStalk_germ]
  have key : F.presheaf.map (homOfLE (le_rfl : V.left ⊓ U ≤ V.left ⊓ U)).op
      (F.presheaf.map (homOfLE (inf_le_left : V.left ⊓ U ≤ V.left)).op m) =
      F.presheaf.map (homOfLE (inf_le_left : V.left ⊓ U ≤ V.left)).op m :=
    AlgebraicGeometry.Scheme.Modules.presheaf_map_map_of_hom F.presheaf _ _ _ m
  exact AlgebraicGeometry.Scheme.Modules.germ_localHom_congr F G φ x
    (V := AlgebraicGeometry.Scheme.Modules.infOver U V.left) (V' := V) ⟨hxV, hxU⟩ hxV
    (V.left ⊓ U) ⟨hxV, hxU⟩ le_rfl inf_le_left key

/-! ### Step 2 (b): the canonical map `c : Hom(F,G)^{pre}_x → Hom_{O_{X,x}}(F_x, G_x)` -/

/-- `φ ↦ φ_x` is compatible with shrinking `U`: `(φ|_{U'})_x = φ_x`. -/
theorem localHomStalk_restrict (F G : X.Modules) {U U' : X.Opens} (i : U' ⟶ U)
    (φ : AlgebraicGeometry.Scheme.Modules.localHomSubmodule F G U) (x : X) (hxU' : x ∈ U') :
    AlgebraicGeometry.Scheme.Modules.localHomStalk F G
        (AlgebraicGeometry.Scheme.Modules.localHomRestrict F G i φ) x hxU' =
      AlgebraicGeometry.Scheme.Modules.localHomStalk F G φ x (i.le hxU') := by
  ext m
  obtain ⟨V, hxV, b, rfl⟩ := F.presheaf.exists_germ_eq m
  rw [AlgebraicGeometry.Scheme.Modules.localHomStalk_germ,
    AlgebraicGeometry.Scheme.Modules.localHomStalk_germ]
  have key : F.presheaf.map (homOfLE (le_rfl : V ⊓ U' ≤ V ⊓ U')).op
      (F.presheaf.map (homOfLE (inf_le_left : V ⊓ U' ≤ V)).op b) =
      F.presheaf.map (homOfLE (inf_le_inf_left V i.le)).op
        (F.presheaf.map (homOfLE (inf_le_left : V ⊓ U ≤ V)).op b) := by
    rw [AlgebraicGeometry.Scheme.Modules.presheaf_map_map_of_hom F.presheaf _ _
      (homOfLE (inf_le_left : V ⊓ U' ≤ V)),
      AlgebraicGeometry.Scheme.Modules.presheaf_map_map_of_hom F.presheaf _ _
      (homOfLE (inf_le_left : V ⊓ U' ≤ V))]
  exact AlgebraicGeometry.Scheme.Modules.germ_localHom_congr F G φ x
    (V := (CategoryTheory.Over.map i).obj (AlgebraicGeometry.Scheme.Modules.infOver U' V))
    (V' := AlgebraicGeometry.Scheme.Modules.infOver U V) ⟨hxV, hxU'⟩ ⟨hxV, i.le hxU'⟩
    (V ⊓ U') ⟨hxV, hxU'⟩ le_rfl (inf_le_inf_left V i.le) key

/-- For fixed `U ∋ x`, `φ ↦ φ_x` is an additive homomorphism. -/
def localHomStalkGerm (F G : X.Modules) (x : X) (U : X.Opens) (hxU : x ∈ U) :
    AlgebraicGeometry.Scheme.Modules.localHomSubmodule F G U →+
      (F.stalk x →ₗ[X.presheaf.stalk x] G.stalk x) where
  toFun φ := AlgebraicGeometry.Scheme.Modules.localHomStalk F G φ x hxU
  map_zero' := by
    ext m
    obtain ⟨V, hxV, b, rfl⟩ := F.presheaf.exists_germ_eq m
    rw [AlgebraicGeometry.Scheme.Modules.localHomStalk_germ]
    change G.presheaf.germ (V ⊓ U) x ⟨hxV, hxU⟩ 0 = 0
    exact map_zero _
  map_add' φ ψ := by
    ext m
    obtain ⟨V, hxV, b, rfl⟩ := F.presheaf.exists_germ_eq m
    rw [LinearMap.add_apply, AlgebraicGeometry.Scheme.Modules.localHomStalk_germ,
      AlgebraicGeometry.Scheme.Modules.localHomStalk_germ,
      AlgebraicGeometry.Scheme.Modules.localHomStalk_germ]
    change G.presheaf.germ (V ⊓ U) x ⟨hxV, hxU⟩ (_ + _) = _
    exact map_add _ _ _

/-- The cocone `U ↦ (φ ↦ φ_x)`. -/
def localHomStalkHomCocone (F G : X.Modules) (x : X) :
    Cocone ((OpenNhds.inclusion x).op ⋙
      (AlgebraicGeometry.Scheme.Modules.internalHomPresheaf F G).presheaf) where
  pt := AddCommGrpCat.of (F.stalk x →ₗ[X.presheaf.stalk x] G.stalk x)
  ι.app U := AddCommGrpCat.ofHom
    (AlgebraicGeometry.Scheme.Modules.localHomStalkGerm F G x U.unop.1 U.unop.2)
  ι.naturality U U' f := by
    ext φ
    exact AlgebraicGeometry.Scheme.Modules.localHomStalk_restrict F G
      ((OpenNhds.inclusion x).map f.unop) φ x U'.unop.2

/-- The canonical map `c` as an additive homomorphism (universal property of the colimit). -/
def localHomStalkHomAdd (F G : X.Modules) (x : X) :
    ↥(TopCat.Presheaf.stalk
        (AlgebraicGeometry.Scheme.Modules.internalHomPresheaf F G).presheaf x) →+
      (F.stalk x →ₗ[X.presheaf.stalk x] G.stalk x) :=
  (colimit.desc _ (AlgebraicGeometry.Scheme.Modules.localHomStalkHomCocone F G x)).hom

theorem localHomStalkHomAdd_germ (F G : X.Modules) (x : X) (U : X.Opens) (hxU : x ∈ U)
    (φ : AlgebraicGeometry.Scheme.Modules.localHomSubmodule F G U) :
    AlgebraicGeometry.Scheme.Modules.localHomStalkHomAdd F G x
        (TopCat.Presheaf.germ
          (AlgebraicGeometry.Scheme.Modules.internalHomPresheaf F G).presheaf U x hxU φ) =
      AlgebraicGeometry.Scheme.Modules.localHomStalk F G φ x hxU :=
  ConcreteCategory.congr_hom
    (colimit.ι_desc (AlgebraicGeometry.Scheme.Modules.localHomStalkHomCocone F G x)
      (op ⟨U, hxU⟩)) φ

/-- **The canonical map `c`**, `O_{X,x}`-linear (Stacks 01CP, first paragraph). -/
def localHomStalkHom (F G : X.Modules) (x : X) :
    ↥(TopCat.Presheaf.stalk
        (AlgebraicGeometry.Scheme.Modules.internalHomPresheaf F G).presheaf x)
      →ₗ[X.presheaf.stalk x] (F.stalk x →ₗ[X.presheaf.stalk x] G.stalk x) where
  toFun := AlgebraicGeometry.Scheme.Modules.localHomStalkHomAdd F G x
  map_add' := map_add _
  map_smul' r h := by
    obtain ⟨W, hxW, a, rfl⟩ := X.presheaf.exists_germ_eq r
    obtain ⟨U, hUW, hxU, φ, rfl⟩ := TopCat.Presheaf.exists_le_germ_eq
      (AlgebraicGeometry.Scheme.Modules.internalHomPresheaf F G).presheaf h hxW
    rw [← X.presheaf.germ_res_apply (homOfLE hUW) x hxU a]
    erw [← PresheafOfModules.germ_smul (R := X.presheaf)
      (AlgebraicGeometry.Scheme.Modules.internalHomPresheaf F G) x U hxU]
    rw [AlgebraicGeometry.Scheme.Modules.localHomStalkHomAdd_germ,
      AlgebraicGeometry.Scheme.Modules.localHomStalkHomAdd_germ]
    ext m
    obtain ⟨V, hVU, hxV, b, rfl⟩ := F.presheaf.exists_le_germ_eq m hxU
    let a' : Γ(X, U) := X.presheaf.map (homOfLE hUW).op a
    let φ' : AlgebraicGeometry.Scheme.Modules.localHomSubmodule F G U := φ
    have h1 := AlgebraicGeometry.Scheme.Modules.localHomStalk_germ_over F G
      (a' • φ') x hxU (CategoryTheory.Over.mk (homOfLE hVU)) hxV b
    have h2 := AlgebraicGeometry.Scheme.Modules.localHomStalk_germ_over F G φ' x hxU
      (CategoryTheory.Over.mk (homOfLE hVU)) hxV b
    rw [LinearMap.smul_apply]
    refine h1.trans (Eq.trans ?_ (congrArg _ h2.symm))
    change G.presheaf.germ V x hxV
      ((show Γ(X, V) from X.presheaf.map (homOfLE hVU).op a') •
        (show Γ(G, V) from φ'.1 (CategoryTheory.Over.mk (homOfLE hVU)) b)) = _
    rw [AlgebraicGeometry.Scheme.Modules.germ_smul_of_modules, X.presheaf.germ_res_apply]
    rfl

theorem localHomStalkHom_germ (F G : X.Modules) (x : X) (U : X.Opens) (hxU : x ∈ U)
    (φ : AlgebraicGeometry.Scheme.Modules.localHomSubmodule F G U) :
    AlgebraicGeometry.Scheme.Modules.localHomStalkHom F G x
        (TopCat.Presheaf.germ
          (AlgebraicGeometry.Scheme.Modules.internalHomPresheaf F G).presheaf U x hxU φ) =
      AlgebraicGeometry.Scheme.Modules.localHomStalk F G φ x hxU :=
  AlgebraicGeometry.Scheme.Modules.localHomStalkHomAdd_germ F G x U hxU φ

/-- Germ formula for the canonical map: `c([U, φ])([V, m]) = [V, φ_V(m)]`. -/
theorem localHomStalkHom_germ_germ (F G : X.Modules) (x : X) (U : X.Opens) (hxU : x ∈ U)
    (φ : AlgebraicGeometry.Scheme.Modules.localHomSubmodule F G U)
    (V : CategoryTheory.Over U) (hxV : x ∈ V.left) (m : Γ(F, V.left)) :
    AlgebraicGeometry.Scheme.Modules.localHomStalkHom F G x
        (TopCat.Presheaf.germ
          (AlgebraicGeometry.Scheme.Modules.internalHomPresheaf F G).presheaf U x hxU φ)
        (F.presheaf.germ V.left x hxV m) =
      G.presheaf.germ V.left x hxV (φ.1 V m) := by
  rw [AlgebraicGeometry.Scheme.Modules.localHomStalkHom_germ,
    AlgebraicGeometry.Scheme.Modules.localHomStalk_germ_over]

/-! ### Step 2 (c): injectivity -/

/-- Explicit form of the membership condition of `localHomSubmodule`: `φ_W(m|_W) = φ_V(m)|_W`
(`W ≤ V`, `V ∈ Over U`). -/
theorem localHom_map_res (F G : X.Modules) {U : X.Opens}
    (φ : AlgebraicGeometry.Scheme.Modules.localHomSubmodule F G U) (V : CategoryTheory.Over U)
    {W : X.Opens} (hWV : W ≤ V.left) (m : Γ(F, V.left)) :
    φ.1 (CategoryTheory.Over.mk (homOfLE (hWV.trans V.hom.le))) (F.presheaf.map (homOfLE hWV).op m) =
      G.presheaf.map (homOfLE hWV).op (φ.1 V m) :=
  φ.2 _ V (CategoryTheory.Over.homMk (homOfLE hWV) (Subsingleton.elim _ _)) m

/-- **Finite type ⇒ the canonical map is injective.**

Source: Stacks 01CP, second paragraph of the proof (only finite type is used).

Proof: suppose `c([U', φ]) = 0` and let `s : Fin n → F(U)` locally generate `F|_U` on `U ∋ x`
(`IsLocalGenerators`). Put `V = U ⊓ U'`.
1. By the germ formula `0 = c([U', φ])([V, s_i|_V]) = [V, φ_V(s_i|_V)]`, so the germ of
   `φ_V(s_i|_V)` vanishes, and `TopCat.Presheaf.germ_eq` gives an open neighbourhood `W_i ≤ V` of `x`
   with `φ_V(s_i|_V)|_{W_i} = 0`.
2. Take `V' = V ⊓ ⨅_i W_i` (a finite intersection, still an open neighbourhood); then
   `φ_{V'}(s_i|_{V'}) = 0` for all `i` (membership condition of `localHomSubmodule`: `φ` commutes with
   restriction).
3. `φ|_{V'} = 0`: for every object `W` of `Over V'` and `t ∈ F(W)`, local generation gives for each
   `y ∈ W` a neighbourhood `W'_y ≤ W` and coefficients `c` with `t|_{W'_y} = Σ c_i s_i|_{W'_y}`, so
   `φ_W(t)|_{W'_y} = φ_{W'_y}(t|_{W'_y}) = Σ c_i φ_{W'_y}(s_i|) = 0`; the `W'_y` cover `W` and `G` is a
   sheaf (`TopCat.Sheaf.eq_of_locally_eq'`), hence `φ_W(t) = 0`.
4. `[U', φ] = [V', φ|_{V'}] = 0` (`TopCat.Presheaf.germ_res_apply`). -/
theorem localHomStalkHom_injective_of_isLocalGenerators (F G : X.Modules) (x : X)
    (c : ↥(TopCat.Presheaf.stalk
        (AlgebraicGeometry.Scheme.Modules.internalHomPresheaf F G).presheaf x)
        →ₗ[X.presheaf.stalk x] (F.stalk x →ₗ[X.presheaf.stalk x] G.stalk x))
    (hc : ∀ (U : X.Opens) (hxU : x ∈ U)
        (φ : AlgebraicGeometry.Scheme.Modules.localHomSubmodule F G U)
        (V : CategoryTheory.Over U) (hxV : x ∈ V.left) (m : Γ(F, V.left)),
        c (TopCat.Presheaf.germ
              (AlgebraicGeometry.Scheme.Modules.internalHomPresheaf F G).presheaf U x hxU φ)
            (F.presheaf.germ V.left x hxV m) =
          G.presheaf.germ V.left x hxV (φ.1 V m))
    {U : X.Opens} (hxU : x ∈ U) {n : ℕ} {s : Fin n → Γ(F, U)}
    (hs : AlgebraicGeometry.Scheme.Modules.IsLocalGenerators F U s) :
    Function.Injective c := by
  rw [injective_iff_map_eq_zero]
  intro h hh
  obtain ⟨U', hxU', φ₀, rfl⟩ := TopCat.Presheaf.exists_germ_eq
    (AlgebraicGeometry.Scheme.Modules.internalHomPresheaf F G).presheaf h
  let φ : AlgebraicGeometry.Scheme.Modules.localHomSubmodule F G U' := φ₀
  change c (TopCat.Presheaf.germ
    (AlgebraicGeometry.Scheme.Modules.internalHomPresheaf F G).presheaf U' x hxU' φ) = 0 at hh
  change TopCat.Presheaf.germ
    (AlgebraicGeometry.Scheme.Modules.internalHomPresheaf F G).presheaf U' x hxU' φ = 0
  have hxV : x ∈ U ⊓ U' := ⟨hxU, hxU'⟩
  -- Step 1: the germ of `φ_V(s_i|_V)` vanishes
  have h1 : ∀ i, G.presheaf.germ (U ⊓ U') x hxV
      (φ.1 (CategoryTheory.Over.mk (homOfLE (inf_le_right : U ⊓ U' ≤ U')))
        (F.presheaf.map (homOfLE (inf_le_left : U ⊓ U' ≤ U)).op (s i))) = 0 := by
    intro i
    have := hc U' hxU' φ (CategoryTheory.Over.mk (homOfLE (inf_le_right : U ⊓ U' ≤ U'))) hxV
      (F.presheaf.map (homOfLE (inf_le_left : U ⊓ U' ≤ U)).op (s i))
    rw [hh, LinearMap.zero_apply] at this
    exact this.symm
  have h2 : ∀ i, ∃ (W : X.Opens) (_ : x ∈ W) (iW : W ⟶ U ⊓ U'),
      G.presheaf.map iW.op
        (φ.1 (CategoryTheory.Over.mk (homOfLE (inf_le_right : U ⊓ U' ≤ U')))
          (F.presheaf.map (homOfLE (inf_le_left : U ⊓ U' ≤ U)).op (s i))) = 0 := by
    intro i
    have h0 : G.presheaf.germ (U ⊓ U') x hxV
        (φ.1 (CategoryTheory.Over.mk (homOfLE (inf_le_right : U ⊓ U' ≤ U')))
          (F.presheaf.map (homOfLE (inf_le_left : U ⊓ U' ≤ U)).op (s i))) =
        G.presheaf.germ (U ⊓ U') x hxV 0 := by
      rw [h1 i, map_zero]
    obtain ⟨W, hxW, iU, iV, hW⟩ := TopCat.Presheaf.germ_eq G.presheaf x hxV hxV _ _ h0
    exact ⟨W, hxW, iU, by rw [hW, map_zero]⟩
  choose W hxW iW hW using h2
  -- Step 2: `V' = V ⊓ ⨅ W_i`
  let V' : X.Opens := (U ⊓ U') ⊓ ⨅ i, W i
  have hxV' : x ∈ V' := by
    refine ⟨hxV, ?_⟩
    show x ∈ ((⨅ i, W i : X.Opens) : Set X)
    rw [Opens.coe_iInf]
    exact Set.mem_iInter.2 hxW
  have hV'V : V' ≤ U ⊓ U' := inf_le_left
  have hV'W : ∀ i, V' ≤ W i := fun i => inf_le_right.trans (iInf_le W i)
  have hV'U' : V' ≤ U' := hV'V.trans inf_le_right
  have hV'U : V' ≤ U := hV'V.trans inf_le_left
  have h3 : ∀ i, φ.1 (CategoryTheory.Over.mk (homOfLE hV'U'))
      (F.presheaf.map (homOfLE hV'U).op (s i)) = 0 := by
    intro i
    have hcomp : φ.1 (CategoryTheory.Over.mk (homOfLE hV'U'))
        (F.presheaf.map (homOfLE hV'V).op
          (F.presheaf.map (homOfLE (inf_le_left : U ⊓ U' ≤ U)).op (s i))) =
        G.presheaf.map (homOfLE hV'V).op
          (φ.1 (CategoryTheory.Over.mk (homOfLE (inf_le_right : U ⊓ U' ≤ U')))
            (F.presheaf.map (homOfLE (inf_le_left : U ⊓ U' ≤ U)).op (s i))) :=
      AlgebraicGeometry.Scheme.Modules.localHom_map_res F G φ
        (CategoryTheory.Over.mk (homOfLE (inf_le_right : U ⊓ U' ≤ U'))) hV'V _
    rw [AlgebraicGeometry.Scheme.Modules.presheaf_map_map_of_hom F.presheaf _ _ (homOfLE hV'U)] at hcomp
    rw [hcomp, ← AlgebraicGeometry.Scheme.Modules.presheaf_map_map_of_hom G.presheaf (homOfLE (hV'W i))
      (iW i) (homOfLE hV'V), hW i, map_zero]
  -- Step 3: `φ|_{V'} = 0`
  have h4 : AlgebraicGeometry.Scheme.Modules.localHomRestrict F G (homOfLE hV'U') φ = 0 := by
    apply Subtype.ext
    funext Wo
    apply LinearMap.ext
    intro t
    change φ.1 ((CategoryTheory.Over.map (homOfLE hV'U')).obj Wo) t = 0
    have hWoV' : Wo.left ≤ V' := Wo.hom.le
    have h5 : ∀ y : {y : X // y ∈ Wo.left}, ∃ (W' : X.Opens) (hW' : W' ≤ Wo.left), y.1 ∈ W' ∧
        ∃ cc : Fin n → Γ(X, W'), F.presheaf.map (homOfLE hW').op t =
          ∑ i, cc i • F.presheaf.map (homOfLE (hW'.trans (hWoV'.trans hV'U))).op (s i) :=
      fun y => hs Wo.left (hWoV'.trans hV'U) t y.1 y.2
    choose W' hW' hyW' cc hcc using h5
    let Gs : TopCat.Sheaf Ab X := ⟨G.presheaf, G.isSheaf⟩
    refine Gs.eq_of_locally_eq' W' Wo.left (fun y => homOfLE (hW' y)) ?_ _ 0 ?_
    · intro z hz
      exact Opens.mem_iSup.2 ⟨⟨z, hz⟩, hyW' ⟨z, hz⟩⟩
    · intro y
      show G.presheaf.map (homOfLE (hW' y)).op
        (φ.1 ((CategoryTheory.Over.map (homOfLE hV'U')).obj Wo) t) =
        G.presheaf.map (homOfLE (hW' y)).op 0
      rw [map_zero]
      have hcomp : φ.1 (CategoryTheory.Over.mk (homOfLE ((hW' y).trans (hWoV'.trans hV'U'))))
          (F.presheaf.map (homOfLE (hW' y)).op t) =
          G.presheaf.map (homOfLE (hW' y)).op
            (φ.1 ((CategoryTheory.Over.map (homOfLE hV'U')).obj Wo) t) :=
        AlgebraicGeometry.Scheme.Modules.localHom_map_res F G φ
          ((CategoryTheory.Over.map (homOfLE hV'U')).obj Wo) (hW' y) t
      rw [← hcomp, hcc y, map_sum]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [LinearMap.map_smul]
      have hc2 : φ.1 (CategoryTheory.Over.mk (homOfLE ((hW' y).trans (hWoV'.trans hV'U'))))
          (F.presheaf.map (homOfLE ((hW' y).trans hWoV')).op
            (F.presheaf.map (homOfLE hV'U).op (s i))) =
          G.presheaf.map (homOfLE ((hW' y).trans hWoV')).op
            (φ.1 (CategoryTheory.Over.mk (homOfLE hV'U')) (F.presheaf.map (homOfLE hV'U).op (s i))) :=
        AlgebraicGeometry.Scheme.Modules.localHom_map_res F G φ
          (CategoryTheory.Over.mk (homOfLE hV'U')) ((hW' y).trans hWoV') _
      rw [AlgebraicGeometry.Scheme.Modules.presheaf_map_map_of_hom F.presheaf _ _
        (homOfLE ((hW' y).trans (hWoV'.trans hV'U)))] at hc2
      rw [hc2, h3 i, map_zero, smul_zero]
  -- Step 4: `[U', φ] = [V', φ|_{V'}] = 0`
  rw [← TopCat.Presheaf.germ_res_apply
    (AlgebraicGeometry.Scheme.Modules.internalHomPresheaf F G).presheaf (homOfLE hV'U') x hxV' φ]
  change TopCat.Presheaf.germ (AlgebraicGeometry.Scheme.Modules.internalHomPresheaf F G).presheaf
    V' x hxV' (AlgebraicGeometry.Scheme.Modules.localHomRestrict F G (homOfLE hV'U') φ) = 0
  rw [h4, map_zero]

/-! ### Step 2 (d): surjectivity — factoring a local homomorphism through the `t_i` by hand (the
"universal property of the cokernel" of Stacks 01CP, third paragraph, unfolded on opens) -/

/-- Two successive restrictions of the structure sheaf equal one restriction. -/
theorem ring_map_map {U V W : X.Opens} (i : W ⟶ V) (j : V ⟶ U) (k : W ⟶ U) (a : Γ(X, U)) :
    X.presheaf.map i.op (X.presheaf.map j.op a) = X.presheaf.map k.op a := by
  rw [Subsingleton.elim k (i ≫ j), op_comp, X.presheaf.map_comp, CommRingCat.comp_apply]

section Surj

variable (F G : X.Modules) {U V' : X.Opens} (hV'U : V' ≤ U) {n m : ℕ}
  (s : Fin n → Γ(F, U)) (r : Fin m → Fin n → Γ(X, U)) (t : Fin n → Γ(G, V'))

/-- The relations are still killed by `t` on `W ≤ V'`. -/
theorem surj_relation_res
    (ht : ∀ j, ∑ i, X.presheaf.map (homOfLE hV'U).op (r j i) • t i = 0)
    {W : X.Opens} (hW : W ≤ V') (j : Fin m) :
    ∑ i, X.presheaf.map (homOfLE (hW.trans hV'U)).op (r j i) •
      G.presheaf.map (homOfLE hW).op (t i) = 0 := by
  have := congrArg (G.presheaf.map (homOfLE hW).op) (ht j)
  rw [map_zero, map_sum] at this
  refine Eq.trans ?_ this
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [AlgebraicGeometry.Scheme.Modules.map_smul,
    AlgebraicGeometry.Scheme.Modules.ring_map_map (homOfLE hW) (homOfLE hV'U)
      (homOfLE (hW.trans hV'U))]

/-- **Independence lemma**: two systems of coefficients representing the same section give the same
combination of the `t_i`. -/
theorem surj_indep (hsr : AlgebraicGeometry.Scheme.Modules.IsLocalPresentation F U s r)
    (ht : ∀ j, ∑ i, X.presheaf.map (homOfLE hV'U).op (r j i) • t i = 0)
    {W : X.Opens} (hW : W ≤ V') (a b : Fin n → Γ(X, W))
    (hab : ∑ i, a i • F.presheaf.map (homOfLE (hW.trans hV'U)).op (s i) =
      ∑ i, b i • F.presheaf.map (homOfLE (hW.trans hV'U)).op (s i)) :
    ∑ i, a i • G.presheaf.map (homOfLE hW).op (t i) =
      ∑ i, b i • G.presheaf.map (homOfLE hW).op (t i) := by
  rw [← sub_eq_zero, ← Finset.sum_sub_distrib]
  simp_rw [← sub_smul]
  have hrel : ∑ i, (a i - b i) • F.presheaf.map (homOfLE (hW.trans hV'U)).op (s i) = 0 := by
    simp_rw [sub_smul]
    rw [Finset.sum_sub_distrib, hab, sub_self]
  have h := fun (y : {y : X // y ∈ W}) =>
    hsr.relations_generate W (hW.trans hV'U) (fun i => a i - b i) hrel y.1 y.2
  choose W' hW' hyW' d hd using h
  let Gs : TopCat.Sheaf Ab X := ⟨G.presheaf, G.isSheaf⟩
  refine Gs.eq_of_locally_eq' W' W (fun y => homOfLE (hW' y))
    (fun z hz => Opens.mem_iSup.2 ⟨⟨z, hz⟩, hyW' ⟨z, hz⟩⟩) _ 0 fun y => ?_
  show G.presheaf.map (homOfLE (hW' y)).op
      (∑ i, (a i - b i) • G.presheaf.map (homOfLE hW).op (t i)) =
    G.presheaf.map (homOfLE (hW' y)).op 0
  rw [map_zero, map_sum]
  have hrest : ∀ i, G.presheaf.map (homOfLE (hW' y)).op
      ((a i - b i) • G.presheaf.map (homOfLE hW).op (t i)) =
      (∑ j, d y j • X.presheaf.map (homOfLE ((hW' y).trans (hW.trans hV'U))).op (r j i)) •
        G.presheaf.map (homOfLE ((hW' y).trans hW)).op (t i) := by
    intro i
    rw [AlgebraicGeometry.Scheme.Modules.map_smul,
      AlgebraicGeometry.Scheme.Modules.presheaf_map_map_of_hom G.presheaf (homOfLE (hW' y)) (homOfLE hW)
        (homOfLE ((hW' y).trans hW)), hd y i]
  simp_rw [hrest, Finset.sum_smul, smul_assoc]
  rw [Finset.sum_comm]
  simp_rw [← Finset.smul_sum]
  have hz := AlgebraicGeometry.Scheme.Modules.surj_relation_res G hV'U r t ht ((hW' y).trans hW)
  simp_rw [hz, smul_zero, Finset.sum_const_zero]

/-- The relation characterizing `φ_W(u)`: for all `W'' ≤ W` and coefficients `a`,
`u|_{W''} = Σ a_i s_i|` ⇒ `g|_{W''} = Σ a_i t_i|`. -/
def SurjRel {W : X.Opens} (hW : W ≤ V') (u : Γ(F, W)) (g : Γ(G, W)) : Prop :=
  ∀ (W'' : X.Opens) (h'' : W'' ≤ W) (a : Fin n → Γ(X, W'')),
    F.presheaf.map (homOfLE h'').op u =
      ∑ i, a i • F.presheaf.map (homOfLE (h''.trans (hW.trans hV'U))).op (s i) →
    G.presheaf.map (homOfLE h'').op g =
      ∑ i, a i • G.presheaf.map (homOfLE (h''.trans hW)).op (t i)

/-- Restricting a sum of "coefficient • restricted section": coefficients and sections restrict
separately. -/
theorem map_sum_smul_map (M : X.Modules) {k : ℕ} {A B C : X.Opens} (hBA : B ≤ A) (hCB : C ≤ B)
    (a : Fin k → Γ(X, B)) (v : Fin k → Γ(M, A)) :
    M.presheaf.map (homOfLE hCB).op (∑ i, a i • M.presheaf.map (homOfLE hBA).op (v i)) =
      ∑ i, X.presheaf.map (homOfLE hCB).op (a i) •
        M.presheaf.map (homOfLE (hCB.trans hBA)).op (v i) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [AlgebraicGeometry.Scheme.Modules.map_smul,
    AlgebraicGeometry.Scheme.Modules.presheaf_map_map_of_hom M.presheaf _ _ (homOfLE (hCB.trans hBA))]

/-- **Local characterization**: if near every point of `W` the sections `u` and `g` are represented by
the same coefficients, then `SurjRel` holds. -/
theorem surjRel_of_local (hsr : AlgebraicGeometry.Scheme.Modules.IsLocalPresentation F U s r)
    (ht : ∀ j, ∑ i, X.presheaf.map (homOfLE hV'U).op (r j i) • t i = 0)
    {W : X.Opens} (hW : W ≤ V') (u : Γ(F, W)) (g : Γ(G, W))
    (h : ∀ y ∈ W, ∃ (W₁ : X.Opens) (h₁ : W₁ ≤ W), y ∈ W₁ ∧ ∃ a : Fin n → Γ(X, W₁),
      F.presheaf.map (homOfLE h₁).op u =
          ∑ i, a i • F.presheaf.map (homOfLE (h₁.trans (hW.trans hV'U))).op (s i) ∧
      G.presheaf.map (homOfLE h₁).op g =
          ∑ i, a i • G.presheaf.map (homOfLE (h₁.trans hW)).op (t i)) :
    AlgebraicGeometry.Scheme.Modules.SurjRel F G hV'U s t hW u g := by
  intro W'' h'' b hb
  choose W₁ h₁ hy a ha hg using h
  let Gs : TopCat.Sheaf Ab X := ⟨G.presheaf, G.isSheaf⟩
  refine Gs.eq_of_locally_eq' (fun y : {y : X // y ∈ W''} => W'' ⊓ W₁ y.1 (h'' y.2)) W''
    (fun y => homOfLE inf_le_left)
    (fun z hz => Opens.mem_iSup.2 ⟨⟨z, hz⟩, ⟨hz, hy z (h'' hz)⟩⟩) _ _ fun y => ?_
  have hP1 : W'' ⊓ W₁ y.1 (h'' y.2) ≤ W'' := inf_le_left
  have hP2 : W'' ⊓ W₁ y.1 (h'' y.2) ≤ W₁ y.1 (h'' y.2) := inf_le_right
  show G.presheaf.map (homOfLE hP1).op (G.presheaf.map (homOfLE h'').op g) =
    G.presheaf.map (homOfLE hP1).op
      (∑ i, b i • G.presheaf.map (homOfLE (h''.trans hW)).op (t i))
  rw [AlgebraicGeometry.Scheme.Modules.presheaf_map_map_of_hom G.presheaf _ _
      (homOfLE (hP1.trans h'')),
    ← AlgebraicGeometry.Scheme.Modules.presheaf_map_map_of_hom G.presheaf (homOfLE hP2)
      (homOfLE (h₁ y.1 (h'' y.2))) (homOfLE (hP1.trans h'')),
    hg, AlgebraicGeometry.Scheme.Modules.map_sum_smul_map,
    AlgebraicGeometry.Scheme.Modules.map_sum_smul_map]
  refine AlgebraicGeometry.Scheme.Modules.surj_indep F G hV'U s r t hsr ht (hP1.trans (h''.trans hW))
    _ _ ?_
  rw [← AlgebraicGeometry.Scheme.Modules.map_sum_smul_map F
      (hBA := (h₁ y.1 (h'' y.2)).trans (hW.trans hV'U)) (hCB := hP2),
    ← AlgebraicGeometry.Scheme.Modules.map_sum_smul_map F (hBA := h''.trans (hW.trans hV'U))
      (hCB := hP1), ← ha, ← hb,
    AlgebraicGeometry.Scheme.Modules.presheaf_map_map_of_hom F.presheaf _ _ (homOfLE (hP1.trans h'')),
    AlgebraicGeometry.Scheme.Modules.presheaf_map_map_of_hom F.presheaf _ _ (homOfLE (hP1.trans h''))]

/-- Uniqueness: the `g` satisfying `SurjRel` is unique (`G` is a sheaf). -/
theorem surjRel_unique (hsr : AlgebraicGeometry.Scheme.Modules.IsLocalPresentation F U s r)
    {W : X.Opens} (hW : W ≤ V') (u : Γ(F, W)) {g g' : Γ(G, W)}
    (hg : AlgebraicGeometry.Scheme.Modules.SurjRel F G hV'U s t hW u g)
    (hg' : AlgebraicGeometry.Scheme.Modules.SurjRel F G hV'U s t hW u g') : g = g' := by
  have h := fun (y : {y : X // y ∈ W}) => hsr.generates W (hW.trans hV'U) u y.1 y.2
  choose W' hW' hyW' a ha using h
  let Gs : TopCat.Sheaf Ab X := ⟨G.presheaf, G.isSheaf⟩
  refine Gs.eq_of_locally_eq' W' W (fun y => homOfLE (hW' y))
    (fun z hz => Opens.mem_iSup.2 ⟨⟨z, hz⟩, hyW' ⟨z, hz⟩⟩) g g' fun y => ?_
  show G.presheaf.map (homOfLE (hW' y)).op g = G.presheaf.map (homOfLE (hW' y)).op g'
  rw [hg (W' y) (hW' y) (a y) (ha y), hg' (W' y) (hW' y) (a y) (ha y)]

/-- Existence: choose a cover and coefficients by local generation; the local sections `Σ a_i t_i`
are compatible by independence and glue by the sheaf condition. -/
theorem surjRel_exists (hsr : AlgebraicGeometry.Scheme.Modules.IsLocalPresentation F U s r)
    (ht : ∀ j, ∑ i, X.presheaf.map (homOfLE hV'U).op (r j i) • t i = 0)
    {W : X.Opens} (hW : W ≤ V') (u : Γ(F, W)) :
    ∃ g, AlgebraicGeometry.Scheme.Modules.SurjRel F G hV'U s t hW u g := by
  have h := fun (y : {y : X // y ∈ W}) => hsr.generates W (hW.trans hV'U) u y.1 y.2
  choose W' hW' hyW' a ha using h
  let Gs : TopCat.Sheaf Ab X := ⟨G.presheaf, G.isSheaf⟩
  let sf : ∀ y, Γ(G, W' y) := fun y =>
    ∑ i, a y i • G.presheaf.map (homOfLE ((hW' y).trans hW)).op (t i)
  have hcover : W ≤ iSup W' := fun z hz => Opens.mem_iSup.2 ⟨⟨z, hz⟩, hyW' ⟨z, hz⟩⟩
  have hcompat : TopCat.Presheaf.IsCompatible Gs.1 W' sf := by
    intro y z
    show G.presheaf.map (homOfLE (inf_le_left : W' y ⊓ W' z ≤ W' y)).op (sf y) =
      G.presheaf.map (homOfLE (inf_le_right : W' y ⊓ W' z ≤ W' z)).op (sf z)
    simp only [sf]
    rw [AlgebraicGeometry.Scheme.Modules.map_sum_smul_map,
      AlgebraicGeometry.Scheme.Modules.map_sum_smul_map]
    refine AlgebraicGeometry.Scheme.Modules.surj_indep F G hV'U s r t hsr ht
      (inf_le_left.trans ((hW' y).trans hW)) _ _ ?_
    rw [← AlgebraicGeometry.Scheme.Modules.map_sum_smul_map F
        (hBA := (hW' y).trans (hW.trans hV'U)) (hCB := (inf_le_left : W' y ⊓ W' z ≤ W' y)),
      ← AlgebraicGeometry.Scheme.Modules.map_sum_smul_map F
        (hBA := (hW' z).trans (hW.trans hV'U)) (hCB := (inf_le_right : W' y ⊓ W' z ≤ W' z)),
      ← ha y, ← ha z,
      AlgebraicGeometry.Scheme.Modules.presheaf_map_map_of_hom F.presheaf _ _
        (homOfLE (inf_le_left.trans (hW' y))),
      AlgebraicGeometry.Scheme.Modules.presheaf_map_map_of_hom F.presheaf _ _
        (homOfLE (inf_le_left.trans (hW' y)))]
  obtain ⟨g, hg, -⟩ := Gs.existsUnique_gluing' W' W (fun y => homOfLE (hW' y)) hcover sf hcompat
  refine ⟨g, AlgebraicGeometry.Scheme.Modules.surjRel_of_local F G hV'U s r t hsr ht hW u g
    fun y hy => ⟨W' ⟨y, hy⟩, hW' ⟨y, hy⟩, hyW' ⟨y, hy⟩, a ⟨y, hy⟩, ha ⟨y, hy⟩, hg ⟨y, hy⟩⟩⟩

/-- Compatibility with restriction. -/
theorem surjRel_res {W W₁ : X.Opens} (hW : W ≤ V') (i : W₁ ⟶ W) {u : Γ(F, W)} {g : Γ(G, W)}
    (hg : AlgebraicGeometry.Scheme.Modules.SurjRel F G hV'U s t hW u g) :
    AlgebraicGeometry.Scheme.Modules.SurjRel F G hV'U s t (i.le.trans hW)
      (F.presheaf.map i.op u) (G.presheaf.map i.op g) := by
  intro W'' h'' a ha
  rw [AlgebraicGeometry.Scheme.Modules.presheaf_map_map_of_hom F.presheaf _ _
    (homOfLE (h''.trans i.le))] at ha
  rw [AlgebraicGeometry.Scheme.Modules.presheaf_map_map_of_hom G.presheaf _ _
    (homOfLE (h''.trans i.le))]
  exact hg W'' (h''.trans i.le) a ha

/-- Additivity. -/
theorem surjRel_add (hsr : AlgebraicGeometry.Scheme.Modules.IsLocalPresentation F U s r)
    (ht : ∀ j, ∑ i, X.presheaf.map (homOfLE hV'U).op (r j i) • t i = 0)
    {W : X.Opens} (hW : W ≤ V') {u u' : Γ(F, W)} {g g' : Γ(G, W)}
    (hg : AlgebraicGeometry.Scheme.Modules.SurjRel F G hV'U s t hW u g)
    (hg' : AlgebraicGeometry.Scheme.Modules.SurjRel F G hV'U s t hW u' g') :
    AlgebraicGeometry.Scheme.Modules.SurjRel F G hV'U s t hW (u + u') (g + g') := by
  refine AlgebraicGeometry.Scheme.Modules.surjRel_of_local F G hV'U s r t hsr ht hW _ _
    fun y hy => ?_
  obtain ⟨W₁, h₁, hy₁, b, hb⟩ := hsr.generates W (hW.trans hV'U) u y hy
  obtain ⟨W₂, h₂, hy₂, c, hc⟩ := hsr.generates W (hW.trans hV'U) u' y hy
  have hP1 : W₁ ⊓ W₂ ≤ W₁ := inf_le_left
  have hP2 : W₁ ⊓ W₂ ≤ W₂ := inf_le_right
  refine ⟨W₁ ⊓ W₂, hP1.trans h₁, ⟨hy₁, hy₂⟩,
    fun i => X.presheaf.map (homOfLE hP1).op (b i) + X.presheaf.map (homOfLE hP2).op (c i), ?_, ?_⟩
  · simp_rw [add_smul]
    rw [Finset.sum_add_distrib, map_add,
      ← AlgebraicGeometry.Scheme.Modules.presheaf_map_map_of_hom F.presheaf (homOfLE hP1) (homOfLE h₁)
        (homOfLE (hP1.trans h₁)),
      ← AlgebraicGeometry.Scheme.Modules.presheaf_map_map_of_hom F.presheaf (homOfLE hP2) (homOfLE h₂)
        (homOfLE (hP1.trans h₁)), hb, hc,
      AlgebraicGeometry.Scheme.Modules.map_sum_smul_map,
      AlgebraicGeometry.Scheme.Modules.map_sum_smul_map]
  · simp_rw [add_smul]
    rw [Finset.sum_add_distrib, map_add,
      ← AlgebraicGeometry.Scheme.Modules.presheaf_map_map_of_hom G.presheaf (homOfLE hP1) (homOfLE h₁)
        (homOfLE (hP1.trans h₁)),
      ← AlgebraicGeometry.Scheme.Modules.presheaf_map_map_of_hom G.presheaf (homOfLE hP2) (homOfLE h₂)
        (homOfLE (hP1.trans h₁)), hg W₁ h₁ b hb, hg' W₂ h₂ c hc,
      AlgebraicGeometry.Scheme.Modules.map_sum_smul_map,
      AlgebraicGeometry.Scheme.Modules.map_sum_smul_map]

/-- Scalar multiplication. -/
theorem surjRel_smul (hsr : AlgebraicGeometry.Scheme.Modules.IsLocalPresentation F U s r)
    (ht : ∀ j, ∑ i, X.presheaf.map (homOfLE hV'U).op (r j i) • t i = 0)
    {W : X.Opens} (hW : W ≤ V') (ρ : Γ(X, W)) {u : Γ(F, W)} {g : Γ(G, W)}
    (hg : AlgebraicGeometry.Scheme.Modules.SurjRel F G hV'U s t hW u g) :
    AlgebraicGeometry.Scheme.Modules.SurjRel F G hV'U s t hW (ρ • u) (ρ • g) := by
  refine AlgebraicGeometry.Scheme.Modules.surjRel_of_local F G hV'U s r t hsr ht hW _ _
    fun y hy => ?_
  obtain ⟨W₁, h₁, hy₁, b, hb⟩ := hsr.generates W (hW.trans hV'U) u y hy
  refine ⟨W₁, h₁, hy₁, fun i => X.presheaf.map (homOfLE h₁).op ρ * b i, ?_, ?_⟩
  · simp_rw [mul_smul]
    rw [← Finset.smul_sum, ← hb, AlgebraicGeometry.Scheme.Modules.map_smul]
  · simp_rw [mul_smul]
    rw [← Finset.smul_sum, ← hg W₁ h₁ b hb, AlgebraicGeometry.Scheme.Modules.map_smul]

/-- Generators: `φ(s_i|_{V'}) = t_i`. -/
theorem surjRel_gen (hsr : AlgebraicGeometry.Scheme.Modules.IsLocalPresentation F U s r)
    (ht : ∀ j, ∑ i, X.presheaf.map (homOfLE hV'U).op (r j i) • t i = 0) (i : Fin n) :
    AlgebraicGeometry.Scheme.Modules.SurjRel F G hV'U s t le_rfl
      (F.presheaf.map (homOfLE hV'U).op (s i)) (t i) := by
  intro W'' h'' a ha
  have hsingle : ∀ (M : X.Modules) (v : Fin n → Γ(M, W'')),
      ∑ k, (Pi.single i (1 : Γ(X, W'')) : Fin n → Γ(X, W'')) k • v k = v i := by
    intro M v
    rw [Finset.sum_eq_single i]
    · rw [Pi.single_eq_same, one_smul]
    · intro k _ hk
      rw [Pi.single_eq_of_ne hk, zero_smul]
    · intro h; exact absurd (Finset.mem_univ i) h
  have e1 : ∑ k, (Pi.single i (1 : Γ(X, W'')) : Fin n → Γ(X, W'')) k •
      G.presheaf.map (homOfLE h'').op (t k) = G.presheaf.map (homOfLE h'').op (t i) :=
    hsingle G (fun k => G.presheaf.map (homOfLE h'').op (t k))
  have e2 : ∑ k, (Pi.single i (1 : Γ(X, W'')) : Fin n → Γ(X, W'')) k •
      F.presheaf.map (homOfLE (h''.trans hV'U)).op (s k) =
      F.presheaf.map (homOfLE (h''.trans hV'U)).op (s i) :=
    hsingle F (fun k => F.presheaf.map (homOfLE (h''.trans hV'U)).op (s k))
  rw [← e1]
  refine AlgebraicGeometry.Scheme.Modules.surj_indep F G hV'U s r t hsr ht (h''.trans le_rfl)
    _ a ?_
  rw [e2, ← ha, AlgebraicGeometry.Scheme.Modules.presheaf_map_map_of_hom F.presheaf _ _
    (homOfLE (h''.trans hV'U))]

/-- `φ_W(u)`: the unique section satisfying `SurjRel` (via `Classical.choose`; uniqueness is
`surjRel_unique`). -/
def surjPhiFun (hsr : AlgebraicGeometry.Scheme.Modules.IsLocalPresentation F U s r)
    (ht : ∀ j, ∑ i, X.presheaf.map (homOfLE hV'U).op (r j i) • t i = 0)
    {W : X.Opens} (hW : W ≤ V') (u : Γ(F, W)) : Γ(G, W) :=
  Classical.choose (AlgebraicGeometry.Scheme.Modules.surjRel_exists F G hV'U s r t hsr ht hW u)

theorem surjPhiFun_spec (hsr : AlgebraicGeometry.Scheme.Modules.IsLocalPresentation F U s r)
    (ht : ∀ j, ∑ i, X.presheaf.map (homOfLE hV'U).op (r j i) • t i = 0)
    {W : X.Opens} (hW : W ≤ V') (u : Γ(F, W)) :
    AlgebraicGeometry.Scheme.Modules.SurjRel F G hV'U s t hW u
      (AlgebraicGeometry.Scheme.Modules.surjPhiFun F G hV'U s r t hsr ht hW u) :=
  Classical.choose_spec _

theorem surjPhiFun_add (hsr : AlgebraicGeometry.Scheme.Modules.IsLocalPresentation F U s r)
    (ht : ∀ j, ∑ i, X.presheaf.map (homOfLE hV'U).op (r j i) • t i = 0)
    {W : X.Opens} (hW : W ≤ V') (u u' : Γ(F, W)) :
    AlgebraicGeometry.Scheme.Modules.surjPhiFun F G hV'U s r t hsr ht hW (u + u') =
      AlgebraicGeometry.Scheme.Modules.surjPhiFun F G hV'U s r t hsr ht hW u +
        AlgebraicGeometry.Scheme.Modules.surjPhiFun F G hV'U s r t hsr ht hW u' :=
  AlgebraicGeometry.Scheme.Modules.surjRel_unique F G hV'U s r t hsr hW _
    (AlgebraicGeometry.Scheme.Modules.surjPhiFun_spec F G hV'U s r t hsr ht hW _)
    (AlgebraicGeometry.Scheme.Modules.surjRel_add F G hV'U s r t hsr ht hW
      (AlgebraicGeometry.Scheme.Modules.surjPhiFun_spec F G hV'U s r t hsr ht hW u)
      (AlgebraicGeometry.Scheme.Modules.surjPhiFun_spec F G hV'U s r t hsr ht hW u'))

theorem surjPhiFun_smul (hsr : AlgebraicGeometry.Scheme.Modules.IsLocalPresentation F U s r)
    (ht : ∀ j, ∑ i, X.presheaf.map (homOfLE hV'U).op (r j i) • t i = 0)
    {W : X.Opens} (hW : W ≤ V') (ρ : Γ(X, W)) (u : Γ(F, W)) :
    AlgebraicGeometry.Scheme.Modules.surjPhiFun F G hV'U s r t hsr ht hW (ρ • u) =
      ρ • AlgebraicGeometry.Scheme.Modules.surjPhiFun F G hV'U s r t hsr ht hW u :=
  AlgebraicGeometry.Scheme.Modules.surjRel_unique F G hV'U s r t hsr hW _
    (AlgebraicGeometry.Scheme.Modules.surjPhiFun_spec F G hV'U s r t hsr ht hW _)
    (AlgebraicGeometry.Scheme.Modules.surjRel_smul F G hV'U s r t hsr ht hW ρ
      (AlgebraicGeometry.Scheme.Modules.surjPhiFun_spec F G hV'U s r t hsr ht hW u))

theorem surjPhiFun_res (hsr : AlgebraicGeometry.Scheme.Modules.IsLocalPresentation F U s r)
    (ht : ∀ j, ∑ i, X.presheaf.map (homOfLE hV'U).op (r j i) • t i = 0)
    {W W₁ : X.Opens} (hW : W ≤ V') (i : W₁ ⟶ W) (u : Γ(F, W)) :
    AlgebraicGeometry.Scheme.Modules.surjPhiFun F G hV'U s r t hsr ht (i.le.trans hW)
        (F.presheaf.map i.op u) =
      G.presheaf.map i.op (AlgebraicGeometry.Scheme.Modules.surjPhiFun F G hV'U s r t hsr ht hW u) :=
  AlgebraicGeometry.Scheme.Modules.surjRel_unique F G hV'U s r t hsr (i.le.trans hW) _
    (AlgebraicGeometry.Scheme.Modules.surjPhiFun_spec F G hV'U s r t hsr ht _ _)
    (AlgebraicGeometry.Scheme.Modules.surjRel_res F G hV'U s t hW i
      (AlgebraicGeometry.Scheme.Modules.surjPhiFun_spec F G hV'U s r t hsr ht hW u))

theorem surjPhiFun_gen (hsr : AlgebraicGeometry.Scheme.Modules.IsLocalPresentation F U s r)
    (ht : ∀ j, ∑ i, X.presheaf.map (homOfLE hV'U).op (r j i) • t i = 0) (i : Fin n) :
    AlgebraicGeometry.Scheme.Modules.surjPhiFun F G hV'U s r t hsr ht le_rfl
      (F.presheaf.map (homOfLE hV'U).op (s i)) = t i :=
  AlgebraicGeometry.Scheme.Modules.surjRel_unique F G hV'U s r t hsr le_rfl _
    (AlgebraicGeometry.Scheme.Modules.surjPhiFun_spec F G hV'U s r t hsr ht _ _)
    (AlgebraicGeometry.Scheme.Modules.surjRel_gen F G hV'U s r t hsr ht i)

/-- **The local homomorphism factored through `t`**: `φ ∈ Hom_{O_{V'}}(F|_{V'}, G|_{V'})` with
`φ(s_i|_{V'}) = t_i`. -/
def surjPhi (hsr : AlgebraicGeometry.Scheme.Modules.IsLocalPresentation F U s r)
    (ht : ∀ j, ∑ i, X.presheaf.map (homOfLE hV'U).op (r j i) • t i = 0) :
    AlgebraicGeometry.Scheme.Modules.localHomSubmodule F G V' :=
  ⟨fun Wo =>
    { toFun := AlgebraicGeometry.Scheme.Modules.surjPhiFun F G hV'U s r t hsr ht Wo.hom.le
      map_add' := AlgebraicGeometry.Scheme.Modules.surjPhiFun_add F G hV'U s r t hsr ht Wo.hom.le
      map_smul' := AlgebraicGeometry.Scheme.Modules.surjPhiFun_smul F G hV'U s r t hsr ht
        Wo.hom.le },
    fun _ Wo' i u =>
      AlgebraicGeometry.Scheme.Modules.surjPhiFun_res F G hV'U s r t hsr ht Wo'.hom.le i.left u⟩

theorem surjPhi_apply (hsr : AlgebraicGeometry.Scheme.Modules.IsLocalPresentation F U s r)
    (ht : ∀ j, ∑ i, X.presheaf.map (homOfLE hV'U).op (r j i) • t i = 0)
    (Wo : CategoryTheory.Over V') (u : Γ(F, Wo.left)) :
    (AlgebraicGeometry.Scheme.Modules.surjPhi F G hV'U s r t hsr ht).1 Wo u =
      AlgebraicGeometry.Scheme.Modules.surjPhiFun F G hV'U s r t hsr ht Wo.hom.le u := rfl

end Surj

/-- **Finite presentation ⇒ the canonical map is surjective.**

Source: Stacks 01CP, third paragraph of the proof (finite presentation part). The statement is
self-contained: `c` enters only as a linear map satisfying the germ formula.

Proof (with the concrete data of `IsLocalPresentation`): let `ψ ∈ Hom_{O_{X,x}}(F_x, G_x)` and let
`(s, r)` be a local presentation of `F` on `U ∋ x` (`s_i ∈ F(U)` generators, `r^j ∈ Γ(X,U)^n`
relations).
1. **Choose `t_i`**: for each `i`, `ψ([U, s_i]) ∈ G_x` is a germ `[V_i, t_i]`
   (`TopCat.Presheaf.exists_le_germ_eq`, with `V_i ≤ U`); there are finitely many `i`, so put
   `V = ⨅_i V_i` (`x ∈ V`, `Opens.coe_iInf`) and restrict the `t_i` to `V`.
2. **The relations are killed**: for each `j`,
   `[V, Σ_i r^j_i|_V • t_i] = Σ_i [r^j_i] • ψ([s_i]) = ψ([Σ_i r^j_i • s_i]) = ψ(0) = 0`
   (`germ_smul`, linearity of `ψ`, `relation`). By `germ_eq` there is a neighbourhood `V_j' ≤ V` of
   `x` with `Σ_i r^j_i|_{V_j'} • t_i|_{V_j'} = 0`; take `V' = ⨅_j V_j'`, so that `Σ_i r^j_i • t_i = 0`
   on `V'` for all `j`.
3. **Independence lemma**: for `W ≤ V'` and coefficients `a, b : Fin n → Γ(X, W)` with
   `Σ a_i s_i|_W = Σ b_i s_i|_W`, we have `Σ a_i t_i|_W = Σ b_i t_i|_W`. Proof: `a - b` is a system of
   relation coefficients, so by `relations_generate`, near every point of `W`, `a - b = Σ_j d_j r^j|`,
   hence `Σ (a_i - b_i) t_i = Σ_j d_j (Σ_i r^j_i t_i) = 0` locally; `G` is a sheaf
   (`TopCat.Sheaf.eq_of_locally_eq'`), so globally.
4. **Construct `φ ∈ Hom_{O_{V'}}(F|_{V'}, G|_{V'})`**: for `W ∈ Over V'` and `t ∈ F(W)`, by `generates`
   choose for each point `y` of `W` a `W_y ≤ W` and `c^y` with `t|_{W_y} = Σ c^y_i s_i|`; the local
   sections `g_y = Σ c^y_i t_i|_{W_y}` agree on `W_y ⊓ W_z` (step 3) and glue by the sheaf condition
   (`TopCat.Sheaf.existsUnique_gluing'`) to a unique `φ_W(t) ∈ G(W)`.
   **Characterization**: `φ_W(t)` is the unique section such that for all `W'' ≤ W` and `c`,
   `t|_{W''} = Σ c_i s_i|` ⇒ `φ_W(t)|_{W''} = Σ c_i t_i|` (existence: compare with the glued pieces,
   then step 3 and separatedness; uniqueness: separatedness). From the characterization, `φ_W` is
   additive, `Γ(X,W)`-linear (`(a t)|_{W''} = Σ (a c_i) s_i|`) and commutes with restriction (membership
   condition for `Over V'`), i.e. `φ ∈ localHomSubmodule F G V'`.
5. **`c([V', φ]) = ψ`**: `φ_{V'}(s_i|_{V'}) = t_i|_{V'}` (characterization with coefficients
   `δ_{ik}`), so by the germ formula
   `c([V', φ])([U, s_i]) = c([V',φ])([V', s_i|_{V'}]) = [V', t_i|_{V'}] = [V_i, t_i] = ψ([U, s_i])`.
   `F_x` is generated by the `[U, s_i]`: any `[W, u] ∈ F_x` satisfies `u|_{W_x} = Σ c_i s_i|`
   (`generates` at `x`), so `[W, u] = Σ [c_i] • [U, s_i]`; two `O_{X,x}`-linear maps agreeing on
   generators are equal.

In the formalization, step 3 is `surj_indep`; `SurjRel` with `surjRel_of_local` / `surjRel_unique` /
`surjRel_exists` (characterization, uniqueness, existence by gluing), `surjRel_add` / `_smul` / `_res` /
`_gen` and `surjPhiFun` / `surjPhi` give the `φ` of step 4; steps 1, 2 and 5 assemble the result. -/
theorem localHomStalkHom_surjective_of_isLocalPresentation (F G : X.Modules) (x : X)
    (c : ↥(TopCat.Presheaf.stalk
        (AlgebraicGeometry.Scheme.Modules.internalHomPresheaf F G).presheaf x)
        →ₗ[X.presheaf.stalk x] (F.stalk x →ₗ[X.presheaf.stalk x] G.stalk x))
    (hc : ∀ (U : X.Opens) (hxU : x ∈ U)
        (φ : AlgebraicGeometry.Scheme.Modules.localHomSubmodule F G U)
        (V : CategoryTheory.Over U) (hxV : x ∈ V.left) (m : Γ(F, V.left)),
        c (TopCat.Presheaf.germ
              (AlgebraicGeometry.Scheme.Modules.internalHomPresheaf F G).presheaf U x hxU φ)
            (F.presheaf.germ V.left x hxV m) =
          G.presheaf.germ V.left x hxV (φ.1 V m))
    {U : X.Opens} (hxU : x ∈ U) {n m : ℕ} {s : Fin n → Γ(F, U)} {r : Fin m → Fin n → Γ(X, U)}
    (hsr : AlgebraicGeometry.Scheme.Modules.IsLocalPresentation F U s r) :
    Function.Surjective c := by
  intro ψ
  -- Step 1: the `t_i`
  have h1 : ∀ i, ∃ V ≤ U, ∃ (hxV : x ∈ V) (t : Γ(G, V)),
      G.presheaf.germ V x hxV t = ψ (F.presheaf.germ U x hxU (s i)) :=
    fun i => TopCat.Presheaf.exists_le_germ_eq G.presheaf _ hxU
  choose V hVU hxV t ht using h1
  let V₀ : X.Opens := U ⊓ ⨅ i, V i
  have hxV₀ : x ∈ V₀ := by
    refine ⟨hxU, ?_⟩
    show x ∈ ((⨅ i, V i : X.Opens) : Set X)
    rw [Opens.coe_iInf]
    exact Set.mem_iInter.2 hxV
  have hV₀U : V₀ ≤ U := inf_le_left
  have hV₀V : ∀ i, V₀ ≤ V i := fun i => inf_le_right.trans (iInf_le V i)
  let t₀ : Fin n → Γ(G, V₀) := fun i => G.presheaf.map (homOfLE (hV₀V i)).op (t i)
  have ht₀ : ∀ i, G.presheaf.germ V₀ x hxV₀ (t₀ i) = ψ (F.presheaf.germ U x hxU (s i)) := by
    intro i
    show G.presheaf.germ V₀ x hxV₀ (G.presheaf.map (homOfLE (hV₀V i)).op (t i)) = _
    rw [TopCat.Presheaf.germ_res_apply]
    exact ht i
  -- Step 2: the germs of the relations vanish
  have h2 : ∀ j, G.presheaf.germ V₀ x hxV₀
      (∑ i, X.presheaf.map (homOfLE hV₀U).op (r j i) • t₀ i) = G.presheaf.germ V₀ x hxV₀ 0 := by
    intro j
    rw [map_zero, map_sum]
    have e : ∀ i, G.presheaf.germ V₀ x hxV₀ (X.presheaf.map (homOfLE hV₀U).op (r j i) • t₀ i) =
        X.presheaf.germ U x hxU (r j i) • ψ (F.presheaf.germ U x hxU (s i)) := by
      intro i
      rw [AlgebraicGeometry.Scheme.Modules.germ_smul_of_modules, ht₀ i,
        X.presheaf.germ_res_apply]
    simp_rw [e, ← LinearMap.map_smul ψ]
    rw [← map_sum ψ]
    have e2 : ∑ i, X.presheaf.germ U x hxU (r j i) • F.presheaf.germ U x hxU (s i) =
        F.presheaf.germ U x hxU (∑ i, r j i • s i) := by
      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ =>
        (AlgebraicGeometry.Scheme.Modules.germ_smul_of_modules F hxU (r j i) (s i)).symm
    rw [e2, hsr.relation j, map_zero, map_zero]
  have h3 : ∀ j, ∃ (W : X.Opens) (_ : x ∈ W) (iW : W ⟶ V₀),
      G.presheaf.map iW.op (∑ i, X.presheaf.map (homOfLE hV₀U).op (r j i) • t₀ i) = 0 := by
    intro j
    obtain ⟨W, hxW, iU, iV, hW⟩ := TopCat.Presheaf.germ_eq G.presheaf x hxV₀ hxV₀ _ _ (h2 j)
    exact ⟨W, hxW, iU, by rw [hW, map_zero]⟩
  choose W hxW iW hW using h3
  let V' : X.Opens := V₀ ⊓ ⨅ j, W j
  have hxV' : x ∈ V' := by
    refine ⟨hxV₀, ?_⟩
    show x ∈ ((⨅ j, W j : X.Opens) : Set X)
    rw [Opens.coe_iInf]
    exact Set.mem_iInter.2 hxW
  have hV'V₀ : V' ≤ V₀ := inf_le_left
  have hV'W : ∀ j, V' ≤ W j := fun j => inf_le_right.trans (iInf_le W j)
  have hV'U : V' ≤ U := hV'V₀.trans hV₀U
  let tV : Fin n → Γ(G, V') := fun i => G.presheaf.map (homOfLE hV'V₀).op (t₀ i)
  have htV : ∀ j, ∑ i, X.presheaf.map (homOfLE hV'U).op (r j i) • tV i = 0 := by
    intro j
    have := congrArg (G.presheaf.map (homOfLE (hV'W j)).op) (hW j)
    rw [map_zero, AlgebraicGeometry.Scheme.Modules.presheaf_map_map_of_hom G.presheaf _ _
      (homOfLE hV'V₀), map_sum] at this
    refine Eq.trans ?_ this
    refine Finset.sum_congr rfl fun i _ => ?_
    show X.presheaf.map (homOfLE hV'U).op (r j i) • G.presheaf.map (homOfLE hV'V₀).op (t₀ i) = _
    rw [AlgebraicGeometry.Scheme.Modules.map_smul,
      AlgebraicGeometry.Scheme.Modules.ring_map_map (homOfLE hV'V₀) (homOfLE hV₀U) (homOfLE hV'U)]
  have htV_germ : ∀ i, G.presheaf.germ V' x hxV' (tV i) = ψ (F.presheaf.germ U x hxU (s i)) := by
    intro i
    show G.presheaf.germ V' x hxV' (G.presheaf.map (homOfLE hV'V₀).op (t₀ i)) = _
    rw [TopCat.Presheaf.germ_res_apply]
    exact ht₀ i
  -- Steps 3 and 4: `φ`
  let φ := AlgebraicGeometry.Scheme.Modules.surjPhi F G hV'U s r tV hsr htV
  refine ⟨TopCat.Presheaf.germ (AlgebraicGeometry.Scheme.Modules.internalHomPresheaf F G).presheaf
    V' x hxV' φ, ?_⟩
  -- Step 5: compare on generators
  apply LinearMap.ext
  intro e
  obtain ⟨Wm, hWmV', hxWm, u, rfl⟩ := TopCat.Presheaf.exists_le_germ_eq F.presheaf e hxV'
  have hgerm : c (TopCat.Presheaf.germ
        (AlgebraicGeometry.Scheme.Modules.internalHomPresheaf F G).presheaf V' x hxV' φ)
        (F.presheaf.germ Wm x hxWm u) =
      G.presheaf.germ Wm x hxWm (φ.1 (CategoryTheory.Over.mk (homOfLE hWmV')) u) :=
    hc V' hxV' φ (CategoryTheory.Over.mk (homOfLE hWmV')) hxWm u
  rw [hgerm]
  obtain ⟨W'', h'', hxW'', a, ha⟩ := hsr.generates Wm (hWmV'.trans hV'U) u x hxWm
  have hφ : G.presheaf.map (homOfLE h'').op
      (AlgebraicGeometry.Scheme.Modules.surjPhiFun F G hV'U s r tV hsr htV hWmV' u) =
      ∑ i, a i • G.presheaf.map (homOfLE (h''.trans hWmV')).op (tV i) :=
    AlgebraicGeometry.Scheme.Modules.surjPhiFun_spec F G hV'U s r tV hsr htV hWmV' u W'' h'' a ha
  change G.presheaf.germ Wm x hxWm
    (AlgebraicGeometry.Scheme.Modules.surjPhiFun F G hV'U s r tV hsr htV hWmV' u) = _
  rw [← TopCat.Presheaf.germ_res_apply G.presheaf (homOfLE h'') x hxW'', hφ, map_sum]
  have e3 : ∀ i, G.presheaf.germ W'' x hxW''
      (a i • G.presheaf.map (homOfLE (h''.trans hWmV')).op (tV i)) =
      X.presheaf.germ W'' x hxW'' (a i) • ψ (F.presheaf.germ U x hxU (s i)) := by
    intro i
    rw [AlgebraicGeometry.Scheme.Modules.germ_smul_of_modules, TopCat.Presheaf.germ_res_apply,
      htV_germ i]
  simp_rw [e3, ← LinearMap.map_smul ψ]
  rw [← map_sum ψ]
  congr 1
  rw [← TopCat.Presheaf.germ_res_apply F.presheaf (homOfLE h'') x hxW'', ha, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [AlgebraicGeometry.Scheme.Modules.germ_smul_of_modules, TopCat.Presheaf.germ_res_apply]

/-! ### Step 2, summary: the canonical map on the presheaf stalk

The following two statements are the actual content of the proof of Stacks 01CP. The first
(existence and well-definedness) is `localHomStalkHom` above; the second is bijectivity for `F` of
finite presentation. Both concern only the stalk of the internal Hom **presheaf** and are
independent of sheafification. -/

/-- **Existence and well-definedness of the canonical map.**

Source: Stacks 01CP (`modules-lemma-stalk-internal-hom`), first paragraph of the proof: "The map
sends the equivalence class of `(U, φ)` … to the induced map on stalks at `x`, namely
`φ_x : F_x → G_x`." No finiteness hypothesis is needed.

Proof:
1. Fix an open `U ∋ x` and `φ ∈ Hom_{O_U}(F|_U, G|_U) = localHomSubmodule F G U`. First construct
   `φ_x : F_x → G_x`. Here `F_x = colim_{V ∋ x} F(V)` (Mathlib's `TopCat.Presheaf.stalk` is the
   colimit over `(OpenNhds x)ᵒᵖ`, a filtered index category). For each `V ∋ x` let
   `F(V) → G_x`, `m ↦ [V ⊓ U, φ_{V ⊓ U}(m|_{V ⊓ U})]` (`V ⊓ U` is an object of `Over U` and
   `x ∈ V ⊓ U`). This family is compatible with restriction: for `V' ≤ V`,
   `φ_{V' ⊓ U}((m|_{V'})|_{V' ⊓ U}) = φ_{V ⊓ U}(m|_{V ⊓ U})|_{V' ⊓ U}`, which is exactly the
   membership condition of `localHomSubmodule` (`φ` commutes with restriction), so the two germs
   agree. The universal property of the colimit gives an additive map `φ_x : F_x → G_x` with
   `φ_x([V, m]) = [V ⊓ U, φ_{V ⊓ U}(m|_{V ⊓ U})]`; for `V ≤ U` we have `V ⊓ U = V`, i.e.
   `φ_x([V, m]) = [V, φ_V(m)]` — the germ formula required in the statement.
2. `φ_x` is `O_{X,x}`-linear: an element of `O_{X,x}` is a germ `[W, r]`; after passing to
   `V ≤ W ⊓ U`, `φ_V(r|_V · m|_V) = r|_V · φ_V(m|_V)` (`φ_V` is `Γ(X, V)`-linear); take germs.
3. `φ ↦ φ_x` is compatible with shrinking `U`: `(φ|_{U'})_x = φ_x` (on a germ `[V, m]` both sides
   are `[V ⊓ U', φ_{V ⊓ U'}(m|…)]`, the values on `V ⊓ U'` and `V ⊓ U` being restrictions of each
   other). The universal property of `Hom(F,G)^{pre}_x = colim_{U ∋ x} localHomSubmodule F G U` then
   gives `c : Hom(F,G)^{pre}_x → Hom_{O_{X,x}}(F_x, G_x)` satisfying the germ formula.
4. `O_{X,x}`-linearity of `c` follows likewise by passing to the colimit from the `Γ(X,U)`-linearity
   of `φ ↦ φ_x` on each `U`.

In the formalization: `germ_localHom_congr` (congruence on germs, handling the passage between
`Over U` and `OpenNhds x`) → `localHomGerm` / `localHomStalkCocone` / `localHomStalk` (`φ_x`, steps
1–2) → `localHomStalk_restrict` / `localHomStalkHomCocone` / `localHomStalkHom` (`c`, steps 3–4);
the germ formula is `localHomStalkHom_germ_germ`. -/
theorem exists_localHomStalkHom (F G : X.Modules) (x : X) :
    ∃ c : ↥(TopCat.Presheaf.stalk
        (AlgebraicGeometry.Scheme.Modules.internalHomPresheaf F G).presheaf x)
        →ₗ[X.presheaf.stalk x] (F.stalk x →ₗ[X.presheaf.stalk x] G.stalk x),
      ∀ (U : X.Opens) (hxU : x ∈ U)
        (φ : AlgebraicGeometry.Scheme.Modules.localHomSubmodule F G U)
        (V : CategoryTheory.Over U) (hxV : x ∈ V.left) (m : Γ(F, V.left)),
        c (TopCat.Presheaf.germ
              (AlgebraicGeometry.Scheme.Modules.internalHomPresheaf F G).presheaf U x hxU φ)
            (F.presheaf.germ V.left x hxV m) =
          G.presheaf.germ V.left x hxV (φ.1 V m) :=
  ⟨AlgebraicGeometry.Scheme.Modules.localHomStalkHom F G x,
    AlgebraicGeometry.Scheme.Modules.localHomStalkHom_germ_germ F G x⟩

/-- **For `F` of finite presentation the canonical map is bijective.**

Source: Stacks 01CP, second and third paragraphs of the proof. The statement is self-contained: `c`
enters only as a linear map satisfying the germ formula, and that formula determines `c` uniquely:
every element of `Hom(F,G)^{pre}_x` is a germ `[U, φ]` (`TopCat.Presheaf.exists_germ_eq`), every
element of `F_x` is a germ `[V, m]` with `V ≤ U` after shrinking (`TopCat.Presheaf.exists_le_germ_eq`),
and the germ formula fixes the value of `c` on all of them.

Proof sketch (following Stacks).

*(Injectivity, using only finite type.)* Let `[U, φ]` be in the kernel, i.e. `φ_x = 0`. Shrink `U` so
that `F|_U` is generated by finitely many sections `s^1, …, s^n ∈ F(U)`. By the germ formula
`0 = c([U,φ])(s^i_x) = [U, φ_U(s^i)]`, so the germ of `φ_U(s^i)` vanishes; since `G_x` is a colimit,
each `i` has an open neighbourhood `V_i ⊆ U` of `x` with `φ_{V_i}(s^i|_{V_i}) = 0`. Take
`V = ⋂ V_i`; then `φ_V(s^i|_V) = 0` for all `i`. The `s^i|_V` generate `F|_V` and `φ|_V` is
`O_V`-linear, so `φ|_V = 0` and `[U, φ] = [V, φ|_V] = 0`.

*(Surjectivity, using finite presentation.)* Let `ψ ∈ Hom_{O_{X,x}}(F_x, G_x)`. Shrink to a
neighbourhood `U` of `x` on which `F|_U` has a presentation
`⊕_{j=1}^m O_U → ⊕_{i=1}^n O_U → F|_U → 0`. Let `s^i ∈ F(U)` be the images of the basis vectors under
the second arrow (generators) and `r^j = (r^j_1, …, r^j_n) ∈ Γ(X,U)^n` those under the first arrow
(relations), so `Σ_i r^j_i s^i = 0`. Choose `t^i ∈ G(V)` (`V ⊆ U` a neighbourhood of `x`) with
`ψ(s^i_x) = [V, t^i]`. For each `j` the germ of `Σ_i r^j_i|_V t^i` is `ψ(Σ_i r^j_i s^i)_x = ψ(0) = 0`;
there are finitely many relations, so after shrinking to `V' ⊆ V`, `Σ_i r^j_i|_{V'} t^i|_{V'} = 0`
for all `j`. Thus `⊕_i O_{V'} → G|_{V'}`, `e_i ↦ t^i|_{V'}` kills all relations and factors uniquely
through the cokernel `F|_{V'}` of the presentation, giving `φ ∈ Hom_{O_{V'}}(F|_{V'}, G|_{V'})` with
`φ_{V'}(s^i|_{V'}) = t^i|_{V'}`. By the germ formula `c([V', φ])` and `ψ` agree on every `s^i_x`;
the `s^i_x` generate `F_x` and both maps are `O_{X,x}`-linear, so `c([V', φ]) = ψ`.

The formalization unfolds `IsFinitePresentation` into the local data `exists_isLocalPresentation`
and realizes the factorization through the cokernel by hand (step 2 (d) above). -/
theorem localHomStalkHom_bijective (F G : X.Modules)
    [F.IsFinitePresentation] (x : X)
    (c : ↥(TopCat.Presheaf.stalk
        (AlgebraicGeometry.Scheme.Modules.internalHomPresheaf F G).presheaf x)
        →ₗ[X.presheaf.stalk x] (F.stalk x →ₗ[X.presheaf.stalk x] G.stalk x))
    (hc : ∀ (U : X.Opens) (hxU : x ∈ U)
        (φ : AlgebraicGeometry.Scheme.Modules.localHomSubmodule F G U)
        (V : CategoryTheory.Over U) (hxV : x ∈ V.left) (m : Γ(F, V.left)),
        c (TopCat.Presheaf.germ
              (AlgebraicGeometry.Scheme.Modules.internalHomPresheaf F G).presheaf U x hxU φ)
            (F.presheaf.germ V.left x hxV m) =
          G.presheaf.germ V.left x hxV (φ.1 V m)) :
    Function.Bijective c := by
  obtain ⟨U, hxU, n, m, s, r, hsr⟩ :=
    AlgebraicGeometry.Scheme.Modules.exists_isLocalPresentation F x
  exact ⟨AlgebraicGeometry.Scheme.Modules.localHomStalkHom_injective_of_isLocalGenerators F G x c hc
      hxU hsr.generates,
    AlgebraicGeometry.Scheme.Modules.localHomStalkHom_surjective_of_isLocalPresentation F G x c hc
      hxU hsr⟩

end AlgebraicGeometry.Scheme.Modules

/-! ### Step 3: assembly -/

/-- **Stacks 01CP** (finite presentation part): for `F` of finite presentation, the canonical map
`Hom(F,G)_x → Hom_{O_{X,x}}(F_x, G_x)`, `(U, φ) ↦ φ_x`, is an isomorphism of `O_{X,x}`-modules.
The canonical map is characterized by its values on germs: a local homomorphism
`φ ∈ Hom_{O_U}(F|_U, G|_U)` (a section over `U` of the internal Hom presheaf, `localHomSubmodule F G U`)
is sent by the sheafification unit into `internalHom F G`, and its germ `[U, φ]` at `x` acts on a germ
`[V, m]` of `F` (`x ∈ V ≤ U`) by `[V, φ_V(m)]`, i.e. `φ_x([m]) = [φ(m)]`. Since sheafification does
not change stalks and `F_x` consists of germs, the linear map satisfying this formula is unique: it
is the canonical map of Stacks. -/
theorem AlgebraicGeometry.Scheme.Modules.stalk_internalHom_iso {X : AlgebraicGeometry.Scheme.{u}}
    (F G : X.Modules) [F.IsFinitePresentation] (x : X) :
    ∃ e : (AlgebraicGeometry.Scheme.Modules.internalHom F G).stalk x ≅
        ModuleCat.of (X.presheaf.stalk x) (F.stalk x →ₗ[X.presheaf.stalk x] G.stalk x),
      ∀ (U : X.Opens) (hxU : x ∈ U)
        (φ : AlgebraicGeometry.Scheme.Modules.localHomSubmodule F G U)
        (V : CategoryTheory.Over U) (hxV : x ∈ V.left) (m : Γ(F, V.left)),
        e.hom ((AlgebraicGeometry.Scheme.Modules.internalHom F G).presheaf.germ U x hxU
            (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
              (AlgebraicGeometry.Scheme.Modules.internalHomPresheaf F G)).app (Opposite.op U) φ))
          (F.presheaf.germ V.left x hxV m) =
        G.presheaf.germ V.left x hxV (φ.1 V m) := by
  obtain ⟨c, hc⟩ := AlgebraicGeometry.Scheme.Modules.exists_localHomStalkHom F G x
  have hbij := AlgebraicGeometry.Scheme.Modules.localHomStalkHom_bijective F G x c hc
  refine ⟨((AlgebraicGeometry.Scheme.Modules.internalHomPresheafStalkEquiv F G x).symm.trans
    (LinearEquiv.ofBijective c hbij)).toModuleIso, ?_⟩
  intro U hxU φ V hxV m
  have hsymm :
      (AlgebraicGeometry.Scheme.Modules.internalHomPresheafStalkEquiv F G x).symm
          ((AlgebraicGeometry.Scheme.Modules.internalHom F G).presheaf.germ U x hxU
            (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
              (AlgebraicGeometry.Scheme.Modules.internalHomPresheaf F G)).app
                (Opposite.op U) φ)) =
        TopCat.Presheaf.germ
          (AlgebraicGeometry.Scheme.Modules.internalHomPresheaf F G).presheaf U x hxU φ := by
    rw [← AlgebraicGeometry.Scheme.Modules.internalHomPresheafStalkEquiv_germ F G x U hxU φ]
    exact (AlgebraicGeometry.Scheme.Modules.internalHomPresheafStalkEquiv F G x).symm_apply_apply _
  change c ((AlgebraicGeometry.Scheme.Modules.internalHomPresheafStalkEquiv F G x).symm _) _ = _
  rw [hsymm]
  exact hc U hxU φ V hxV m

/-- Corollary: there exists an `O_{X,x}`-linear isomorphism
`Hom(F,G)_x ≅ Hom_{O_{X,x}}(F_x, G_x)`. -/
theorem AlgebraicGeometry.Scheme.Modules.stalk_internalHom_nonempty_iso {X : AlgebraicGeometry.Scheme.{u}}
    (F G : X.Modules) [F.IsFinitePresentation] (x : X) :
    Nonempty ((AlgebraicGeometry.Scheme.Modules.internalHom F G).stalk x ≅
      ModuleCat.of (X.presheaf.stalk x) (F.stalk x →ₗ[X.presheaf.stalk x] G.stalk x)) :=
  (AlgebraicGeometry.Scheme.Modules.stalk_internalHom_iso F G x).elim fun e _ => ⟨e⟩

end
