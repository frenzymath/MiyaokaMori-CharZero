import MiyaokaMori.Prelude
import MiyaokaMori.CategoryTheory.CommgrpHasColimits
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.QuotientSheafLocal

/-! # Stalks of the quotient sheaf

The stalk of the quotient sheaf of a morphism `i : G ⟶ F` of sheaves of commutative groups is the
quotient of the stalks: `(F/G)_x ≅ F_x / i_x(G_x)` (exactness of the stalk functor; sheafification
does not change stalks).

Route: instead of the general exactness of the stalk functor, only the two local properties of the
quotient map `π` from `QuotientSheafLocal` are used — `π` is locally surjective and `ker π` lies
locally in `im i` — together with bookkeeping of germs: `π_x` is surjective and
`ker π_x = range i_x`, so `QuotientGroup.lift` induces a bijection.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- `i ≫ quotientπ i` is the trivial homomorphism on every open set: `cokernel.condition` transported
through `sheafCompose` and `CommGrpCat ≌ AddCommGrpCat`; both sides agree by definition. -/

theorem TopCat.Sheaf.comp_quotientπ_hom_app_apply {X : TopCat.{u}} {F G : TopCat.Sheaf CommGrpCat.{u} X}
    (i : G ⟶ F) (U : (Opens X)ᵒᵖ) (s : G.presheaf.obj U) :
    (i ≫ TopCat.Sheaf.quotientπ i).hom.app U s = 1 :=
  ConcreteCategory.congr_hom (congrArg (fun φ => φ.hom.app U)
    (cokernel.condition ((sheafCompose (Opens.grothendieckTopology X)
      commGroupAddCommGroupEquivalence.functor).map i))) (Additive.ofMul s)

/-- A morphism of sheaves that is trivial on every open set is trivial on every stalk (every element
of a stalk is a germ). -/

theorem TopCat.Sheaf.stalkFunctor_map_apply_eq_one {X : TopCat.{u}} {F G : TopCat.Sheaf CommGrpCat.{u} X}
    (φ : G ⟶ F) (hφ : ∀ U s, φ.hom.app U s = 1) (x : X) (t : G.presheaf.stalk x) :
    ((TopCat.Presheaf.stalkFunctor CommGrpCat x).map φ.hom) t = 1 := by
  obtain ⟨U, hx, s, rfl⟩ := G.presheaf.exists_germ_eq t
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply, hφ]
  exact map_one _

/-- `range i_x ≤ ker π_x`: `i ≫ π` is the trivial morphism; take stalks. -/

theorem TopCat.Sheaf.range_stalkFunctor_map_le_ker_quotientπ {X : TopCat.{u}}
    {F G : TopCat.Sheaf CommGrpCat.{u} X} (i : G ⟶ F) (x : X) :
    ((TopCat.Presheaf.stalkFunctor CommGrpCat x).map i.hom).hom.range ≤
      ((TopCat.Presheaf.stalkFunctor CommGrpCat x).map (TopCat.Sheaf.quotientπ i).hom).hom.ker := by
  intro y hy
  obtain ⟨g, rfl⟩ := MonoidHom.mem_range.mp hy
  rw [MonoidHom.mem_ker, ← MonoidHom.comp_apply, ← CommGrpCat.hom_comp, ← Functor.map_comp]
  exact TopCat.Sheaf.stalkFunctor_map_apply_eq_one (i ≫ TopCat.Sheaf.quotientπ i)
    (TopCat.Sheaf.comp_quotientπ_hom_app_apply i) x g

/-- The quotient map is surjective on every stalk: `quotientπ i` is locally surjective
(`TopCat.Sheaf.quotientπ_exists_local`, i.e. `cokernel.π` is an epimorphism of sheaves), every
element of the stalk is the germ of a section `s ∈ (F/G)(W)`, and after restricting `s` to a
neighbourhood `U` of `x` it comes from `g ∈ F(U)`, so `germ s = germ (s|_U) = π_x (germ g)`.
(Stacks 007T: locally surjective iff surjective on stalks.) -/

theorem TopCat.Sheaf.stalkFunctor_map_quotientπ_surjective {X : TopCat.{u}}
    {F G : TopCat.Sheaf CommGrpCat.{u} X} (i : G ⟶ F) (x : X) :
    Function.Surjective
      ((TopCat.Presheaf.stalkFunctor CommGrpCat x).map (TopCat.Sheaf.quotientπ i).hom) := by
  intro t
  obtain ⟨W, hx, s, rfl⟩ := (TopCat.Sheaf.quotient i).presheaf.exists_germ_eq t
  obtain ⟨U, hxU, hUW, g, hg⟩ := TopCat.Sheaf.quotientπ_exists_local i W s x hx
  refine ⟨F.presheaf.germ U x hxU g, ?_⟩
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply, ← hg]
  exact TopCat.Presheaf.germ_res_apply _ (homOfLE hUW) x hxU s

/-- `ker π_x ≤ range i_x`: if `π_x (germ a) = 1`, then `π(a)` and `1` agree on some neighbourhood `V`
of `x` (`germ_eq`), so `π_V (a|_V) = 1`; the kernel of the quotient map lies locally in the image of
`i` (`TopCat.Sheaf.exists_local_preimage_of_quotientπ_eq_one`: `im i ↪ F` is the kernel of
`cokernel.π`, kernels are computed sectionwise, and `G ↠ im i` is locally surjective), so on a
smaller neighbourhood `V'` we have `a|_{V'} = i(b)`, whence `germ a = germ (a|_{V'}) = i_x (germ b)`.
This is the middle term of the exactness of the stalk functor (Stacks 04EP / 01AJ(3)), obtained
here from the two local properties alone. -/

theorem TopCat.Sheaf.ker_stalkFunctor_map_quotientπ_le_range {X : TopCat.{u}}
    {F G : TopCat.Sheaf CommGrpCat.{u} X} (i : G ⟶ F) (x : X) :
    ((TopCat.Presheaf.stalkFunctor CommGrpCat x).map (TopCat.Sheaf.quotientπ i).hom).hom.ker ≤
      ((TopCat.Presheaf.stalkFunctor CommGrpCat x).map i.hom).hom.range := by
  intro y hy
  rw [MonoidHom.mem_ker] at hy
  obtain ⟨W, hx, a, rfl⟩ := F.presheaf.exists_germ_eq y
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply] at hy
  have h1 : (TopCat.Sheaf.quotient i).presheaf.germ W x hx
        ((TopCat.Sheaf.quotientπ i).hom.app (op W) a) =
      (TopCat.Sheaf.quotient i).presheaf.germ W x hx 1 := by
    rw [map_one]; exact hy
  obtain ⟨V, hxV, iV, iV', hVW⟩ := (TopCat.Sheaf.quotient i).presheaf.germ_eq x hx hx _ _ h1
  rw [Subsingleton.elim iV' iV] at hVW
  have h2 : (TopCat.Sheaf.quotientπ i).hom.app (op V) (F.presheaf.map iV.op a) = 1 := by
    have hnat := ConcreteCategory.congr_hom ((TopCat.Sheaf.quotientπ i).hom.naturality iV.op) a
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hnat
    rw [hnat]
    exact hVW.trans (map_one _)
  obtain ⟨V', hxV', hV'V, b, hb⟩ :=
    TopCat.Sheaf.exists_local_preimage_of_quotientπ_eq_one i V (F.presheaf.map iV.op a) h2 x hxV
  refine ⟨G.presheaf.germ V' x hxV' b, ?_⟩
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply, hb]
  exact (TopCat.Presheaf.germ_res_apply _ (homOfLE hV'V) x hxV' _).trans
    (TopCat.Presheaf.germ_res_apply _ iV x hxV a)

/-- The map `F_x / i_x(G_x) → (F/G)_x` induced by `π_x` is bijective (Stacks 007T / 01AJ(3):
exactness of the stalk functor, and sheafification does not change stalks).

Proof: surjective because `π_x` is (`stalkFunctor_map_quotientπ_surjective`); injective because
`ker π_x = range i_x` (`≥` is `range_stalkFunctor_map_le_ker_quotientπ`, `≤` is
`ker_stalkFunctor_map_quotientπ_le_range`), by `QuotientGroup.injective_lift_iff`. -/

theorem TopCat.Sheaf.quotientStalkIso_lift_bijective {X : TopCat.{u}} {F G : TopCat.Sheaf CommGrpCat.{u} X}
    (i : G ⟶ F) [CategoryTheory.Mono i] (x : X) :
    Function.Bijective
      (QuotientGroup.lift ((TopCat.Presheaf.stalkFunctor CommGrpCat x).map i.hom).hom.range
        ((TopCat.Presheaf.stalkFunctor CommGrpCat x).map (TopCat.Sheaf.quotientπ i).hom).hom
        (TopCat.Sheaf.range_stalkFunctor_map_le_ker_quotientπ i x)) := by
  refine ⟨?_, QuotientGroup.lift_surjective_of_surjective _ _
    (TopCat.Sheaf.stalkFunctor_map_quotientπ_surjective i x) _⟩
  rw [QuotientGroup.injective_lift_iff]
  exact le_antisymm (TopCat.Sheaf.range_stalkFunctor_map_le_ker_quotientπ i x)
    (TopCat.Sheaf.ker_stalkFunctor_map_quotientπ_le_range i x)

/-- The stalk of the quotient sheaf is the quotient of the stalks: `(F/G)_x ≅ F_x / i_x(G_x)`. -/
noncomputable def TopCat.Sheaf.quotientStalkIso {X : TopCat.{u}} {F G : TopCat.Sheaf CommGrpCat.{u} X}
    (i : G ⟶ F) [CategoryTheory.Mono i] (x : X) :
    (TopCat.Sheaf.quotient i).presheaf.stalk x ≅
      CommGrpCat.of (F.presheaf.stalk x ⧸ ((TopCat.Presheaf.stalkFunctor CommGrpCat x).map i.hom).hom.range) :=
  -- the stalk map F_x → (F/G)_x of π kills the image of i_x (`range_stalkFunctor_map_le_ker_quotientπ`)
  -- and induces a bijection on the quotient (`quotientStalkIso_lift_bijective`); the forward map is
  -- constructed, the inverse is determined by bijectivity
  (MulEquiv.ofBijective
    (QuotientGroup.lift ((TopCat.Presheaf.stalkFunctor CommGrpCat x).map i.hom).hom.range
      ((TopCat.Presheaf.stalkFunctor CommGrpCat x).map (TopCat.Sheaf.quotientπ i).hom).hom
      (TopCat.Sheaf.range_stalkFunctor_map_le_ker_quotientπ i x))
    (TopCat.Sheaf.quotientStalkIso_lift_bijective i x)).symm.toCommGrpIso

end
