import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S2WeightedJets.Cone.PuncturedConeIsPuncturedLineBundleBackwardTransport

/-! # Two-spelling transport for the backward morphism

Variable-level companion of `…BackwardTransport` (all schemes, morphisms and sections are variables),
used in `MiyaokaMori.Paper.S2WeightedJets.Cone.PuncturedConeIsPuncturedLineBundleBackward`
to prove `hom_isTotalSpaceToConeHom`.

**Why a second module.** The body of `def IsTotalSpaceToConeHom` (module `…Contract`) carries
*abstracted instance proofs* (`conePuncturedLineBundle.eval._proof_1 : HasPullback …`,
`IsConeToTotalSpaceHom._proof_3/_proof_4`; visible with `pp.explicit`), while every theorem statement elaborated
elsewhere carries the inline instances (`Scheme.Pullback.instHasPullback` etc.). The two spellings are
proof-irrelevant, but they sit under `DFunLike.coe` / `Functor.obj` heads, and comparing two such terms that differ
only inside makes both the elaborator and the kernel unfold `Modules.pullback`/`pullbackComp` down to linear maps
(a single such `rfl` can take more than a minute). The way out is to **never compare the two
spellings at the level of sections**: `coordinate_transport_two` has one variable per datum in the goal spelling
(`S β π pr₁ z …`) and one per datum in the spelling of the available facts (`S' β' π' pr₁' z' …`), related by
equations that are only ever checked at the level of schemes and morphisms (`Eq`/`HEq`, discharged by `rfl`),
and all implicit arguments come first so that the conclusion is unified with the goal *before* any explicit
argument (whose type carries the other spelling) is elaborated. The remaining `hts`/`hy` pair lets the unfolding of
`puncturedConeToProduct.coordOverProduct` (whose abstracted proof `coordOverProduct._proof_1` is not
`(comp_fst …).symm` syntactically) be matched by `delta … ; rfl`, again without retyping anything.

Source: eq. (2.1) of the paper (the definition `β^*z_i = z_i` of `β`); categorical bookkeeping. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

/-- `coordinate_transport_of` with the base equation in the form `hts : t = g ≫ pr₁` (so that `pullbackCongr hts`
is exactly the transport appearing in the unfolding of `puncturedConeToProduct.coordOverProduct`). -/
theorem coordinate_transport_of_ts {S T P C : AlgebraicGeometry.Scheme.{u}} (β : S ⟶ T) (g : T ⟶ P) (π : S ⟶ P)
    (hβ : β ≫ g = π) (pr₁ : P ⟶ C) (t : T ⟶ C) (hts : t = g ≫ pr₁) (hπ : β ≫ t = π ≫ pr₁) (A : C.Modules)
    (x : (((pullback t).obj A).val.obj (Opposite.op ⊤) : Type u))
    (z : (((pullback π).obj ((pullback pr₁).obj A)).val.obj (Opposite.op ⊤) : Type u))
    (hx : (((pullbackCongr hπ).hom.app A).val.app (Opposite.op ⊤)).hom
        ((((pullbackComp β t).hom.app A).val.app (Opposite.op ⊤)).hom (sectionPullbackAlong β x))
      = (((pullbackComp π pr₁).hom.app A).val.app (Opposite.op ⊤)).hom z) :
    ((pullbackCongr hβ).hom.app _).app ⊤
        (((pullbackComp β g).hom.app _).app ⊤
          (sectionPullbackAlong β
            (((pullbackComp g pr₁).inv.app A).app ⊤ (((pullbackCongr hts).hom.app A).app ⊤ x)))) = z := by
  subst hts
  exact coordinate_transport_of β g π hβ pr₁ _ rfl hπ A x z hx

/-- **Two-spelling form of the coordinate identity of `IsTotalSpaceToConeHom`.** Every scheme, morphism and
section that occurs in the goal in one spelling (the abstracted instance proofs of the body of
`IsTotalSpaceToConeHom`) and in the available facts in another (the inline instances of their statements) is a
separate variable — unprimed for the goal, primed for the facts — related by an equation (`Eq` for schemes, `HEq`
for morphisms and sections), so that at the use site each of them is matched only against its own spelling. All
implicit arguments come first, so that the conclusion is unified with the goal before any explicit argument is
elaborated (see the module docstring). Use: `exact coordinate_transport_two hπ x (by delta …; rfl) hx rfl rfl
HEq.rfl HEq.rfl HEq.rfl HEq.rfl`. -/
theorem coordinate_transport_two {S S' T P P' C : AlgebraicGeometry.Scheme.{u}} {β : S ⟶ T} {β' : S' ⟶ T}
    {g : T ⟶ P} {π : S ⟶ P} {π' : S' ⟶ P'} {hβ₀ : β ≫ g = π} {pr₁ : P ⟶ C} {pr₁' : P' ⟶ C} {t : T ⟶ C}
    {hts : t = g ≫ pr₁} {A : C.Modules}
    {y : (((pullback g).obj ((pullback pr₁).obj A)).val.obj (Opposite.op ⊤) : Type u)}
    {z : (((pullback π).obj ((pullback pr₁).obj A)).val.obj (Opposite.op ⊤) : Type u)}
    {z' : (((pullback π').obj ((pullback pr₁').obj A)).val.obj (Opposite.op ⊤) : Type u)}
    (hπ : β' ≫ t = π' ≫ pr₁') (x : (((pullback t).obj A).val.obj (Opposite.op ⊤) : Type u))
    (hy : y = ((pullbackComp g pr₁).inv.app A).app ⊤ (((pullbackCongr hts).hom.app A).app ⊤ x))
    (hx : (((pullbackCongr hπ).hom.app A).val.app (Opposite.op ⊤)).hom
        ((((pullbackComp β' t).hom.app A).val.app (Opposite.op ⊤)).hom (sectionPullbackAlong β' x))
      = (((pullbackComp π' pr₁').hom.app A).val.app (Opposite.op ⊤)).hom z')
    (hS : S' = S) (hP : P' = P) (hβ : HEq β' β) (hπ' : HEq π' π) (hpr : HEq pr₁' pr₁) (hz : HEq z z') :
    ((pullbackCongr hβ₀).hom.app _).app ⊤
        (((pullbackComp β g).hom.app _).app ⊤ (sectionPullbackAlong β y)) = z := by
  subst hS hP
  have e1 := eq_of_heq hβ
  have e2 := eq_of_heq hπ'
  have e3 := eq_of_heq hpr
  subst e1 e2 e3
  have e4 := eq_of_heq hz
  subst e4 hy
  exact coordinate_transport_of_ts _ _ _ hβ₀ _ _ hts hπ _ x _ hx

end AlgebraicGeometry.Scheme.Modules

end
