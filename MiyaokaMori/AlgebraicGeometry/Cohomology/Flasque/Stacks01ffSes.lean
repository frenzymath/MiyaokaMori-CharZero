import MiyaokaMori.Prelude

/-! # Short exact sequences of diagrams for Stacks 01FF

Bookkeeping for the proof of Stacks 01FF (cohomology-lemma-quasi-separated-cohomology-colimit):
* `Stmt F q`: the statement of 01FF in degree `q` for a diagram `F` (surjectivity of
  `colim_j H^q(X, F_j) → H^q(X, colim F)` and "kernel elements die at a later stage");
* for a monomorphism of diagrams `ι : F ⟶ I` in `J ⥤ Sh(X, Ab)`: the short exact sequence
  `sesOf ι = (0 → F → I → coker ι → 0)`, its evaluation `sesAt ι j` at `j` and its colimit `sesColim ι`, both
  short exact (evaluation is exact; filtered colimits are exact in the Grothendieck abelian category `Sh(X, Ab)`,
  Mathlib `IsGrothendieckAbelian`), the morphisms of short complexes `toColimHom ι j : sesAt ι j ⟶ sesColim ι`
  (`colimit.ι`) and `transHom ι a : sesAt ι j ⟶ sesAt ι k`, and the resulting naturality of the connecting
  class `extClass` (`ShortComplex.ShortExact.extClass_naturality`). -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

noncomputable section

namespace Stacks01ff

variable {X : TopCat.{u}} {J : Type u} [SmallCategory J]

/-- The statement of Stacks 01FF in degree `q` for the diagram `F`: the canonical map
`colim_j H^q(X, F_j) → H^q(X, colim F)`, `e ↦ e ∘ mk₀(colimit.ι F j)`, is surjective, and every element of
its kernel dies at a later stage. -/
def Stmt (F : J ⥤ Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (q : ℕ) : Prop :=
  (∀ x : Sheaf.H (colimit F) q, ∃ (j : J) (e : Sheaf.H (F.obj j) q),
      e.comp (Abelian.Ext.mk₀ (colimit.ι F j)) (add_zero q) = x) ∧
  (∀ (j : J) (e : Sheaf.H (F.obj j) q),
      e.comp (Abelian.Ext.mk₀ (colimit.ι F j)) (add_zero q) = 0 →
        ∃ (k : J) (a : j ⟶ k), e.comp (Abelian.Ext.mk₀ (F.map a)) (add_zero q) = 0)

section Step

variable {F I : J ⥤ Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}} (ι : F ⟶ I) [Mono ι]

/-- The short exact sequence of diagrams `0 → F → I → coker ι → 0`. -/
abbrev sesOf : ShortComplex (J ⥤ Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
  ShortComplex.mk ι (cokernel.π ι) (cokernel.condition ι)

theorem sesOf_shortExact : (sesOf ι).ShortExact := { exact := ShortComplex.exact_cokernel ι }

/-- Its value at `j`: `0 → F_j → I_j → (coker ι)_j → 0`. -/
abbrev sesAt (j : J) : ShortComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
  ShortComplex.mk (ι.app j) ((cokernel.π ι).app j)
    (by rw [← NatTrans.comp_app, cokernel.condition]; rfl)

theorem sesAt_shortExact (j : J) : (sesAt ι j).ShortExact :=
  (sesOf_shortExact ι).map_of_exact
    ((evaluation J (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})).obj j)

/-- Its colimit: `0 → colim F → colim I → colim (coker ι) → 0`. -/
abbrev sesColim : ShortComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
  ShortComplex.mk (colimMap ι) (colimMap (cokernel.π ι))
    (by rw [← colim_map, ← colim_map, ← Functor.map_comp, cokernel.condition, Functor.map_zero])

/-- Exactness of filtered colimits (AB5) in the Grothendieck abelian category `Sh(X, Ab)`. -/
theorem sesColim_shortExact [IsFiltered J] : (sesColim ι).ShortExact :=
  haveI : PreservesFiniteColimits
      (colim : (J ⥤ Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) ⥤ _) :=
    ⟨fun _ _ _ => inferInstance⟩
  (sesOf_shortExact ι).map_of_exact colim

/-- `colimit.ι` as a morphism of short complexes `sesAt ι j ⟶ sesColim ι`. -/
abbrev toColimHom (j : J) : sesAt ι j ⟶ sesColim ι where
  τ₁ := colimit.ι F j
  τ₂ := colimit.ι I j
  τ₃ := colimit.ι (cokernel ι) j
  comm₁₂ := ι_colimMap ι j
  comm₂₃ := ι_colimMap (cokernel.π ι) j

/-- The transition map `a : j ⟶ k` as a morphism of short complexes `sesAt ι j ⟶ sesAt ι k`. -/
abbrev transHom {j k : J} (a : j ⟶ k) : sesAt ι j ⟶ sesAt ι k where
  τ₁ := F.map a
  τ₂ := I.map a
  τ₃ := (cokernel ι).map a
  comm₁₂ := ι.naturality a
  comm₂₃ := (cokernel.π ι).naturality a

/-- Naturality of the connecting class along `colimit.ι`. -/
theorem extClass_toColim [IsFiltered J] (j : J) :
    (sesAt_shortExact ι j).extClass.comp (Abelian.Ext.mk₀ (colimit.ι F j)) (add_zero 1) =
      (Abelian.Ext.mk₀ (colimit.ι (cokernel ι) j)).comp (sesColim_shortExact ι).extClass
        (zero_add 1) :=
  ShortComplex.ShortExact.extClass_naturality _ _ (toColimHom ι j)

/-- Naturality of the connecting class along a transition map. -/
theorem extClass_trans {j k : J} (a : j ⟶ k) :
    (sesAt_shortExact ι j).extClass.comp (Abelian.Ext.mk₀ (F.map a)) (add_zero 1) =
      (Abelian.Ext.mk₀ ((cokernel ι).map a)).comp (sesAt_shortExact ι k).extClass (zero_add 1) :=
  ShortComplex.ShortExact.extClass_naturality _ _ (transHom ι a)

end Step

end Stacks01ff

end
