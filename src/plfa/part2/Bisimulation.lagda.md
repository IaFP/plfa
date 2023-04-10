---
title     : "Bisimulation: Relating reduction systems"
permalink : /Bisimulation/
---

```agda
module plfa.part2.Bisimulation where
```

Some constructs can be defined in terms of other constructs. In the
previous chapter, we saw how _let_ terms can be rewritten as an
application of an abstraction, and how two alternative formulations of
products — one with projections and one with case — can be formulated
in terms of each other.  In this chapter, we look at how to formalise
such claims.

Given two different systems, with different terms and reduction rules,
we define what it means to claim that one _simulates_ the other.
Let's call our two systems _source_ and _target_.  Let `M`, `N` range
over terms of the source, and `M†`, `N†` range over terms of the
target.  We define a relation

    M ~ M†

between corresponding terms of the two systems. We have a
_simulation_ of the source by the target if every reduction
in the source has a corresponding reduction sequence
in the target:

_Simulation_: For every `M`, `M†`, and `N`:
If `M ~ M†` and `M —→ N`
then `M† —↠ N†` and `N ~ N†`
for some `N†`.

Or, in a diagram:

    M  --- —→ --- N
    |             |
    |             |
    ~             ~
    |             |
    |             |
    M† --- —↠ --- N†

Sometimes we will have a stronger condition, where each reduction in the source
corresponds to a reduction (rather than a reduction sequence)
in the target:

    M  --- —→ --- N
    |             |
    |             |
    ~             ~
    |             |
    |             |
    M† --- —→ --- N†

This stronger condition is known as _lock-step_ or _on the nose_ simulation.

We are particularly interested in the situation where there is also
a simulation from the target to the source: every reduction in the
target has a corresponding reduction sequence in the source.  This
situation is called a _bisimulation_.

@AH: N.B. This is *not* confluence.

(Although I think we haven't covered Confluence yet.)

--------------------------------------------------------------------------------
-- @AH.
-- A bit on motivation.

Let us remember the capital-p Point: We have, at first, meaningless symbols
(syntax). We give these symbols meaning (semantics). How "meaningful" are these
semantics? How do we even phrase an argument that says "our semantics is more
meaningful than the empty semantics?"

 (By the "empty semantics", I refer to the denotation 
  ⟦ M ⟧ = ⊥ 
for all terms M and with codomain = { ⊥ }.)

Previous chapters have answered this question in the form of soundness,
completeness, and so forth. 

However, there are other ways in which we may want to say a language has a
meaningful semantics. In particular, a _translation_ may be meaningful. Consider a
compiler which translates from the source language many times. For example, GHC
translates along this path:

Haskell → (Haskell Core / System FC) → STG → C-- → (C | ASM | LLVM | ...)

(See https://gitlab.haskell.org/ghc/ghc/-/wikis/commentary/compiler/hsc-main).

The obvious question to ask here is "does what I meant when I wrote Haskell code
do what I mean it to do as C vode?" _Simulation_ helps us answer this question.
_Bisimulation_ helps us answer something stronger. 

For example, bisimulations can be used to show *program equivalence*: that if I
have program A and program B, that these are contextually (or observationally)
equivalent in some
way. [Example](https://www.ccs.neu.edu/home/wand/papers/esop-06.pdf).

(And there are many more applications of bisimulation & simulation, of which I
am sure Garrett or Cesare can describe.)

In this chapter, we will use bisimulation to show that the `let` construct could
just as easily be expressed using only λ-I and λ-E. In particular, we show that
the term
  let x := M in N 
is equivalently expressed as
  (λ x. N) M
in the STLC. You can view this as de-sugaring the `let` construct. So, you see 
why the bisimulation result is desirable: it tells us that the syntactic sugar
really was just sugar.

(Note that this equivalence statement is not true in Hindley-Milner systems,
where let-bound terms may be instantiated with polymorphic arguments. So, we
are using `let` statements to demonstrate a case for bisimulation. We are *not*
using bisimulation to show this particular result is broadly true.)

--------------------------------------------------------------------------------

Simulation is established by case analysis over all possible
reductions and all possible terms to which they are related.  For each
reduction step in the source we must show a corresponding reduction
sequence in the target.

For instance, the source might be lambda calculus with _let_
added, and the target the same system with `let` translated out.
The key rule defining our relation will be:

    M ~ M†
    N ~ N†
    --------------------------------
    let x = M in N ~ (ƛ x ⇒ N†) · M†

All the other rules are congruences: variables relate to
themselves, and abstractions and applications relate if their
components relate:

    -----
    x ~ x

    N ~ N†
    ------------------
    ƛ x ⇒ N ~ ƛ x ⇒ N†

    L ~ L†
    M ~ M†
    ---------------
    L · M ~ L† · M†

Covering the other constructs of our language — naturals,
fixpoints, products, and so on — would add little save length.

In this case, our relation can be specified by a function
from source to target:

     _† : 
    (x) †               =  x
    (ƛ x ⇒ N) †         =  ƛ x ⇒ (N †)
    (L · M) †           =  (L †) · (M †)
    (let x = M in N) †  =  (ƛ x ⇒ (N †)) · (M †)

And we have

    M † ≡ N
    -------
    M ~ N

and conversely. But in general we may have a relation without any
corresponding function.

This chapter formalises establishing that `~` as defined
above is a simulation from source to target.  We leave
establishing it in the reverse direction as an exercise.
Another exercise is to show the alternative formulations
of products in
Chapter [More](/More/)
are in bisimulation.


## Imports

We import our source language from
Chapter [More](/More/):
```agda
open import plfa.part2.More
open import Data.Nat
open import Data.Unit
open import Data.Empty
open import Data.Product 
  using (_×_)
  renaming (proj₁ to left ; proj₂ to right ; _,_ to ⟨_,_⟩)

open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (True; toWitness; fromWitness)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong₂; _≢_)
```


## Simulation

The simulation is a straightforward formalisation of the rules
in the introduction:
```agda
infix  4 _~_
infix  5 ~ƛ_
infix  7 _~·_

data _~_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where

  -- Reflexivity.
  ~` : ∀ {Γ A} {x : Γ ∋ A}
     ---------
   → ` x ~ ` x

  -- λ-I Congruence.
  ~ƛ_ : ∀ {Γ A B} {N N† : Γ , A ⊢ B}
    → N ~ N†
      ----------
    → ƛ N ~ ƛ N†

  -- λ-E Congruence.
  _~·_ : ∀ {Γ A B} {L L† : Γ ⊢ A ⇒ B} {M M† : Γ ⊢ A}
    → L ~ L†
    → M ~ M†
      ---------------
    → L · M ~ L† · M†

  -- Translating Let to beta reduction.
  ~let : ∀ {Γ A B} {M M† : Γ ⊢ A} {N N† : Γ , A ⊢ B}
    → M ~ M†
    → N ~ N†
      ----------------------
    → `let M N ~ (ƛ N†) · M†
```
The language in Chapter [More](/More/) has more constructs, which we could easily add.
However, leaving the simulation small lets us focus on the essence.
It's a handy technical trick that we can have a large source language,
but only bother to include in the simulation the terms of interest.

#### Exercise `_†` (practice)

Formalise the translation from source to target given in the introduction.
Show that `M † ≡ N` implies `M ~ N`, and conversely.

**Hint:** For simplicity, we focus on only a few constructs of the language,
so `_†` should be defined only on relevant terms. One way to do this is
to use a decidable predicate to pick out terms in the domain of `_†`, using
[proof by reflection](/Decidable/#proof-by-reflection).

--------------------------------------------------------------------------------
@AH.
So, this is a bit more involved than the **Hint** would have you believe.
We want to restrict our term syntax down to a more manageable subset:
variables, functions, applications, and let statements.

We are going to do so using proof by reflection. To review,
let's give an easier example.

Suppose we have this function `f` that accepts a Nat, but, really, we want it
to only accept Zero (in such a way that passing it anything else would be a
type error.)

(i) We first define a predicate that only zero can satisfy.

```agda
data IsZero : ℕ → Set where
  iszero : IsZero 0
```

(ii) We next show this predicate is decidable.

```agda
decIsZero : ∀ (n : ℕ) → Dec (IsZero n)
decIsZero zero    = yes iszero
decIsZero (suc _) = no (λ ())
```
(iii) We now qualify the function `f` with implicit evidence that n is in
      fact zero. We do so using the `True` predicate. The `True` predicate
      takes a witness of type (Dec P) and smashes it ⊤ if P is true and ⊥
      otherwise.  Thus, an inhabitant of (True (Dec P)) is tt if (Dec P) is
      true, and uninhabitable otherwise. This means Agda is smart enough to
      infer from the evidence {_ : True (decIsZero n)} that we do not need
      to pattern match on the case
          f (suc n) = ...
      as it would be impossible for such a case to occur.
```agda
f : ∀ (n : ℕ) {_ : True (decIsZero n)} → ℕ
f zero = suc zero
```

We will use the same trick to project from the term structure of Part2.More
down to a smaller calculus. (N.B. This is effectively the inverse of the
expression problem [Wadler98]. It's also a PITA.)
--------------------------------------------------------------------------------

```agda
-- (i) Define the predicate.
data Tm-- : ∀ {Γ τ} → Γ ⊢ τ → Set where
  var : ∀ {Γ τ} {x : Γ ∋ τ} → 

        ----------
        Tm-- (` x)

  λI : ∀ {Γ τ τ'} {M : Γ , τ' ⊢ τ} → 
         Tm-- M →
         ----------
         Tm-- (ƛ M)

  λE : ∀ {Γ τ τ'} {M : Γ ⊢ τ ⇒ τ'} {N : Γ ⊢ τ} → 
       Tm-- M →
       Tm-- N → 
       ------------
       Tm-- (M · N)

  LetI : ∀ {Γ τ τ'} {M : Γ ⊢ τ}{N : Γ , τ ⊢ τ'} →

         Tm-- M → 
         Tm-- N →
         ---------------
         Tm-- (`let M N)
  
-- (ii) Show the predicate is decidable.
tm-- : ∀ {Γ τ} → (M : Γ ⊢ τ) → Dec (Tm-- M)
tm-- (` x) = yes var
tm-- (ƛ M) with tm-- M
... | yes P = yes (λI P)
... | no  P = no (λ { (λI ev) → P ev })
tm-- (M · N) with tm-- M | tm-- N
... | yes P₁ | yes P₂ = yes (λE P₁ P₂) 
... | yes _  | no  P₂ = no (λ { (λE _ Tm--N) → P₂ Tm--N }) 
... | no P₁  | yes _ = no (λ { (λE Tm--M _) → P₁ Tm--M })
... | no P₁  | no  _ = no (λ { (λE Tm--M _) → P₁ Tm--M }) 
tm-- (`let M N) with tm-- M | tm-- N
... | yes P₁ | yes P₂ = yes (LetI P₁ P₂)
... | yes _  | no  P₂ = no (λ { (LetI _ Tm--N) → P₂ Tm--N }) 
... | no P₁  | yes _ =  no (λ { (LetI Tm--M _) → P₁ Tm--M }) 
... | no P₁  | no  _ =  no (λ { (LetI Tm--M _) → P₁ Tm--M }) 
tm-- `zero = no (λ ())
tm-- (`suc M) = no (λ ())
tm-- (case M M₁ M₂) = no (λ ())
tm-- (μ M) = no (λ ())
tm-- (con x) = no (λ ())
tm-- (M `* N)  = no (λ ())
tm-- `⟨ M , M₁ ⟩ = no (λ ())
tm-- (`proj₁ M) = no (λ ())
tm-- (`proj₂ M) = no (λ ())
tm-- (case× M M₁) = no (λ ())

-- (iii) Use the predicate to ensure the term M : Γ ⊢ τ is formed only by our
--       restricted syntax.

_† : ∀ {Γ τ} → 
     (M : Γ ⊢ τ) → True (tm-- M) → Γ ⊢ τ
((` x) †) _ = ` x
((ƛ M) †) w with toWitness w
... | λI P = ƛ (_† M (fromWitness P))
((M · N) †) w with toWitness w
... | λE P₁ P₂ = (_† M (fromWitness P₁)) · (_† N (fromWitness P₂))
(`let M N †) w with toWitness w
... | LetI P₁ P₂ = (ƛ (_† N (fromWitness P₂))) · (_† M (fromWitness P₁))

-- Show that `M † ≡ N` iff `M ~ N`.
†⇒~ : ∀ {Γ τ} →
        (M N : Γ ⊢ τ) → 
        (ev : True (tm-- M)) → 
        _† M ev ≡ N → M ~ N
†⇒~ (` x) N ev eq rewrite (sym eq) = ~`
†⇒~ (ƛ M) N ev eq with toWitness ev 
... | λI w-M rewrite (sym eq) = 
  let 
    t = fromWitness w-M
  in ~ƛ †⇒~ M ((M †) t) t refl
†⇒~ (M · M') N ev eq with toWitness ev
... | λE w-M w-M' rewrite (sym eq) =
  let
    t = fromWitness w-M
    t' = fromWitness w-M'
  in (†⇒~ M ((M †) t) t refl) ~· †⇒~ M' ((M' †) t') t' refl
†⇒~ (`let M M') N ev eq with toWitness ev
... | LetI w-M w-M' rewrite (sym eq) = 
  let
    t = fromWitness w-M
    t' = fromWitness w-M'
  in ~let (†⇒~ M ((M †) t) t refl) (†⇒~ M' ((M' †) t') t' refl)

-- And the converse.
†⇐~ : ∀ {Γ τ} →
        (M N : Γ ⊢ τ) → 
        (ev : True (tm-- M)) → 
        M ~ N → _† M ev ≡ N
†⇐~ .(` _) .(` _) ev ~` = refl
†⇐~ .(ƛ _) .(ƛ _) ev (~ƛ s) with toWitness ev
... | λI w rewrite †⇐~ _ _ (fromWitness w) s = refl
†⇐~ .(_ · _) .(_ · _) ev (s ~· s') with toWitness ev
... | λE w-M w-M' rewrite 
  †⇐~ _ _ (fromWitness w-M) s |
  †⇐~ _ _ (fromWitness w-M') s' = refl
†⇐~ .(`let _ _) .((ƛ _) · _) ev (~let s s') with toWitness ev
... | LetI w-M w-M' rewrite
 †⇐~ _ _ (fromWitness w-M) s |
  †⇐~ _ _ (fromWitness w-M') s' = refl
```

## Simulation commutes with values

We need a number of technical results. The first is that simulation
commutes with values.  That is, if `M ~ M†` and `M` is a value then
`M†` is also a value:

@AH:

I like to think of it like this:  if you have the arrows on the top-to-right and
top-to-bottom, you may conclude Value M†. 

```agda
~val : ∀ {Γ A} {M M† : Γ ⊢ A}
  → M ~ M†
  → Value M
    --------
  → Value M†
~val ~`           ()
~val (~ƛ ~N)      V-ƛ  =  V-ƛ
~val (~L ~· ~M)   ()
~val (~let ~M ~N) ()
```
It is a straightforward case analysis, where here the only value
of interest is a lambda abstraction.

#### Exercise `~val⁻¹` (practice)

Show that this also holds in the reverse direction: if `M ~ M†`
and `Value M†` then `Value M`.

@AH:

Now we have:

           ?
    M  ----------- Value M
    |             |
    |             |
  ✓ ~            |
    |             |
    |      ✓     |
    M† ---------- Value M†


```agda
~val⁻¹ : ∀ {Γ A} {M M† : Γ ⊢ A}
  → M ~ M†
  → Value M†
    --------
  → Value M
~val⁻¹ (~ƛ s) V-ƛ = V-ƛ
```


## Simulation commutes with renaming

The next technical result is that simulation commutes with renaming.
That is, if `ρ` maps any judgment `Γ ∋ A` to a judgment `Δ ∋ A`,
and if `M ~ M†` then `rename ρ M ~ rename ρ M†`:

@AH: 

        rename ρ
    M  ----------- rename ρ M
    |             |
    |             |
    ~            ~
    |             |
    |   rename ρ  |
    M† ---------- rename ρ M†


```agda
~rename : ∀ {Γ Δ}
  → (ρ : ∀ {A} → Γ ∋ A → Δ ∋ A)
    ----------------------------------------------------------
  → (∀ {A} {M M† : Γ ⊢ A} → M ~ M† → rename ρ M ~ rename ρ M†)
-- @AH. As we saw in DeBruijn, `ext` is necessary because λ 
-- and let bindings have subdata with extended environments.
~rename ρ (~`)          =  ~`
~rename ρ (~ƛ ~N)       =  ~ƛ (~rename (ext ρ) ~N)
~rename ρ (~L ~· ~M)    =  (~rename ρ ~L) ~· (~rename ρ ~M)
~rename ρ (~let ~M ~N)  =  ~let (~rename ρ ~M) (~rename (ext ρ) ~N)
```
The structure of the proof is similar to the structure of renaming itself:
reconstruct each term with recursive invocation, extending the environment
where appropriate (in this case, only for the body of an abstraction).


## Simulation commutes with substitution

The third technical result is that simulation commutes with substitution.
It is more complex than renaming, because where we had one renaming map
`ρ` here we need two substitution maps, `σ` and `σ†`.

The proof first requires we establish an analogue of extension.
If `σ` and `σ†` both map any judgment `Γ ∋ A` to a judgment `Δ ⊢ A`,
such that for every `x` in `Γ ∋ A` we have `σ x ~ σ† x`,
then for any `x` in `Γ , B ∋ A` we have `exts σ x ~ exts σ† x`:

@AH:
recall that exts is defined as:
  exts : ∀ {Γ Δ} → (∀ {A} → Γ ∋ A → Δ ⊢ A) → (∀ {A B} → Γ , A ∋ B → Δ , A ⊢ B)
  exts σ Z      =  ` Z
  exts σ (S x)  =  rename S_ (σ x)

in other words, exts is repeated renaming. So it follows that
exts also agrees with _~_, as renaming agrees with _~_.

```agda

~exts : ∀ {Γ Δ}
  → {σ  : ∀ {A} → Γ ∋ A → Δ ⊢ A}
  → {σ† : ∀ {A} → Γ ∋ A → Δ ⊢ A}
  → (∀ {A} → (x : Γ ∋ A) → σ x ~ σ† x)
    --------------------------------------------------
  → (∀ {A B} → (x : Γ , B ∋ A) → exts σ x ~ exts σ† x)
~exts ~σ Z      =  ~`
~exts ~σ (S x)  =  ~rename S_ (~σ x)
```
The structure of the proof is similar to the structure of extension itself.
The newly introduced variable trivially relates to itself, and otherwise
we apply renaming to the hypothesis.

With extension under our belts, it is straightforward to show
substitution commutes.  If `σ` and `σ†` both map any judgment `Γ ∋ A`
to a judgment `Δ ⊢ A`, such that for every `x` in `Γ ∋ A` we have `σ
x ~ σ† x`, and if `M ~ M†`, then `subst σ M ~ subst σ† M†`:

@AH:

```agda
~subst : ∀ {Γ Δ}
  → {σ  : ∀ {A} → Γ ∋ A → Δ ⊢ A}
  → {σ† : ∀ {A} → Γ ∋ A → Δ ⊢ A}
  → (∀ {A} → (x : Γ ∋ A) → σ x ~ σ† x)
    ---------------------------------------------------------
  → (∀ {A} {M M† : Γ ⊢ A} → M ~ M† → subst σ M ~ subst σ† M†)
~subst ~σ (~` {x = x})  =  ~σ x
~subst ~σ (~ƛ ~N)       =  ~ƛ (~subst (~exts ~σ) ~N)
~subst ~σ (~L ~· ~M)    =  (~subst ~σ ~L) ~· (~subst ~σ ~M)
~subst ~σ (~let ~M ~N)  =  ~let (~subst ~σ ~M) (~subst (~exts ~σ) ~N)
```
Again, the structure of the proof is similar to the structure of
substitution itself: reconstruct each term with recursive invocation,
extending the environment where appropriate (in this case, only for
the body of an abstraction).

From the general case of substitution, it is also easy to derive
the required special case. If `N ~ N†` and `M ~ M†`, then
`N [ M ] ~ N† [ M† ]`:
```agda
~sub : ∀ {Γ A B} {N N† : Γ , B ⊢ A} {M M† : Γ ⊢ B}
  → N ~ N†
  → M ~ M†
    -----------------------
  → (N [ M ]) ~ (N† [ M† ])
~sub {Γ} {A} {B} ~N ~M = ~subst {Γ , B} {Γ} ~σ {A} ~N
  where
  ~σ : ∀ {A} → (x : Γ , B ∋ A) → _ ~ _
  ~σ Z      =  ~M
  ~σ (S x)  =  ~`
```
Once more, the structure of the proof resembles the original.


## The relation is a simulation

Finally, we can show that the relation actually is a simulation.
In fact, we will show the stronger condition of a lock-step simulation.
What we wish to show is:

_Lock-step simulation_: For every `M`, `M†`, and `N`:
If `M ~ M†` and `M —→ N`
then `M† —→ N†` and `N ~ N†`
for some `N†`.

Or, in a diagram:

    M  --- —→ --- N
    |             |
    |             |
    ~             ~
    |             |
    |             |
    M† --- —→ --- N†

We first formulate a concept corresponding to the lower leg
of the diagram, that is, its right and bottom edges:

@AH: This is just as much for convenience as it is abstraction;
     saves us the bother of writing
       ∀ {N†} → N ~ N† × M† —→ N†
     Note that we are quantifying over *all* N†.
     You may think of this as saying "given top-left part of the diagram,
     I can always give you a bottom right."

```agda
data Leg {Γ A} (M† N : Γ ⊢ A) : Set where

  leg : ∀ {N† : Γ ⊢ A}
    → N ~ N†
    → M† —→ N†
      --------
    → Leg M† N
```
For our formalisation, in this case, we can use a stronger
relation than `—↠`, replacing it by `—→`.

We can now state and prove that the relation is a simulation.
Again, in this case, we can use a stronger relation than
`—↠`, replacing it by `—→`:
```agda
sim : ∀ {Γ A} {M M† N : Γ ⊢ A}
  → M ~ M†
  → M —→ N
    ---------
  → Leg  M† N
-- Let's do this together.
-- Proceed by induction oh both relations.
sim M~M† M—→N = {!!}





-- -- variables and lambdas don't step.
-- sim ~`              ()
-- sim (~ƛ ~N)         ()

-- -- Case:
-- --     → L —→ L′
-- --      ---------------
-- --    → L · M —→ L′ · M
-- sim (~L ~· ~M)      (ξ-·₁ L—→)
--   with sim ~L L—→
-- ...  | leg ~L′ L†—→                 =  leg (~L′ ~· ~M)   (ξ-·₁ L†—→)

-- -- Case:
-- --    → Value V
-- --    → M —→ M′
-- --    ---------------
-- --    → V · M —→ V · M′
-- sim (~V ~· ~M)      (ξ-·₂ VV M—→)
--   with sim ~M M—→
-- ...  | leg ~M′ M†—→                 =  leg (~V ~· ~M′)   (ξ-·₂ (~val ~V VV) M†—→)


-- -- Case:
-- --    → Value V
-- --    --------------------
-- --    → (ƛ N) · V —→ N [ V ]
-- sim ((~ƛ ~N) ~· ~V) (β-ƛ VV)        =  leg (~sub ~N ~V)  (β-ƛ (~val ~V VV))

-- -- Case:
-- --    → M —→ M′
-- --    ---------------------
-- --    → `let M N —→ `let M′ N
-- sim (~let ~M ~N)    (ξ-let M—→)
--   with sim ~M M—→
-- ...  | leg ~M′ M†—→                 =  leg (~let ~M′ ~N) (ξ-·₂ V-ƛ M†—→)

-- -- Case:
-- --  → Value V
-- --     -------------------
-- --  → `let V N —→ N [ V ]

-- sim (~let ~V ~N)    (β-let VV)      =  leg (~sub ~N ~V)  (β-ƛ (~val ~V VV))
```
The proof is by case analysis, examining each possible instance of `M ~ M†`
and each possible instance of `M —→ M†`, using recursive invocation whenever
the reduction is by a `ξ` rule, and hence contains another reduction.
In its structure, it looks a little bit like a proof of progress:

* If the related terms are variables, no reduction applies.
* If the related terms are abstractions, no reduction applies.
* If the related terms are applications, there are three subcases:
  - The source term reduces via `ξ-·₁`, in which case the target term does as well.
    Recursive invocation gives us

        L  --- —→ ---  L′
        |              |
        |              |
        ~              ~
        |              |
        |              |
        L† --- —→ --- L′†

    from which follows:

         L · M  --- —→ ---  L′ · M
           |                   |
           |                   |
           ~                   ~
           |                   |
           |                   |
        L† · M† --- —→ --- L′† · M†

  - The source term reduces via `ξ-·₂`, in which case the target term does as well.
    Recursive invocation gives us

        M  --- —→ ---  M′
        |              |
        |              |
        ~              ~
        |              |
        |              |
        M† --- —→ --- M′†

    from which follows:

         V · M  --- —→ ---  V · M′
           |                  |
           |                  |
           ~                  ~
           |                  |
           |                  |
        V† · M† --- —→ --- V† · M′†

    Since simulation commutes with values and `V` is a value, `V†` is also a value.

  - The source term reduces via `β-ƛ`, in which case the target term does as well:

         (ƛ x ⇒ N) · V  --- —→ ---  N [ x := V ]
              |                           |
              |                           |
              ~                           ~
              |                           |
              |                           |
        (ƛ x ⇒ N†) · V† --- —→ --- N† [ x :=  V† ]

    Since simulation commutes with values and `V` is a value, `V†` is also a value.
    Since simulation commutes with substitution and `N ~ N†` and `V ~ V†`,
    we have `N [ x := V ] ~ N† [ x := V† ]`.

* If the related terms are a let and an application of an abstraction,
  there are two subcases:

  - The source term reduces via `ξ-let`, in which case the target term
    reduces via `ξ-·₂`.  Recursive invocation gives us

        M  --- —→ ---  M′
        |              |
        |              |
        ~              ~
        |              |
        |              |
        M† --- —→ --- M′†

    from which follows:

        let x = M in N --- —→ --- let x = M′ in N
              |                         |
              |                         |
              ~                         ~
              |                         |
              |                         |
        (ƛ x ⇒ N) · M  --- —→ --- (ƛ x ⇒ N) · M′

  - The source term reduces via `β-let`, in which case the target
    term reduces via `β-ƛ`:

        let x = V in N  --- —→ ---  N [ x := V ]
              |                         |
              |                         |
              ~                         ~
              |                         |
              |                         |
        (ƛ x ⇒ N†) · V† --- —→ --- N† [ x := V† ]

    Since simulation commutes with values and `V` is a value, `V†` is also a value.
    Since simulation commutes with substitution and `N ~ N†` and `V ~ V†`,
    we have `N [ x := V ] ~ N† [ x := V† ]`.


#### Exercise `sim⁻¹` (practice)

Show that we also have a simulation in the other direction, and hence that we have
a bisimulation.

--------------------------------------------------------------------------------
@AH:

For a simulation, we suppose that
  M —→ N
  and
  M ~ M†
and then define a Leg,

   data Leg {Γ A} (M† N : Γ ⊢ A) : Set where

     leg : ∀ {N† : Γ ⊢ A}
           → N ~ N†
           → M† —→ N†
           --------
           → Leg M† N

which specifies that the two question marked paths exist.

     M  --- —→ --- N
     |             |
     |             |
     ~             ~  ?
     |             |
     |      ?      |
     M† --- —→ --- N†

So, in English, if M and M† are related and M steps to N, then there exists
N† related to N such that M† steps to N†. In other words: the relation ~ maps 
related inputs to related outputs.

Now, we wish to show the other direction. Visually, split the diagram in half.

     M  --- —→ --- N
     |           / |
     |         /   |
     ~       /     ~   
     |     /       |
     |   /         |
     M† --- —→ --- N†

Before, we assumed the top left (M ~ M† and M —→ N) and showed the bottom
right. We are not going to precisely show the dual -- that would mean assuming
M† —→ N† and N ~ N† and Showing that there exists M related to M† such that 
M —→ N, which is not what we want. Rather, we assume again that M ~ M† and also
 that M† —→ N†, and show that there exists N related to N† such that M —→ N.
  
             ?
     M  --- —→ --- N
     |           / |
     |         /   |
     ~       /     ~ ?
     |     /       |
     |   /         |
     M† --- —→ --- N†

```agda



data Arm {Γ A} (M N† : Γ ⊢ A) : Set where
    arm : ∀ {N : Γ ⊢ A}
        → N ~ N†
        → M —→ N
        --------
        → Arm M N†


sim⁻¹ : ∀ {Γ A} {M M† N† : Γ ⊢ A}
  → M ~ M†
  → M† —→ N†
    ---------
  → Arm M N†

-- Let's do this together.
-- Proceed by induction oh both relations.
sim⁻¹ M~M† M†→N† = {!!}

















-- sim⁻¹ ~` ()
-- sim⁻¹ (~ƛ r) ()
-- sim⁻¹ (~L ~· ~M) (ξ-·₁ L—→) with sim⁻¹ ~L L—→ 
-- ... | arm N~L' L→N = arm (N~L' ~· ~M) (ξ-·₁ L→N)
-- sim⁻¹ (~L ~· ~M) (ξ-·₂ VL† M†—→M') with sim⁻¹ ~M M†—→M'
-- ... | arm N~M' M—→N = arm (~L ~· N~M') (ξ-·₂ (~val⁻¹ ~L VL†) M—→N)
-- sim⁻¹ ((~ƛ ~N) ~· ~M) (β-ƛ VM†) = arm (~sub ~N ~M) (β-ƛ (~val⁻¹ ~M VM†))
-- sim⁻¹ (~let ~M ~N) (ξ-·₂ VƛN† M†—→M') with sim⁻¹ ~M M†—→M' 
-- ... | arm ~N₁ N₁—→M' = arm (~let ~N₁ ~N) (ξ-let N₁—→M')
-- sim⁻¹ (~let ~M ~N) (β-ƛ VM†) = arm (~sub ~N ~M) (β-let (~val⁻¹ ~M VM†))
```

#### Exercise `products` (practice)


Show that the two formulations of products in
Chapter [More](/More/)
are in bisimulation.  The only constructs you need to include are
variables, and those connected to functions and products.
In this case, the simulation is _not_ lock-step.

```agda

data _~'_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where

  -- Reflexivity.
  ~` : ∀ {Γ A} {x : Γ ∋ A}
     ---------
   → (` x) ~' (` x)

  -- λ-I Congruence.
  ~ƛ_ : ∀ {Γ A B} {N N† : Γ , A ⊢ B}
    → N ~ N†
      ----------
    → (ƛ N) ~' (ƛ N†)

  -- λ-E Congruence.
  _~·_ : ∀ {Γ A B} {L L† : Γ ⊢ A ⇒ B} {M M† : Γ ⊢ A}
    → L ~ L†
    → M ~ M†
      ---------------
    → (L · M) ~' (L† · M†)

  -- Congruence for products.
  _~⟨_,_⟩ : ∀ {Γ A B} {L L† : Γ ⊢ A} {M M† : Γ ⊢ B}
    → L ~ L†
    → M ~ M†
    ---------------
    → `⟨ L , M ⟩ ~' `⟨ L† , M† ⟩

  -- -- N.B.
  -- -- We can translate proj₁ and proj₂ to case×,
  -- -- or vice versa. Let's eliminate case×.
  -- ~case× : 

  ~case× : ∀ {Γ A B C} {L L† : Γ ⊢ A} {M M† : Γ ⊢ B} {N N† : Γ ⊢ C}
    → L ~ L†
    → M ~ M†
    → N ~ N†
    ---------------
    → case× `⟨ L , M ⟩ {!N!} ~' {!!} {!!}

  -- -- relating proj₁ to case×.
  -- ~proj₁ : ∀ {Γ A B} {L L† : Γ ⊢ A} {M M† : Γ ⊢ B}
  --   → L ~ L†
  --   → M ~ M†
  --   ---------------
  --   → `proj₁ (`⟨ L , M ⟩) ~' case× `⟨ L† , M† ⟩ (rename (λ x → S (S x)) L†)

  -- ~proj₂ : ∀ {Γ A B} {L L† : Γ ⊢ A} {M M† : Γ ⊢ B}
  --   → L ~ L†
  --   → M ~ M†
  --   ---------------
  --   → `proj₂ (`⟨ L , M ⟩) ~' case× `⟨ L† , M† ⟩ (rename (λ x → S (S x)) M†)

```

## Unicode

This chapter uses the following unicode:

    †  U+2020  DAGGER (\dag)
    ⁻  U+207B  SUPERSCRIPT MINUS (\^-)
    ¹  U+00B9  SUPERSCRIPT ONE (\^1)

--------------------------------------------------------------------------------
-- Bibliography.
--
-- [Wadler 98]
