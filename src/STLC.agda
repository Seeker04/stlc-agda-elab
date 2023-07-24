{-# OPTIONS --prop --rewriting --guardedness #-}

module STLC where

-- Most of the code in this file is Ambrus Kaposi's work taken from: https://bitbucket.org/akaposi/typesystems/src/master/
--   * STT, Fin, Ind and Coind languages were merged into this single one
--   * dependency on that project's Lib.lagda was replaced with usage of agda-stdlib
--   * here follows a brief summary, but to learn more about these concepts, please refer to the linked projects's main.pdf

-- Our object theory (using Agda as the meta theory) is based on STLC (Simply Typed Lambda Calculus)
--
-- It has types and constructors/destructors for:
--   * function space
--   * finite types: booleans, nullary and binary products and sums
--   * inductive types: naturals, lists, trees (and their iterators)
--   * coinductive types: streams, machines
--   * a few additional built-in operators
--
-- Variable bindings are formalised using De Bruijn indices and
-- substitution calculus (a simply typed category with families)
--
-- The model is quotiented by equations between syntactic terms
-- (program equivalence can be proven using equational reasoning for example)
--
-- We define a standard model and an interpretation into it for a bridge to our metatheory
-- We can use this as an evaluator, because Agda can normalise the resuling terms for us

open import Agda.Primitive using (lsuc; _⊔_)
open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Data.Bool renaming (Bool to 𝟚; true to tt; false to ff)
open import Data.Product using (_×_; _,_) renaming (proj₁ to π₁; proj₂ to π₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Relation.Binary.PropositionalEquality.Core
open ≡-Reasoning

infix 4 _≈_
postulate _≈_ : ∀{ℓ}{A : Set ℓ}(a : A) → A → Set ℓ
{-# BUILTIN REWRITE _≈_ #-}

postulate transp     : ∀{ℓ}{A : Set ℓ}{ℓ'}(P : A → Set ℓ'){a a' : A} → a ≡ a' → P a → P a'
postulate transprefl : ∀{ℓ}{A : Set ℓ}{ℓ'}{P : A → Set ℓ'}{a : A}{e : a ≡ a}{p : P a} → transp P e p ≈ p
{-# REWRITE transprefl #-}

postulate funext : ∀{ℓ}{A : Set ℓ}{ℓ'}{B : A → Set ℓ'}{f g : (x : A) → B x} → ((x : A) → f x ≡ g x) → f ≡ g

_,×=_ : ∀{ℓ}{A : Set ℓ}{ℓ'}{B : Set ℓ'}{a a' : A}(e : a ≡ a') → {b b' : B} → b  ≡ b' → (a , b) ≡ (a' , b')
_,×=_ refl refl = refl

ind⊎ : ∀{ℓ ℓ' ℓ''}{A : Set ℓ}{B : Set ℓ'}(P : A ⊎ B → Set ℓ'') →
       ((a : A) → P (inj₁ a)) → ((b : B) → P (inj₂ b)) → (t : A ⊎ B) → P t
ind⊎ P u v (inj₁ t) = u t
ind⊎ P u v (inj₂ t) = v t

iteℕ : ∀{ℓ}{A : Set ℓ}(u : A)(v : A → A)(t : ℕ) → A
iteℕ u v zero = u
iteℕ u v (suc t) = v (iteℕ u v t)

--------------------------------------
-- Initial model (syntax), can be interpreted into any model (i.e., there is a homomorphism from here to any model)

module I where
  infixl 6 _⊚_
  infixl 6 _[_]
  infixl 5 _▹_
  infixl 5 _,o_
  infixr 5 _⇒_
  infixl 5 _$_

  data Ty      : Set where
    _⇒_        : Ty → Ty → Ty
    _×o_       : Ty → Ty → Ty
    Unit       : Ty
    _+o_       : Ty → Ty → Ty
    Empty      : Ty
    Bool       : Ty
    Nat        : Ty
    List       : Ty → Ty
    Tree       : Ty → Ty
    Stream     : Ty → Ty
    Machine    : Ty

  data Con     : Set where
    ◇          : Con
    _▹_        : Con → Ty → Con

  postulate
    Sub        : Con → Con → Set
    _⊚_        : ∀{Γ Δ Θ} → Sub Δ Γ → Sub Θ Δ → Sub Θ Γ
    ass        : ∀{Γ Δ Θ Ξ}{γ : Sub Δ Γ}{δ : Sub Θ Δ}{θ : Sub Ξ Θ} → (γ ⊚ δ) ⊚ θ ≡ γ ⊚ (δ ⊚ θ)
    id         : ∀{Γ} → Sub Γ Γ
    idl        : ∀{Γ Δ}{γ : Sub Δ Γ} → id ⊚ γ ≡ γ
    idr        : ∀{Γ Δ}{γ : Sub Δ Γ} → γ ⊚ id ≡ γ

    ε          : ∀{Γ} → Sub Γ ◇
    ◇η         : ∀{Γ}{σ : Sub Γ ◇} → σ ≡ ε

    Tm         : Con → Ty → Set
    _[_]       : ∀{Γ Δ A} → Tm Γ A → Sub Δ Γ → Tm Δ A
    [∘]        : ∀{Γ Δ Θ A}{t : Tm Γ A}{γ : Sub Δ Γ}{δ : Sub Θ Δ} →  t [ γ ⊚ δ ] ≡ t [ γ ] [ δ ]
    [id]       : ∀{Γ A}{t : Tm Γ A} → t [ id ] ≡ t
    _,o_       : ∀{Γ Δ A} → Sub Δ Γ → Tm Δ A → Sub Δ (Γ ▹ A)
    p          : ∀{Γ A} → Sub (Γ ▹ A) Γ
    q          : ∀{Γ A} → Tm (Γ ▹ A) A
    ▹β₁        : ∀{Γ Δ A}{γ : Sub Δ Γ}{t : Tm Δ A} → p ⊚ (γ ,o t) ≡ γ
    ▹β₂        : ∀{Γ Δ A}{γ : Sub Δ Γ}{t : Tm Δ A} → q [ γ ,o t ] ≡ t
    ▹η         : ∀{Γ Δ A}{γa : Sub Δ (Γ ▹ A)} → p ⊚ γa ,o q [ γa ] ≡ γa

    lam        : ∀{Γ A B} → Tm (Γ ▹ A) B → Tm Γ (A ⇒ B)
    _$_        : ∀{Γ A B} → Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B
    ⇒β         : ∀{Γ A B}{t : Tm (Γ ▹ A) B}{u : Tm Γ A} → lam t $ u ≡ t [ id ,o u ]
    ⇒η         : ∀{Γ A B}{t : Tm Γ (A ⇒ B)} → lam (t [ p ] $ q) ≡ t
    lam[]      : ∀{Γ A B}{t : Tm (Γ ▹ A) B}{Δ}{γ : Sub Δ Γ} →
                 (lam t) [ γ ] ≡ lam (t [ γ ⊚ p ,o q ])
    $[]        : ∀{Γ A B}{t : Tm Γ (A ⇒ B)}{u : Tm Γ A}{Δ}{γ : Sub Δ Γ} →
                 (t $ u) [ γ ] ≡ t [ γ ] $ u [ γ ]

    ⟨_,_⟩     : ∀{Γ A B} → Tm Γ A → Tm Γ B → Tm Γ (A ×o B)
    fst       : ∀{Γ A B} → Tm Γ (A ×o B) → Tm Γ A
    snd       : ∀{Γ A B} → Tm Γ (A ×o B) → Tm Γ B
    ×β₁       : ∀{Γ A B}{u : Tm Γ A}{v : Tm Γ B} → fst ⟨ u , v ⟩ ≡ u
    ×β₂       : ∀{Γ A B}{u : Tm Γ A}{v : Tm Γ B} → snd ⟨ u , v ⟩ ≡ v
    ×η        : ∀{Γ A B}{t : Tm Γ (A ×o B)} → ⟨ fst t , snd t ⟩ ≡ t
    ,[]       : ∀{Γ A B}{u : Tm Γ A}{v : Tm Γ B}{Δ}{γ : Sub Δ Γ} →
                ⟨ u , v ⟩ [ γ ] ≡ ⟨ u [ γ ] , v [ γ ] ⟩

    trivial    : ∀{Γ} → Tm Γ Unit
    iteUnit    : ∀{Γ A} → Tm Γ A → Tm Γ Unit → Tm Γ A
    Unitβ      : ∀{Γ A t} → iteUnit {Γ}{A} t trivial ≡ t
    Unitη      : ∀{Γ}{u : Tm Γ Unit} → u ≡ trivial
    trivial[]  : ∀{Γ Δ}{γ : Sub Δ Γ} → trivial [ γ ] ≡ trivial
    iteUnit[]  : ∀{Γ A t u Δ}{γ : Sub Δ Γ} →
                 iteUnit {Γ}{A} u t [ γ ] ≡ iteUnit (u [ γ ]) (t [ γ ])

    inl       : ∀{Γ A B} → Tm Γ A → Tm Γ (A +o B)
    inr       : ∀{Γ A B} → Tm Γ B → Tm Γ (A +o B)
    caseo     : ∀{Γ A B C} → Tm (Γ ▹ A) C → Tm (Γ ▹ B) C → Tm (Γ ▹ A +o B) C
    +β₁       : ∀{Γ A B C}{u : Tm (Γ ▹ A) C}{v : Tm (Γ ▹ B) C}{t : Tm Γ A} →
                caseo u v [ id ,o inl t ] ≡ u [ id ,o t ]
    +β₂       : ∀{Γ A B C}{u : Tm (Γ ▹ A) C}{v : Tm (Γ ▹ B) C}{t : Tm Γ B} →
                caseo u v [ id ,o inr t ] ≡ v [ id ,o t ]
    +η        : ∀{Γ A B C}{t : Tm (Γ ▹ A +o B) C} →
                caseo (t [ p ,o inl q ]) (t [ p ,o inr q ]) ≡ t
    inl[]     : ∀{Γ A B}{t : Tm Γ A}{Δ}{γ : Sub Δ Γ} →
                (inl {B = B} t) [ γ ] ≡ inl (t [ γ ])
    inr[]     : ∀{Γ A B}{t : Tm Γ B}{Δ}{γ : Sub Δ Γ} →
                (inr {A = A} t) [ γ ] ≡ inr (t [ γ ])
    case[]    : ∀{Γ A B C}{u : Tm (Γ ▹ A) C}{v : Tm (Γ ▹ B) C}{Δ}{γ : Sub Δ Γ} →
                (caseo u v) [ γ ⊚ p ,o q ] ≡
                caseo (u [ γ ⊚ p ,o q ]) (v [ γ ⊚ p ,o q ])

    absurd    : ∀{Γ A} → Tm (Γ ▹ Empty) A
    Emptyη    : ∀{Γ A}{t : Tm (Γ ▹ Empty) A} → t ≡ absurd

    true       : ∀{Γ} → Tm Γ Bool
    false      : ∀{Γ} → Tm Γ Bool
    iteBool    : ∀{Γ A} → Tm Γ A → Tm Γ A → Tm Γ Bool → Tm Γ A
    Boolβ₁     : ∀{Γ A u v} → iteBool {Γ}{A} u v true ≡ u
    Boolβ₂     : ∀{Γ A u v} → iteBool {Γ}{A} u v false ≡ v
    true[]     : ∀{Γ Δ}{γ : Sub Δ Γ} → true [ γ ] ≡ true
    false[]    : ∀{Γ Δ}{γ : Sub Δ Γ} → false [ γ ] ≡ false
    iteBool[]  : ∀{Γ A t u v Δ}{γ : Sub Δ Γ} →
                 iteBool {Γ}{A} u v t [ γ ] ≡ iteBool (u [ γ ]) (v [ γ ]) (t [ γ ])

    zeroo      : ∀{Γ} → Tm Γ Nat
    suco       : ∀{Γ} → Tm Γ Nat → Tm Γ Nat
    iteNat     : ∀{Γ A} → Tm Γ A → Tm (Γ ▹ A) A → Tm Γ Nat → Tm Γ A
    Natβ₁      : ∀{Γ A}{u : Tm Γ A}{v : Tm (Γ ▹ A) A} → iteNat u v zeroo ≡ u
    Natβ₂      : ∀{Γ A}{u : Tm Γ A}{v : Tm (Γ ▹ A) A}{t : Tm Γ Nat} →
                 iteNat u v (suco t) ≡ v [ id ,o iteNat u v t ]
    zero[]     : ∀{Γ Δ}{γ : Sub Δ Γ} → zeroo [ γ ] ≡ zeroo
    suc[]      : ∀{Γ}{t : Tm Γ Nat}{Δ}{γ : Sub Δ Γ} → (suco t) [ γ ] ≡ suco (t [ γ ])
    iteNat[]   : ∀{Γ A}{u : Tm Γ A}{v : Tm (Γ ▹ A) A}{t : Tm Γ Nat}{Δ}{γ : Sub Δ Γ} →
                 iteNat u v t [ γ ] ≡ iteNat (u [ γ ]) (v [ γ ⊚ p ,o q ]) (t [ γ ])

    nil        : ∀{Γ A} → Tm Γ (List A)
    cons       : ∀{Γ A} → Tm Γ A → Tm Γ (List A) → Tm Γ (List A)
    iteList    : ∀{Γ A B} → Tm Γ B → Tm (Γ ▹ A ▹ B) B → Tm Γ (List A) → Tm Γ B
    Listβ₁     : ∀{Γ A B}{u : Tm Γ B}{v : Tm (Γ ▹ A ▹ B) B} → iteList u v nil ≡ u
    Listβ₂     : ∀{Γ A B}{u : Tm Γ B}{v : Tm (Γ ▹ A ▹ B) B}{t₁ : Tm Γ A}{t : Tm Γ (List A)} →
                 iteList u v (cons t₁ t) ≡ (v [ id ,o t₁ ,o iteList u v t ])
    nil[]      : ∀{Γ A Δ}{γ : Sub Δ Γ} → nil {Γ}{A} [ γ ] ≡ nil {Δ}{A}
    cons[]     : ∀{Γ A}{t₁ : Tm Γ A}{t : Tm Γ (List A)}{Δ}{γ : Sub Δ Γ} →
                 (cons t₁ t) [ γ ] ≡ cons (t₁ [ γ ]) (t [ γ ])
    iteList[]  : ∀{Γ A B}{u : Tm Γ B}{v : Tm (Γ ▹ A ▹ B) B}{t : Tm Γ (List A)}{Δ}{γ : Sub Δ Γ} →
                 iteList u v t [ γ ] ≡ iteList (u [ γ ]) (v [ (γ ⊚ p ,o q) ⊚ p ,o q ]) (t [ γ ])

    leaf       : ∀{Γ A} → Tm Γ A → Tm Γ (Tree A)
    node       : ∀{Γ A} → Tm Γ (Tree A) → Tm Γ (Tree A) → Tm Γ (Tree A)
    iteTree    : ∀{Γ A B} → Tm (Γ ▹ A) B → Tm (Γ ▹ B ▹ B) B → Tm Γ (Tree A) → Tm Γ B
    Treeβ₁     : ∀{Γ A B}{l : Tm (Γ ▹ A) B}{n : Tm (Γ ▹ B ▹ B) B}{a : Tm Γ A} → iteTree l n (leaf a) ≡ l [ id ,o a ]
    Treeβ₂     : ∀{Γ A B}{l : Tm (Γ ▹ A) B}{n : Tm (Γ ▹ B ▹ B) B}{ll rr : Tm Γ (Tree A)} →
                 iteTree l n (node ll rr) ≡ n [ id ,o iteTree l n ll ,o iteTree l n rr ]
    leaf[]     : ∀{Γ A}{a : Tm Γ A}{Δ}{γ : Sub Δ Γ} → (leaf a) [ γ ] ≡ leaf (a [ γ ])
    node[]     : ∀{Γ A}{ll rr : Tm Γ (Tree A)}{Δ}{γ : Sub Δ Γ} →
                 (node ll rr) [ γ ] ≡ node (ll [ γ ]) (rr [ γ ])
    iteTree[]  : ∀{Γ A B}{l : Tm (Γ ▹ A) B}{n : Tm (Γ ▹ B ▹ B) B}{t : Tm Γ (Tree A)}{Δ}{γ : Sub Δ Γ} →
                 iteTree l n t [ γ ] ≡ iteTree (l [ (γ ⊚ p) ,o q ]) (n [ (γ ⊚ p ⊚ p) ,o (q [ p ]) ,o q ]) (t [ γ ])

    head          : ∀{Γ A} → Tm Γ (Stream A) → Tm Γ A
    tail          : ∀{Γ A} → Tm Γ (Stream A) → Tm Γ (Stream A)
    genStream     : ∀{Γ A C} → Tm (Γ ▹ C) A → Tm (Γ ▹ C) C → Tm Γ C → Tm Γ (Stream A)
    Streamβ₁      : ∀{Γ A C}{u : Tm (Γ ▹ C) A}{v : Tm (Γ ▹ C) C}{t : Tm Γ C} →
                    head (genStream u v t) ≡ u [ id ,o t ]
    Streamβ₂      : ∀{Γ A C}{u : Tm (Γ ▹ C) A}{v : Tm (Γ ▹ C) C}{t : Tm Γ C} →
                    tail (genStream u v t) ≡ genStream u v (v [ id ,o t ])
    head[]        : ∀{Γ A}{as : Tm Γ (Stream A)}{Δ}{γ : Sub Δ Γ} →
                    head as [ γ ] ≡ head (as [ γ ])
    tail[]        : ∀{Γ A}{as : Tm Γ (Stream A)}{Δ}{γ : Sub Δ Γ} → tail as [ γ ] ≡ tail (as [ γ ])
    genStream[]   : ∀{Γ A C}{u : Tm (Γ ▹ C) A}{v : Tm (Γ ▹ C) C}{t : Tm Γ C}{Δ}
                    {γ : Sub Δ Γ} →
                    genStream u v t [ γ ] ≡ genStream (u [ γ ⊚ p ,o q ]) (v [ γ ⊚ p ,o q ]) (t [ γ ])

    put           : ∀{Γ} → Tm Γ Machine → Tm Γ Nat → Tm Γ Machine
    set           : ∀{Γ} → Tm Γ Machine → Tm Γ Machine
    get           : ∀{Γ} → Tm Γ Machine → Tm Γ Nat
    genMachine    : ∀{Γ C} → Tm (Γ ▹ C ▹ Nat) C → Tm (Γ ▹ C) C → Tm (Γ ▹ C) Nat →
                    Tm Γ C → Tm Γ Machine
    Machineβ₁     : ∀{Γ C}{u : Tm (Γ ▹ C ▹ Nat) C}{v : Tm (Γ ▹ C) C}{w : Tm (Γ ▹ C) Nat}
                    {t : Tm Γ C}{t' : Tm Γ Nat} →
                    put (genMachine u v w t) t' ≡ genMachine u v w (u [ id ,o t ,o t' ])
    Machineβ₂     : ∀{Γ C}{u : Tm (Γ ▹ C ▹ Nat) C}{v : Tm (Γ ▹ C) C}{w : Tm (Γ ▹ C) Nat}
                    {t : Tm Γ C} →
                    set (genMachine u v w t) ≡ genMachine u v w (v [ id ,o t ])
    Machineβ₃     : ∀{Γ C}{u : Tm (Γ ▹ C ▹ Nat) C}{v : Tm (Γ ▹ C) C}{w : Tm (Γ ▹ C) Nat}
                    {t : Tm Γ C} →
                    get (genMachine u v w t) ≡ w [ id ,o t ]
    put[]         : ∀{Γ}{t : Tm Γ Machine}{u : Tm Γ Nat}{Δ}{γ : Sub Δ Γ} →
                    put t u [ γ ] ≡ put (t [ γ ]) (u [ γ ])
    set[]         : ∀{Γ}{t : Tm Γ Machine}{Δ}{γ : Sub Δ Γ} → set t [ γ ] ≡ set (t [ γ ])
    get[]         : ∀{Γ}{t : Tm Γ Machine}{Δ}{γ : Sub Δ Γ} → get t [ γ ] ≡ get (t [ γ ])
    genMachine[]  : ∀{Γ C}{u : Tm (Γ ▹ C ▹ Nat) C}{v : Tm (Γ ▹ C) C}{w : Tm (Γ ▹ C) Nat}
                    {t : Tm Γ C}{Δ}{γ : Sub Δ Γ} →
                    genMachine u v w t [ γ ] ≡
                    genMachine (u [ (γ ⊚ p ,o q) ⊚ p ,o q ]) (v [ γ ⊚ p ,o q ]) (w [ γ ⊚ p ,o q ]) (t [ γ ]) 

  def : ∀{Γ A B} → Tm Γ A → Tm (Γ ▹ A) B → Tm Γ B
  def t u = u [ id ,o t ]

  v0 : {Γ : Con} → {A : Ty} → Tm (Γ ▹ A) A
  v0 = q
  v1 : {Γ : Con} → {A B : Ty} → Tm (Γ ▹ A ▹ B) A
  v1 = q [ p ]
  v2 : {Γ : Con} → {A B C : Ty} → Tm (Γ ▹ A ▹ B ▹ C) A
  v2 = q [ p ⊚ p ]
  v3 : {Γ : Con} → {A B C D : Ty} → Tm (Γ ▹ A ▹ B ▹ C ▹ D) A
  v3 = q [ p ⊚ p ⊚ p ]

--------------------------------------
-- Model of our language
-- like a specification, interface or contract: any model must satisfy all equations (i.e., provide proofs that they hold)

record Model {i j k l} : Set (lsuc (i ⊔ j ⊔ k ⊔ l)) where
  infixl 6 _⊚_
  infixl 6 _[_]
  infixl 5 _▹_
  infixl 5 _,o_
  infixr 5 _⇒_
  infixl 5 _$_
  infixl 7 _×o_
  infixl 5 ⟨_,_⟩
  infixl 6 _+o_

  field
    Con       : Set i
    Sub       : Con → Con → Set j
    _⊚_       : ∀{Γ Δ Θ} → Sub Δ Γ → Sub Θ Δ → Sub Θ Γ
    ass       : ∀{Γ Δ Θ Ξ}{γ : Sub Δ Γ}{δ : Sub Θ Δ}{θ : Sub Ξ Θ} → (γ ⊚ δ) ⊚ θ ≡ γ ⊚ (δ ⊚ θ)
    id        : ∀{Γ} → Sub Γ Γ
    idl       : ∀{Γ Δ}{γ : Sub Δ Γ} → id ⊚ γ ≡ γ
    idr       : ∀{Γ Δ}{γ : Sub Δ Γ} → γ ⊚ id ≡ γ

    ◇         : Con
    ε         : ∀{Γ} → Sub Γ ◇
    ◇η        : ∀{Γ}{σ : Sub Γ ◇} → σ ≡ ε

    Ty        : Set k
    Tm        : Con → Ty → Set l
    _[_]      : ∀{Γ Δ A} → Tm Γ A → Sub Δ Γ → Tm Δ A
    [∘]       : ∀{Γ Δ Θ A}{t : Tm Γ A}{γ : Sub Δ Γ}{δ : Sub Θ Δ} →  t [ γ ⊚ δ ] ≡ t [ γ ] [ δ ]
    [id]      : ∀{Γ A}{t : Tm Γ A} → t [ id ] ≡ t
    _▹_       : Con → Ty → Con
    _,o_      : ∀{Γ Δ A} → Sub Δ Γ → Tm Δ A → Sub Δ (Γ ▹ A)
    p         : ∀{Γ A} → Sub (Γ ▹ A) Γ
    q         : ∀{Γ A} → Tm (Γ ▹ A) A
    ▹β₁       : ∀{Γ Δ A}{γ : Sub Δ Γ}{t : Tm Δ A} → p ⊚ (γ ,o t) ≡ γ
    ▹β₂       : ∀{Γ Δ A}{γ : Sub Δ Γ}{t : Tm Δ A} → q [ γ ,o t ] ≡ t
    ▹η        : ∀{Γ Δ A}{γa : Sub Δ (Γ ▹ A)} → p ⊚ γa ,o q [ γa ] ≡ γa

    _⇒_       : Ty → Ty → Ty
    lam       : ∀{Γ A B} → Tm (Γ ▹ A) B → Tm Γ (A ⇒ B)
    _$_       : ∀{Γ A B} → Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B
    ⇒β        : ∀{Γ A B}{t : Tm (Γ ▹ A) B}{u : Tm Γ A} → lam t $ u ≡ t [ id ,o u ]
    ⇒η        : ∀{Γ A B}{t : Tm Γ (A ⇒ B)} → lam (t [ p ] $ q) ≡ t
    lam[]     : ∀{Γ A B}{t : Tm (Γ ▹ A) B}{Δ}{γ : Sub Δ Γ} →
                (lam t) [ γ ] ≡ lam (t [ γ ⊚ p ,o q ])
    $[]       : ∀{Γ A B}{t : Tm Γ (A ⇒ B)}{u : Tm Γ A}{Δ}{γ : Sub Δ Γ} →
                (t $ u) [ γ ] ≡ t [ γ ] $ u [ γ ]

    _×o_      : Ty → Ty → Ty
    ⟨_,_⟩     : ∀{Γ A B} → Tm Γ A → Tm Γ B → Tm Γ (A ×o B)
    fst       : ∀{Γ A B} → Tm Γ (A ×o B) → Tm Γ A
    snd       : ∀{Γ A B} → Tm Γ (A ×o B) → Tm Γ B
    ×β₁       : ∀{Γ A B}{u : Tm Γ A}{v : Tm Γ B} → fst ⟨ u , v ⟩ ≡ u
    ×β₂       : ∀{Γ A B}{u : Tm Γ A}{v : Tm Γ B} → snd ⟨ u , v ⟩ ≡ v
    ×η        : ∀{Γ A B}{t : Tm Γ (A ×o B)} → ⟨ fst t , snd t ⟩ ≡ t
    ,[]       : ∀{Γ A B}{u : Tm Γ A}{v : Tm Γ B}{Δ}{γ : Sub Δ Γ} →
                ⟨ u , v ⟩ [ γ ] ≡ ⟨ u [ γ ] , v [ γ ] ⟩

    _+o_      : Ty → Ty → Ty
    inl       : ∀{Γ A B} → Tm Γ A → Tm Γ (A +o B)
    inr       : ∀{Γ A B} → Tm Γ B → Tm Γ (A +o B)
    caseo     : ∀{Γ A B C} → Tm (Γ ▹ A) C → Tm (Γ ▹ B) C → Tm (Γ ▹ A +o B) C
    +β₁       : ∀{Γ A B C}{u : Tm (Γ ▹ A) C}{v : Tm (Γ ▹ B) C}{t : Tm Γ A} →
                caseo u v [ id ,o inl t ] ≡ u [ id ,o t ]
    +β₂       : ∀{Γ A B C}{u : Tm (Γ ▹ A) C}{v : Tm (Γ ▹ B) C}{t : Tm Γ B} →
                caseo u v [ id ,o inr t ] ≡ v [ id ,o t ]
    +η        : ∀{Γ A B C}{t : Tm (Γ ▹ A +o B) C} →
                caseo (t [ p ,o inl q ]) (t [ p ,o inr q ]) ≡ t
    inl[]     : ∀{Γ A B}{t : Tm Γ A}{Δ}{γ : Sub Δ Γ} →
                (inl {B = B} t) [ γ ] ≡ inl (t [ γ ])
    inr[]     : ∀{Γ A B}{t : Tm Γ B}{Δ}{γ : Sub Δ Γ} →
                (inr {A = A} t) [ γ ] ≡ inr (t [ γ ])
    case[]    : ∀{Γ A B C}{u : Tm (Γ ▹ A) C}{v : Tm (Γ ▹ B) C}{Δ}{γ : Sub Δ Γ} →
                (caseo u v) [ γ ⊚ p ,o q ] ≡
                caseo (u [ γ ⊚ p ,o q ]) (v [ γ ⊚ p ,o q ])

    Empty     : Ty
    absurd    : ∀{Γ A} → Tm (Γ ▹ Empty) A
    Emptyη    : ∀{Γ A}{t : Tm (Γ ▹ Empty) A} → t ≡ absurd

    Unit      : Ty
    trivial   : ∀{Γ} → Tm Γ Unit
    iteUnit   : ∀{Γ A} → Tm Γ A → Tm Γ Unit → Tm Γ A
    Unitβ     : ∀{Γ A t} → iteUnit {Γ}{A} t trivial ≡ t
    Unitη     : ∀{Γ}{u : Tm Γ Unit} → u ≡ trivial
    trivial[] : ∀{Γ Δ}{γ : Sub Δ Γ} → trivial [ γ ] ≡ trivial
    iteUnit[] : ∀{Γ A t u Δ}{γ : Sub Δ Γ} →
                iteUnit {Γ}{A} u t [ γ ] ≡ iteUnit (u [ γ ]) (t [ γ ])

    Bool      : Ty
    true      : ∀{Γ} → Tm Γ Bool
    false     : ∀{Γ} → Tm Γ Bool
    iteBool   : ∀{Γ A} → Tm Γ A → Tm Γ A → Tm Γ Bool → Tm Γ A
    Boolβ₁    : ∀{Γ A u v} → iteBool {Γ}{A} u v true ≡ u
    Boolβ₂    : ∀{Γ A u v} → iteBool {Γ}{A} u v false ≡ v
    true[]    : ∀{Γ Δ}{γ : Sub Δ Γ} → true [ γ ] ≡ true
    false[]   : ∀{Γ Δ}{γ : Sub Δ Γ} → false [ γ ] ≡ false
    iteBool[] : ∀{Γ A t u v Δ}{γ : Sub Δ Γ} →
                iteBool {Γ}{A} u v t [ γ ] ≡ iteBool (u [ γ ]) (v [ γ ]) (t [ γ ])
    Nat        : Ty
    zeroo      : ∀{Γ} → Tm Γ Nat
    suco       : ∀{Γ} → Tm Γ Nat → Tm Γ Nat
    iteNat     : ∀{Γ A} → Tm Γ A → Tm (Γ ▹ A) A → Tm Γ Nat → Tm Γ A
    Natβ₁      : ∀{Γ A}{u : Tm Γ A}{v : Tm (Γ ▹ A) A} → iteNat u v zeroo ≡ u
    Natβ₂      : ∀{Γ A}{u : Tm Γ A}{v : Tm (Γ ▹ A) A}{t : Tm Γ Nat} →
                 iteNat u v (suco t) ≡ v [ id ,o iteNat u v t ]
    zero[]     : ∀{Γ Δ}{γ : Sub Δ Γ} → zeroo [ γ ] ≡ zeroo
    suc[]      : ∀{Γ}{t : Tm Γ Nat}{Δ}{γ : Sub Δ Γ} → (suco t) [ γ ] ≡ suco (t [ γ ])
    iteNat[]   : ∀{Γ A}{u : Tm Γ A}{v : Tm (Γ ▹ A) A}{t : Tm Γ Nat}{Δ}{γ : Sub Δ Γ} →
                 iteNat u v t [ γ ] ≡ iteNat (u [ γ ]) (v [ γ ⊚ p ,o q ]) (t [ γ ])
    List       : Ty → Ty
    nil        : ∀{Γ A} → Tm Γ (List A)
    cons       : ∀{Γ A} → Tm Γ A → Tm Γ (List A) → Tm Γ (List A)
    iteList    : ∀{Γ A B} → Tm Γ B → Tm (Γ ▹ A ▹ B) B → Tm Γ (List A) → Tm Γ B
    Listβ₁     : ∀{Γ A B}{u : Tm Γ B}{v : Tm (Γ ▹ A ▹ B) B} → iteList u v nil ≡ u
    Listβ₂     : ∀{Γ A B}{u : Tm Γ B}{v : Tm (Γ ▹ A ▹ B) B}{t₁ : Tm Γ A}{t : Tm Γ (List A)} →
                 iteList u v (cons t₁ t) ≡ (v [ id ,o t₁ ,o iteList u v t ])
    nil[]      : ∀{Γ A Δ}{γ : Sub Δ Γ} → nil {Γ}{A} [ γ ] ≡ nil {Δ}{A}
    cons[]     : ∀{Γ A}{t₁ : Tm Γ A}{t : Tm Γ (List A)}{Δ}{γ : Sub Δ Γ} →
                 (cons t₁ t) [ γ ] ≡ cons (t₁ [ γ ]) (t [ γ ])
    iteList[]  : ∀{Γ A B}{u : Tm Γ B}{v : Tm (Γ ▹ A ▹ B) B}{t : Tm Γ (List A)}{Δ}{γ : Sub Δ Γ} →
                 iteList u v t [ γ ] ≡ iteList (u [ γ ]) (v [ (γ ⊚ p ,o q) ⊚ p ,o q ]) (t [ γ ])

    Tree       : Ty → Ty
    leaf       : ∀{Γ A} → Tm Γ A → Tm Γ (Tree A)
    node       : ∀{Γ A} → Tm Γ (Tree A) → Tm Γ (Tree A) → Tm Γ (Tree A)
    iteTree    : ∀{Γ A B} → Tm (Γ ▹ A) B → Tm (Γ ▹ B ▹ B) B → Tm Γ (Tree A) → Tm Γ B
    Treeβ₁     : ∀{Γ A B}{l : Tm (Γ ▹ A) B}{n : Tm (Γ ▹ B ▹ B) B}{a : Tm Γ A} →
                 iteTree l n (leaf a) ≡ l [ id ,o a ]
    Treeβ₂     : ∀{Γ A B}{l : Tm (Γ ▹ A) B}{n : Tm (Γ ▹ B ▹ B) B}{ll rr : Tm Γ (Tree A)} →
                 iteTree l n (node ll rr) ≡ n [ id ,o iteTree l n ll ,o iteTree l n rr ]
    leaf[]     : ∀{Γ A}{a : Tm Γ A}{Δ}{γ : Sub Δ Γ} → (leaf a) [ γ ] ≡ leaf (a [ γ ])
    node[]     : ∀{Γ A}{ll rr : Tm Γ (Tree A)}{Δ}{γ : Sub Δ Γ} →
                 (node ll rr) [ γ ] ≡ node (ll [ γ ]) (rr [ γ ])
    iteTree[]  : ∀{Γ A B}{l : Tm (Γ ▹ A) B}{n : Tm (Γ ▹ B ▹ B) B}{t : Tm Γ (Tree A)}
                 {Δ}{γ : Sub Δ Γ} →
                 iteTree l n t [ γ ] ≡
                 iteTree (l [ (γ ⊚ p) ,o q ]) (n [ (γ ⊚ p ⊚ p) ,o (q [ p ]) ,o q ]) (t [ γ ])

    Stream        : Ty → Ty
    head          : ∀{Γ A} → Tm Γ (Stream A) → Tm Γ A
    tail          : ∀{Γ A} → Tm Γ (Stream A) → Tm Γ (Stream A)
    genStream     : ∀{Γ A C} → Tm (Γ ▹ C) A → Tm (Γ ▹ C) C → Tm Γ C → Tm Γ (Stream A)
    Streamβ₁      : ∀{Γ A C}{u : Tm (Γ ▹ C) A}{v : Tm (Γ ▹ C) C}{t : Tm Γ C} →
                    head (genStream u v t) ≡ u [ id ,o t ]
    Streamβ₂      : ∀{Γ A C}{u : Tm (Γ ▹ C) A}{v : Tm (Γ ▹ C) C}{t : Tm Γ C} →
                    tail (genStream u v t) ≡ genStream u v (v [ id ,o t ])
    head[]        : ∀{Γ A}{as : Tm Γ (Stream A)}{Δ}{γ : Sub Δ Γ} →
                    head as [ γ ] ≡ head (as [ γ ])
    tail[]        : ∀{Γ A}{as : Tm Γ (Stream A)}{Δ}{γ : Sub Δ Γ} → tail as [ γ ] ≡ tail (as [ γ ])
    genStream[]   : ∀{Γ A C}{u : Tm (Γ ▹ C) A}{v : Tm (Γ ▹ C) C}{t : Tm Γ C}{Δ}
                    {γ : Sub Δ Γ} →
                    genStream u v t [ γ ] ≡ genStream (u [ γ ⊚ p ,o q ]) (v [ γ ⊚ p ,o q ]) (t [ γ ])

    Machine       : Ty
    put           : ∀{Γ} → Tm Γ Machine → Tm Γ Nat → Tm Γ Machine
    set           : ∀{Γ} → Tm Γ Machine → Tm Γ Machine
    get           : ∀{Γ} → Tm Γ Machine → Tm Γ Nat
    genMachine    : ∀{Γ C} → Tm (Γ ▹ C ▹ Nat) C → Tm (Γ ▹ C) C → Tm (Γ ▹ C) Nat →
                    Tm Γ C → Tm Γ Machine
    Machineβ₁     : ∀{Γ C}{u : Tm (Γ ▹ C ▹ Nat) C}{v : Tm (Γ ▹ C) C}{w : Tm (Γ ▹ C) Nat}
                    {t : Tm Γ C}{t' : Tm Γ Nat} →
                    put (genMachine u v w t) t' ≡ genMachine u v w (u [ id ,o t ,o t' ])
    Machineβ₂     : ∀{Γ C}{u : Tm (Γ ▹ C ▹ Nat) C}{v : Tm (Γ ▹ C) C}{w : Tm (Γ ▹ C) Nat}
                    {t : Tm Γ C} →
                    set (genMachine u v w t) ≡ genMachine u v w (v [ id ,o t ])
    Machineβ₃     : ∀{Γ C}{u : Tm (Γ ▹ C ▹ Nat) C}{v : Tm (Γ ▹ C) C}{w : Tm (Γ ▹ C) Nat}
                    {t : Tm Γ C} →
                    get (genMachine u v w t) ≡ w [ id ,o t ]
    put[]         : ∀{Γ}{t : Tm Γ Machine}{u : Tm Γ Nat}{Δ}{γ : Sub Δ Γ} →
                    put t u [ γ ] ≡ put (t [ γ ]) (u [ γ ])
    set[]         : ∀{Γ}{t : Tm Γ Machine}{Δ}{γ : Sub Δ Γ} → set t [ γ ] ≡ set (t [ γ ])
    get[]         : ∀{Γ}{t : Tm Γ Machine}{Δ}{γ : Sub Δ Γ} → get t [ γ ] ≡ get (t [ γ ])
    genMachine[]  : ∀{Γ C}{u : Tm (Γ ▹ C ▹ Nat) C}{v : Tm (Γ ▹ C) C}{w : Tm (Γ ▹ C) Nat}
                    {t : Tm Γ C}{Δ}{γ : Sub Δ Γ} →
                    genMachine u v w t [ γ ] ≡
                    genMachine (u [ (γ ⊚ p ,o q) ⊚ p ,o q ]) (v [ γ ⊚ p ,o q ]) (w [ γ ⊚ p ,o q ]) (t [ γ ]) 

  def : ∀{Γ A B} → Tm Γ A → Tm (Γ ▹ A) B → Tm Γ B
  def t u = u [ id ,o t ]
  v0 : ∀{Γ A}        → Tm (Γ ▹ A) A
  v0 = q
  v1 : ∀{Γ A B}      → Tm (Γ ▹ A ▹ B) A
  v1 = q [ p ]
  v2 : ∀{Γ A B C}    → Tm (Γ ▹ A ▹ B ▹ C) A
  v2 = q [ p ⊚ p ]
  v3 : ∀{Γ A B C D}  → Tm (Γ ▹ A ▹ B ▹ C ▹ D) A
  v3 = q [ p ⊚ p ⊚ p ]
  ▹η' : ∀{Γ A} → p ,o q ≡ id {Γ ▹ A}
  ▹η' {Γ}{A} =
    p ,o q
      ≡⟨ cong {A = Sub (Γ ▹ A) Γ × Tm (Γ ▹ A) A} (λ w → π₁ w ,o π₂ w) (sym (idr ,×= [id])) ⟩
    p ⊚ id ,o q [ id ]
      ≡⟨ ▹η ⟩
    id
      ∎

  ,∘ : ∀{Γ Δ Θ A}{γ : Sub Δ Γ}{t : Tm Δ A}{δ : Sub Θ Δ} →
    (γ ,o t) ⊚ δ ≡ γ ⊚ δ ,o t [ δ ]
  ,∘ {Γ}{Δ}{Θ}{A}{γ}{t}{δ} =
    (γ ,o t) ⊚ δ
      ≡⟨ sym ▹η ⟩
    (p ⊚ ((γ ,o t) ⊚ δ) ,o q [ (γ ,o t) ⊚ δ ])
      ≡⟨ cong (λ w → π₁ w ,o π₂ w) (sym ass ,×= [∘]) ⟩
    ((p ⊚ (γ ,o t)) ⊚ δ ,o q [ γ ,o t ] [ δ ])
      ≡⟨ cong (λ w → π₁ w ,o π₂ w) (cong (_⊚ δ) ▹β₁ ,×= cong (_[ δ ]) ▹β₂) ⟩
    γ ⊚ δ ,o t [ δ ]
      ∎

  ^∘ : ∀{Γ Δ}{γ : Sub Δ Γ}{A}{Θ}{δ : Sub Θ Δ}{t : Tm Θ A} →
    (γ ⊚ p ,o q) ⊚ (δ ,o t) ≡ (γ ⊚ δ ,o t)
  ^∘ {Γ}{Δ}{γ}{A}{Θ}{δ}{t} =
    (γ ⊚ p ,o q) ⊚ (δ ,o t)
      ≡⟨ ,∘ ⟩
    (γ ⊚ p ⊚ (δ ,o t) ,o q [ δ ,o t ])
      ≡⟨ cong (λ x → (x ,o q [ δ ,o t ])) ass ⟩
    (γ ⊚ (p ⊚ (δ ,o t)) ,o q [ δ ,o t ])
      ≡⟨ cong (λ x → (γ ⊚ x ,o q [ δ ,o t ])) ▹β₁ ⟩
    (γ ⊚ δ ,o q [ δ ,o t ])
      ≡⟨ cong (λ x → γ ⊚ δ ,o x) ▹β₂ ⟩
    (γ ⊚ δ ,o t)
      ∎

  fst[] : ∀{Γ Δ A B}{t : Tm Γ (A ×o B)}{γ : Sub Δ Γ} →
    (fst t) [ γ ] ≡ fst (t [ γ ])
  fst[] {Γ}{Δ}{A}{B}{t}{γ} =
    fst t [ γ ]
                          ≡⟨ sym ×β₁ ⟩
    fst ⟨ fst t [ γ ] , snd t [ γ ] ⟩
                          ≡⟨ cong fst (sym ,[]) ⟩
    fst (⟨ fst t , snd t ⟩ [ γ ])
                          ≡⟨ cong (λ x → fst (x [ γ ])) ×η ⟩
    fst (t [ γ ])
                          ∎

  snd[] : ∀{Γ Δ A B}{t : Tm Γ (A ×o B)}{γ : Sub Δ Γ} →
    (snd t) [ γ ] ≡ snd (t [ γ ])
  snd[] {Γ}{Δ}{A}{B}{t}{γ} =
    snd t [ γ ]
                          ≡⟨ sym ×β₂ ⟩
    snd ⟨ fst t [ γ ] , snd t [ γ ] ⟩
                          ≡⟨ cong snd (sym ,[]) ⟩
    snd (⟨ fst t , snd t ⟩ [ γ ])
                          ≡⟨ cong (λ x → snd (x [ γ ])) ×η ⟩
    snd (t [ γ ])
                          ∎

  +β₁' : ∀{Γ A B C}{u : Tm (Γ ▹ A) C}{v : Tm (Γ ▹ B) C}{Δ}{γ : Sub Δ Γ}{t : Tm Δ A} →
    caseo u v [ γ ,o inl t ] ≡ u [ γ ,o t ]
  +β₁' {Γ}{A}{B}{C}{u}{v}{Δ}{γ}{t} =
    caseo u v [ γ ,o inl t ]
      ≡⟨ cong (λ x → caseo u v [ x ,o inl t ]) (sym idr) ⟩
    caseo u v [ (γ ⊚ id ,o inl t) ]
      ≡⟨ cong (caseo u v [_]) (sym ^∘)  ⟩
    caseo u v [ (γ ⊚ p ,o q) ⊚ (id ,o inl t) ]
      ≡⟨ [∘] ⟩
    caseo u v [ γ ⊚ p ,o q ] [ id ,o inl t ]
      ≡⟨ cong (_[ id ,o inl t ]) case[] ⟩
    caseo (u [ γ ⊚ p ,o q ]) (v [ γ ⊚ p ,o q ]) [ id ,o inl t ]
      ≡⟨ +β₁ ⟩
    u [ γ ⊚ p ,o q ] [ id ,o t ]
      ≡⟨ sym [∘] ⟩
    u [ (γ ⊚ p ,o q) ⊚ (id ,o t) ]
      ≡⟨ cong (u [_]) ^∘ ⟩
    u [ γ ⊚ id ,o t ]
      ≡⟨ cong (λ x → u [ x ,o t ]) idr ⟩
    u [ γ ,o t ]
      ∎

  +β₂' : ∀{Γ A B C}{u : Tm (Γ ▹ A) C}{v : Tm (Γ ▹ B) C}{Δ}{γ : Sub Δ Γ}{t : Tm Δ B} →
    caseo u v [ γ ,o inr t ] ≡ v [ γ ,o t ]
  +β₂' {Γ}{A}{B}{C}{u}{v}{Δ}{γ}{t} =
    caseo u v [ γ ,o inr t ]
      ≡⟨ cong (λ x → caseo u v [ x ,o inr t ]) (sym idr) ⟩
    caseo u v [ (γ ⊚ id ,o inr t) ]
      ≡⟨ cong (caseo u v [_]) (sym ^∘)  ⟩
    caseo u v [ (γ ⊚ p ,o q) ⊚ (id ,o inr t) ]
      ≡⟨ [∘] ⟩
    caseo u v [ γ ⊚ p ,o q ] [ id ,o inr t ]
      ≡⟨ cong (_[ id ,o inr t ]) case[] ⟩
    caseo (u [ γ ⊚ p ,o q ]) (v [ γ ⊚ p ,o q ]) [ id ,o inr t ]
      ≡⟨ +β₂ ⟩
    v [ γ ⊚ p ,o q ] [ id ,o t ]
      ≡⟨ sym [∘] ⟩
    v [ (γ ⊚ p ,o q) ⊚ (id ,o t) ]
      ≡⟨ cong (v [_]) ^∘ ⟩
    v [ γ ⊚ id ,o t ]
      ≡⟨ cong (λ x → v [ x ,o t ]) idr ⟩
    v [ γ ,o t ]
      ∎

  absurd[] : ∀{Γ A}{Δ}{γ : Sub Δ Γ} →
    absurd {Γ}{A} [ γ ⊚ p ,o q ] ≡ absurd
  absurd[] = Emptyη

--------------------------------------
-- Rewriting rules for interpretation

  ⟦_⟧T : I.Ty → Ty
  ⟦ A I.⇒ B ⟧T = ⟦ A ⟧T ⇒ ⟦ B ⟧T
  ⟦ A I.×o B ⟧T = ⟦ A ⟧T ×o ⟦ B ⟧T
  ⟦ I.Unit ⟧T = Unit
  ⟦ A I.+o B ⟧T = ⟦ A ⟧T +o ⟦ B ⟧T
  ⟦ I.Empty ⟧T = Empty
  ⟦ I.Bool ⟧T = Bool
  ⟦ I.Nat ⟧T = Nat
  ⟦ I.List A ⟧T = List ⟦ A ⟧T
  ⟦ I.Tree A ⟧T = Tree ⟦ A ⟧T
  ⟦ I.Stream A ⟧T = Stream ⟦ A ⟧T
  ⟦ I.Machine ⟧T = Machine

  ⟦_⟧C : I.Con → Con
  ⟦ I.◇ ⟧C = ◇
  ⟦ Γ I.▹ A ⟧C = ⟦ Γ ⟧C ▹ ⟦ A ⟧T

  postulate
    ⟦_⟧S      : ∀{Γ Δ} → I.Sub Δ Γ → Sub ⟦ Δ ⟧C ⟦ Γ ⟧C
    ⟦_⟧t      : ∀{Γ A} → I.Tm  Γ A → Tm  ⟦ Γ ⟧C ⟦ A ⟧T
    ⟦∘⟧       : ∀{Γ Δ Θ}{γ : I.Sub Δ Γ}{δ : I.Sub Θ Δ} →
                         ⟦ γ I.⊚ δ ⟧S     ≈ ⟦ γ ⟧S ⊚ ⟦ δ ⟧S
    ⟦id⟧      : ∀{Γ} →   ⟦ I.id {Γ} ⟧S    ≈ id
    ⟦ε⟧       : ∀{Γ} →   ⟦ I.ε {Γ} ⟧S     ≈ ε
    ⟦[]⟧      : ∀{Γ Δ A}{γ : I.Sub Δ Γ}{t : I.Tm Γ A} →
                         ⟦ t I.[ γ ] ⟧t   ≈ ⟦ t ⟧t [ ⟦ γ ⟧S ]
    ⟦,⟧       : ∀{Γ Δ A}{γ : I.Sub Δ Γ}{t : I.Tm Δ A} →
                         ⟦ γ I.,o t ⟧S    ≈ ⟦ γ ⟧S ,o ⟦ t ⟧t
    ⟦p⟧       : ∀{Γ A} → ⟦ I.p {Γ} {A} ⟧S ≈ p
    ⟦q⟧       : ∀{Γ A} → ⟦ I.q {Γ} {A} ⟧t ≈ q
    {-# REWRITE ⟦∘⟧ ⟦id⟧ ⟦ε⟧ ⟦[]⟧ ⟦,⟧ ⟦p⟧ ⟦q⟧ #-}

    ⟦lam⟧     : ∀{Γ A B}{t : I.Tm (Γ I.▹ A) B} →
                         ⟦ I.lam t ⟧t    ≈ lam ⟦ t ⟧t
    ⟦$⟧       : ∀{Γ A B}{t : I.Tm Γ (A I.⇒ B)}{u : I.Tm Γ A} →
                         ⟦ t I.$ u ⟧t     ≈ ⟦ t ⟧t $ ⟦ u ⟧t
    {-# REWRITE ⟦lam⟧ ⟦$⟧ #-}

    ⟦⟨,⟩⟧     : ∀{Γ A B}{u : I.Tm Γ A}{v : I.Tm Γ B} → ⟦ I.⟨ u , v ⟩ ⟧t ≈ ⟨ ⟦ u ⟧t , ⟦ v ⟧t ⟩
    ⟦fst⟧     : ∀{Γ A B}{t : I.Tm Γ (A I.×o B)} →      ⟦ I.fst t ⟧t     ≈ fst  ⟦ t ⟧t
    ⟦snd⟧     : ∀{Γ A B}{t : I.Tm Γ (A I.×o B)} →      ⟦ I.snd t ⟧t     ≈ snd  ⟦ t ⟧t
    {-# REWRITE ⟦⟨,⟩⟧ ⟦fst⟧ ⟦snd⟧ #-}

    ⟦trivial⟧ : ∀{Γ} → ⟦ I.trivial {Γ} ⟧t ≈ trivial
    ⟦iteUnit⟧ : ∀{Γ A}{u : I.Tm Γ A}{t : I.Tm Γ I.Unit} → ⟦ I.iteUnit u t ⟧t ≈ iteUnit ⟦ u ⟧t ⟦ t ⟧t
    {-# REWRITE ⟦trivial⟧ ⟦iteUnit⟧ #-}

    ⟦inl⟧     : ∀{Γ A B}{t : I.Tm Γ A} → ⟦ I.inl {Γ}{A}{B} t  ⟧t ≈ inl ⟦ t ⟧t
    ⟦inr⟧     : ∀{Γ A B}{t : I.Tm Γ B} → ⟦ I.inr {Γ}{A}{B} t  ⟧t ≈ inr ⟦ t ⟧t
    ⟦case⟧    : ∀{Γ A B C}{u : I.Tm (Γ I.▹ A) C}{v : I.Tm (Γ I.▹ B) C} →
                                         ⟦ I.caseo u v        ⟧t ≈ caseo ⟦ u ⟧t ⟦ v ⟧t
    {-# REWRITE ⟦inl⟧ ⟦inr⟧ ⟦case⟧ #-}

    ⟦absurd⟧  : ∀{Γ A} → ⟦ I.absurd {Γ}{A} ⟧t ≈ absurd
    {-# REWRITE ⟦absurd⟧ #-}

    ⟦true⟧    : ∀{Γ} →   ⟦ I.true {Γ} ⟧t  ≈ true
    ⟦false⟧   : ∀{Γ} →   ⟦ I.false {Γ} ⟧t ≈ false
    ⟦iteBool⟧     : ∀{Γ A}{u v : I.Tm Γ A}{t : I.Tm Γ I.Bool} →
                         ⟦ I.iteBool u v t ⟧t ≈ iteBool ⟦ u ⟧t ⟦ v ⟧t ⟦ t ⟧t
    {-# REWRITE ⟦true⟧ ⟦false⟧ ⟦iteBool⟧ #-}

    ⟦zero⟧    : ∀{Γ}                   → ⟦ I.zeroo {Γ} ⟧t    ≈ zeroo
    ⟦suc⟧     : ∀{Γ}{t : I.Tm Γ I.Nat} → ⟦ I.suco t ⟧t       ≈ suco ⟦ t ⟧t
    ⟦iteNat⟧  : ∀{Γ A}{u : I.Tm Γ A}{v : I.Tm (Γ I.▹ A) A}{t : I.Tm Γ I.Nat} →
                                         ⟦ I.iteNat u v t ⟧t ≈ iteNat ⟦ u ⟧t ⟦ v ⟧t ⟦ t ⟧t
    {-# REWRITE ⟦zero⟧ ⟦suc⟧ ⟦iteNat⟧ #-}

    ⟦nil⟧     : ∀{Γ A} → ⟦ I.nil {Γ}{A}    ⟧t ≈ nil
    ⟦cons⟧    : ∀{Γ A}{u : I.Tm Γ A}{v : I.Tm Γ (I.List A)} →
                         ⟦ I.cons u v      ⟧t ≈ cons ⟦ u ⟧t ⟦ v ⟧t
    ⟦iteList⟧ : ∀{Γ A B}{u : I.Tm Γ B}{v : I.Tm (Γ I.▹ A I.▹ B) B}{t : I.Tm Γ (I.List A)} → 
                         ⟦ I.iteList u v t ⟧t ≈ iteList ⟦ u ⟧t ⟦ v ⟧t ⟦ t ⟧t
    {-# REWRITE ⟦nil⟧ ⟦cons⟧ ⟦iteList⟧ #-}

    ⟦leaf⟧    : ∀{Γ A}{t : I.Tm Γ A}            → ⟦ I.leaf t        ⟧t ≈ leaf ⟦ t ⟧t
    ⟦node⟧    : ∀{Γ A}{u v : I.Tm Γ (I.Tree A)} → ⟦ I.node u v      ⟧t ≈ node ⟦ u ⟧t ⟦ v ⟧t
    ⟦iteTree⟧ : ∀{Γ A B}{u : I.Tm (Γ I.▹ A) B}{v : I.Tm (Γ I.▹ B I.▹ B) B}{t : I.Tm Γ (I.Tree A)} →
                                                  ⟦ I.iteTree u v t ⟧t ≈ iteTree ⟦ u ⟧t ⟦ v ⟧t ⟦ t ⟧t
    {-# REWRITE ⟦leaf⟧ ⟦node⟧ ⟦iteTree⟧ #-}

    ⟦head⟧        : ∀{Γ A}{t : I.Tm Γ (I.Stream A)} → 
                    ⟦ I.head t          ⟧t ≈ head ⟦ t ⟧t
    ⟦tail⟧        : ∀{Γ A}{t : I.Tm Γ (I.Stream A)} → 
                    ⟦ I.tail t          ⟧t ≈ tail ⟦ t ⟧t
    ⟦genStream⟧   : ∀{Γ A C}{u : I.Tm (Γ I.▹ C) A}{v : I.Tm (Γ I.▹ C) C}{t : I.Tm Γ C} → 
                    ⟦ I.genStream u v t ⟧t ≈ genStream ⟦ u ⟧t ⟦ v ⟧t ⟦ t ⟧t
    {-# REWRITE ⟦head⟧ ⟦tail⟧ ⟦genStream⟧ #-}

    ⟦put⟧         : ∀{Γ}{t : I.Tm Γ I.Machine}{u : I.Tm Γ I.Nat} →
                    ⟦ I.put t u ⟧t ≈ put ⟦ t ⟧t ⟦ u ⟧t
    ⟦set⟧         : ∀{Γ}{t : I.Tm Γ I.Machine} →
                    ⟦ I.set t   ⟧t ≈ set ⟦ t ⟧t
    ⟦get⟧         : ∀{Γ}{t : I.Tm Γ I.Machine} →
                    ⟦ I.get t   ⟧t ≈ get ⟦ t ⟧t
    ⟦genMachine⟧  : ∀{Γ C}{u : I.Tm (Γ I.▹ C I.▹ I.Nat) C}{v : I.Tm (Γ I.▹ C) C}
                    {w : I.Tm (Γ I.▹ C) I.Nat}{t : I.Tm Γ C} →
                    ⟦ I.genMachine u v w t ⟧t ≈ genMachine ⟦ u ⟧t ⟦ v ⟧t ⟦ w ⟧t ⟦ t ⟧t
    {-# REWRITE ⟦put⟧ ⟦set⟧ ⟦get⟧ ⟦genMachine⟧ #-}

--------------------------------------
-- Agda (metatheoretic) implementations of types used in the standard model

data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A
iteList : {A B : Set} → B → (A → B → B) → List A → B
iteList b f [] = b
iteList b f (a ∷ as) = f a (iteList b f as)

data Tree (A : Set) : Set where
  leaf : A → Tree A
  node : Tree A → Tree A → Tree A
iteTree : {A B : Set} → (A → B) → (B → B → B) → Tree A → B
iteTree f g (leaf a) = f a
iteTree f g (node t t') = g (iteTree f g t) (iteTree f g t')

record Stream (A : Set) : Set where
  coinductive
  field
    head : A
    tail : Stream A
open Stream
genStream : {A C : Set} → (C → A) → (C → C) → C → Stream A
head (genStream f g c) = f c
tail (genStream f g c) = genStream f g (g c)

record Machine : Set where
  coinductive
  field
    put : ℕ → Machine
    set : Machine
    get : ℕ
open Machine
genMachine : {C : Set} → (C → ℕ → C) → (C → C) → (C → ℕ) → C → Machine
put (genMachine f g h c) n = genMachine f g h (f c n)
set (genMachine f g h c) = genMachine f g h (g c)
get (genMachine f g h c) = h c

--------------------------------------
-- Standard model, we map everything to Agda types
-- all equations hold (most of the proofs are just refl)

St : Model
St = record
  { Con       = Set
  ; Sub       = λ Δ Γ → Δ → Γ
  ; _⊚_       = λ γ δ θ* → γ (δ θ*)
  ; ass       = λ {Γ}{Δ}{Θ}{Ξ} → refl {A = Ξ → Γ}
  ; id        = λ γ* → γ*
  ; idl       = λ {Γ}{Δ} → refl {A = Δ → Γ}
  ; idr       = λ {Γ}{Δ} → refl {A = Δ → Γ}

  ; ◇         = ⊤
  ; ε         = _
  ; ◇η        = λ {Γ}{σ} → refl {A = Γ → ⊤}

  ; Ty        = Set

  ; Tm        = λ Γ A → Γ → A
  ; _[_]      = λ a γ δ* → a (γ δ*)
  ; [∘]       = λ {Γ}{Δ}{Θ}{A} → refl {A = Θ → A}
  ; [id]      = λ {Γ}{A}{a} → refl {A = Γ → A}
  ; _▹_       = _×_
  ; _,o_      = λ γ t δ* → γ δ* , t δ*
  ; p         = π₁
  ; q         = π₂
  ; ▹β₁       = λ {Γ}{Δ} → refl {A = Δ → Γ}
  ; ▹β₂       = λ {Γ}{Δ}{A} → refl {A = Δ → A}
  ; ▹η        = λ {Γ}{Δ}{A} → refl {A = Δ → Γ × A}

  ; _⇒_       = λ A B → A → B
  ; lam       = λ t γ* α* → t (γ* , α*)
  ; _$_       = λ t u γ* → t γ* (u γ*)
  ; ⇒β        = λ {Γ}{A}{B}{t}{u} → refl {A = Γ → B}
  ; ⇒η        = λ {Γ}{A}{B}{t} → refl {A = Γ → A → B}
  ; lam[]     = λ {Γ}{A}{B}{t}{Δ}{γ} → refl {A = Δ → A → B}
  ; $[]       = λ {Γ}{A}{B}{t}{u}{Δ}{γ} → refl {A = Δ → B}

  ; _×o_      = _×_
  ; ⟨_,_⟩     = λ a b γ* → (a γ* , b γ*)
  ; fst       = λ t γ* → π₁ (t γ*)
  ; snd       = λ t γ* → π₂ (t γ*)
  ; ×β₁       = λ {Γ}{A}{B}{u}{v} → refl {A = Γ → A}
  ; ×β₂       = λ {Γ}{A}{B}{u}{v} → refl {A = Γ → B}
  ; ×η        = λ {Γ}{A}{B}{t} → refl {A = Γ → A × B}
  ; ,[]       = λ {Γ}{A}{B}{u}{v}{Δ}{γ} → refl {A = Δ → A × B}

  ; Unit      = ⊤
  ; trivial   = λ _ → tt
  ; iteUnit   = λ z _ → z
  ; Unitβ     = refl
  ; Unitη     = λ {Γ}{u} → refl {A = Γ → ⊤}
  ; trivial[] = refl
  ; iteUnit[] = refl

  ; _+o_      = _⊎_
  ; inl       = λ a γ* → inj₁ (a γ*)
  ; inr       = λ b γ* → inj₂ (b γ*)
  ; caseo     = λ u v γw* → [ (λ a* → u (π₁ γw* , a*)) , (λ b* → v (π₁ γw* , b*)) ]′ (π₂ γw*)
  ; +β₁       = refl
  ; +β₂       = refl
  ; +η        = λ {Γ}{A}{B}{C}{t} → funext λ γw → (ind⊎
                (λ x → [ (λ a* → t (π₁ γw , inj₁ a*)) , (λ b* → t (π₁ γw , inj₂ b*)) ]′ x ≡ t (π₁ γw , x))
                (λ a → refl {A = C})
                (λ b → refl {A = C})
                (π₂ γw))
  ; inl[]     = refl
  ; inr[]     = refl
  ; case[]    = refl

  ; Empty     = ⊥
  ; absurd    = λ γb → ⊥-elim (π₂ γb)
  ; Emptyη    = funext λ γa → ⊥-elim (π₂ γa)

  ; Bool      = 𝟚
  ; true      = λ _ → tt
  ; false     = λ _ → ff
  ; iteBool   = λ u v t γ* → if t γ* then u γ* else v γ*
  ; Boolβ₁    = refl
  ; Boolβ₂    = refl
  ; true[]    = refl
  ; false[]   = refl
  ; iteBool[] = refl

  ; Nat        = ℕ
  ; zeroo      = λ _ → zero
  ; suco       = λ t γ* → suc (t γ*)
  ; iteNat     = λ u v t γ* → iteℕ (u γ*) (λ x → v (γ* , x)) (t γ*)
  ; Natβ₁      = refl
  ; Natβ₂      = refl
  ; zero[]     = refl
  ; suc[]      = refl
  ; iteNat[]   = refl

  ; List       = List
  ; nil        = λ _ → []
  ; cons       = λ u v γ* → u γ* ∷ v γ*
  ; iteList    = λ u v t γ* → iteList (u γ*) (λ x y → v ((γ* , x) , y)) (t γ*)
  ; Listβ₁     = refl
  ; Listβ₂     = refl
  ; nil[]      = refl
  ; cons[]     = refl
  ; iteList[]  = refl

  ; Tree       = Tree
  ; leaf       = λ t γ* → leaf (t γ*)
  ; node       = λ u v γ* → node (u γ*) (v γ*)
  ; iteTree    = λ {Γ}{A}{B} u v t γ* → iteTree (λ x → u (γ* , x)) (λ x y → v ((γ* , x) , y)) (t γ*)
  ; Treeβ₁     = refl
  ; Treeβ₂     = refl
  ; leaf[]     = refl
  ; node[]     = refl
  ; iteTree[]  = refl

  ; Stream        = Stream
  ; head          = λ t γ* → head (t γ*)
  ; tail          = λ t γ* → tail (t γ*)
  ; genStream     = λ u v t γ* → genStream (λ x → u (γ* , x)) (λ x → v (γ* , x)) (t γ*)
  ; Streamβ₁      = refl
  ; Streamβ₂      = refl
  ; head[]        = refl
  ; tail[]        = refl
  ; genStream[]   = refl

  ; Machine       = Machine
  ; put           = λ t u γ* → put (t γ*) (u γ*) 
  ; set           = λ t γ* → set (t γ*)
  ; get           = λ t γ* → get (t γ*)
  ; genMachine    = λ u v w t γ* → genMachine (λ x y → u ((γ* , x) , y))
                    (λ x → v (γ* , x)) (λ x → w (γ* , x)) (t γ*)
  ; Machineβ₁     = refl
  ; Machineβ₂     = refl
  ; Machineβ₃     = refl
  ; put[]         = refl
  ; set[]         = refl
  ; get[]         = refl
  ; genMachine[]  = refl
  }
