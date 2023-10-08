{-# OPTIONS --prop --rewriting --guardedness #-}

module Nats where

open import Data.Bool hiding (not) renaming (Bool to 𝟚; true to tt; false to ff)
open import Data.Nat using (suc)
open import Data.String using (_++_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Elaborator
open import STLC
open STLC.I

-- Peano numbers is an inductive type with constructors: zeroo and suco

_ : compile-eval "0" ≡ inj₁ (Nat , zeroo , λ γ* → 0)
_ = refl
_ : compile-eval "3" ≡ inj₁ (Nat , suco (suco (suco zeroo)) , λ γ* → 3)
_ = refl

-- destructor: isZero

_ : compile-eval "isZero 0" ≡ inj₁ (Bool , iteNat true false zeroo , (λ γ* → tt))
_ = refl
_ : compile-eval "isZero 1" ≡ inj₁ (Bool , iteNat true false (suco zeroo) , (λ γ* → ff))
_ = refl

-- destructor: _+_

_ : compile-eval "0 + 0" ≡ inj₁ (Nat , iteNat zeroo (suco q) zeroo , (λ γ* → 0))
_ = refl
_ : compile-eval "0 + 1" ≡ inj₁ (Nat , iteNat (suco zeroo) (suco q) zeroo , (λ γ* → 1))
_ = refl
_ : compile-eval "1 + 0" ≡ inj₁ (Nat , iteNat zeroo (suco q) (suco zeroo) , (λ γ* → 1))
_ = refl
_ : compile-eval "2 + 3" ≡ inj₁ (Nat , iteNat (suco (suco (suco zeroo))) (suco q) (suco (suco zeroo)) , (λ γ* → 5))
_ = refl

-- associativity of _+_ gives us chains, it associates to the left by default:

_ : compile-eval "0 + 1 + 2" ≡ inj₁ (Nat , iteNat (suco (suco zeroo)) (suco q) (iteNat (suco zeroo) (suco q) zeroo)
                                         , λ γ* → 3)
_ = refl

-- but we can, of course, parenthesize differently:

_ : compile-eval "0 + (1 + 2)" ≡ inj₁ (Nat , iteNat (iteNat (suco (suco zeroo)) (suco q) (suco zeroo)) (suco q) zeroo
                                           , λ γ* → 3)
_ = refl

-- combined usage of the two destructors

_ : compile-eval "isZero 0 + 0" ≡ inj₁ (Bool , iteNat true false (iteNat zeroo (suco q) zeroo) , (λ γ* → tt))
_ = refl
_ : compile-eval "isZero 1 + 0" ≡ inj₁ (Bool , iteNat true false (iteNat zeroo (suco q) (suco zeroo)) , (λ γ* → ff))
_ = refl

-- some well-known arithmetic functions

iden     = "(λ x. x)     : ℕ → ℕ"
+1       = "(λ x. x+1)   : ℕ → ℕ"
double   = "(λ x. x+x)   : ℕ → ℕ"
triple   = "(λ x. x+x+x) : ℕ → ℕ"
plus     = "(λ x y. iteℕ x (λz.z + 1) y) : ℕ → ℕ → ℕ"
multiply = "(λ x y. iteℕ 0 (λz.z + x) y) : ℕ → ℕ → ℕ"
twice    = "(λ f x. f f x)   : (ℕ → ℕ) → ℕ → ℕ"
3-times  = "(λ f x. f f f x) : (ℕ → ℕ) → ℕ → ℕ"
∘        = "(λ f g x. f g x) : (ℕ → ℕ) → (ℕ → ℕ) → ℕ → ℕ"

-- identity
_ : compile-eval iden ≡ inj₁ (Nat ⇒ Nat , lam q , λ γ* x → x)
_ = refl

-- _+1
_ : compile-eval +1 ≡ inj₁ (Nat ⇒ Nat , lam (iteNat (suco zeroo) (suco q) q)
                                      , λ γ* x → iteℕ 1 (λ y → suc y) x)
_ = refl

-- double
_ : compile-eval double ≡ inj₁ (Nat ⇒ Nat , lam (iteNat q (suco q) q)
                                          , λ γ* x → iteℕ x (λ y → suc y) x)
_ = refl

-- triple
_ : compile-eval triple ≡ inj₁ (Nat ⇒ Nat , lam (iteNat q (suco q) (iteNat q (suco q) q))
                                          , λ γ* x → iteℕ x (λ y → suc y) (iteℕ x (λ y → suc y) x))
_ = refl

-- we can implement _+_ with a function using the iterator of ℕ
_ : compile-eval plus ≡ inj₁ (Nat ⇒ Nat ⇒ Nat , lam (lam (iteNat (q [ p ])
                                               (lam (iteNat (suco zeroo) (suco q) q) [ p ] $ q) q))
                                              , λ γ* x y → iteℕ x (λ z → iteℕ 1 (λ w → suc w) z) y)
_ = refl

-- our language does not have built-in multiplication, but we can implement one:
_ : compile-eval multiply ≡ inj₁ (Nat ⇒ Nat ⇒ Nat , lam (lam (iteNat zeroo
                                                   (lam (iteNat (q [ p ] [ p ]) (suco q) q) [ p ] $ q) q))
                                                  , λ γ* x y → iteℕ 0 (λ z → iteℕ x (λ w → suc w) z) y)
_ = refl

-- twice
_ : compile-eval twice ≡ inj₁ ((Nat ⇒ Nat) ⇒ Nat ⇒ Nat , lam (lam (q [ p ] $ (q [ p ] $ q)))
                                                       , λ γ* f x → f (f x))
_ = refl

-- 3-times
_ : compile-eval 3-times ≡ inj₁ ((Nat ⇒ Nat) ⇒ Nat ⇒ Nat , lam (lam (q [ p ] $ (q [ p ] $ (q [ p ] $ q))))
                                                         , λ γ* f x → f (f (f x)))
_ = refl

-- composition: f∘g
_ : compile-eval ∘ ≡ inj₁ ((Nat ⇒ Nat) ⇒ (Nat ⇒ Nat) ⇒ Nat ⇒ Nat , lam (lam (lam (q [ p ] [ p ] $ (q [ p ] $ q))))
                                                                 , λ γ* f g x → f (g x))
_ = refl

-- some concrete computations

_ : eval (triple ++ₛ "8")                   ≡ inj₁ (Nat , λ γ* → 24)
_ = refl
_ : eval (plus ++ₛ "3" ++ₛ "8")             ≡ inj₁ (Nat , λ γ* → 11)
_ = refl
_ : eval (multiply ++ₛ "6" ++ₛ "20")        ≡ inj₁ (Nat , λ γ* → 120)
_ = refl
_ : eval (3-times ++ₛ +1 ++ₛ "10")          ≡ inj₁ (Nat , λ γ* → 13)
_ = refl
_ : eval (∘ ++ₛ double ++ₛ triple ++ₛ "10") ≡ inj₁ (Nat , λ γ* → 60)
_ = refl

-- mixing with booleans and showing some composability

not  = "((λ a. if a then false else true) : 𝕃 → 𝕃)" 

-- we are just rewriting the structure: suc(suc(suc(zero))) ⟶  ¬(¬(¬(true)))

even = "((λ x. iteℕ true (λa." ++ not ++ "a) x) : ℕ → 𝕃)"

-- here we just add one more negation

odd = "(λ x. " ++ not ++ "(" ++ even ++ "x)) : ℕ → 𝕃"

_ : eval (even ++ₛ "3") ≡ inj₁ (Bool , λ γ* → ff)
_ = refl
_ : eval (odd  ++ₛ "3") ≡ inj₁ (Bool , λ γ* → tt)
_ = refl
