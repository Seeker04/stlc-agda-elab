{-# OPTIONS --prop --rewriting --guardedness #-}

module Products where

open import Data.Bool renaming (Bool to 𝟚; true to tt; false to ff)
open import Data.Nat using (suc)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_×_; _,_) renaming (proj₁ to π₁; proj₂ to π₂)
open import Data.Unit renaming (tt to triv)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Elaborator
open import STLC
open STLC.I

-- nullary product
_ : compile-eval "trivial" ≡ inj₁ (Unit , trivial , λ γ* → triv)
_ = refl

-- binary product with the _,_ constructor (often called pair)
_ : compile-eval "1,2" ≡ inj₁ (Nat ×o Nat , ⟨ suco zeroo , suco (suco zeroo) ⟩ , λ γ* → 1 , 2)
_ = refl

-- non-homogeneous binary product
_ : compile-eval "0 , false" ≡ inj₁ (Nat ×o Bool , ⟨ zeroo , false ⟩ , λ γ* → 0 , ff)
_ = refl

-- right associativity of _×_ and _,_ gives us chains of products (triples, quadruples,...)
_ : compile-eval "3,2,1,0" ≡ inj₁ (Nat ×o (Nat ×o (Nat ×o Nat))
                                , ⟨ suco (suco (suco zeroo)) , ⟨ suco (suco zeroo) , ⟨ suco zeroo , zeroo ⟩ ⟩ ⟩
                                , λ γ* → 3 , 2 , 1 , 0)
_ = refl

_ : compile-eval "1, trivial, (isZero 1)" ≡ inj₁ (Nat ×o (Unit ×o Bool)
                                               , ⟨ suco zeroo , ⟨ trivial , iteNat true false (suco zeroo) ⟩ ⟩
                                               , λ γ* → 1 , triv , ff)
_ = refl

_ : compile-eval "trivial , 1+2 , ((λ x.x) : 𝕃 → 𝕃)" ≡ inj₁ (Unit ×o (Nat ×o (Bool ⇒ Bool)) ,
                                                              ⟨ trivial , ⟨ lam (lam (iteNat q (suco q) (q [ p ])))
                                                              $ suco zeroo $ suco (suco zeroo) , lam q ⟩ ⟩
                                                            , λ γ* → triv , 3 , λ x → x)
_ = refl

-- destructing pairs
_ : compile-eval "fst (2,3)" ≡ inj₁ (Nat , fst ⟨ suco (suco zeroo) , suco (suco (suco zeroo)) ⟩ , λ γ* → 2)
_ = refl

_ : compile-eval "snd (2,3)" ≡ inj₁ (Nat , snd ⟨ suco (suco zeroo) , suco (suco (suco zeroo)) ⟩ , λ γ* → 3)
_ = refl

-- destructing triples
_ : compile-eval "fst     (0,1,2)" ≡ inj₁ (Nat , fst      ⟨ zeroo , ⟨ suco zeroo , suco (suco zeroo) ⟩ ⟩  , λ γ* → 0)
_ = refl
_ : compile-eval "fst snd (0,1,2)" ≡ inj₁ (Nat , fst (snd ⟨ zeroo , ⟨ suco zeroo , suco (suco zeroo) ⟩ ⟩) , λ γ* → 1)
_ = refl
_ : compile-eval "snd snd (0,1,2)" ≡ inj₁ (Nat , snd (snd ⟨ zeroo , ⟨ suco zeroo , suco (suco zeroo) ⟩ ⟩) , λ γ* → 2)
_ = refl

-- function that extracts the third component from triples of ℕ
third = "(λ t. snd snd t) : (ℕ × ℕ × ℕ → ℕ)"

_ : compile-eval third ≡ inj₁ (Nat ×o (Nat ×o Nat) ⇒ Nat , lam (snd (snd q)) , λ γ* α* → π₂ (π₂ α*))
_ = refl

_ : eval (third ++ₛ "10, 20, 30") ≡ inj₁ (Nat , (λ γ* → 30))
_ = refl

_ : eval (third ++ₛ "5+5, 42, (if (isZero 0) then (6+2) else 0)") ≡ inj₁ (Nat , (λ γ* → 8))
_ = refl

-- curry and uncurry over ℕ → ℕ → ℕ functions

curry = "(λ f. λ x y. f (x,y)) : (ℕ × ℕ → ℕ) → (ℕ → ℕ → ℕ)"

uncurry = "(λ f. λ p. (f (fst p)) (snd p)) : (ℕ → ℕ → ℕ) → (ℕ × ℕ → ℕ)"

add = "(λ x y. x + y) : ℕ → ℕ → ℕ"

_ : compile-eval curry ≡ inj₁ (((Nat ×o Nat) ⇒ Nat) ⇒ (Nat ⇒ Nat ⇒ Nat)
                             , lam (lam (lam (q [ p ] [ p ] $ ⟨ q [ p ] , q ⟩)))
                             , λ γ* f x y → f (x , y))
_ = refl
_ : compile-eval uncurry ≡ inj₁ ((Nat ⇒ Nat ⇒ Nat) ⇒ ((Nat ×o Nat) ⇒ Nat)
                               , lam (lam (q [ p ] $ fst q $ snd q))
                               , λ γ* f p → f (π₁ p) (π₂ p))
_ = refl

_ : eval (uncurry ++ₛ add ++ₛ "(3 , 4)") ≡ inj₁ (Nat , (λ γ* → 7))
_ = refl

-- curry is the inverse of uncurry (we get back to where we came from)
_ : eval (curry ++ₛ (uncurry ++ₛ add)) ≡ eval add
_ = refl
