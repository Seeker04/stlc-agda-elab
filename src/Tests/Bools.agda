{-# OPTIONS --prop --rewriting --guardedness #-}

module Bools where

open import Data.Bool hiding (not) renaming (Bool to 𝟚; true to tt; false to ff)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)
open import Data.String using (_++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Elaborator
open import STLC
open STLC.I

-- constructors: true and false

_ : compile-eval "true" ≡ inj₁ (Bool , true , λ γ* → tt)
_ = refl

_ : compile-eval "false" ≡ inj₁ (Bool , false , λ γ* → ff)
_ = refl

-- destructor: if_then_else_, used in the following well-known functions:

-- negation ¬
not = "(λ a. if a then false else true) : 𝕃 → 𝕃" 

_ : compile-eval not ≡ inj₁ (Bool ⇒ Bool , lam (iteBool false true q)
                                         , λ γ* a → if a then ff else tt)
_ = refl

-- conjunction ∧
and = "(λ a b. if a then b else false) : 𝕃 → 𝕃 → 𝕃" 

_ : compile-eval and ≡ inj₁ (Bool ⇒ Bool ⇒ Bool , lam (lam (iteBool q false (q [ p ])))
                                                , λ γ* a b → if a then b else ff)
_ = refl

-- disjunction ∨
or = "(λ a b. if a then true else b) : 𝕃 → 𝕃 → 𝕃" 

_ : compile-eval or ≡ inj₁ (Bool ⇒ Bool ⇒ Bool , lam (lam (iteBool true q (q [ p ])))
                                               , λ γ* a b → if a then tt else b)
_ = refl

-- exclusive disjunction ⊕   (of course, we can nest them and create "else if" branching)
xor = "(λ a b.             \
\         if a then        \
\           if b then      \
\             false        \
\           else           \
\             true         \
\         else if b then   \
\           true           \
\         else             \
\           false)         : 𝕃 → 𝕃 → 𝕃"

_ : compile-eval xor ≡ inj₁ (Bool ⇒ Bool ⇒ Bool
                            , lam (lam (iteBool (iteBool false true q) (iteBool true false q) (q [ p ])))
                            , λ γ* a b → if a then if b then ff else tt else (if b then tt else ff))
_ = refl

-- some example computations

_ : eval (xor ++ₛ "false" ++ₛ "false") ≡ inj₁ (Bool , λ γ* → ff)
_ = refl
_ : eval (xor ++ₛ "true"  ++ₛ "false") ≡ inj₁ (Bool , λ γ* → tt)
_ = refl
_ : eval (xor ++ₛ "false" ++ₛ "true")  ≡ inj₁ (Bool , λ γ* → tt)
_ = refl
_ : eval (xor ++ₛ "true"  ++ₛ "true")  ≡ inj₁ (Bool , λ γ* → ff)
_ = refl

-- logical consequence ⇒
implication = "(λ a b. if a then b else true) : 𝕃 → 𝕃 → 𝕃"

_ : compile-eval implication ≡ inj₁ (Bool ⇒ Bool ⇒ Bool , lam (lam (iteBool q true (q [ p ])))
                                                        , (λ γ* a b → if a then b else tt))
_ = refl

-- logical equivalence ⇔
equiv = "(λ a b. ((" ++ and ++ ")                   \
\                  (((" ++ implication ++ ") a) b)) \
\                  (((" ++ implication ++ ") b) a)) : 𝕃 → 𝕃 → 𝕃"

_ : compile-eval equiv ≡ inj₁ (Bool ⇒ Bool ⇒ Bool
                            , lam (lam (lam (lam (iteBool q false (q [ p ])))
                                $ (lam (lam (iteBool q true (q [ p ]))) $ q [ p ] $ q)
                                $ (lam (lam (iteBool q true (q [ p ]))) $ q $ q [ p ])))
                            , (λ γ* a b → if if a then b else tt then if b then a else tt else ff))
_ = refl
