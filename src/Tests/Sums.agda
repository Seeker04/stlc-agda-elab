{-# OPTIONS --prop --rewriting --guardedness #-}

module Sums where

open import Data.Bool renaming (Bool to 𝟚; true to tt; false to ff)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit renaming (tt to triv)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Elaborator
open import STLC
open STLC.I

-- nullary sum
{-
_ : compile-eval "_ : ⊥" ≡ {!!} -- of course, no way to write a term whose type is Bottom (empty set has no member)
_ = refl
-}

-- binary sum (disjunct union) with the inl and inr constructors (left and right injections)
-- of course, we need the type annotation for deducing the whole type

_ : compile-eval "(inl trivial) : ⊤ ⊎ ℕ" ≡ inj₁ (Unit +o Nat , inl trivial , λ γ* → inj₁ triv)
_ = refl

_ : compile-eval "(inr 2) : ⊤ ⊎ ℕ" ≡ inj₁ (Unit +o Nat , inr (suco (suco zeroo)) , λ γ* → inj₂ 2)
_ = refl

-- sums with more than two terms (_⊎_ is right associative)

_ : compile-eval "(inl trivial) : ⊤ ⊎ ℕ ⊎ [𝕃]" ≡ inj₁ (Unit +o (Nat +o Ty.List Bool) , inl trivial , λ γ* → inj₁ triv)
_ = refl

_ : compile-eval "(inr ((inl 2) : ℕ ⊎ [𝕃])) : ⊤ ⊎ ℕ ⊎ [𝕃]" ≡ inj₁ (Unit +o (Nat +o Ty.List Bool)
                                                                , inr (inl (suco (suco zeroo)))
                                                                , λ γ* → inj₂ (inj₁ 2))
_ = refl

_ : compile-eval "(inr ((inr [true, false]) : ℕ ⊎ [𝕃])) : ⊤ ⊎ ℕ ⊎ [𝕃]" ≡ inj₁ (Unit +o (Nat +o Ty.List Bool)
                                                                       , inr (inr (cons true (cons false nil)))
                                                                       , λ γ* → inj₂ (inj₂ (tt ∷ (ff ∷ []))))
_ = refl

-- destructing sums with case splitting

_ : compile-eval "(case ((λ _ .     0) : ⊤ → ℕ)   \
\                  or   ((λ n . n + 1) : ℕ → ℕ))  \
\                 ((inr 1) : ⊤ ⊎ ℕ)" ≡ inj₁ (Nat , lam (caseo (lam zeroo [ p ] $ q)
                  (lam (lam (lam (iteNat q (suco q) (q [ p ]))) $ q $ suco zeroo) [ p ] $ q)) $ inr (suco zeroo)
                  , (λ γ* → 2))
_ = refl

-- we have built-in booleans but they are isomorphic to any type that has two values (i.e., set with cardinality two)
-- so we can simulate Bool, true, false and if_then_else_ with the following constructs:

bool'  = "⊤ ⊎ ⊤"
true'  = "inl trivial"
false' = "inr trivial"
ite'   = "(λ cond x y . (case ((λ_.x):⊤→ℕ) or ((λ_.y):⊤→ℕ)) cond) : ⊤ ⊎ ⊤ → ℕ → ℕ → ℕ"

_ : compile-eval (ite' ++ₛ true' ++ₛ "1" ++ₛ "0") ≡ inj₁ (Nat ,
                                                         lam (lam (lam (lam
                                                         (caseo (lam (q [ p ] [ p ]) [ p ] $ q) (lam (q [ p ]) [ p ] $ q))
                                                         $ q [ p ] [ p ]))) $ inl trivial $ suco zeroo $ zeroo
                                                         , λ γ* → 1)
_ = refl

-- note: our object language does not support polymorphic functions, so we cannot write a polymorphic ite
--       that's why we baked in the arbitrary ℕ return value in the previous example
