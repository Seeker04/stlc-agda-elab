{-# OPTIONS --prop --rewriting --guardedness #-}

module Others where

open import Data.Bool hiding (not) renaming (Bool to 𝟚; true to tt; false to ff)
open import Data.Nat using (suc)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)
open import Data.Unit renaming (tt to triv)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Elaborator
open import STLC
open STLC.I

-- A collection of tests that don't really fit anywhere else

-- alpha equivalence

_ : compile-eval "(λx.x) : ℕ → ℕ" ≡ compile-eval "(λy.y) : ℕ → ℕ"
_ = refl

-- unrolling shorthand lambda notation

_ : compile-eval "(λ x y z. x+y+z) : ℕ → ℕ → ℕ → ℕ" ≡ compile-eval "(λ x. λ y. λ z. x+y+z) : ℕ → ℕ → ℕ → ℕ"
_ = refl
