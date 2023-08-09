{-# OPTIONS --prop --rewriting --guardedness #-}

module Errors where

open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Elaborator
open import STLC
open STLC.I

-- Syntax errors

_ : compile "isZero"             ≡ inj₂ syntax-error
_ = refl
_ : compile "1 + "               ≡ inj₂ syntax-error
_ = refl
_ : compile " + 2"               ≡ inj₂ syntax-error
_ = refl
_ : compile "if 0 then 1"        ≡ inj₂ syntax-error
_ = refl
_ : compile "if 0 else 0 then 1" ≡ inj₂ syntax-error
_ = refl
_ : compile "10 ,"               ≡ inj₂ syntax-error
_ = refl
_ : compile "inl"                ≡ inj₂ syntax-error
_ = refl
_ : compile "((10)"              ≡ inj₂ syntax-error
_ = refl
_ : compile ") false"            ≡ inj₂ syntax-error
_ = refl
_ : compile "()"                 ≡ inj₂ syntax-error
_ = refl
_ : compile ""                   ≡ inj₂ syntax-error
_ = refl
_ : compile "10 ∷ 20 ∷"          ≡ inj₂ syntax-error
_ = refl
_ : compile "<42> | "            ≡ inj₂ syntax-error
_ = refl

-- Syntax errors in type annotations

_ : compile "(foo) : float"       ≡ inj₂ syntax-error
_ = refl
_ : compile "(foo) : →"           ≡ inj₂ syntax-error
_ = refl
_ : compile "(foo) : 𝕃 →"         ≡ inj₂ syntax-error
_ = refl
_ : compile "(foo) : → 𝕃"         ≡ inj₂ syntax-error
_ = refl
_ : compile "(foo) : ⊤ → → ⊥"     ≡ inj₂ syntax-error
_ = refl
_ : compile "(foo) : ℕ × ℕ ×"     ≡ inj₂ syntax-error
_ = refl
_ : compile "(foo) : ⊎ ⊤"         ≡ inj₂ syntax-error
_ = refl
_ : compile "(foo) : List"        ≡ inj₂ syntax-error
_ = refl
_ : compile "(foo) : Tree → List" ≡ inj₂ syntax-error
_ = refl
_ : compile "(foo) : ℕ Stream"    ≡ inj₂ syntax-error
_ = refl

-- Scope errors

_ : compile "foo"                                         ≡ inj₂ scope-error
_ = refl
_ : compile "(λ foo. bar) : ℕ → ℕ"                        ≡ inj₂ scope-error
_ = refl
_ : compile "(λ x y. if x then y else x + z) : ℕ → ℕ → ℕ" ≡ inj₂ scope-error
_ = refl
_ : compile "((λx.x) : ℕ → ℕ) x"                          ≡ inj₂ scope-error
_ = refl
_ : compile "(((λx.x) : ℕ → ℕ) 1) + (((λy.x) : ℕ → ℕ) 2)" ≡ inj₂ scope-error
_ = refl
_ : compile "(λx. (((λy. y) : ℕ → ℕ) 4) + y) : ℕ → ℕ"     ≡ inj₂ scope-error
_ = refl

-- Type errors

_ : compile "1 + 2 + nil + 3"            ≡ inj₂ type-error -- cannot add Nat and list
_ = refl
_ : compile "if true then 0 else false"  ≡ inj₂ type-error -- branches have different types
_ = refl
_ : compile "if 42 then 0 else 1"        ≡ inj₂ type-error -- condition must be Bool
_ = refl
_ : compile "λx.x"                       ≡ inj₂ type-error -- not annotated, type unknown
_ = refl
_ : compile "10 true"                    ≡ inj₂ type-error -- application on non-function type
_ = refl
_ : compile "(λf. f true) : 𝕃 → ℕ → ℕ"   ≡ inj₂ type-error -- → is right associative (we curry by default)
_ = refl
_ : compile "((λn . n+1) : ℕ → ℕ) false" ≡ inj₂ type-error -- argument has incorrect type
_ = refl
_ : compile "inl 2"                      ≡ inj₂ type-error -- cannot deduce full type
_ = refl
_ : compile "true ∷ (isZero 0)"          ≡ inj₂ type-error -- 2nd operand to cons is not a list
_ = refl
_ : compile "[1, trivial]"               ≡ inj₂ type-error -- different type of elements
_ = refl
_ : compile "[]"                         ≡ inj₂ type-error -- type cannot be deduced
_ = refl
_ : compile "([]) : ℕ"                   ≡ inj₂ type-error -- Nat is not a List type
_ = refl
_ : compile "[0, false, 1]"              ≡ inj₂ type-error -- list is not homogeneous
_ = refl
_ : compile "<0> | (<1> | <true>)"       ≡ inj₂ type-error -- tree is not homogeneous
_ = refl
_ : compile "(inl trivial) : ℕ ⊎ ⊤"      ≡ inj₂ type-error -- inl instead of inr
_ = refl
_ : compile "(inr 42)      : ℕ ⊎ ⊤"      ≡ inj₂ type-error -- inr instead of inl
_ = refl
