{-# OPTIONS --prop --rewriting --guardedness #-}

module Streams where

open import Data.Bool hiding (not) renaming (Bool to 𝟚; true to tt; false to ff)
open import Data.Nat using (suc)
open import Data.Sum using (inj₁; inj₂)
open import Data.String using (_++_)
open import Data.Product using (_,_)
open import Data.Unit renaming (tt to triv)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Elaborator
open import STLC
open STLC.I

-- Streams are coinductive types with the constructor: genStream

-- here we construct the infinite streams of even and odd numbers

--                    head op    tail op  seed    -- seed: we start from 0 (from 1 in odds)
evens = "genStream ((λn.n):ℕ→ℕ) (λn.n+2)   0"     -- head op: returns current state (what's in "memory")
                                                  -- tail op: advances stream by adding 2 to the previous state
odds  = "genStream ((λn.n):ℕ→ℕ) (λn.n+2)   1"

_ : compile-eval evens ≡ inj₁ (Ty.Stream Nat
                            , I.genStream (lam q [ p ] $ q) (lam (lam (lam (iteNat q (suco q) (q [ p ])))
                              $ q $ suco (suco zeroo)) [ p ] $ q) zeroo
                            , λ γ* → STLC.genStream (λ n → n) (λ n → iteℕ 2 (λ m → suc m) n) 0)
_ = refl
_ : compile-eval odds  ≡ inj₁ (Ty.Stream Nat
                            , I.genStream (lam q [ p ] $ q) (lam (lam (lam (iteNat q (suco q) (q [ p ])))
                              $ q $ suco (suco zeroo)) [ p ] $ q) (suco zeroo)
                            , λ γ* → STLC.genStream (λ n → n) (λ n → iteℕ 2 (λ m → suc m) n) 1)
_ = refl

-- destructors: head (returns result) and tail (advances a stream by constructing a new one from the old state)

_ : eval ("head"           ++ evens) ≡ inj₁ (Nat , λ γ* → 0)
_ = refl
_ : eval ("head tail"      ++ evens) ≡ inj₁ (Nat , λ γ* → 2)
_ = refl
_ : eval ("head tail tail" ++ evens) ≡ inj₁ (Nat , λ γ* → 4)
_ = refl

_ : eval ("head"           ++ odds) ≡ inj₁ (Nat , λ γ* → 1)
_ = refl
_ : eval ("head tail"      ++ odds) ≡ inj₁ (Nat , λ γ* → 3)
_ = refl
_ : eval ("head tail tail" ++ odds) ≡ inj₁ (Nat , λ γ* → 5)
_ = refl

-- generating the trivial lists of all lengths

trivial-lists = "genStream ((λts.ts):[⊤]→[⊤]) (λ ts. trivial ∷ ts) (nil : [⊤])"

_ : compile-eval trivial-lists ≡ inj₁ (Ty.Stream (Ty.List Unit)
                                    , I.genStream (lam q [ p ] $ q) (lam (cons trivial q) [ p ] $ q) nil
                                    , λ γ* → STLC.genStream (λ ts → ts) (λ ts → triv ∷ ts) [])
_ = refl

_ : eval ("head"           ++ trivial-lists) ≡ inj₁ (Ty.List Unit , λ γ* → [])
_ = refl
_ : eval ("head tail"      ++ trivial-lists) ≡ inj₁ (Ty.List Unit , λ γ* → triv ∷ [])
_ = refl
_ : eval ("head tail tail" ++ trivial-lists) ≡ inj₁ (Ty.List Unit , λ γ* → triv ∷ (triv ∷ []))
_ = refl

-- generating the lists of the first n naturals for all n ∈ ℕ

length = "((λ ns. iteList 0 (λ _ n. n+1) ns) : [ℕ] → ℕ)"

first-n = "genStream ((λns.ns):[ℕ]→[ℕ]) (λ ns. (" ++ length ++ " ns) ∷ ns) (nil : [ℕ])"

_ : compile-eval first-n ≡ inj₁ (Ty.Stream (Ty.List Nat)
                              , I.genStream (lam q [ p ] $ q) (lam (cons (lam (I.iteList zeroo
                                ((lam (lam (lam (lam (iteNat q (suco q) (q [ p ]))) $ q $ suco zeroo))
                                [ p ] $ q) [ p ] $ q) q) $ q) q) [ p ] $ q) nil
                              , λ γ* → STLC.genStream (λ ns → ns)
                                                      (λ ns → STLC.iteList 0 (λ _ n → iteℕ 1 (λ m → suc m) n) ns ∷ ns)
                                                      [])
_ = refl

_ : eval ("head"                ++ first-n) ≡ inj₁ (Ty.List Nat , (λ γ* → []))
_ = refl
_ : eval ("head tail"           ++ first-n) ≡ inj₁ (Ty.List Nat , (λ γ* → 0 ∷ []))
_ = refl
_ : eval ("head tail tail"      ++ first-n) ≡ inj₁ (Ty.List Nat , (λ γ* → 1 ∷ (0 ∷ [])))
_ = refl
_ : eval ("head tail tail tail" ++ first-n) ≡ inj₁ (Ty.List Nat , (λ γ* → 2 ∷ (1 ∷ (0 ∷ []))))
_ = refl

-- of course, we can parameterize genStream by returning it from a function

step-n = "(λ start diff. genStream ((λn.n):ℕ→ℕ) (λn. n+diff) start) : ℕ → ℕ → (Stream ℕ)"

_ : compile-eval step-n ≡ inj₁ (Nat ⇒ Nat ⇒ Ty.Stream Nat
                             , lam (lam (I.genStream (lam q [ p ] $ q) (lam (lam (lam
                               (iteNat q (suco q) (q [ p ]))) $ q $ q [ p ]) [ p ] $ q) (q [ p ])))
                             , (λ γ* start diff → STLC.genStream (λ n → n) (λ n → iteℕ diff (λ m → suc m) n) start))
_ = refl

_ : eval ("head           ((" ++ step-n ++ ") 10) 5") ≡ inj₁ (Nat , λ γ* → 10)
_ = refl
_ : eval ("head tail      ((" ++ step-n ++ ") 10) 5") ≡ inj₁ (Nat , λ γ* → 15)
_ = refl
_ : eval ("head tail tail ((" ++ step-n ++ ") 10) 5") ≡ inj₁ (Nat , λ γ* → 20)
_ = refl

_ : eval ("head           ((" ++ step-n ++ ") 0) 33") ≡ inj₁ (Nat , λ γ* → 0)
_ = refl
_ : eval ("head tail      ((" ++ step-n ++ ") 0) 33") ≡ inj₁ (Nat , λ γ* → 33)
_ = refl
_ : eval ("head tail tail ((" ++ step-n ++ ") 0) 33") ≡ inj₁ (Nat , λ γ* → 66)
_ = refl

-- but writing out a lot of tails to get later elements can get tiring...

-- so let's extract the nth (indexed from 0) element

get-nth = "(λ s n. head iteℕ s (λ ss. tail ss) n) : (Stream ℕ) → ℕ → ℕ"

_ : compile-eval get-nth ≡ inj₁ (Ty.Stream Nat ⇒ Nat ⇒ Nat
                              , lam (lam (head (iteNat (q [ p ]) (lam (tail q) [ p ] $ q) q)))
                              , (λ γ* s n → Stream.head (iteℕ s Stream.tail n)))
_ = refl

_ : eval (get-nth ++ₛ odds  ++ₛ  "8") ≡ inj₁ (Nat , λ γ* → 17)
_ = refl
_ : eval (get-nth ++ₛ evens ++ₛ "13") ≡ inj₁ (Nat , λ γ* → 26)
_ = refl

_ : eval ("((" ++ get-nth ++ ") (((" ++ step-n ++ ") 100) 25))" ++ "3") ≡ inj₁ (Nat , λ γ* → 175)
_ = refl
_ : eval ("((" ++ get-nth ++ ") (((" ++ step-n ++ ")   0) 30))" ++ "5") ≡ inj₁ (Nat , λ γ* → 150)
_ = refl

-- did we just accidentally reinvent multiplication? :-)
