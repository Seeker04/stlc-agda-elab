{-# OPTIONS --prop --rewriting --guardedness #-}

module Machines where

open import Data.Bool hiding (not) renaming (Bool to 𝟚; true to tt; false to ff)
open import Data.Nat using (suc)
open import Data.Sum using (inj₁; inj₂)
open import Data.String using (_++_)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Unit renaming (tt to triv)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Elaborator
open import STLC
open STLC.I

-- Machines are coinductive types with the constructor: genMachine

-- here we construct a machine that can add together its input, can reset to 0 and return the result
                                                           -- seed: we start from 0
--                            put      set    get  seed    -- put: we increment the sum with the input
sum-machine = "genMachine (λs i. s+i) (λ_.0) (λs.s) 0"     -- set: resets the sum to 0
                                                           -- get: returns the current sum (what's in "memory")
_ : compile-eval sum-machine ≡ inj₁ (Ty.Machine ,
                 I.genMachine ((lam (lam (iteNat q (suco q) (q [ p ]))) [ p ] $ q) [ p ] $ q)
                              (lam zeroo [ p ] $ q)
                              (lam q [ p ] $ q)
                              zeroo
                 , λ γ* → STLC.genMachine (λ s i → iteℕ i (λ x → suc x) s)
                                          (λ _ → 0)
                                          (λ s → s)
                                          0)
_ = refl

-- destructors: put (inserts value), set (sends a signal), get (returns state)

_ : eval ("get "                 ++ sum-machine)                ≡ inj₁ (Nat , λ γ* →  0)
_ = refl
_ : eval ("get put "             ++ sum-machine ++ " 10")       ≡ inj₁ (Nat , λ γ* → 10)
_ = refl
_ : eval ("get put put put "     ++ sum-machine ++ " 10 20 30") ≡ inj₁ (Nat , λ γ* → 60)
_ = refl
_ : eval ("get put put set put " ++ sum-machine ++ " 10 20 30") ≡ inj₁ (Nat , λ γ* → 50)
_ = refl

-- this machine works similarly, but adds together the odd and even numbers separately
-- it has a switch, which can be toggled using the set operation, that determines which sum get returns
-- (it returns the sum of odd numbers by default)
-- the machine stores the sum of odd numbers, sum of even numbers and the switch's state in a 𝕃 × ℕ × ℕ triple

not  = "((λ a. if a then false else true)       : 𝕃 → 𝕃)" 
even = "((λ x. iteℕ true (λa." ++ not ++ "a) x) : ℕ → 𝕃)" -- explained in Nats.agda

partitioned-sums = "genMachine                                                  \
\                     (λs i. if (" ++ even ++ "i) then                          \
\                       ((fst s) ,  (fst snd s)      , ((snd snd s) + i))       \
\                     else                                                      \
\                       ((fst s) , ((fst snd s) + i) ,  (snd snd s)    ))       \
\                     (λs. (" ++ not ++ "(fst s)) , (fst snd s) , (snd snd s))  \
\                     (λs. if (fst s) then (fst snd s) else (snd snd s))        \
\                     (true , 0 , 0)"

_ : compile-eval partitioned-sums ≡ inj₁ (Ty.Machine ,
 I.genMachine
 ((lam (lam
   (iteBool
     ⟨ fst (q [ p ]) , ⟨ fst (snd (q [ p ])) , iteNat q (suco q) (snd (snd (q [ p ]))) ⟩ ⟩
     ⟨ fst (q [ p ]) , ⟨ iteNat q (suco q) (fst (snd (q [ p ]))) , snd (snd (q [ p ])) ⟩ ⟩
     (lam (iteNat true (lam (lam (iteBool false true q) $ q) [ p ] $ q) q) $ q))) [ p ] $ q) [ p ] $ q)

 (lam
   ⟨ lam (iteBool false true q) $ fst q ,
   ⟨ fst (snd q) ,
   snd (snd q) ⟩ ⟩
   [ p ] $ q)

 (lam (iteBool (fst (snd q)) (snd (snd q)) (fst q)) [ p ] $ q)

 ⟨ true , ⟨ zeroo , zeroo ⟩ ⟩

 ,

 (λ γ* → STLC.genMachine
    (λ s i →
       if iteℕ tt (λ b → if b then ff else tt) i then
         proj₁ s ,
         proj₁ (proj₂ s) ,
         iteℕ i (λ x → suc x) (proj₂ (proj₂ s))
       else
         proj₁ s ,
         iteℕ i (λ x → suc x) (proj₁ (proj₂ s)) ,
         proj₂ (proj₂ s))

    (λ s → (if proj₁ s then ff else tt) , proj₁ (proj₂ s) , proj₂ (proj₂ s))

    (λ s → if proj₁ s then proj₁ (proj₂ s) else proj₂ (proj₂ s))

    (tt , 0 , 0)))

_ = refl

_ : eval ("get put put put put"     ++ partitioned-sums ++ "3 10 1 8") ≡ inj₁ (Nat , λ γ* → 4)
_ = refl
_ : eval ("get put put put put set" ++ partitioned-sums ++ "3 10 1 8") ≡ inj₁ (Nat , λ γ* → 18)
_ = refl

-- we already see that we can construct inner states of arbitrary complexity
-- similarly, we could support machine types which have more than one input methods (like put),
-- output methods (like get) and signals (like set), essentially simulating things like
-- Turing machines, REPLs or even operating systems...
