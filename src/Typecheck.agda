{-# OPTIONS --prop --rewriting --guardedness #-}

module Typecheck where

open import Level hiding (suc)
open import Agda.Builtin.Sigma using (Σ)
open import Agda.Builtin.Bool hiding (Bool) renaming (true to tt; false to ff)
open import Data.Nat using (ℕ; suc)
open import Data.Fin using (Fin; zero; suc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)

open import Parser Level.zero hiding (_⇒_; num)
open import Scopecheck hiding (lookup)
open import STLC
open STLC.I

--------------------------------------
-- Type inference and checking

length : Con → ℕ
length = λ { ◇ → 0 ; (Γ ▹ _) → suc (length Γ) }

lookup : (Γ : Con) → Fin (length Γ) → (Σ Ty λ A → Tm Γ A)
lookup (Γ ▹ A) zero    = A , q
lookup (Γ ▹ A) (suc n) = proj₁ rest , proj₂ rest [ p ] where
  rest : Σ Ty λ A → Tm Γ A
  rest = lookup Γ n

fconv : {Γ : Con}{A B : Ty} → Tm Γ (A ⇒ B) → Tm (Γ ▹ A) B
fconv f = f [ p ] $ q
-- In fact, Tm Γ (A ⇒ B) and Tm (Γ ▹ A) B are isomorphic (the other direction is the definition of lam itself)

_≟_ : (A B : Ty) → Dec (A ≡ B)
Nat  ≟ Nat      = yes refl
Nat  ≟ Bool     = no λ ()
Nat  ≟ Unit     = no λ ()
Nat  ≟ Empty    = no λ ()
Nat  ≟ (_ ⇒  _) = no λ ()
Nat  ≟ (_ ×o _) = no λ ()
Nat  ≟ (_ +o _) = no λ ()
Nat  ≟ List _   = no λ ()
Nat  ≟ Tree _   = no λ ()
Nat  ≟ Stream _ = no λ ()
Nat  ≟ Machine  = no λ ()

Bool ≟ Nat      = no λ ()
Bool ≟ Bool     = yes refl
Bool ≟ Unit     = no λ ()
Bool ≟ Empty    = no λ ()
Bool ≟ (_ ⇒  _) = no λ ()
Bool ≟ (_ ×o _) = no λ ()
Bool ≟ (_ +o _) = no λ ()
Bool ≟ List _   = no λ ()
Bool ≟ Tree _   = no λ ()
Bool ≟ Stream _ = no λ ()
Bool ≟ Machine  = no λ ()

Unit ≟ Nat      = no λ ()
Unit ≟ Bool     = no λ ()
Unit ≟ Unit     = yes refl
Unit ≟ Empty    = no λ ()
Unit ≟ (_ ⇒  _) = no λ ()
Unit ≟ (_ ×o _) = no λ ()
Unit ≟ (_ +o _) = no λ ()
Unit ≟ List _   = no λ ()
Unit ≟ Tree _   = no λ ()
Unit ≟ Stream _ = no λ ()
Unit ≟ Machine  = no λ ()

Empty ≟ Nat      = no λ ()
Empty ≟ Bool     = no λ ()
Empty ≟ Unit     = no λ ()
Empty ≟ Empty    = yes refl
Empty ≟ (_ ⇒  _) = no λ ()
Empty ≟ (_ ×o _) = no λ ()
Empty ≟ (_ +o _) = no λ ()
Empty ≟ List _   = no λ ()
Empty ≟ Tree _   = no λ ()
Empty ≟ Stream _ = no λ ()
Empty ≟ Machine  = no λ ()

(_ ⇒ _) ≟ Nat      = no λ ()
(_ ⇒ _) ≟ Bool     = no λ ()
(_ ⇒ _) ≟ Unit     = no λ ()
(_ ⇒ _) ≟ Empty    = no λ ()
(_ ⇒ _) ≟ (_ ×o _) = no λ ()
(_ ⇒ _) ≟ (_ +o _) = no λ ()
(_ ⇒ _) ≟ List _   = no λ ()
(_ ⇒ _) ≟ Tree _   = no λ ()
(_ ⇒ _) ≟ Stream _ = no λ ()
(_ ⇒ _) ≟ Machine  = no λ ()
(A₁ ⇒ A₂) ≟ (B₁ ⇒ B₂) with A₁ ≟ B₁ | A₂ ≟ B₂
... | yes e₁ | yes e₂ = yes (cong₂ _⇒_ e₁ e₂)
... | yes e₁ | no ¬e₂ = no λ hyp → ¬e₂ (cong ⇒snd hyp) where
  ⇒snd : Ty → Ty
  ⇒snd = λ { (A ⇒ B) → B ; X → X }
... | no ¬e₁ | yes e₂ = no λ hyp → ¬e₁ (cong ⇒fst hyp) where
  ⇒fst : Ty → Ty
  ⇒fst = λ { (A ⇒ B) → A ; X → X }
... | no ¬e₁ | no ¬e₂ = no λ hyp → ¬e₁ (cong ⇒fst hyp) where
  ⇒fst : Ty → Ty
  ⇒fst = λ { (A ⇒ B) → A ; X → X }

(_ ×o _) ≟ Nat      = no λ ()
(_ ×o _) ≟ Bool     = no λ ()
(_ ×o _) ≟ Unit     = no λ ()
(_ ×o _) ≟ Empty    = no λ ()
(_ ×o _) ≟ (_ +o _) = no λ ()
(_ ×o _) ≟ (_ ⇒ _)  = no λ ()
(_ ×o _) ≟ List _   = no λ ()
(_ ×o _) ≟ Tree _   = no λ ()
(_ ×o _) ≟ Stream _ = no λ ()
(_ ×o _) ≟ Machine  = no λ ()
(A₁ ×o A₂) ≟ (B₁ ×o B₂) with A₁ ≟ B₁ | A₂ ≟ B₂
... | yes e₁ | yes e₂ = yes (cong₂ _×o_ e₁ e₂)
... | yes e₁ | no ¬e₂ = no λ hyp → ¬e₂ (cong ×snd hyp) where
  ×snd : Ty → Ty
  ×snd = λ { (A ×o B) → B ; X → X }
... | no ¬e₁ | yes e₂ = no λ hyp → ¬e₁ (cong ×fst hyp) where
  ×fst : Ty → Ty
  ×fst = λ { (A ×o B) → A ; X → X }
... | no ¬e₁ | no ¬e₂ = no λ hyp → ¬e₁ (cong ×fst hyp) where
  ×fst : Ty → Ty
  ×fst = λ { (A ×o B) → A ; X → X }

(_ +o _) ≟ Nat      = no λ ()
(_ +o _) ≟ Bool     = no λ ()
(_ +o _) ≟ Unit     = no λ ()
(_ +o _) ≟ Empty    = no λ ()
(_ +o _) ≟ (_ ⇒ _)  = no λ ()
(_ +o _) ≟ (_ ×o _) = no λ ()
(_ +o _) ≟ List _   = no λ ()
(_ +o _) ≟ Tree _   = no λ ()
(_ +o _) ≟ Stream _ = no λ ()
(_ +o _) ≟ Machine  = no λ ()
(A₁ +o A₂) ≟ (B₁ +o B₂) with A₁ ≟ B₁ | A₂ ≟ B₂
... | yes e₁ | yes e₂ = yes (cong₂ _+o_ e₁ e₂)
... | yes e₁ | no ¬e₂ = no λ hyp → ¬e₂ (cong +snd hyp) where
  +snd : Ty → Ty
  +snd = λ { (A +o B) → B ; X → X }
... | no ¬e₁ | yes e₂ = no λ hyp → ¬e₁ (cong +fst hyp) where
  +fst : Ty → Ty
  +fst = λ { (A +o B) → A ; X → X }
... | no ¬e₁ | no ¬e₂ = no λ hyp → ¬e₁ (cong +fst hyp) where
  +fst : Ty → Ty
  +fst = λ { (A +o B) → A ; X → X }

List _ ≟ Nat      = no λ ()
List _ ≟ Bool     = no λ ()
List _ ≟ Unit     = no λ ()
List _ ≟ Empty    = no λ ()
List _ ≟ (_ ⇒ _)  = no λ ()
List _ ≟ (_ ×o _) = no λ ()
List _ ≟ (_ +o _) = no λ ()
List _ ≟ Tree _   = no λ ()
List _ ≟ Stream _ = no λ ()
List _ ≟ Machine  = no λ ()
List A ≟ List B with A ≟ B
... | yes e = yes (cong Ty.List e)
... | no ¬e = no λ hyp → ¬e (cong (λ { (Ty.List A) → A ; X → X }) hyp)

Tree _ ≟ Nat      = no λ ()
Tree _ ≟ Bool     = no λ ()
Tree _ ≟ Unit     = no λ ()
Tree _ ≟ Empty    = no λ ()
Tree _ ≟ (_ ⇒ _)  = no λ ()
Tree _ ≟ (_ ×o _) = no λ ()
Tree _ ≟ (_ +o _) = no λ ()
Tree _ ≟ List _   = no λ ()
Tree _ ≟ Stream _ = no λ ()
Tree _ ≟ Machine  = no λ ()
Tree A ≟ Tree B with A ≟ B
... | yes e = yes (cong Ty.Tree e)
... | no ¬e = no λ hyp → ¬e (cong (λ { (Ty.Tree A) → A ; X → X }) hyp)

Stream _ ≟ Nat      = no λ ()
Stream _ ≟ Bool     = no λ ()
Stream _ ≟ Unit     = no λ ()
Stream _ ≟ Empty    = no λ ()
Stream _ ≟ (_ ⇒ _)  = no λ ()
Stream _ ≟ (_ ×o _) = no λ ()
Stream _ ≟ (_ +o _) = no λ ()
Stream _ ≟ List _   = no λ ()
Stream _ ≟ Machine  = no λ ()
Stream _ ≟ Tree _   = no λ ()
Stream A ≟ Stream B with A ≟ B
... | yes e = yes (cong Ty.Stream e)
... | no ¬e = no λ hyp → ¬e (cong (λ { (Ty.Stream A) → A ; X → X }) hyp)

Machine ≟ Nat      = no λ ()
Machine ≟ Bool     = no λ ()
Machine ≟ Unit     = no λ ()
Machine ≟ Empty    = no λ ()
Machine ≟ (_ ⇒ _)  = no λ ()
Machine ≟ (_ ×o _) = no λ ()
Machine ≟ (_ +o _) = no λ ()
Machine ≟ List _   = no λ ()
Machine ≟ Stream _ = no λ ()
Machine ≟ Tree _   = no λ ()
Machine ≟ Machine  = yes refl

infer-ty : SType → Maybe Ty
infer-ty s-Nat  = just Nat
infer-ty s-Bool = just Bool
infer-ty s-⊤    = just Unit
infer-ty s-⊥    = just Empty
infer-ty (A s-→ B) with infer-ty A | infer-ty B
... | just A' | just B' = just (A' ⇒ B')
... | _       | _       = nothing
infer-ty (A s-× B) with infer-ty A | infer-ty B
... | just A' | just B' = just (A' ×o B')
... | _       | _       = nothing
infer-ty (A s-⊎ B) with infer-ty A | infer-ty B
... | just A' | just B' = just (A' +o B')
... | _       | _       = nothing
infer-ty (s-List A) with infer-ty A
... | just A' = just (Ty.List A')
... | nothing = nothing
infer-ty (s-Tree A) with infer-ty A
... | just A' = just (Ty.Tree A')
... | nothing = nothing
infer-ty (s-Stream A) with infer-ty A
... | just A' = just (Ty.Stream A')
... | nothing = nothing
infer-ty (s-Machine) = just Ty.Machine

infer : (Γ : Con) → ABT (length Γ) → Maybe (Σ Ty λ A → Tm Γ A)
check : (Γ : Con) → (A : Ty) → ABT (length Γ) → Maybe (Tm Γ A)

-- Infer

infer Γ abt-true  = just (Bool , true)
infer Γ abt-false = just (Bool , false)

infer Γ (abt-ite t u v) with infer Γ t | infer Γ u | infer Γ v
... | just (Bool , t') | just (A , u') | just (B , v') with B ≟ A
... | yes e = just (A , iteBool u' (transp (λ X → Tm Γ X) e v') t')
... | _     = nothing
infer Γ (abt-ite t u v) | _ | _ | _ = nothing

infer Γ (abt-isZero t) with infer Γ t
... | just (Nat , t') = just (Bool , iteNat true false t')
... | _               = nothing

infer Γ (u abt-+ v) with infer Γ u | infer Γ v
... | just (Nat , u') | just (Nat , v') = just (Nat , lam (lam (iteNat q (suco q) (q [ p ]))) $ u' $ v')
... | _               | _               = nothing

infer Γ (abt-num 0) = just (Nat , zeroo)
infer Γ (abt-num (suc n)) with infer Γ (abt-num n)
... | just (Nat , n') = just (Nat , suco n')
... | _ = nothing

infer Γ (abt-λ t)   = nothing

infer Γ (u abt-$ v)     with infer Γ u
... | just (A ⇒ B , u') with check Γ A v
... | just v' = just (B , u' $ v')
... | nothing = nothing
infer Γ (u abt-$ v) | _ = nothing

infer Γ (abt-var n) = just (lookup Γ n)

infer Γ (u abt-, v) with infer Γ u | infer Γ v
... | just (A , u') | just (B , v') = just (A ×o B , ⟨ u' , v' ⟩)
... | _             | _             = nothing

infer Γ (abt-fst u) with infer Γ u
... | just (A ×o B , u') = just (A , fst u')
... | _                  = nothing

infer Γ (abt-snd u) with infer Γ u
... | just (A ×o B , u') = just (B , snd u')
... | _                  = nothing

infer Γ (abt-inl u) = nothing
infer Γ (abt-inr u) = nothing

infer Γ (abt-case u v) with infer Γ u | infer Γ v
... | just (A ⇒ C₁ , u') | just (B ⇒ C₂ , v') with C₂ ≟ C₁
... | yes e = just ((A +o B) ⇒ C₁ , lam (caseo (fconv u')
                                               (fconv (transp (λ X → Tm Γ (B ⇒ X)) e v'))))
... | no ¬e = nothing
infer Γ (abt-case u v) | _ | _ = nothing

infer Γ abt-triv = just (Unit , trivial)

infer Γ abt-nil = nothing

infer Γ (u abt-∷ v) with infer Γ u
... | just (A , u') with check Γ (Ty.List A) v
... | just v' = just (Ty.List A , cons u' v')
... | nothing = nothing
infer Γ (u abt-∷ v) | _ = nothing

infer Γ (abt-leaf t) with infer Γ t
... | just (A , t') = just (Ty.Tree A , I.leaf t')
... | nothing = nothing

infer Γ (u abt-node v) with infer Γ u | infer Γ v
... | just (Ty.Tree A , u') | just (Ty.Tree B , v') with B ≟ A
... | yes e = just (Ty.Tree A , I.node u' (transp (λ X → Tm Γ (Ty.Tree X)) e v'))
... | no ¬e = nothing
infer Γ (u abt-node v) | _ | _ = nothing

infer Γ (abt-iteℕ t u v) with infer Γ t | infer Γ v
... | just (A , t') | just (Nat , v') with check Γ (A ⇒ A) u
... | just u' = just (A , iteNat t' (fconv u') v')
... | nothing = nothing
infer Γ (abt-iteℕ t u v) | _ | _ = nothing

infer Γ (abt-iteList t u v) with infer Γ t | infer Γ v
... | just (B , t') | just (List A , v') with check Γ (A ⇒ B ⇒ B) u
... | just u' = just (B , I.iteList t' (fconv (fconv u')) v')
... | nothing = nothing
infer Γ (abt-iteList t u v) | _ | _ = nothing

infer Γ (abt-iteTree t u v) with infer Γ t | infer Γ v
... | just (A ⇒ B , t') | just (Tree F , v') with A ≟ F | check Γ (B ⇒ B ⇒ B) u
... | yes e | just u' = just (B , I.iteTree (fconv (transp (λ X → Tm Γ (X ⇒ _)) e t')) (fconv (fconv u')) v')
... | _     | _       = nothing
infer Γ (abt-iteTree t u v) | _ | _ = nothing

infer Γ (abt-head t) with infer Γ t
... | just (Stream A , t') = just (A , I.head t')
... | _                    = nothing

infer Γ (abt-tail t) with infer Γ t
... | just (Stream A , t') = just (Ty.Stream A , I.tail t')
... | _                    = nothing

infer Γ (abt-genStream hd tl seed) with infer Γ hd | infer Γ seed
... | just (B ⇒ A , hd') | just (S , seed') with B ≟ S | check Γ (S ⇒ S) tl
... | yes e | just tl' = just (Ty.Stream A , I.genStream (fconv (transp (λ X → Tm Γ (X ⇒ A)) e hd'))
                                                         (fconv tl')
                                                         seed')
... | _     | _        = nothing
infer Γ (abt-genStream hd tl seed) | _ | _ = nothing

infer Γ (abt-put u v) with infer Γ u | infer Γ v
... | just (Machine , u') | just (Nat , v') = just (Ty.Machine , put u' v')
... | _                   | _               = nothing

infer Γ (abt-set t) with infer Γ t
... | just (Machine , t') = just (Ty.Machine , set t')
... | _                   = nothing

infer Γ (abt-get t) with infer Γ t
... | just (Machine , t') = just (Nat , get t')
... | _                   = nothing

infer Γ (abt-genMachine put set get seed) with infer Γ seed
... | just (S , seed') with check Γ (S ⇒ Nat ⇒ S) put | check Γ (S ⇒ S) set | check Γ (S ⇒ Nat) get
... | just put' | just set' | just get' = just (Ty.Machine , I.genMachine (fconv (fconv put'))
                                                                          (fconv set')
                                                                          (fconv get')
                                                                          seed')
... | _         | _         | _         = nothing
infer Γ (abt-genMachine put set get seed) | _ = nothing

infer Γ (abt-ann t ty) with infer-ty ty
... | just A           with check Γ A t
... | just t' = just (A , t')
... | nothing = nothing
infer Γ (abt-ann t ty) | nothing = nothing

-- Check

check Γ (A +o _) (abt-inl t) with infer Γ t
... | just (B , t') with B ≟ A
... | yes e = just (inl (transp (λ X → Tm Γ X) e t'))
... | _     = nothing
check Γ (A +o _) (abt-inl t) | nothing = nothing

check Γ (_ +o A) (abt-inr t) with infer Γ t
... | just (B , t') with B ≟ A
... | yes e = just (inr (transp (λ X → Tm Γ X) e t'))
... | _     = nothing
check Γ (_ +o A) (abt-inr t) | nothing = nothing

check Γ (List A) abt-nil = just nil

check Γ (A ⇒ B) (abt-λ t) with check (Γ ▹ A) B t
... | just t' = just (lam t')
... | nothing = nothing

check Γ A (abt-ann t ty) with infer Γ (abt-ann t ty)
... | just (B , t') with B ≟ A
... | yes e = just (transp (λ X → Tm Γ X) e t')
... | no ¬e = nothing
check Γ A (abt-ann t ty) | nothing = nothing

check Γ A t with infer Γ t
... | nothing = nothing
... | just (B , t') with B ≟ A
... | yes e = just (transp (λ X → Tm Γ X) e t')
... | _     = nothing

--------------------------------------
-- Examples (see: Tests.agda for more)

private
  _ : infer ◇ (abt-num 1 abt-+ abt-true) ≡ nothing
  _ = refl

  _ : infer ◇ (abt-num 1 abt-+ abt-num 2) ≡ just (Nat , lam (lam (iteNat q (suco q) (q [ p ])))
                                                        $ suco zeroo $ suco (suco zeroo))
  _ = refl
  _ : infer ◇ (abt-ann (abt-λ (abt-λ
              (abt-var (suc Fin.zero) abt-+ abt-var Fin.zero)))
              (s-Nat s-→ (s-Nat s-→ s-Nat))) ≡ just (Nat ⇒ Nat ⇒ Nat ,
                                                     lam (lam (lam (lam
                                                     (iteNat q (suco q) (q [ p ]))) $ q [ p ] $ q)))

  _ = refl
