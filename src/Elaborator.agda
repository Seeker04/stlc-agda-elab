{-# OPTIONS --prop --rewriting --guardedness #-}

open import Level hiding (suc)
open import Agda.Builtin.Sigma using (Σ)
open import Data.Bool renaming (Bool to 𝟚; true to tt; false to ff)
open import Data.Fin using (Fin; zero; suc)
open import Data.String using (String)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; _∷_; [])
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Lexer
open import Text.Lexer keywords breaking default
open import Parser Level.zero hiding (_⇒_; num)
open import Scopecheck hiding (lookup)
open import Typecheck

open import STLC
open STLC.I
module St = Model St

--------------------------------------
-- Elaboration

-- elaborate     returns each intermediate step of the process
-- compile-eval  returns error or compiled program and its evaluation in the standard model
-- compile       returns error or compiled program
-- eval          returns error or evaluation
-- compileM      Maybe version of compile
-- evalM         Maybe version of eval

Program    = Σ Ty λ A → Tm ◇ A                    -- a term with its type that is valid in the empty context
Evaluation = Σ Ty λ A → St.Tm St.⟦ ◇ ⟧C St.⟦ A ⟧T -- interpretation in the standard model (which Agda can normalise for us)
ProgEval   = Σ Ty λ A → (Tm ◇ A × St.Tm St.⟦ ◇ ⟧C St.⟦ A ⟧T)

elaborate : String → Maybe ((Data.List.List Token) × Maybe (AST × Maybe (ABT 0 × Maybe ProgEval)))
elaborate code = case just (tokenize code)                     of λ where
  nothing               → nothing
  (just tokens)         → case parse code                      of λ where
    nothing             → just (tokens , nothing)
    (just ast)          → case scopecheck ast                  of λ where
      nothing           → just (tokens , just (ast , nothing))
      (just abt)        → case infer ◇ abt                     of λ where
        nothing         → just (tokens , just (ast , just (abt , nothing)))
        (just (A , tm)) → just (tokens , just (ast , just (abt , just (A , (tm , St.⟦ tm ⟧t)))))

-- note: putting `parse code` into a with abstraction leads Agda 2.6.2.2 to an infinite loop for some reason,
--       but thankfully, case_of_ does not

data Error : Set where
  lexical-error : Error
  syntax-error  : Error
  scope-error   : Error
  type-error    : Error

compile-eval : String → ProgEval ⊎ Error
compile-eval code = case elaborate code of λ where
  nothing                                        → inj₂ lexical-error
  (just (_  , nothing))                          → inj₂ syntax-error
  (just (_ , just (_ , nothing)))                → inj₂ scope-error
  (just (_ , just (_ , just(_ , nothing))))      → inj₂ type-error
  (just (_ , just (_ , just(_ , just tm-eval)))) → inj₁ tm-eval

compile : String → Program ⊎ Error
compile code = case compile-eval code of λ where
  (inj₂ error)        → inj₂ error
  (inj₁ (A , tm , _)) → inj₁ (A , tm)

eval : String → Evaluation ⊎ Error
eval code = case compile-eval code of λ where
  (inj₂ error)          → inj₂ error
  (inj₁ (A , _ , eval)) → inj₁ (A , eval)

compileM : String → Maybe Program
compileM code = case compile code of λ where
  (inj₂ _)  → nothing
  (inj₁ tm) → just tm

evalM : String → Maybe Evaluation
evalM code = case eval code of λ where
  (inj₂ _)    → nothing
  (inj₁ eval) → just eval

--------------------------------------
-- Examples (see: Tests.agda for more)

private
  _ : elaborate "(λ x. isZero x) : ℕ → 𝕃" ≡ just ((record { line = 0 ; offset =  0 } , t-lpar   ) ∷
                                                  (record { line = 0 ; offset =  1 } , t-λ      ) ∷
                                                  (record { line = 0 ; offset =  3 } , t-var "x") ∷
                                                  (record { line = 0 ; offset =  4 } , t-dot    ) ∷
                                                  (record { line = 0 ; offset =  6 } , t-isZero ) ∷
                                                  (record { line = 0 ; offset = 13 } , t-var "x") ∷
                                                  (record { line = 0 ; offset = 14 } , t-rpar   ) ∷
                                                  (record { line = 0 ; offset = 16 } , t-:      ) ∷
                                                  (record { line = 0 ; offset = 18 } , t-ℕ      ) ∷
                                                  (record { line = 0 ; offset = 20 } , t-→      ) ∷
                                                  (record { line = 0 ; offset = 22 } , t-𝕃      ) ∷ [] ,
                                                  just (s-ann (s-λ ("x" ∷ []) (s-isZero (s-var "x"))) (s-Nat s-→ s-Bool) ,
                                                  just (abt-ann (abt-λ (abt-isZero (abt-var Fin.zero))) (s-Nat s-→ s-Bool) ,
                                                  just (Nat ⇒ Bool , lam (iteNat true false q) ,
                                                                     (λ γ* α* → iteℕ tt (λ x → ff) α*)))))
  _ = refl

  _ : compile-eval "1 + 2 + 3" ≡ inj₁ (Nat , (lam (lam (iteNat q (suco q) (q [ p ]))) $
                                             (lam (lam (iteNat q (suco q) (q [ p ]))) $
                                             suco zeroo $ suco (suco zeroo)) $ suco (suco (suco zeroo)))
                                           , λ γ* → 6)
  _ = refl

  _ : compile "if true then else" ≡ inj₂ syntax-error
  _ = refl
  _ : compile "10 + "             ≡ inj₂ syntax-error
  _ = refl
  _ : compile "10 + foo"          ≡ inj₂ scope-error
  _ = refl
  _ : compile "10 + true"         ≡ inj₂ type-error
  _ = refl
  _ : compile "[1, 2, true, 4]"   ≡ inj₂ type-error
  _ = refl
  _ : compile "(λx.x) : ℕ → ℕ"    ≡ inj₁ (Nat ⇒ Nat , lam q)
  _ = refl

  _ : eval "if isZero 0 then [1,2,(1+2)] else [42]" ≡ inj₁ (Ty.List Nat , (λ γ* → 1 ∷ (2 ∷ (3 ∷ []))))
  _ = refl
