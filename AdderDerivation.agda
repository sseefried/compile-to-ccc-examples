{-# OPTIONS --without-K --safe #-}

module AdderDerivation where

open import Data.Product
open import Data.Bool
open import Relation.Binary.PropositionalEquality
open import FunctionCategory

private
  variable
    A B C : Set

adder : Bool × Bool × Bool → Bool
adder = λ (a , b , c) → xor (a , xor (b , c ))


adderDerivation : (λ (a , b , c) → xor (a , xor (b , c ))) ≡ (xor ∘ (exl △ (xor ∘ ((exl ∘ exr) △ (exr ∘ exr)))))
adderDerivation = begin
    (λ (a , b , c) → xor (a , xor (b , c )))
 ≡⟨⟩ -- desugar pairs
    (λ p → xor (exl p , xor ((exl ∘ exr) p , (exr ∘ exr) p)))
 ≡⟨⟩ -- application rule
    apply ∘ ((λ p → xor) △ λ p → (exl p , xor ((exl ∘ exr) p , (exr ∘ exr) p)))
 ≡⟨⟩ -- eta expand
    (apply ∘ ((λ p → xor) △ λ p → (exl p , (λ q → xor (((exl ∘ exr) q , (exr ∘ exr) q))) p)))
 ≡⟨⟩ -- const rule and definition of △
    apply ∘ ((const xor) △ (exl △ (λ q → xor (((exl ∘ exr) q , (exr ∘ exr) q)))))
 ≡⟨⟩ -- applyConstFork rule from DerivedCCCRules.agda
    xor ∘ (exl △ (λ q → xor (((exl ∘ exr) q , (exr ∘ exr) q))))
 ≡⟨⟩ -- application rule
    xor ∘ (exl △ (apply ∘ ((λ q → xor) △ (λ q → (((exl ∘ exr) q , (exr ∘ exr) q))))))
 ≡⟨⟩ -- const rule and definition of △
    xor ∘ (exl △ (apply ∘ ((const xor) △ ((exl ∘ exr) △ (exr ∘ exr)))))
 ≡⟨⟩ -- applyConstFork rule above
    (xor ∘ (exl △ (xor ∘ ((exl ∘ exr) △ (exr ∘ exr)))))
  ∎
  where open ≡-Reasoning


simplerAdderDerivation : (λ (a , b , c) → xor (a , xor (b , c ))) ≡ (xor ∘ (exl △ (xor ∘ ((exl ∘ exr) △ (exr ∘ exr)))))
simplerAdderDerivation = begin
    (λ (a , b , c) → xor (a , xor (b , c )))
 ≡⟨⟩ -- desugar pairs
    (λ p → xor (exl p , xor ((exl ∘ exr) p , (exr ∘ exr) p)))
 ≡⟨⟩ -- eta expand
    (λ p → xor (exl p , ((λ q → xor ((exl ∘ exr) q , (exr ∘ exr) q)) p)))
 ≡⟨⟩ -- composeFork rule from DerivedCCCRules.agda
    xor ∘ (exl △ (λ q → xor ((exl ∘ exr) q , (exr ∘ exr) q)))
 ≡⟨⟩ -- composeFork rule from DerivedCCCRules.agda
    (xor ∘ (exl △ (xor ∘ ((exl ∘ exr) △ (exr ∘ exr)))))
  ∎
  where open ≡-Reasoning
