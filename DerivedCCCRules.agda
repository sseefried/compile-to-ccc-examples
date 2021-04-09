{-# OPTIONS --without-K --safe #-}

module DerivedCCCRules where

open import Data.Product
open import Data.Bool
open import Relation.Binary.PropositionalEquality
open import FunctionCategory

private
  variable
    A B C X : Set

applyConstFork : ∀ (f : B → C) (g : A → B) → (apply ∘ ((const f) △ g)) ≡ f ∘ g
applyConstFork f g = begin
     apply ∘ ((const f) △ g)
 ≡⟨⟩ -- definition of △
     apply ∘ (λ x → (const f x , g x))
 ≡⟨⟩ -- Definition of const
     apply ∘ (λ x → (f , g x))
 ≡⟨⟩ -- Definition of ∘
     (λ y → apply ((λ x → (f , g x)) y)) -- lambdas require brackets around them due to binding precedence
 ≡⟨⟩ -- simplify
     (λ y → apply (f , g y))
 ≡⟨⟩ -- Definition of apply
     (λ y → f (g y))
 ≡⟨⟩ -- Definition of ∘
     f ∘ g
 ∎
  where open ≡-Reasoning

composeFork : ∀ (a : X → A) (b : X → B) (f : A × B → C) → (λ p → f (a p , b p)) ≡ f ∘ (a △ b)
composeFork a b f = begin
    (λ p → f (a p , b p))
  ≡⟨⟩ -- application rule
    apply ∘ ((λ p → f) △ λ p → (a p , b p))
  ≡⟨⟩ -- Definition of △
    apply ∘ ((λ p → f) △ (a △ b))
  ≡⟨⟩ -- Const rule
    apply ∘ ((const f) △ (a △ b))
  ≡⟨⟩ -- applyConstFork rule above
    f ∘ (a △ b)
  ∎
  where open ≡-Reasoning

compose : ∀  (f : B → C) → (g : A → B) → (λ p → f (g p)) ≡ f ∘ g
compose f g = begin
    (λ p → f (g p))
  ≡⟨⟩ -- Definition of composea
    f ∘ g
  ∎
  where open ≡-Reasoning

fork : ∀ (a : X → A) (b : X → B) (f : A × B → C) → (λ p → (a p , b p)) ≡ f ∘ (a △ b)
fork a b f = begin
    (λ p → f (a p , b p))
  ≡⟨⟩ -- application rule
    apply ∘ ((λ p → f) △ λ p → (a p , b p))
  ≡⟨⟩ -- Definition of △
    apply ∘ ((λ p → f) △ (a △ b))
  ≡⟨⟩ -- Const rule
    apply ∘ ((const f) △ (a △ b))
  ≡⟨⟩ -- applyConstFork rule above
    f ∘ (a △ b)
  ∎
  where open ≡-Reasoning
