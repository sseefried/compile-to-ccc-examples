{-# OPTIONS --without-K --safe #-}

module AdderDerivation where

open import Level
open import Data.Product
open import Data.Bool renaming (_xor_ to _xor'_)
open import Relation.Binary.PropositionalEquality

private
  variable
    A : Set
    B : Set
    C : Set

infixr 7 _△_

_△_ : (A → B) → (A → C) → (A → B × C)
f △ g = λ x → (f x , g x)

_∘_ : (B → C) → (A → B) → (A → C)
f ∘ g = λ x → f (g x)

const : B → A → B
const x _ = x

xor : Bool × Bool → Bool
xor = uncurry _xor'_

exl : A × B → A
exl (a , _) = a

exr : A × B → B
exr (_ , b) = b

apply : (A → B) × A → B
apply (f , x) = f x 

adder : Bool × Bool × Bool → Bool
adder = λ (a , b , c) → xor (a , xor (b , c ))

applyConstFork : ∀ (f : B → C) (g : A → B) → (apply ∘ ((const f) △ g)) ≡ f ∘ g
applyConstFork f g = begin
     apply ∘ ((const f) △ g)
 ≡⟨⟩
     apply ∘ (λ x → (const f x , g x))
 ≡⟨⟩
     apply ∘ (λ x → (f , g x))
 ≡⟨⟩
     (λ y → apply ((λ x → (f , g x)) y)) -- lambdas require brackets around them due to binding precendence
 ≡⟨⟩
     (λ y → apply (f , g y))
 ≡⟨⟩
     (λ y → f (g y))
 ≡⟨⟩
     f ∘ g
 ∎
  where open ≡-Reasoning

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
 ≡⟨⟩ -- applyConstFork rule above
    xor ∘ (exl △ (λ q → xor (((exl ∘ exr) q , (exr ∘ exr) q))))
 ≡⟨⟩ -- application rule
    xor ∘ (exl △ (apply ∘ ((λ q → xor) △ (λ q → (((exl ∘ exr) q , (exr ∘ exr) q))))))
 ≡⟨⟩ -- const rule and definition of △
    xor ∘ (exl △ (apply ∘ ((const xor) △ ((exl ∘ exr) △ (exr ∘ exr)))))
 ≡⟨⟩ -- applyConstFork rule above
    (xor ∘ (exl △ (xor ∘ ((exl ∘ exr) △ (exr ∘ exr)))))
  ∎
  where open ≡-Reasoning
