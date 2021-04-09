{-# OPTIONS --without-K --safe #-}

module FunctionCategory where

open import Data.Product
open import Data.Bool renaming (_xor_ to _xor'_)

private
  variable
    A B C : Set

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
