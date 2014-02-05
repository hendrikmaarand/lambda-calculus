{-# OPTIONS --type-in-type #-}

module Examples where

open import Function
open import Relation.Binary.HeterogeneousEquality

open import CategoryTheory
open import Syntax

Sets : Cat
Sets = record{ Obj  = Set;
               Hom  = λ X Y → X → Y;
               iden = id;
               comp = λ f g → f ∘ g;
               idl  = refl;
               idr  = refl;
               ass  = refl}


data Maybe (A : Set) : Set where
  Just    : A → Maybe A
  Nothing : Maybe A

mbind : {X Y : Set} → (X → Maybe Y) → Maybe X → Maybe Y
mbind f (Just x) = f x
mbind f Nothing = Nothing

mlaw1 : ∀{A}(a : Maybe A) → mbind Just a ≅ id a
mlaw1 (Just x) = refl
mlaw1 Nothing = refl

mlaw3 : ∀{A B C}{f : A → Maybe B}{g : B → Maybe C}(a : Maybe A) → mbind (mbind g ∘ f) a ≅ (mbind g ∘ mbind f) a
mlaw3 (Just x) = refl
mlaw3 Nothing = refl


MaybeMonad : Monad Sets
MaybeMonad = record { T    = Maybe;
                      η    = Just;
                      bind = mbind;
                      law1 = ext mlaw1;
                      law2 = refl;
                      law3 = ext mlaw3}
