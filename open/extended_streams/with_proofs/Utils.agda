module Utils where

open import Relation.Binary.HeterogeneousEquality
open import Data.Product hiding (map)



Σeq : {A : Set} {A' : Set} {B : A → Set} {B' : A' → Set} → {a : A} → {a' : A'} → a ≅ a' → B ≅ B' → {b : B a} → {b' : B' a'} → b ≅ b' → _,_ {B = B} a b ≅ _,_ {B = B'} a' b'
Σeq refl refl refl = refl

ir : ∀{A A' : Set} → {a : A} → {a' : A'} → {p q : a ≅ a'} → p ≅ q
ir {p = refl} {q = refl} = refl

fixedtypes : ∀{A A' A'' A''' : Set}{a : A}{a' : A'}{a'' : A''}{a''' : A'''} → {p : a ≅ a'} → {q : a'' ≅ a'''} → a' ≅ a'' → p ≅ q
fixedtypes {p = refl} {q = refl} refl = refl

fixedtypesleft : ∀{A A' A'' A''' : Set}{a : A}{a' : A'}{a'' : A''}{a''' : A'''} → {p : a ≅ a'} → {q : a'' ≅ a'''} → a ≅ a'' → p ≅ q
fixedtypesleft {p = refl} {q = refl} refl = refl

fixedtypesright : ∀{A A' A'' A''' : Set}{a : A}{a' : A'}{a'' : A''}{a''' : A'''} → {p : a ≅ a'} → {q : a'' ≅ a'''} → a' ≅ a''' → p ≅ q
fixedtypesright {p = refl} {q = refl} refl = refl



ifcong : {A : Set}{B : A → Set}{f f' : {a : A} → B a} → _≅_ {_}{ {a : A} → B a } f { {a : A} → B a } f' → (a : A) → f {a} ≅ f' {a}
ifcong refl a = refl

fcong : ∀{A B : Set} → {f f' : A → B} → f ≅ f' → (a : A) → f a ≅ f' a
fcong refl a = refl