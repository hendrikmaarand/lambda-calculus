{-# OPTIONS --type-in-type #-}

module CategoryTheory where

open import Relation.Binary.HeterogeneousEquality
open ≅-Reasoning renaming (begin_ to proof_)

open import Function

open import Syntax
open import Evaluator


record Cat : Set where
  field Obj  : Set
        Hom  : Obj → Obj → Set
        iden : ∀{X} → Hom X X
        comp : ∀{X Y Z} → Hom Y Z → Hom X Y → Hom X Z
        idl  : ∀{X Y}{f : Hom X Y} → comp iden f ≅ f
        idr  : ∀{X Y}{f : Hom X Y} → comp f iden ≅ f
        ass  : ∀{W X Y Z}{f : Hom Y Z}{g : Hom X Y}{h : Hom W X} → comp (comp f g) h ≅ comp f (comp g h)
open Cat

record Fun (C D : Cat) : Set where
  field OMap : Obj C → Obj D
        HMap : ∀{X Y} → Hom C X Y → Hom D (OMap X) (OMap Y)
        fid  : ∀{X} → HMap (iden C {X}) ≅ iden D {OMap X}
        fcomp : ∀{X Y Z}{f : Hom C Y Z}{g : Hom C X Y} → HMap (comp C f g) ≅ comp D (HMap f) (HMap g)
open Fun

Fam : Set → Cat
Fam I = record {
  Obj = I → Set;
  Hom = λ A B → ∀{i} → A i → B i;
  iden = id;
  comp = λ f g → f ∘ g;
  idl = refl;
  idr = refl;
  ass = refl}


record Monad (C : Cat) : Set where
  field T    : Obj C → Obj C
        η    : ∀{X} → Hom C X (T X)
        bind : ∀{X Y} → Hom C X (T Y) → Hom C (T X) (T Y)
        law1 : ∀{X} → bind (η {X}) ≅ iden C {T X}
        law2 : ∀{X Y}{f : Hom C X (T Y)} → comp C (bind f) η ≅ f
        law3 : ∀{X Y Z}{f : Hom C X (T Y)}{g : Hom C Y (T Z)} → bind (comp C (bind g) f) ≅ comp C (bind g) (bind f)


record RMonad {C D : Cat}(J : Fun C D) : Set where
  field T : Obj C → Obj D
        η : ∀{X} → Hom D (OMap J X) (T X)
        bind : ∀{X Y} → Hom D (OMap J X) (T Y) → Hom D (T X) (T Y)
        law1 : ∀{X} → bind (η {X}) ≅ iden D {T X}
        law2 : ∀{X Y}{f : Hom D (OMap J X) (T Y)} → comp D (bind f) η ≅ f
        law3 : ∀{X Y Z}{f : Hom D (OMap J X) (T Y)}{g : Hom D (OMap J Y) (T Z)} → bind (comp D (bind g) f) ≅ comp D (bind g) (bind f)

record RAlg {C D : Cat}{J : Fun C D}(M : RMonad J) : Set where
  open RMonad
  field acar : Obj D
        astr : ∀{Z} → Hom D (OMap J Z) acar → Hom D (T M Z) acar
        alaw1 : ∀{Z}{f : Hom D (OMap J Z) acar} → f ≅ comp D (astr f) (η M)
        alaw2 : ∀{Z}{W}{k : Hom D (OMap J Z) (T M W)}{f : Hom D (OMap J W) acar } → astr (comp D (astr f) k) ≅ comp D (astr f) (bind  M k)



record RAlgMorph {C D : Cat}{J : Fun C D}{M : RMonad J}(A B : RAlg M) : Set where
  open RAlg
  field amor : Hom D (acar A) (acar B)
        ahom : ∀{Z}{f : Hom D (OMap J Z) (acar A)} → comp D amor (astr A f) ≅ astr B (comp D amor f)
open RAlgMorph


funnycong : ∀{A}{B : A → Set}{C : Set}{a a' : A} →
            a ≅ a' → {b : B a}{b' : B a'} → b ≅ b' →
            (f : (a : A) → B a → C) → f a b ≅ f a' b'
funnycong refl refl f = refl

{-
RAlgMorphEq : ∀{C D}{J : Fun C D}{M : RMonad J}{X Y : RAlg M}{f g : RAlgMorph X Y} → amor f ≅ amor g → f ≅ g
RAlgMorphEq {C}{D}{J}{M}{X}{Y}{f}{g} p = {!!}

EM : ∀{C D}{J : Fun C D} → RMonad J → Cat 
EM M = record {Obj = RAlg M;
               Hom = RAlgMorph;
               iden = {!!};
               comp = {!!};
               idl = {!!};
               idr = {!!};
               ass = {!!}}
-}

