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


RAlgMorphEq : ∀{C D}{J : Fun C D}{M : RMonad J}{X Y : RAlg M}{f g : RAlgMorph X Y} → amor f ≅ amor g → f ≅ g
RAlgMorphEq {C}{D}{J}{M}{X}{Y}{f}{g} p = funnycong 
  {Hom D (RAlg.acar X) (RAlg.acar Y)}
  {λ amor → ∀ {Z}{f : Hom D (OMap J Z) (RAlg.acar X)} → comp D amor (RAlg.astr X f) ≅ RAlg.astr Y (comp D amor f)}
  p 
  (iext λ Z → iext λ f' → fixedtypes (
    proof
    RAlg.astr Y (comp D (amor f) f') 
    ≅⟨ sym (ahom f) ⟩
    comp D (amor f) (RAlg.astr X f') 
    ≅⟨ cong (λ p' → comp D p' (RAlg.astr X f')) p ⟩
    comp D (amor g) (RAlg.astr X f')
    ∎)) 
  (λ x y → record {amor = x; ahom = y})


IdMorph : ∀{C D}{J : Fun C D}{M : RMonad J}{A : RAlg M} → RAlgMorph A A 
IdMorph {C}{D}{A = A} = record{
  amor = iden D; 
  ahom = λ {Z} {f} → proof
    comp D (iden D) (RAlg.astr A f) 
    ≅⟨ idl D ⟩
    RAlg.astr A f
    ≅⟨ cong (RAlg.astr A) (sym (idl D)) ⟩
    RAlg.astr A (comp D (iden D) f)
    ∎}


CompMorph : ∀{C D}{J : Fun C D}{M : RMonad J}{X Y Z : RAlg M} → RAlgMorph Y Z → RAlgMorph X Y → RAlgMorph X Z
CompMorph {C}{D}{J}{M}{X}{Y}{Z} f g = record{
  amor = comp D (amor f) (amor g); 
  ahom = λ {Z'} {f'} → proof
    comp D (comp D (amor f) (amor g)) (RAlg.astr X f') 
    ≅⟨ ass D ⟩
    comp D (amor f) (comp D (amor g) (RAlg.astr X f'))
    ≅⟨ cong (comp D (amor f)) (ahom g) ⟩
    comp D (amor f) (RAlg.astr Y (comp D (amor g) f'))
    ≅⟨ ahom f ⟩
    RAlg.astr Z (comp D (amor f) (comp D (amor g) f'))
    ≅⟨ cong (RAlg.astr Z) (sym (ass D)) ⟩
    RAlg.astr Z (comp D (comp D (amor f) (amor g)) f')
    ∎}


idlMorph : ∀{C D}{J : Fun C D}{M : RMonad J}{X Y : RAlg M}{f : RAlgMorph X Y} → CompMorph IdMorph f ≅ f
idlMorph {C}{D} = RAlgMorphEq (idl D)

idrMorph : ∀{C D}{J : Fun C D}{M : RMonad J}{X Y : RAlg M}{f : RAlgMorph X Y} → CompMorph f IdMorph ≅ f
idrMorph {C}{D} = RAlgMorphEq (idr D)

assMorph : ∀{C D}{J : Fun C D}{M : RMonad J}{W X Y Z : RAlg M}{f : RAlgMorph Y Z}{g : RAlgMorph X Y}{h : RAlgMorph W X} → 
                                                             CompMorph (CompMorph f g) h ≅ CompMorph f (CompMorph g h)
assMorph {C}{D} = RAlgMorphEq (ass D)


EM : ∀{C D}{J : Fun C D} → RMonad J → Cat 
EM M = record {Obj = RAlg M;
               Hom = RAlgMorph;
               iden = IdMorph;
               comp = CompMorph;
               idl = idlMorph;
               idr = idrMorph;
               ass = λ {_ _ _ _ f g h} → assMorph {f = f}{g = g}{h = h}}

record Init (C : Cat) : Set where
  field I : Obj C
        i : ∀{X} → Hom C I X
        law : ∀{X}{f : Hom C I X} → i {X} ≅ f


