constant symbol Sort : TYPE;    // Apred    Pred     Impred
constant symbol Set : Sort;     // Set   ↪ Set0 and Type0
constant symbol Prop : Sort;    // Prop  ↪ Set0 and Prop
constant symbol TSet : Sort;    // TSet  ↪ Set1 and Type1
constant symbol TProp : Sort;   // TProp ↪ Set1 and Type0
constant symbol ∀Prop : Sort;   // ∀Prop ↪ Set1 and Prop
constant symbol U : Sort → TYPE;

symbol El : Π (s : Sort), U s → TYPE;

constant symbol set : U TSet;    // Set  : TSet  ↪ Set0 : Set1 and Type0 : Type1 
rule El _ set ↪ U Set;
constant symbol prop : U TProp;  // Prop : TProp ↪ Set0 : Set1 and Prop  : Type0
rule El _ prop ↪ U Prop;

constant symbol ⊤ : TYPE;
constant symbol I : ⊤;
symbol ∨ : Π (s1 s2 s3 : Sort), TYPE;
// Set and Prop
rule ∨ Set   Set   Set   ↪ ⊤  // (Set,   Set,   Set)   ↪ (Set0,  Set0,  Set0) and (Type0, Type0, Type0)
with ∨ Prop  Prop  Prop  ↪ ⊤  // (Prop,  Prop,  Prop)  ↪ (Set0,  Set0,  Set0) and (Prop,  Prop,  Prop)
with ∨ Set   Prop  Prop  ↪ ⊤  // (Set,   Prop,  Prop)  ↪ (Set0,  Set0,  Set0) and (Type0, Prop,  Prop)
with ∨ Prop  Set   Set   ↪ ⊤  // (Prop,  Set,   Set)   ↪ (Set0,  Set0,  Set0) and (Prop,  Type0, Type0)
// TSet and TProp
with ∨ TSet  TSet  TSet  ↪ ⊤  // (TSet,  TSet,  TSet)  ↪ (Set1,  Set1,  Set1) and (Type1, Type1, Type1)
with ∨ TProp TProp TProp ↪ ⊤  // (TProp, TProp, TProp) ↪ (Set1,  Set1,  Set1) and (Type0, Type0, Type0)
with ∨ TSet  TProp TSet  ↪ ⊤  // (TSet,  TProp, TSet)  ↪ (Set1,  Set1,  Set1) and (Type1, Type0, Type1)
with ∨ TProp TSet  TSet  ↪ ⊤  // (TProp, TSet,  TSet)  ↪ (Set1,  Set1,  Set1) and (Type0, Type1, Type1)
// Sort ∨ TSort
with ∨ Prop  TProp TProp ↪ ⊤  // (Prop,  TProp, TProp) ↪ (Set0,  Set1,  Set1) and (Prop,  Type0, Type0)
with ∨ Set   TSet  TSet  ↪ ⊤  // (Set,   TSet,  TSet)  ↪ (Set0,  Set1,  Set1) and (Type0, Type1, Type1)
with ∨ Set   TProp TProp ↪ ⊤  // (Set,   TProp, TProp) ↪ (Set0,  Set1,  Set1) and (Type0, Type0, Type0)
with ∨ Prop  TSet  TSet  ↪ ⊤  // (Prop,  TSet,  TSet)  ↪ (Set0,  Set1,  Set1) and (Prop,  Type1, Type1)
// TSort ∨ Sort
with ∨ TSet  Set   TSet  ↪ ⊤  // (TSet,  Set,   TSet)  ↪ (Set1,  Set0,  Set1) and (Type1, Type0, Type1)
with ∨ TProp Set   TProp ↪ ⊤  // (TProp, Set,   TProp) ↪ (Set1,  Set0,  Set1) and (Type0, Type0, Type0)
with ∨ TProp Prop  ∀Prop ↪ ⊤  // (TProp, Prop,  ∀Prop) ↪ (Set1,  Set0,  Set1) and (Type0, Prop,  Prop)
with ∨ TSet  Prop  ∀Prop ↪ ⊤  // (TSet,  Prop,  ∀Prop) ↪ (Set1,  Set0,  Set1) and (Type1, Prop,  Prop)
// TSort ∨ ∀Prop
with ∨ TSet  ∀Prop ∀Prop ↪ ⊤  // (TSet,  ∀Prop, ∀Prop) ↪ (Set1,  Set1,  Set1) and (Type1, Prop,  Prop)
with ∨ TProp ∀Prop ∀Prop ↪ ⊤  // (TProp, ∀Prop, ∀Prop) ↪ (Set1,  Set1,  Set1) and (Type0, Prop,  Prop)

// Sort ∨ ∀Prop
with ∨ Set   ∀Prop ∀Prop ↪ ⊤  // (Set,   ∀Prop, ∀Prop) ↪ (Set0,  Set1,  Set1) and (Type0, Prop,  Prop)
with ∨ Prop  ∀Prop ∀Prop ↪ ⊤; // (Prop,  ∀Prop, ∀Prop) ↪ (Set0,  Set1,  Set1) and (Prop,  Prop,  Prop)

constant symbol ⇝ : Π (s1 s2: Sort) {s3 : Sort} (_ : ∨ s1 s2 s3) (A : U s1), (El s1 A → U s2) → U s3;
rule El _ (⇝ $s1 $s2 _ $A $B) ↪ Π (x : El $s1 $A), El $s2 ($B x);
