constant symbol Sort : TYPE;    // Apred    Pred     Impred
constant symbol Set : Sort;     // Set   ↪ Set0 and Type0
constant symbol Prop : Sort;    // Prop  ↪ Set0 and Prop
constant symbol TSet : Sort;    // TSet  ↪ Set1 and Type1
constant symbol TProp : Sort;   // TProp ↪ Set1 and Type0
symbol ∀Prop : Sort;   // ∀Prop ↪ Set1 and Prop
constant symbol U : Sort → TYPE;

symbol El : Π (s : Sort), U s → TYPE;

constant symbol set : U TSet;    // Set  : TSet  ↪ Set0 : Set1 and Type0 : Type1 
rule El _ set ↪ U Set;
constant symbol prop : U TProp;  // Prop : TProp ↪ Set0 : Set1 and Prop  : Type0
rule El _ prop ↪ U Prop;

constant symbol tt : TYPE;
constant symbol I : tt;
symbol ∨ : Π (s1 s2 s3 : Sort), TYPE;
// Set and Prop
rule ∨ Set   Set   Set   ↪ tt  // (Set,   Set,   Set)   ↪ (Set0,  Set0,  Set0) and (Type0, Type0, Type0) <- \⇝ and ⇝d in U
with ∨ Prop  Prop  Prop  ↪ tt  // (Prop,  Prop,  Prop)  ↪ (Set0,  Set0,  Set0) and (Prop,  Prop,  Prop)  <- ⇒ and ⇒d in U
with ∨ Set   Prop  Prop  ↪ tt  // (Set,   Prop,  Prop)  ↪ (Set0,  Set0,  Set0) and (Type0, Prop,  Prop)  <- ∀ in U
with ∨ Prop  Set   Set   ↪ tt  // (Prop,  Set,   Set)   ↪ (Set0,  Set0,  Set0) and (Prop,  Type0, Type0) <- π in U
// TSet and TProp
with ∨ TSet  TSet  TSet  ↪ tt  // (TSet,  TSet,  TSet)  ↪ (Set1,  Set1,  Set1) and (Type1, Type1, Type1) <- Scheme1 in U
with ∨ TProp TProp TProp ↪ tt  // (TProp, TProp, TProp) ↪ (Set1,  Set1,  Set1) and (Type0, Type0, Type0) <- \⇝ and ⇝d for TProp
with ∨ TSet  TProp TSet  ↪ tt  // (TSet,  TProp, TSet)  ↪ (Set1,  Set1,  Set1) and (Type1, Type0, Type1) <- not in U
with ∨ TProp TSet  TSet  ↪ tt  // (TProp, TSet,  TSet)  ↪ (Set1,  Set1,  Set1) and (Type0, Type1, Type1) <- Scheme2 for TProp
// Sort ∨ TSort
with ∨ Prop  TProp TProp ↪ tt  // (Prop,  TProp, TProp) ↪ (Set0,  Set1,  Set1) and (Prop,  Type0, Type0) <- π for TProp
with ∨ Set   TSet  TSet  ↪ tt  // (Set,   TSet,  TSet)  ↪ (Set0,  Set1,  Set1) and (Type0, Type1, Type1) <- Scheme2 in U
with ∨ Set   TProp TProp ↪ tt  // (Set,   TProp, TProp) ↪ (Set0,  Set1,  Set1) and (Type0, Type0, Type0) <- 
with ∨ Prop  TSet  TSet  ↪ tt  // (Prop,  TSet,  TSet)  ↪ (Set0,  Set1,  Set1) and (Prop,  Type1, Type1)
// TSort ∨ Sort
with ∨ TSet  Set   TSet  ↪ tt  // (TSet,  Set,   TSet)  ↪ (Set1,  Set0,  Set1) and (Type1, Type0, Type1)
with ∨ TProp Set   TProp ↪ tt  // (TProp, Set,   TProp) ↪ (Set1,  Set0,  Set1) and (Type0, Type0, Type0)
with ∨ TProp Prop  ∀Prop ↪ tt  // (TProp, Prop,  ∀Prop) ↪ (Set1,  Set0,  Set1) and (Type0, Prop,  Prop)
with ∨ TSet  Prop  ∀Prop ↪ tt  // (TSet,  Prop,  ∀Prop) ↪ (Set1,  Set0,  Set1) and (Type1, Prop,  Prop)
// TSort ∨ ∀Prop
with ∨ TSet  ∀Prop ∀Prop ↪ tt  // (TSet,  ∀Prop, ∀Prop) ↪ (Set1,  Set1,  Set1) and (Type1, Prop,  Prop)
with ∨ TProp ∀Prop ∀Prop ↪ tt  // (TProp, ∀Prop, ∀Prop) ↪ (Set1,  Set1,  Set1) and (Type0, Prop,  Prop)

// Sort ∨ ∀Prop
with ∨ Set   ∀Prop ∀Prop ↪ tt  // (Set,   ∀Prop, ∀Prop) ↪ (Set0,  Set1,  Set1) and (Type0, Prop,  Prop)
with ∨ Prop  ∀Prop ∀Prop ↪ tt  // (Prop,  ∀Prop, ∀Prop) ↪ (Set0,  Set1,  Set1) and (Prop,  Prop,  Prop)

// other products with ∀Prop
with ∨ ∀Prop  ∀Prop ∀Prop ↪ tt  // (∀Prop,  ∀Prop, ∀Prop) ↪ (Set1,  Set1,  Set1) and (Prop,  Prop,  Prop)
with ∨ ∀Prop  Prop  ∀Prop ↪ tt; // (∀Prop,   Prop, ∀Prop) ↪ (Set1,  Set0,  Set1) and (Prop,  Prop,  Prop)



constant symbol ⇝ : Π (s1 s2: Sort) {s3 : Sort} (_ : ∨ s1 s2 s3) (A : U s1), (El s1 A → U s2) → U s3;
rule El _ (⇝ $s1 $s2 _ $A $B) ↪ Π (x : El $s1 $A), El $s2 ($B x);
