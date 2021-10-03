constant symbol Sort : TYPE;    // Apred    Pred     Impred
constant symbol Set0 : Sort;     // Set0  ↪ Set0 and Type0
constant symbol Prop0 : Sort;    // Prop0 ↪ Set0 and Prop
constant symbol Set1 : Sort;    //  Set1  ↪ Set1 and Type1
constant symbol Prop1 : Sort;   //  Prop1 ↪ Set1 and Type0
constant symbol Set2 : Sort;    //  Set2  ↪ Set2 and Type2
constant symbol Prop2 : Sort;   //  Prop2 ↪ Set2 and Type1
constant symbol ∀Prop : Sort;   //  ∀Prop ↪ Set1 and Prop
constant symbol U : Sort → TYPE;

symbol El : Π (s : Sort), U s → TYPE;

constant symbol set0 : U Set1;    // Set0  : Set1  ↪ Set0 : Set1 and Type0 : Type1 
rule El _ set0 ↪ U Set0;
constant symbol prop0 : U Prop1;  // Prop0 : Prop1 ↪ Set0 : Set1 and Prop  : Type0
rule El _ prop0 ↪ U Prop0;
constant symbol set1 : U Set2;    // Set1  : Set2  ↪ Set1 : Set2 and Type1 : Type2 
rule El _ set1 ↪ U Set1;
constant symbol prop1 : U Prop2;  // Prop1 : Prop2 ↪ Set1 : Set2 and Type0  : Type1
rule El _ prop1 ↪ U Prop1;


constant symbol ⊤ : TYPE;
constant symbol I : ⊤;
symbol ∨ : Π (s1 s2 s3 : Sort), TYPE;
// Set0 and Prop0
rule ∨ Set0   Set0   Set0   ↪ ⊤  // (Set0,   Set0,   Set0)   ↪ (Set0,  Set0,  Set0) and (Type0, Type0, Type0) <- \⇝ and ⇝d in U
with ∨ Prop0  Prop0  Prop0  ↪ ⊤  // (Prop0,  Prop0,  Prop0)  ↪ (Set0,  Set0,  Set0) and (Prop,  Prop,  Prop)  <- ⇒ and ⇒d in U
with ∨ Set0   Prop0  Prop0  ↪ ⊤  // (Set0,   Prop0,  Prop0)  ↪ (Set0,  Set0,  Set0) and (Type0, Prop,  Prop)  <- ∀ in U
with ∨ Prop0  Set0   Set0   ↪ ⊤  // (Prop0,  Set0,   Set0)   ↪ (Set0,  Set0,  Set0) and (Prop,  Type0, Type0) <- π in U
// Set1 and Prop1
with ∨ Set1  Set1  Set1  ↪ ⊤  // (Set1,  Set1,  Set1)  ↪ (Set1,  Set1,  Set1) and (Type1, Type1, Type1) <- Scheme1 in U
with ∨ Prop1 Prop1 Prop1 ↪ ⊤  // (Prop1, Prop1, Prop1) ↪ (Set1,  Set1,  Set1) and (Type0, Type0, Type0) <- \⇝ and ⇝d for Prop1
with ∨ Set1  Prop1 Set1  ↪ ⊤  // (Set1,  Prop1, Set1)  ↪ (Set1,  Set1,  Set1) and (Type1, Type0, Type1) <- not in U
with ∨ Prop1 Set1  Set1  ↪ ⊤  // (Prop1, Set1,  Set1)  ↪ (Set1,  Set1,  Set1) and (Type0, Type1, Type1) <- Scheme2 for Prop1
// Set1 and Prop1
with ∨ Set2  Set2  Set2  ↪ ⊤  // (Set1,  Set1,  Set1)  ↪ (Set1,  Set1,  Set1) and (Type1, Type1, Type1) <- Scheme1 in U
with ∨ Prop2 Prop2 Prop2 ↪ ⊤  // (Prop1, Prop1, Prop1) ↪ (Set1,  Set1,  Set1) and (Type0, Type0, Type0) <- \⇝ and ⇝d for Prop1
with ∨ Set2  Prop2 Set2  ↪ ⊤  // (Set1,  Prop1, Set1)  ↪ (Set1,  Set1,  Set1) and (Type1, Type0, Type1) <- not in U
with ∨ Prop2 Set2  Set2  ↪ ⊤  // (Prop1, Set1,  Set1)  ↪ (Set1,  Set1,  Set1) and (Type0, Type1, Type1) <- Scheme2 for Prop1
// Sort0 ∨ Sort1
with ∨ Prop0  Prop1 Prop1 ↪ ⊤  // (Prop0,  Prop1, Prop1) ↪ (Set0,  Set1,  Set1) and (Prop,  Type0, Type0) <- π for Prop1
with ∨ Set0   Set1  Set1  ↪ ⊤  // (Set0,   Set1,  Set1)  ↪ (Set0,  Set1,  Set1) and (Type0, Type1, Type1) <- Scheme2 in U
with ∨ Set0   Prop1 Prop1 ↪ ⊤  // (Set0,   Prop1, Prop1) ↪ (Set0,  Set1,  Set1) and (Type0, Type0, Type0) <- 
with ∨ Prop0  Set1  Set1  ↪ ⊤  // (Prop0,  Set1,  Set1)  ↪ (Set0,  Set1,  Set1) and (Prop,  Type1, Type1)
// Sort1 ∨ Sort2
with ∨ Prop1  Prop2 Prop2 ↪ ⊤  // (Prop0,  Prop1, Prop1) ↪ (Set0,  Set1,  Set1) and (Prop,  Type0, Type0) <- π for Prop1
with ∨ Set1   Set2  Set2  ↪ ⊤  // (Set0,   Set1,  Set1)  ↪ (Set0,  Set1,  Set1) and (Type0, Type1, Type1) <- Scheme2 in U
with ∨ Set1   Prop2 Prop2 ↪ ⊤  // (Set0,   Prop1, Prop1) ↪ (Set0,  Set1,  Set1) and (Type0, Type0, Type0) <- 
with ∨ Prop1  Set2  Set2  ↪ ⊤  // (Prop0,  Set1,  Set1)  ↪ (Set0,  Set1,  Set1) and (Prop,  Type1, Type1)
// Sort1 ∨ Sort0
with ∨ Set1  Set0   Set1  ↪ ⊤  // (Set1,  Set0,   Set1)  ↪ (Set1,  Set0,  Set1) and (Type1, Type0, Type1)
with ∨ Prop1 Set0   Prop1 ↪ ⊤  // (Prop1, Set0,   Prop1) ↪ (Set1,  Set0,  Set1) and (Type0, Type0, Type0)
with ∨ Prop1 Prop0  ∀Prop ↪ ⊤  // (Prop1, Prop0,  ∀Prop) ↪ (Set1,  Set0,  Set1) and (Type0, Prop,  Prop)
with ∨ Set1  Prop0  ∀Prop ↪ ⊤  // (Set1,  Prop0,  ∀Prop) ↪ (Set1,  Set0,  Set1) and (Type1, Prop,  Prop)
// Sort2 ∨ Sort1
with ∨ Set2  Set1   Set2  ↪ ⊤  // (Set2,  Set1,   Set2)  ↪ (Set2,  Set1,  Set2) and (Type2, Type1, Type2)
with ∨ Prop2 Set1   Prop2 ↪ ⊤  // (Prop2, Set1,   Prop2) ↪ (Set2,  Set1,  Set2) and (Type1, Type1, Type1)
with ∨ Prop2 Prop1  Prop2 ↪ ⊤  // (Prop2, Prop1,  Prop2) ↪ (Set2,  Set1,  Set2) and (Type1, Type0,  Type1)
with ∨ Set2  Prop1  Set2  ↪ ⊤  // (Set2,  Prop1,  Set2)  ↪ (Set2,  Set1,  Set2) and (Type2, Type0,  Type2)

// Sort1 ∨ ∀Prop
with ∨ Set1  ∀Prop ∀Prop ↪ ⊤  // (Set1,  ∀Prop, ∀Prop) ↪ (Set1,  Set1,  Set1) and (Type1, Prop,  Prop)
with ∨ Prop1 ∀Prop ∀Prop ↪ ⊤  // (Prop1, ∀Prop, ∀Prop) ↪ (Set1,  Set1,  Set1) and (Type0, Prop,  Prop)

// ∀Prop ∨ Sort1
with ∨ ∀Prop Set1  ∀Prop ↪ ⊤  // (∀Prop, Set1,  ∀Prop) ↪ (Set1,  Set1,  Set1) and (Prop,  Type1, Type1)
// with ∨ Prop1 ∀Prop ? ↪ DOES NOT EXIST

// Sort0 ∨ ∀Prop
with ∨ Set0  ∀Prop ∀Prop ↪ ⊤ // (Set0,  ∀Prop,  ∀Prop) ↪ (Set0,  Set1,  Set1) and (Type0,  Prop,  Prop)
with ∨ Prop0 ∀Prop ∀Prop ↪ ⊤ // (Prop0, ∀Prop,  ∀Prop) ↪ (Set0,  Set1,  Set1) and (Prop,  Prop,  Prop)

// ∀Prop ∨ Sort0
with ∨ ∀Prop  Prop0 ∀Prop ↪ ⊤ // (∀Prop,   Prop0, ∀Prop) ↪ (Set1,  Set0,  Set1) and (Prop,  Prop,  Prop)
//with ∨ ∀Prop  Set0  ?  ↪  DOES NOT EXIST

// ∀Prop ∨ Sort2
with ∨ ∀Prop Set2  Set2  ↪ ⊤  // (∀Prop, Set2,  Set2)  ↪ (Set1,  Set2,  Set2) and (Prop, Type2,  Type2)
with ∨ ∀Prop Prop2 Prop2 ↪ ⊤  // (∀Prop, Prop2, Prop2) ↪ (Set1,  Set1,  Set1) and (Prop, Type1,  Type1)

// Sort2 ∨ ∀Prop
//with ∨ Set2  ∀Prop Set2  ↪ ⊤  // (Set2, ∀Prop,  Set2)  ↪ (Set2,  Set1,  Set2) and (Type2, Prop,  Prop)
//with ∨ Prop2 ∀Prop Prop2 ↪ ⊤  // (Prop2, ∀Prop, Prop2) ↪ (Set2,  Set1,  Set2) and (Type1, Prop,  )

with ∨ ∀Prop  ∀Prop ∀Prop ↪ ⊤;  // (∀Prop,  ∀Prop, ∀Prop) ↪ (Set1,  Set1,  Set1) and (Prop,  Prop,  Prop)

constant symbol ⇝ : Π (s1 s2: Sort) {s3 : Sort} (_ : ∨ s1 s2 s3) (A : U s1), (El s1 A → U s2) → U s3;
rule El _ (⇝ $s1 $s2 _ $A $B) ↪ Π (x : El $s1 $A), El $s2 ($B x);
