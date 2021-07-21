// Levels
symbol L : TYPE;
symbol O : L;
symbol S : L → L;
symbol ⊔ : L → L → L;
rule ⊔ O $x ↪ $x
with ⊔ $x O ↪ $x
with ⊔ (S $x) (S $y) ↪ S (⊔ $x $y);

// Naturals
symbol N : TYPE;
symbol z : N;
symbol s : N → N;
symbol max : N → N → N;

// Sorts
symbol Sort : TYPE;
symbol U : Sort → TYPE;
symbol Set : L → Sort;
symbol Prop : L → Sort;
symbol Setω : N → Sort;

// Rule
symbol ∨ : Sort → Sort → Sort;
rule ∨ (Set $i) (Set $j) ↪ Set (⊔ $i $j)
with ∨ (Prop $i) (Prop $j) ↪ Prop (⊔ $i $j)
with ∨ (Setω $n) (Setω $m) ↪ Setω (max $n $m)
with ∨ (Set $i) (Prop $j) ↪ Prop (⊔ $i $j)
with ∨ (Prop $i) (Set $j) ↪ Set (⊔ $i $j)
with ∨ (Set _) (Setω $n) ↪ Setω $n
with ∨ (Setω $n) (Set _) ↪ Setω $n
with ∨ (Prop _) (Setω $n) ↪ Setω $n
with ∨ (Setω $n) (Prop _) ↪ Setω $n;

// Axiom
symbol □ : Sort → Sort;
rule □ (Set $i) ↪ Set (S $i)
with □ (Prop $i) ↪ Set (S $i)
with □ (Setω $n) ↪ Setω (s $n);

// Terms
symbol El : Π (s : Sort), U s → TYPE;

// Sort inclusion
symbol ⋄ : Π (s : Sort), U (□ s);
rule El _ (⋄ $s) ↪ U $s; 
//symbol ⇝ : TYPE;

// Products
symbol ⇝ : Π (s s' : Sort) (A : U s), (El s A → U s') → U (∨ s s');
rule El _ (⇝ $s $s' $A $B) ↪ Π (x : El $s $A), El $s' ($B x);


// Universe Polymorphism
symbol ∀s : Π α : L → L, (Π (i : L), U (Set (α i))) → U (Setω z);
rule El _ (∀s $α $A) ↪ Π (i : L), El (Set ($α i)) ($A i);
symbol ∀p : Π (α : L → L), (Π (i : L), U (Prop (α i))) → U (Setω z);
rule El _ (∀p $α $A) ↪ Π (i : L), El (Prop ($α i)) ($A i);
symbol ∀ω : Π (n : N), (L → U (Setω n)) → U (Setω n);
rule El _ (∀ω $n $A) ↪ Π (i : L), El (Setω $n) ($A i);

// Conjecture : The encoding described until here is both correct and complete


// Level lives in Set0
symbol Level : U (Set O);
rule El _ Level ↪ L;

// Conjecture : The encoding described until here is correct
// Problem : It is not complete
assert B ⊢ El (Set O) (⇝ (Set O) (Set O) Level B) ≡ El (Setω z) (∀s (λ _, O) B);
