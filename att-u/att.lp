
// levels
constant symbol Lvl : TYPE;
constant symbol z : Lvl;
constant symbol s : Lvl → Lvl;
symbol ⊔ : Lvl → Lvl → Lvl;
notation ⊔ infix left 6;
rule z      ⊔ $x     ↪ $x
with $x     ⊔ z      ↪ $x
with (s $x) ⊔ (s $y) ↪ s ($x ⊔ $y);

// sorts
constant symbol Sort : TYPE; 
constant symbol set  : Lvl → Sort;
constant symbol prop : Lvl → Sort;
constant symbol U : Sort → TYPE;

// terms
symbol El : Π {s : Sort}, U s → TYPE;

// axiom
symbol □ : Sort → Sort;
rule □ (set $i) ↪ set (s $i)
with □ (prop $i) ↪ prop (s $i);

// sort inclusion
symbol ⋄ : Π (s : Sort), U (□ s);
rule El (⋄ $s) ↪ U $s; 

// products
symbol ∨ : Sort → Sort → Sort;
notation ∨ infix left 6;
rule (set $i)  ∨ (set $j)  ↪ set ($i ⊔ $j)
with (prop $i) ∨ (prop $j) ↪ prop ($i ⊔ $j)
with (prop $i) ∨ (set $j)  ↪ set ($i ⊔ $j)
with (set $i)  ∨ (prop $j) ↪ prop ($i ⊔ $j);

constant symbol ⇝ : Π {s1 s2: Sort} (A : U s1), (El A → U s2) → U (s1 ∨ s2);
notation ⇝ infix left 6;
rule El ($A ⇝ $B) ↪ Π (x : El $A), El ($B x);
