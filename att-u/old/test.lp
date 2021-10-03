constant symbol Set : TYPE;
symbol El : Set → TYPE;
symbol ⇝ : Set → Set → Set;
rule El (⇝ $A $B) ↪ El $A → El $B;

constant symbol Nat : Set;
constant symbol Bool : Set;

rule El (⇝ Nat Bool) ↪ El (⇝ Bool Bool);

