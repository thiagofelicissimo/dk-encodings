symbol L : TYPE;
symbol O : L;
symbol S : L → L;
symbol ∪ : L → L → L;

symbol Sort : TYPE;
symbol Set : L → Sort;
symbol Setω : Sort;

symbol U : Sort → TYPE;
symbol El : Π (s : Sort), U s → TYPE;
symbol set : Π (i : L), U (Set (S i));

rule El _ (set $i) ↪ U (Set $i);

symbol Pi : Π (i j : L) (A : U (Set i)), (El (Set i) A → U (Set j)) → U (Set (∪ i j));
rule El _ (Pi $i $j $A $B) ↪ Π (x : El (Set $i) $A), El (Set $j) ($B x);

symbol ∀ : Π (α : L → Sort), (Π (i : L), U (α i)) → U Setω;
rule El _ (∀ $α $A) ↪ Π (i : L), El ($α i) ($A i);



