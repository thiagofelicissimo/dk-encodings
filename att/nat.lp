require open dk-encodings.att.att;

// type
constant symbol Nat : U Set;

// constructors
constant symbol zero : El Set Nat;
constant symbol succ : El Set Nat → El Set Nat;

// eliminators
symbol nat_ind : Π P : El Set Nat → U Prop,
                   El Prop (P zero) →
                   (Π n : El Set Nat, El Prop (P n) → El Prop (P (succ n))) →
                   Π n : El Set Nat, 
                   El Prop (P n);

symbol nat_rec : Π P : El Set Nat → U Set,
                   El Set (P zero) →
                   (Π n : El Set Nat, El Set (P n) → El Set (P (succ n))) →
                   Π n : El Set Nat, 
                   El Set (P n);

symbol nat_hind : Π P : El Set Nat → U TProp,
                    El TProp (P zero) →
                    (Π n : El Set Nat, El TProp (P n) → El TProp (P (succ n))) →
                    Π n : El Set Nat, 
                    El TProp (P n);

symbol nat_hrec : Π P : El Set Nat → U TSet,
                    El TSet (P zero) →
                    (Π n : El Set Nat, El TSet (P n) → El TSet (P (succ n))) →
                    Π n : El Set Nat, 
                    El TSet (P n);

// computation rules                
rule nat_ind _ $p0 _ zero ↪ $p0
with nat_ind $P $p0 $ps (succ $n) ↪ $ps $n (nat_ind $P $p0 $ps $n);

rule nat_rec _ $p0 _ zero ↪ $p0
with nat_rec $P $p0 $ps (succ $n) ↪ $ps $n (nat_rec $P $p0 $ps $n);

rule nat_hind _ $p0 _ zero ↪ $p0
with nat_hind $P $p0 $ps (succ $n) ↪ $ps $n (nat_hind $P $p0 $ps $n);

rule nat_hrec _ $p0 _ zero ↪ $p0
with nat_hrec $P $p0 $ps (succ $n) ↪ $ps $n (nat_hrec $P $p0 $ps $n);
