require open dk-encodings.att.att;

// type
constant symbol Or : U Prop → U Prop → U Prop;

// constructors
constant symbol inl : Π (A B : U Prop), 
                      El Prop A → El Prop (Or A B);
constant symbol inr : Π (A B : U Prop), 
                      El Prop B → El Prop (Or A B);

// eliminators
symbol or_ind : Π (A B : U Prop) (P : El Prop (Or A B) → U Prop), 
                (Π a : El Prop A, El Prop (P (inl A B a))) →
                (Π b : El Prop B, El Prop (P (inr A B b))) →
                Π x : El Prop (Or A B), El Prop (P x);

symbol or_rec : Π (A B : U Prop) (P : El Prop (Or A B) → U Set), 
                (Π a : El Prop A, El Set (P (inl A B a))) →
                (Π b : El Prop B, El Set (P (inr A B b))) →
                Π x : El Prop (Or A B), El Set (P x);

symbol or_hind : Π (A B : U Prop) (P : El Prop (Or A B) → U TProp), 
                (Π a : El Prop A, El TProp (P (inl A B a))) →
                (Π b : El Prop B, El TProp (P (inr A B b))) →
                Π x : El Prop (Or A B), El TProp (P x);

symbol or_hrec : Π (A B : U Prop) (P : El Prop (Or A B) → U TSet), 
                (Π a : El Prop A, El TSet (P (inl A B a))) →
                (Π b : El Prop B, El TSet (P (inr A B b))) →
                Π x : El Prop (Or A B), El TSet (P x);

// computation rules
rule or_ind $A $B _ $pl _ (inl $A $B $a) ↪ $pl $a; // NON-LINEAR ! 
rule or_ind $A $B _ _ $pr (inr $A $B $a) ↪ $pr $a;

rule or_rec $A $B _ $pl _ (inl $A $B $a) ↪ $pl $a;
rule or_rec $A $B _ _ $pr (inr $A $B $a) ↪ $pr $a;

rule or_hind $A $B _ $pl _ (inl $A $B $a) ↪ $pl $a;
rule or_hind $A $B _ _ $pr (inr $A $B $a) ↪ $pr $a;

rule or_hrec $A $B _ $pl _ (inl $A $B $a) ↪ $pl $a;
rule or_hrec $A $B _ _ $pr (inr $A $B $a) ↪ $pr $a;




