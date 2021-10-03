require open 
  dk-encodings.att.att;

// type
constant symbol Existsp : Π (A : U Prop) (B : El Prop A → U Prop), U Prop;

// constructors
constant symbol exp :  Π (A : U Prop) (B : El Prop A → U Prop), 
                      Π a : El Prop A, El Prop (B a) → El Prop (Existsp A B);

// destructors
symbol exp_ind :  Π (A : U Prop) (B : El Prop A → U Prop) (P : El Prop (Existsp A B) → U Prop), 
                 (Π (a : El Prop A) (b : El Prop (B a)), El Prop (P (exp A B a b))) → 
                 Π (x : El Prop (Existsp A B)), El Prop (P x);

symbol exp_rec :  Π (A : U Prop) (B : El Prop A → U Prop) (P : El Prop (Existsp A B) → U Set), 
                 (Π (a : El Prop A) (b : El Prop (B a)), El Set (P (exp A B a b))) → 
                 Π (x : El Prop (Existsp A B)), El Set (P x);

symbol exp_hind :  Π (A : U Prop) (B : El Prop A → U Prop) (P : El Prop (Existsp A B) → U TProp), 
                 (Π (a : El Prop A) (b : El Prop (B a)), El TProp (P (exp A B a b))) → 
                 Π (x : El Prop (Existsp A B)), El TProp (P x);

symbol exp_hrec :  Π (A : U Prop) (B : El Prop A → U Prop) (P : El Prop (Existsp A B) → U TSet), 
                 (Π (a : El Prop A) (b : El Prop (B a)), El TSet (P (exp A B a b))) → 
                 Π (x : El Prop (Existsp A B)), El TSet (P x);

// computation rules
rule exp_ind $A $B $P $p (exp $A $B $a $b) ↪ $p $a $b;
rule exp_rec $A $B $P $p (exp $A $B $a $b) ↪ $p $a $b;
rule exp_hind $A $B $P $p (exp $A $B $a $b) ↪ $p $a $b;
rule exp_hrec $A $B $P $p (exp $A $B $a $b) ↪ $p $a $b;




                          


     
