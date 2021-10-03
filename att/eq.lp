require open dk-encodings.att.att;

// type
constant symbol eq : Π A : U Set, El Set A → El Set A → U Prop;

// constructor
constant symbol refl : Π (A : U Set) (a : El Set A), El Prop (eq A a a);

// eliminators

// into Prop
symbol eq_ind : Π (A : U Set)
                  (x : El Set A)
                  (P : Π y : El Set A, El Prop (eq A x y) → U Prop)
                  (_ : El Prop (P x (refl A x)))
                  (y : El Set A)
                  (e : El Prop (eq A x y)),
                  El Prop (P y e);

// into TProp (large)
symbol eq_hind : Π (A : U Set)
                  (x : El Set A)
                  (P : Π y : El Set A, El Prop (eq A x y) → U TProp)
                  (_ : El TProp (P x (refl A x)))
                  (y : El Set A)
                  (e : El Prop (eq A x y)),
                  El TProp (P y e);

// into Set (large)
symbol eq_rec : Π (A : U Set)
                  (x : El Set A)
                  (P : Π y : El Set A, El Prop (eq A x y) → U Set)
                  (_ : El Set (P x (refl A x)))
                  (y : El Set A)
                  (e : El Prop (eq A x y)),
                  El Set (P y e);

// into TSet (large)
symbol eq_hrec : Π (A : U Set)
                  (x : El Set A)
                  (P : Π y : El Set A, El Prop (eq A x y) → U TSet)
                  (_ : El TSet (P x (refl A x)))
                  (y : El Set A)
                  (e : El Prop (eq A x y)),
                  El TSet (P y e);

// computation rules                
rule eq_ind $A $x _ $px $x (refl $A $x) ↪ $px; // QUESTION : why is the non-linearity really necessary ?
rule eq_hind $A $x _ $px $x (refl $A $x) ↪ $px; // QUESTION : why is the non-linearity really necessary ?
rule eq_rec $A $x _ $px $x (refl $A $x) ↪ $px; // QUESTION : why is the non-linearity really necessary ?
rule eq_hrec $A $x _ $px $x (refl $A $x) ↪ $px; // QUESTION : why is the non-linearity really necessary ?
