require open dk-encodings.att.att;

// type
constant symbol ⊥ : U Prop;

// constructor 
// empty

// eliminators

// into Prop
symbol ⊥_ind : Π (A : U Prop),
                 El Prop ⊥ →
                 El Prop A;

// into TProp (large)
symbol ⊥_hind : Π (A : U TProp),
                 El Prop ⊥ →
                 El TProp A;

// into Set (large)
symbol ⊥_rec : Π (A : U Set),
                 El Prop ⊥ →
                 El Set A;

// into TSet (large)
symbol ⊥_hrec : Π (A : U TSet),
                 El Prop ⊥ →
                 El TSet A;

// computation rules
// empty
