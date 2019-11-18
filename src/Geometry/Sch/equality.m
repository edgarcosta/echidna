//////////////////////////////////////////////////////////////////////////////
//                                                                          // 
//            Equality of Schemes, Points, and Morphisms                    //
//                                                                          // 
//  Copyright (C) 2001 David Kohel <kohel@maths.usyd.edu>                   //
//                                                                          //
//  Distributed under the terms of the GNU General Public License (GPL)     //
//                  http://www.gnu.org/licenses/                            //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

intrinsic IsEqual(X::Sch,Y::Sch) -> BoolElt
    {}
    PP := Ambient(X);
    if PP ne Ambient(Y) then return false; end if;
    test := Ideal(X) eq Ideal(Y);
    if IsAffine(PP) or test then return test; end if;
    // Projective: test equality on each affine patch
    // Problem: There don't currently exist a complete set
    // of affine patches for weighted projective spaces.
    // Put this in as a require statement (should be fixed):
    require IsOrdinaryProjective(PP) :
    "Ambient spaces of arguments must be an unweighted projective space.";
    for i in [1..Dimension(PP)+1] do
	AA := AffinePatch(PP,i);
	test := Ideal(AA!!AffinePatch(X,i)) eq Ideal(AA!!AffinePatch(Y,i));
	printf "i = %o: %o\n", i, test;
	if not test then return test; end if;
    end for;
    return true;
end intrinsic;

intrinsic IsEqual(X::Sch,Y::Sch) -> BoolElt
    {}
    PP := Ambient(X);
    if PP ne Ambient(Y) then return false; end if;
    test := Ideal(X) eq Ideal(Y);
    if IsAffine(PP) or test then return test; end if;
    // Projective:
    //    Need to test equality on all affine patches
    for i in [1..Dimension(PP)+1] do
	AA := AffinePatch(PP,i);
	test := Ideal(AA!!AffinePatch(X,i)) eq Ideal(AA!!AffinePatch(Y,i));
	printf "i = %o: %o\n", i, test;
	if not test then return test; end if;
    end for;
    return true;
end intrinsic;

intrinsic AffinePatch(X::Sch,f::RngMPolElt) -> Sch
    {}
    require IsProjective(X) : "Argument 1 must be projective.";
    PP := Ambient(X);
    PR := CoordinateRing(PP);
    mons := Monomials(f);
    require f in PR and #mons eq 1 : 
        "Argument 2 must be a monomial in the ambient coordinate ring.";
    exps := Exponents(mons[1]);
    crit_exps := [ i : i in [1..Rank(PR)] | exps[i] ne 0 ];
    require #crit_exps gt 0 : 
        "Argument 2 must be a monomial in the ambient coordinate ring.";
    grds := Gradings(PP);
    require #grds eq 1 : "No idea what multiple gradings mean!";
    wts := grds[1];
    require GCD([ wts[i] : i in crit_exps ]) eq 1 :
        "Affine patch only exists where gradings have GCD 1.";
    if #crit_exps eq 1 then
	return AffinePatch(X,crit_exps[1]);
    end if;
    AR := PolynomialRing(BaseRing(X),Rank(PR));
    return X;
end intrinsic;

function IsGenericEqual(P,Q)
    // PRE: P and Q are points in the same ambient projective space.
    // OUT: true if and only if P and Q are equal as projective points.
    PP := Ambient(Scheme(P));
    grds := Gradings(PP);
    error if #grds ne 1, "No idea what multiple gradings mean!";
    wts := grds[1];
    dim := Dimension(PP);
    return &and[
        &and[ P[i]^wts[j]*Q[j]^wts[i] eq P[j]^wts[i]*Q[i]^wts[j] : 
 	    j in [i+1..dim+1] ] : i in [1..dim] ];
end function;

function IsNormalEqual(P,Q)
    // PRE: P and Q are points in the same ambient projective space.
    // OUT: true if and only if P and Q are equal as projective points.
    d := Dimension(Ambient(Scheme(P)));
    return &and[ P[i] eq Q[i] : i in [1..d+1] ];
end function;

intrinsic IsEqual(P::Pt,Q::Pt) -> BoolElt
    {}
    return IsGenericEqual(P,Q);
end intrinsic;

intrinsic IsEqual(f::MapSch,g::MapSch) -> BoolElt
    {}
    // PRE: Assume that domain and/or (which?) codomain is projective,
    // otherwise this is not needed.
    X := Domain(f);
    Y := Codomain(f);
    if X ne Domain(g) and Y ne Codomain(g) then return false; end if;
    feqns := DefiningEquations(f);
    geqns := DefiningEquations(g);
    require Universe(feqns) eq
       CoordinateRing(Ambient(X)) : "Ooops, wrong assumption.";
    R := CoordinateRing(X);
    P := Y(R)!feqns;
    Q := Y(R)!geqns;
    return IsGenericEqual(P,Q);
end intrinsic;

