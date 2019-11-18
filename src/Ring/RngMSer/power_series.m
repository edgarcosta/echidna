////////////////////////////////////////////////////////////////////////
//                                                                    //
//                  Multivariate Power Series Rings                   //
//                            David Kohel                             //
//                                                                    //
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                      Attribute declarations                        //
//                                                                    //
////////////////////////////////////////////////////////////////////////

declare type RngMSer[RngMSerElt];

declare attributes RngMSer:
    PolynomialRing,
    PrecisionIdeal;

declare attributes RngMSerElt:
    Parent,
    Polynomial,
    PrecisionIdeal;
    // Translation;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                        Creation functions                          //
//                                                                    //
////////////////////////////////////////////////////////////////////////

intrinsic MultivariatePowerSeriesRing(R::Rng,n::RngIntElt : 
    Precision := 0) -> RngMSer
    {A Laurent series ring in n variables over R.}
    R := PolynomialRing(R,n,"grevlex"); 
    P := New(RngMSer);
    P`PolynomialRing := R;
    P`PrecisionIdeal :=	Precision gt 0
	select ideal< R | [ R.i^Precision : i in [1..n] ] >
	else ideal< R | 0 >;
    return P;
end intrinsic;

intrinsic AssignNames(~P::RngMSer, S::[MonStgElt])
    {Assign names to generating elements.}
    n := Rank(P`PolynomialRing);
    require #S le n : "Argument 2 must have length at most", n;
    AssignNames(~(P`PolynomialRing),S);
end intrinsic;

intrinsic Name(P::RngMSer,i::RngIntElt) -> RngMSerElt
    {The ith generator.}
    n := Rank(P`PolynomialRing);
    require 1 le i and i le n :
	"Argument 2 must have length at most", n;
    n := Rank(P`PolynomialRing);
    return P.i;
end intrinsic;

intrinsic '.'(P::RngMSer,i::RngIntElt) -> RngMSerElt
    {The ith generator.}
    n := Rank(P`PolynomialRing);
    require 1 le i and i le n :
	"Argument 2 must have length at most", n;
    x := New(RngMSerElt);
    x`Parent := P;
    // Not sure what this should be. Used to be:
    // x`Polynomial := P`PolynomialRing.(n+1-i);
    // The old code caused the monomials to be
    // printed opposite to how they were stored. eg:
    // typing "s1;" would cause s2 to be printed 
    // and vice versa.
    x`Polynomial := P`PolynomialRing.i;
    x`PrecisionIdeal := P`PrecisionIdeal;
    // x`Translation := RSpace(Integers(),n)!0;
    return x;
end intrinsic;

intrinsic BigO(S::[RngMSerElt]) -> RngMSerElt
    {}
    P := Universe(S);
    R := P`PolynomialRing; 
    x := New(RngMSerElt);
    x`Parent := P;
    x`Polynomial := R!0;
    x`PrecisionIdeal := ideal< R | [ x`Polynomial : x in S ] >;
    return x;
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                           Coercions                                //
//                                                                    // 
////////////////////////////////////////////////////////////////////////

intrinsic IsCoercible(P::RngMSer,S::.) -> BoolElt, RngMSerElt
    {}
    if Type(S) eq RngMSerElt and P eq Parent(S) then
	return true, S;  
    elif ISA(Type(S),RngElt) then
	bool, S := IsCoercible(BaseRing(P),S);
	if bool then
	    n := Rank(P`PolynomialRing);
	    x := New(RngMSerElt);
	    x`Parent := P;       
	    x`Polynomial := P`PolynomialRing!S;
	    x`PrecisionIdeal := P`PrecisionIdeal;
	    return true, x;
	end if;
    end if;
    return false, "Illegal coercion.";
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                           Printing                                 //
//                                                                    //
////////////////////////////////////////////////////////////////////////

intrinsic Print(P::RngMSer, level::MonStgElt)
    {}
    printf "Laurent series ring in %o variables over %o",
	Rank(R), BaseRing(R) where R := P`PolynomialRing; 
end intrinsic;

intrinsic Print(x::RngMSerElt, level::MonStgElt)
    {}
    B := GroebnerBasis(x`PrecisionIdeal);
    naked := true; // should we print a plus?
    if x`Polynomial ne 0 then
	terms := Terms(x`Polynomial);
	deg := 0;
	xx := 0;
        // we print the terms of lower degree first (hence Reverse())
        // but if we printed straight we would print things of the
        // same degree in the wrong order: eg: X2 + X1 + X2^2 + ...
	for xi in Reverse(terms) do
	    degi := TotalDegree(xi);
	    if degi gt deg then
		if xx ne 0 then
		    if not naked then printf " + "; end if;
		    printf "%o", xx;
		    naked := false;
		end if;
		xx := xi;
		deg := degi;
	    else
		xx +:= xi;
	    end if;
	end for;
        // Geordie 24/6 changed the location of this code.
        // This "if xx ne 0" condition used to be outside the "if x`Polynomial" condition.
        // This leads to a bug if you type, for example, BigO([s1,s2]) (as xx isn't defined).
        if xx ne 0 then
            if not naked then printf " + "; end if;
            printf "%o", xx;
            naked := false;
        end if;
    else // We only get here if the polynomial is zero.
        if #B eq 0 then printf "0"; end if; 
    end if;
    if #B gt 0 then
	if not naked then printf " + "; end if;
	printf "O(";
	for i in [1..#B-1] do
	    printf "%o,", B[i];
	end for;
	printf "%o)", B[#B];
        naked := false;
    end if;
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                  Membership and equality testing                   //
//                                                                    //
////////////////////////////////////////////////////////////////////////

intrinsic 'in'(x::., P::RngMSer) -> BoolElt
    {Returns true if x is in P.}
    if Type(x) eq RngMSerElt then
	return Parent(x) eq P;
    elif Type(x) eq RngMSer then
	return IsCoercible(P`BaseRing,x);
    end if;
    return false;
end intrinsic;

intrinsic Parent(x::RngMSerElt) -> RngMSer
    {}
    return x`Parent;
end intrinsic;

intrinsic 'eq' (R::RngMSer,S::RngMSer) -> BoolElt
    {}
    return R`PolynomialRing cmpeq S`PolynomialRing;
end intrinsic;

intrinsic 'eq' (x::RngMSerElt,y::RngMSerElt) -> BoolElt
    {}
    return Parent(x) eq Parent(y) and x`Polynomial eq y`Polynomial;
    // and x`Translation eq y`Translation;
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                      Attribute Access Functions                    //
//                                                                    //
////////////////////////////////////////////////////////////////////////

intrinsic Ngens(P::RngMSer) -> BoolElt
    {}
    return Rank(P`PolynomialRing);
end intrinsic;

intrinsic Rank(P::RngMSer) -> BoolElt
    {}
    return Rank(P`PolynomialRing);
end intrinsic;

intrinsic BaseRing(P::RngMSer) -> Rng
    {}
    return BaseRing(P`PolynomialRing);
end intrinsic;

//element attributes:

intrinsic Polynomial(Elt::RngMSerElt) -> RngMPolElt
    {}
    return Elt`Polynomial;
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//               Functionality, arithmetic operations, etc.           //
//                                                                    //
////////////////////////////////////////////////////////////////////////

intrinsic '-' (x::RngMSerElt) -> RngMSerElt
    {}
    y := New(RngMSerElt);
    y`Parent := x`Parent;
    y`Polynomial := -x`Polynomial;
    y`PrecisionIdeal := x`PrecisionIdeal;
    return y;
end intrinsic;

function Lowertrans(v1,v2)
    V := Parent(v1);
    n := Rank(V);
    return V![ Min(v1[i],v2[i]) : i in [1..n] ];
end function;

intrinsic '-' (x::RngElt,y::RngMSerElt) -> RngMSerElt
    {}
    P := y`Parent;
    bool, x := IsCoercible(BaseRing(P),x);
    require bool :
	"Argument 1 must coerce into the base ring of argument 2";
    z := New(RngMSerElt);
    z`Parent := P;
    z`Polynomial := x - y`Polynomial;
    z`PrecisionIdeal := y`PrecisionIdeal;
    return z;
end intrinsic;

intrinsic '-' (x::RngMSerElt,y::RngElt) -> RngMSerElt
    {}
    P := x`Parent;
    bool, y := IsCoercible(BaseRing(P),y);
    require bool :
	"Argument 1 must coerce into the base ring of argument 2";
    z := New(RngMSerElt);
    z`Parent := P;
    z`Polynomial := x`Polynomial - y;
    z`PrecisionIdeal := x`PrecisionIdeal;
    return z;
end intrinsic;

intrinsic '-' (x::RngMSerElt,y::RngMSerElt) -> RngMSerElt
    {}
    require x`Parent eq y`Parent : 
	"Arguments must have the same parent.";
    z := New(RngMSerElt);
    z`Parent := x`Parent;
    z`Polynomial := x`Polynomial - y`Polynomial;
    z`PrecisionIdeal := x`PrecisionIdeal + y`PrecisionIdeal;
    return z;
end intrinsic;

intrinsic '+' (x::RngElt,y::RngMSerElt) -> RngMSerElt
    {}
    P := y`Parent;
    bool, x := IsCoercible(BaseRing(P),x);
    require bool :
	"Argument 1 must coerce into the base ring of argument 2";
    z := New(RngMSerElt);
    z`Parent := P;
    z`Polynomial := x + y`Polynomial;
    z`PrecisionIdeal := y`PrecisionIdeal;
    return z;
end intrinsic;

intrinsic '+' (x::RngMSerElt,y::RngElt) -> RngMSerElt
    {}
    P := x`Parent;
    bool, y := IsCoercible(BaseRing(P),y);
    require bool :
	"Argument 2 must coerce into the base ring of argument 1";
    z := New(RngMSerElt);
    z`Parent := P;
    z`Polynomial := x`Polynomial + y;
    z`PrecisionIdeal := x`PrecisionIdeal;
    return z;
end intrinsic;

intrinsic '+' (x::RngMSerElt,y::RngMSerElt) -> RngMSerElt
    {}
    require x`Parent eq y`Parent:
	"Arguments must have the same parent.";
    z := New(RngMSerElt);
    z`Parent := x`Parent;
    z`Polynomial := x`Polynomial + y`Polynomial;
    z`PrecisionIdeal := x`PrecisionIdeal + y`PrecisionIdeal;
    return z;
end intrinsic;

intrinsic '*' (x::RngElt,y::RngMSerElt) -> RngMSerElt
    {}
    P := y`Parent; 
    bool, x := IsCoercible(BaseRing(P),x);
    z := New(RngMSerElt);
    z`Parent := P;
    z`PrecisionIdeal := y`PrecisionIdeal;
    z`Polynomial := x * y`Polynomial;
    return z;
end intrinsic;

intrinsic '*' (x::RngMSerElt,y::RngElt) -> RngMSerElt
    {}
    P := x`Parent; 
    bool, y := IsCoercible(BaseRing(P),y);
    z := New(RngMSerElt);
    z`Parent := P;
    z`PrecisionIdeal := x`PrecisionIdeal;
    z`Polynomial := y * x`Polynomial;
    return z;
end intrinsic;

intrinsic '*' (x::RngMSerElt,y::RngMSerElt) -> RngMSerElt
    {}
    P := x`Parent; 
    require P eq y`Parent: "Arguments must have the same parent.";
    R := P`PolynomialRing;
    xpoly := x`Polynomial;
    ypoly := y`Polynomial;
    z := New(RngMSerElt);
    z`Parent := P;
    // Geordie: changed this to deal with problems with, for example BigO([s1,s2])^2.
    // Used to be:
    // z`PrecisionIdeal :=
//	ideal< R | [ ypoly*f : f in GroebnerBasis(x`PrecisionIdeal) ] > + 
//	ideal< R | [ xpoly*f : f in GroebnerBasis(y`PrecisionIdeal) ] > + 
//	P`PrecisionIdeal;
    PI := GroebnerBasis(x`PrecisionIdeal);
    RI := GroebnerBasis(y`PrecisionIdeal);
    z`PrecisionIdeal :=
	ideal< R | [ ypoly*f : f in PI ] > + 
	ideal< R | [ xpoly*f : f in RI ] > + 
	ideal< R | [ f*g : f in PI, g in RI] >;
    z`Polynomial := NormalForm(xpoly * ypoly,z`PrecisionIdeal); 
    return z;
end intrinsic;

intrinsic '/' (x::RngMSerElt,y::RngElt) -> RngMSerElt
    {}
    P := x`Parent; 
    bool1, y := IsCoercible(BaseRing(P),y);
    bool2, u := IsInvertible(y);
    require bool1 and bool2 : 
	"Argument 2 must be a unit in the base ring of argument 1";
    z := New(RngMSerElt);
    z`Parent := P;
    z`PrecisionIdeal := x`PrecisionIdeal;
    z`Polynomial := u * x`Polynomial;
    return z;
end intrinsic;

intrinsic '/' (x::RngMSerElt,y::RngMSerElt) -> RngMSerElt
    {}
    P := x`Parent; 
    require P eq y`Parent: "Arguments must have the same parent.";
    R := P`PolynomialRing;
    xpoly := x`Polynomial;
    ypoly := y`Polynomial;
    a0 := MonomialCoefficient(ypoly,R!1);
    bool, u0 := IsInvertible(a0);
    require bool : "Argument 2 must be invertible.";
    I := x`PrecisionIdeal + y`PrecisionIdeal + P`PrecisionIdeal;
    xpoly := u0 * xpoly;
    mpoly := u0*(ypoly-a0);
    upoly := R!1;
    i := 0; 
    mipoly := NormalForm(mpoly,I);
    assert I ne ideal< R | 0 >;
    while mipoly ne 0 do
	i +:= 1;
	upoly +:= (-1)^i*mipoly;
	mipoly := NormalForm(mpoly*mipoly,I);
    end while;
    z := New(RngMSerElt);
    z`Parent := P;
    z`PrecisionIdeal := I;
    z`Polynomial := NormalForm(xpoly * upoly, I);
    return z;
end intrinsic;

intrinsic '^' (x::RngMSerElt,n::RngIntElt) -> RngMSerElt
    {}
    require n ge 0 : "Argument 2 must be nonnegative.";
    if n eq 0 then
	return Parent(x)!1;
    elif n eq 1 then
	return x;
    elif n eq 2 then
	return x*x;
    end if;
    P := x`Parent;
    R := P`PolynomialRing;
    y := New(RngMSerElt);
    y`Parent := P;
    xpoly := x`Polynomial;
    ypoly := Parent(xpoly)!1;
    b := IntegerToSequence(n,2);
    I := P`PrecisionIdeal;
    Iy := x`PrecisionIdeal;
    for i in [1..#b] do
	if b[i] eq 1 then
	    Iy +:= ideal< R | [ xpoly*f : f in GroebnerBasis(Iy) ] >;
	    ypoly := NormalForm(xpoly*ypoly,Iy);
	end if;
	if i ne #b then
	    xpoly := NormalForm(xpoly^2,I);
	end if;
    end for;
    y`Polynomial := ypoly;
    y`PrecisionIdeal := Iy;
    return y;
end intrinsic;

////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////

intrinsic Evaluate(f::RngSerElt,t::RngMSerElt) -> RngMSerElt
    {}
    P := Parent(t);
    // Should check weaker coercibility...
    require BaseRing(Parent(f)) cmpeq BaseRing(P) :
	"Arguments must have the same base ring.";
    cf, vf := Eltseq(f);
    ft := P!0; 
    ti := t^vf;
    for i in [1..#cf] do
	ft +:= cf[i]*ti;
	ti := t*ti;
    end for;
    return ft;
end intrinsic;

intrinsic Evaluate(f::RngMPolElt,S::[RngMSerElt]) -> RngMSerElt
    {}
    rank := Rank(Parent(f));
    require rank eq #S : "Argument 2 must have length equal" *
                                  " to the rank of the polynomial ring";
    coeffs := Coefficients(f);
    mons := Monomials(f);
    output := 0;
    for i in [1..#coeffs] do
        exps := Exponents(mons[i]);
        output +:= coeffs[i]*(&*[ S[j]^exps[j] : j in [1..rank]]);
    end for;
    return output;
end intrinsic;

intrinsic Evaluate(f::RngMSerElt,S::[RngElt]) -> RngMSerElt
    {}
    require #S eq Rank(Parent(f)) :
	"Argument 2 must have length equal to twice " *
	"the power series rank.";
    return Evaluate(f`Polynomial,S);
end intrinsic;
