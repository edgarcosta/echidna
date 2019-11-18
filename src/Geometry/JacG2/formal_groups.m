//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//                        Formal Groups                                     //
//        Copyright (C) 2013 David Kohel <David.Kohel@univ-amu.fr>          //
//                                                                          //
//  Distributed under the terms of the GNU General Public License (GPL)     //
//                                                                          //
//                  http://www.gnu.org/licenses/                            //
//                                                                          //
//        All rights granted to distribute under the GPL, version 2,        //
//          or (at your option) any later version of the license.           //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

/* Created David Kohel, 2004 */

declare type GrpFrml[GrpFrmlElt];

declare attributes GrpFrml:
    GeometricObject,  // The scheme of which this is a formal completion
    SeriesRing, // A power series ring in n variables.
    BaseRing,   // The base ring of the formal group.
    GroupLaw,   // A power series in 2n variables defining the group law
    SSeries,	// EC-only: defines an injection t --> (t:-1:SSeries(t))
    /*
    XSeries,	// t/SSeries(t)
    YSeries,	// -1/SSeries(t)
    */
    Type,       // Elliptic, Additive, Multiplicative
    Dimension,  // Currently: 1.
    Precision;

declare attributes GrpFrmlElt:
    Element,    // A sequence of elements over the base ring
    Parent;

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//                            Creation functions                            //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////
    
intrinsic FormalGroupLaw(FG::GrpFrml,prec::RngIntElt :
    UsePowerSeries := false) -> RngElt
    {}
    C := FG`GeometricObject;
    R := FG`BaseRing;
    if FG`Type eq "Elliptic" then
	if assigned FG`GroupLaw and FG`Precision ge prec then
	    return FG`GroupLaw;
	end if;
	// Define the polynomial f which describes the elliptic curve 
	// near the origin such that (t : -1 : u) = (x : y : z).
	P<t,s> := PolynomialRing(R, 2);
	a1, a2, a3, a4, a6 := Explode([ R!a : a in Eltseq(C) ]);
	f := t^3 + a1*t*s + a2*t^2*s + a3*s^2 + a4*t*s^2 + a6*s^3;
	// Construct the power-series for s in terms of t.
	// TODO: express iterations as a function of a precision
	// which is optionally passed to FormalGroup.
    
	// Remember here that if may be worth calculating the series
	// to S one term beyond so that we have the right number of
	// terms when we come to compute m below.
	A<u> := PowerSeriesRing(R);
	S := BigO(u^3);
	for i in [3..(prec-1)] do
	    S := Evaluate(f,[u,S]);
	end for;

	// Construct the group law of the formal group.
	// If fixed precision rings aren't used the the algorithm
	// is _much_ slower.
	if UsePowerSeries then
	    T1<t1> := PowerSeriesRing(R, prec);
	    T2<t2> := PowerSeriesRing(T1,prec);
	    s1 := T2!Evaluate(S, t1);
	    s2 := Evaluate(S, t2);
	    t1 := T2!t1;
	else
	    T2<t1,t2> := MultivariatePowerSeriesRing(R,2 : Precision := prec);
	    s1 := Evaluate(S, t1);
	    s2 := Evaluate(S, t2);
	end if;
	// Explicit formula for m = gradient between the points
	// (t1:-1:S(t1)) and (t2:-1:S(t2))
	cS, v0 := Eltseq(S);
	m := &+[ T2 | 
	    cS[i] * &+[ t1^k * t2^(v0+i-2-k) : k in [0..v0+i-2] ] : i in [1..#cS] ];
	b := s1 - m*t1;
	A := 1 + a2*m + a4*m^2 + a6*m^3;
	t3 := -t1 -t2 - (a1*m + a2*b + a3*m^2 + 2*a4*m*b + 3*a6*m^2*b)/A; 
	s3 := Evaluate(S, t3);
	FG`SSeries := S;
	FG`GroupLaw := -t3/(1 - a1*t3 - a3*s3);
	FG`Precision := prec;
    elif FG`Type eq "Additive" then
	if UsePowerSeries then
	    T1<t1> := PowerSeriesRing(R, prec);
	    T2<t2> := PowerSeriesRing(T1,prec);
	    t1 := T2!t1;
	else
	    T2<t1,t2> := MultivariatePowerSeriesRing(R,2 : Precision := prec);
	end if;
	FG`GroupLaw := t1 + t2;
	FG`Precision := prec;
    elif FG`Type eq "Multiplicative" then
	if UsePowerSeries then
	    T1<t1> := PowerSeriesRing(R, prec);
	    T2<t2> := PowerSeriesRing(T1,prec);
	    t1 := T2!t1;
	else
	    T2<t1,t2> := MultivariatePowerSeriesRing(R,2 : Precision := prec);
	end if;
	FG`GroupLaw := t1 + t2 + t1*t2;
	FG`Precision := prec;
    else // Not Elliptic, Additive, or Multiplicative...
	require false :
	    "Unknown type of formal group scheme.";
    end if;
    return FG`GroupLaw;
end intrinsic;


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//                              Constructors                                //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

intrinsic FormalGroup(E::CrvEll) -> GrpFrml
    {Create the formal groups corresponding to the elliptic curve E.}
    R := BaseRing(E);
    FG := New(GrpFrml);
    FG`GeometricObject := E;
    FG`SeriesRing := PowerSeriesRing(R);
    FG`BaseRing := R;
    FG`Type := "Elliptic";
    FG`Precision := 16; 
    return FG;
end intrinsic;


intrinsic FormalGroup(E::CrvEll,R::Rng) -> GrpFrml
    {Create the formal groups corresponding to the elliptic curve E.}
    FG := New(GrpFrml);
    FG`GeometricObject := E;
    // Consider creating over the base ring of E:
    FG`SeriesRing := PowerSeriesRing(R);
    FG`BaseRing := R;
    FG`Type := "Elliptic";
    FG`Precision := 16; 
    return FG;
end intrinsic;


intrinsic FormalAdditiveGroup(R::Rng) -> GrpFrml
    {The formal additive group G_a.}
    FG := New(GrpFrml);
    FG`GeometricObject := AffineSpace(R,1);
    FG`SeriesRing := PowerSeriesRing(R);
    FG`BaseRing := R;
    FG`Type := "Additive";
    FG`Precision := 16; 
    return FG;
end intrinsic;

intrinsic FormalMultiplicativeGroup(R::Rng) -> GrpFrml
    {The formal multiplicative group G_m.}
    FG := New(GrpFrml);
    FG`GeometricObject := AffineSpace(R,1);
    FG`SeriesRing := PowerSeriesRing(R);
    FG`BaseRing := R;
    FG`Type := "Multiplicative";
    FG`Precision := 16;
    return FG;
end intrinsic;


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//                              Coercions                                   //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

function GrpFrmlCreateElt(G, S)
    x := New(GrpFrmlElt);
    x`Parent := G;
    x`Element := S;
    return x;
end function;

intrinsic IsCoercible(G::GrpFrml,S::.) -> BoolElt, GrpFrmlElt
    {Coerce the element S into the formal group G.}
    // There are are two possibilities in which coercion is possible:
    // -- S is a power-series without constant term which can be coerced
    // into BaseRing(G).
    // -- The formal group G is defined over a pAdic field and the element
    // S can be coerced as an element (x:y:1) in the parent curve with
    // xy^{-1} in the maximal ideal of the corresponding local ring.

    // First the trivial case:
    if Type(S) eq GrpFrmlElt then
	if Parent(S) eq G then return true, S; end if;
    // Now we do the power-series case:
    elif ISA(Type(S),RngSerElt) then
	// This handles the series ring:
	bool, x := IsCoercible(G`SeriesRing, S);
        if bool then
            if Valuation(x) ge 1 then return true, GrpFrmlCreateElt(G,x);
            else return false, "The power series must have no constant term";
            end if;
	end if;
	// Also handle base ring...
    end if;
    // Lastly we do the elliptic curve case:
    // S is a sequence which can be regarded as a point on the parent curve.
    if ISA(Type(S), SeqEnum) or ISA(Type(S), PtEll) or ISA(Type(S), RngElt) then
        if not ISA(Type(BaseRing(G`GeometricObject)), FldPad) then
            return false, "this coercion is only possible over a local field";
        end if;
    end if;
    if ISA(Type(S), SeqEnum) then
        bool, S := IsCoercible(G`GeometricObject, S);
	if not bool then return false,
	    "couldn't coerce sequence into parent curve"; end if;
    end if;
    if ISA(Type(S), PtEll) then
        print "sorry, not yet implemented!";
    end if;
    if ISA(Type(S), RngElt) then
        print "sorry, not yet implemented!";
    end if;
    return false, "Illegal coercion in formal group";
end intrinsic;


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//                                  Printing                                //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

intrinsic Print(G::GrpFrml, level::MonStgElt)
   {}
   printf "Formal group of %o", G`GeometricObject;
end intrinsic;

intrinsic Print(x::GrpFrmlElt, level::MonStgElt)
   {}
   printf "%o", x`Element;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//                         Membership and Equality                          //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

intrinsic 'in'(x::., X::GrpFrml) -> BoolElt
   {Returns true if x is in X.}
   if Type(x) eq GrpFrmlElt then
      return x`Parent eq X;
   end if;
   return false;
end intrinsic;

intrinsic Parent(x::GrpFrmlElt) -> GrpFrml
   {}
   return x`Parent;
end intrinsic;

intrinsic 'eq' (G1::GrpFrml,G2::GrpFrml) -> BoolElt
   {Return true if the two formal groups are equal.}
   return G1`GeometricObject cmpeq G2`GeometricObject;
end intrinsic;

intrinsic 'eq' (x::GrpFrmlElt,y::GrpFrmlElt) -> BoolElt
   {Return true if the two formal group elements are equal.}
   return Parent(x) eq Parent(y) and x`Element eq y`Element;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//                                Addition Law                              //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

intrinsic '+' (x::GrpFrmlElt,y::GrpFrmlElt : Precision := 0) -> BoolElt
    {}
    G := Parent(x);
    require G eq Parent(y) : "Arguments must have the same parent.";
    prec := Precision eq 0 select G`Precision else Precision;
    // one-dimensional case:
    F := FormalGroupLaw(G,prec); 
    return Parent(x)!Evaluate(F,[x`Element,y`Element]);
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
