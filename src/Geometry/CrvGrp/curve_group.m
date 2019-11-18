//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//                       SINGULAR CUBIC CURVES                              //
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

/* Created David Kohel, 1999 */

/*----------------------------------------------------------------------
   Attribute declaractions
   Creation, coercions, membership and equality
   Points, group law, division polynomials
----------------------------------------------------------------------*/

////////////////////////////////////////////////////////////////////////
//                      Attribute declarations                        //
////////////////////////////////////////////////////////////////////////

declare type CrvGrp;

declare attributes CrvGrp:
    Curve,
    Discriminant,   // can be nonzero in mixed characteristic
    BaseIsField,    // true or false
    IsSingular,     // currently true (else elliptic curve)
    NonPoints,      // for fields only
    VoidLocus,      // for arbitrary rings
    FunctionField,  // for fields only
    GenericCurve,   // temp hack for division polynomials
    GenericIndices, // for specialization map to curve
    GroupType;      // additive or multiplicative

declare type SetPtGrp[PtGrp];

declare attributes SetPtGrp:
    Scheme,
    Ring;

declare attributes PtGrp:
    Parent,
    Point;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                          Miscellanea                               //
//                                                                    //
////////////////////////////////////////////////////////////////////////

intrinsic AmbientDimension(C::CrvGrp) -> RngIntElt
    {The dimension of the ambient space.}
    return Dimension(AmbientSpace(C));
end intrinsic;

intrinsic AmbientSpace(C::CrvGrp) -> Sch
    {}
    if Type(C`Curve) in {Aff,Prj} then
	return C`Curve;
    end if;
    return AmbientSpace(C`Curve);
end intrinsic;

intrinsic '#'(P::PtGrp) -> RngIntElt
    {}
    return #Coordinates(P);
end intrinsic;

intrinsic DefiningPolynomial(C::CrvGrp) -> RngElt
    {}
    return Polynomial(C);
end intrinsic;

intrinsic DefiningEquation(C::CrvGrp) -> RngElt
    {}
    return Polynomial(Curve(C));
end intrinsic;

intrinsic IsFieldType(R::Rng) -> BoolElt
    {}
    if Type(R) in { RngIntRes } then
	// Other special cases?
	return false;
    end if;
    return IsField(R);
end intrinsic;

intrinsic PlaneCurve(C::CrvGrp) -> Crv
    {}
    return C`Curve;
end intrinsic;

intrinsic Curve(X::SetPtGrp) -> CrvGrp
    {}
    return X`Scheme;
end intrinsic;

intrinsic Scheme(X::SetPtGrp) -> CrvGrp
    {}
    return X`Scheme;
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                       Creation functions                           //
//                                                                    //
////////////////////////////////////////////////////////////////////////

intrinsic GenericEllipticCurve(K::Fld) -> CrvEll
    {Returns an elliptic with generic coefficients.}
    F5<a1,a2,a3,a4,a6> := FunctionField(K,5);
    return EllipticCurve([a1,a2,a3,a4,a6]);
end intrinsic;

intrinsic GenericEllipticCurve(S::SeqEnum) -> CrvEll
    {Returns a generic elliptic curve with support on
    the nonzero coefficients of S.}

    error if #S notin {2,5}, "Invalid sequence.";
    R := Universe(S);
    if R cmpeq Integers() then
	R := RationalField();
    end if;
    error if not IsField(R), "Invalid coefficient ring.";
    if #S eq 2 then
	a4,a6 := Explode(S);
	t := 2;
    else
	a1,a2,a3,a4,a6 := Explode(S);
	if &and[ S[i] eq 0 : i in [1..3] ] then
	    t := 2;
	else
	    t := 5;
	end if;
    end if;

    if t eq 2 then
	if a4 eq 0 then
	    F<b> := FunctionField(R);
	    return EllipticCurve([0,b]);
	elif a6 eq 0 then
	    if R!2 eq 0 then
		F<a1,a4> := FunctionField(R,2);
		return EllipticCurve([a1,0,0,a4,0]);
	    end if;
	    F<a> := FunctionField(R);
	    return EllipticCurve([a,0]);
	else
	    F<a,b> := FunctionField(R,2);
	    return EllipticCurve([a,b]);
	end if;
    elif t eq 5 then
	Wts := [1,2,3,4,6];
	I := [ Wts[i] : i in [1..5] | S[i] ne 0 ];
	if 4 notin I and 6 notin I then
	    I := I cat [6];
	end if;
	if Characteristic(R) eq 2 and 1 notin I then
	    I := [1] cat I;
	end if;
	F := FunctionField(R,#I);
	AssignNames(~F, [ "x" cat IntegerToString(k) : k in I ]);
	S := [ F!0 : i in [1..5] ];
	for i in [1..#I] do
	    S[Index(Wts,I[i])] := F.i;
	end for;
	return EllipticCurve(S);
    end if;
end intrinsic;

intrinsic SingularCubicCurve(S::SeqEnum : Projective := true) -> CrvGrp
    {The singular cubic curve defined as a plane cubic in
    Weierstrass form.}

    R := Universe(S);
    if #S eq 2 then
	a4,a6 := Explode(S);
	a1 := R!0; a2 := R!0; a3 := R!0;
    elif #S eq 5 then
	a1,a2,a3,a4,a6 := Explode(S);
    else
	error "Invalid defining sequence.";
    end if;
    disc := -a1^6*a6 + a1^5*a3*a4 - a1^4*a2*a3^2 -
	12*a1^4*a2*a6 + a1^4*a4^2 + 8*a1^3*a2*a3*a4 +
	a1^3*a3^3 + 36*a1^3*a3*a6 - 8*a1^2*a2^2*a3^2 -
	48*a1^2*a2^2*a6 + 8*a1^2*a2*a4^2 - 30*a1^2*a3^2*a4 +
	72*a1^2*a4*a6 + 16*a1*a2^2*a3*a4 + 36*a1*a2*a3^3 +
	144*a1*a2*a3*a6 - 96*a1*a3*a4^2 - 16*a2^3*a3^2 -
	64*a2^3*a6 + 16*a2^2*a4^2 + 72*a2*a3^2*a4 +
	288*a2*a4*a6 - 27*a3^4 - 216*a3^2*a6 -
	64*a4^3 - 432*a6^2;
    /*
    if (disc ne 0) and IsFieldType(R) then
        return EllipticScheme(S);
    end if;
    */
    C := New(CrvGrp);
    if not IsFieldType(R) then
	Projective := true;
    end if;
    if Projective then
	A<X,Y,Z> := ProjectiveSpace(R,2);
    else
	A<x,y> := AffineSpace(R,2);
	X := x;
	Y := y;
	Z := R!1;
    end if;
    f := Y^2*Z + (a1*X + a3*Z)*Y*Z
	- (X^3 + a2*X^2*Z + a4*X*Z^2 + a6*Z^3);
    C`Curve := Curve(A,f);
    C`Discriminant := disc;
    if IsUnit(R!disc) then
	C`IsSingular := false;
    else
	C`IsSingular := true;
    end if;

    if not IsFieldType(R) then
	C`VoidLocus := SingularSubscheme(C`Curve);
    else
	Sngpts := RationalPoints(SingularSubscheme(C`Curve));
	if #Sngpts eq 1 then
	    C`NonPoints := Sngpts;
	end if;
	F1<x> := FunctionField(R);
	P2<T> := PolynomialRing(F1);
	f := T^2 + (a1*x + a3)*T - (x^3 + a2*x^2 + a4*x + a6);   
	if IsSeparable(f) then 
	    FF<y> := FunctionField(f);
	else 
	    FF<y> := quo< P2 | f >;  
	end if;
	C`FunctionField := FF;
	C`GenericCurve := GenericEllipticCurve(S);
	// This is a bit of a hack -- the implementaion 
	// of GenericEllipticCurve could change.
	// Make both call a GenericCoefficients function.
	if (#S eq 2) or (&and [ S[i] eq 0 : i in [1..3] ]) then
	    if a4 eq 0 then 
		C`GenericIndices := [5];
	    elif a6 eq 0 then 
		if R!2 eq 0 then
		    C`GenericIndices := [1,4];
		else 
		    C`GenericIndices := [4];
		end if;
	    else
		C`GenericIndices := [4,5];
	    end if;
	else
	    I := [ i : i in [1..5] | S[i] ne 0 ];
	    if 4 notin I and 5 notin I then
		I := I cat [5];
	    end if; 
	    C`GenericIndices := I;
	end if;
    end if;
    return C;
end intrinsic;

intrinsic MultiplicativeGroupScheme(R::Rng : Split := true) -> CrvGrp 
    {The multiplicative group over the base ring R.}
    X := New(CrvGrp);
    A<x> := AffineSpace(R,1);
    X`Curve := A;
    X`NonPoints := [ [0] ];
    X`VoidLocus := Scheme(A,x);
    X`IsSingular := false;
    X`Discriminant := R!1; // no places of bad reduction
    X`GroupType := "Multiplicative";
    return X;
end intrinsic;

intrinsic AdditiveGroupScheme(R::Rng) -> CrvGrp 
    {The multiplicative group over the base ring R.}
    X := New(CrvGrp);
    A<x> := AffineSpace(R,1);
    X`Curve := A;
    X`NonPoints := [ ];
    X`VoidLocus := Scheme(A,CoordinateRing(A)!1);
    X`IsSingular := false;
    X`Discriminant := R!1; // no places of bad reduction
    X`GroupType := "Additive";
    return X;
end intrinsic;

intrinsic IsSingular(C::CrvGrp) -> BoolElt
    {True if C is singular plane model.}
    return C`IsSingular;
end intrinsic;

intrinsic SingularPoints(C::CrvGrp) -> Pt
    {The singularity of the closure of C.}
    error if not C`IsSingular, "Curve is nonsingular."; 
    error if not assigned C`NonPoints, 
	"Singular point undetermined.";
    return C`NonPoints;
end intrinsic;

intrinsic SingularSubscheme(C::CrvGrp) -> Sch
    {The singular locus of the underlying curve of C.}
    error if not C`IsSingular, "Curve is nonsingular."; 
    if not assigned C`VoidLocus then 
	C`VoidLocus := SingularSubscheme(C`Curve);
    end if;
    return C`VoidLocus;
end intrinsic;

intrinsic VoidLocus(C::CrvGrp) -> Sch
    {The locus of points not in the singular cubic curve C.}
    if not assigned C`VoidLocus then
	C`VoidLocus := SingularSubscheme(C`Curve);
    end if;
    return C`VoidLocus;
end intrinsic;

intrinsic Curve(C::CrvGrp) -> Crv
    {The underlying curve of C.}
    return C`Curve;
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                         Coercions                                  //
//                                                                    //
////////////////////////////////////////////////////////////////////////

intrinsic IsCoercible(C::CrvGrp,P::.) -> BoolElt, PtGrp
    {The point on C defined by P.}
    A := AmbientSpace(C);
    R := BaseRing(C);
    if Type(P) eq RngIntElt then
	if P eq 0 then
	    Xset := New(SetPtGrp);
	    Xset`Scheme := C;
	    Xset`Ring := R;
	    Xpt := New(PtGrp);
	    Xpt`Parent := Xset;
	    if AmbientDimension(C) eq 1 then
		if IsMultiplicative(C) then
		    if IsAffine(C) then
			Xpt`Point := A![1];
		    else
			Xpt`Point := A![1,1];
		    end if;
		else
		    if IsAffine(C) then
			Xpt`Point := A![0];
		    else
			Xpt`Point := A![0,1];
		    end if;
		end if;
	    else
		Xpt`Point := A![R|0,1,0];
	    end if;
	    return true, Xpt;
	end if;
    end if;

    if Type(P) eq SeqEnum then
	S := Universe(P);
	if Type(S) eq RngInt then
	    P := [ R!x : x in P ];
	    S := R;
	end if;
	// A := BaseExtend(A,S);
	if IsAffine(A) then
	    if P eq [ S | 0,1,0 ] then
		Xset := New(SetPtGrp);
		Xset`Scheme := C;
		Xset`Ring := S;
		Xpt := New(PtGrp);
		Xpt`Parent := Xset;
		Xpt`Point := P;
		return true, Xpt;
	    end if;
	    n := Dimension(A);
	else
	    n := Dimension(A) + 1;
	    if #P eq 2 and n eq 3 then
		P cat:= [1];
	    end if;
	end if;
	if #P eq n and P in Curve(C) then
	    Xset := New(SetPtGrp);
	    Xset`Scheme := C;
	    Xset`Ring := S;
	    Xpt := New(PtGrp);
	    Xpt`Parent := Xset;
	    Xpt`Point := A!P;
	    return true, Xpt;
	end if;
    end if;
    return false, "Illegal coercion: point is not on curve.";
end intrinsic;

intrinsic IsCoercible(X::SetPtGrp,P::.) -> BoolElt, PtGrp
    {The point on C defined by P.}
    C := X`Scheme;
    A := AmbientSpace(X`Scheme);
    R := BaseRing(A);
    if Type(P) eq RngIntElt then
	if P eq 0 then
	    Xpt := New(PtGrp);
	    Xpt`Parent := X;
	    if Dimension(A) eq 1 then
		if IsMultiplicative(C) then
		    if IsAffine(C) then
			Xpt`Point := A![1];
		    else
			Xpt`Point := A![1,1];
		    end if;
		else
		    if IsAffine(C) then
			Xpt`Point := A![0];
		    else
			Xpt`Point := A![0,1];
		    end if;
		end if;
	    else
		Xpt`Point := A![R|0,1,0];
	    end if;
	    return true, Xpt;
	end if;
    end if;
    if Type(P) eq PtGrp then
	if Parent(P) cmpeq X then
	    return true, P;
	end if;
	P := Eltseq(P);
    end if;

    if Type(P) eq SeqEnum then
	S := Universe(P);
	if Type(S) eq RngInt then
	    P := [ R!x : x in P ];
	    S := R;
	end if;
	// A := BaseExtend(A,S);
	if IsAffine(A) then
	    if P eq [ S | 0,1,0 ] then
		Xpt := New(PtGrp);
		Xpt`Parent := X;
		Xpt`Point := P;
		return true, Xpt;
	    end if;
	    n := Dimension(A);
	else
	    n := Dimension(A) + 1;
	end if;
	if #P eq n and P in Curve(C) then
	    Xpt := New(PtGrp);
	    Xpt`Parent := X;
	    Xpt`Point := A!P;
	    return true, Xpt;
	end if;
    end if;
    return false, "Illegal coercion: point is not on curve.";
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                         Printing                                   //
//                                                                    //
////////////////////////////////////////////////////////////////////////

intrinsic Print(C::CrvGrp, level::MonStgElt)
    {}
    if AmbientDimension(C) eq 1 then
	if IsMultiplicative(C) then
	    printf "Multiplicative group scheme of dimension 1 over %o", BaseRing(C);
	else
	    printf "Additive affine group of dimension 1 over %o", BaseRing(C);
	end if;
	return;
    end if;
    a1,a2,a3,a4,a6 := Explode(aInvariants(C));
    R := AmbientSpace(C);
    X := R.1; Y := R.2; Z := IsProjective(C) select R.3 else R!1;
    f := X^3 + a2*X^2*Z + a4*X*Z^2 + a6*Z^3;
    if C`IsSingular then
	Text := "Singular cubic curve with defining equation ";
    else
	Text := "Elliptic curve with defining equation ";
    end if;
    if a1 eq 0 and a3 eq 0 then
	printf Text cat "%o = %o over %o", Y^2*Z, f, BaseRing(C);
    else
	printf Text cat "%o + %o = %o over %o",
	    Y^2*Z, a1*X*Y*Z + a3*Y*Z^2, f, BaseRing(C);
    end if;
end intrinsic;

intrinsic Print(X::SetPtGrp, level::MonStgElt)
    {}
    C := X`Scheme;
    printf "Set of points of %o over %o", C, X`Ring;
end intrinsic;

intrinsic Print(P::PtGrp, level::MonStgElt)
    {}
    S := Eltseq(P`Point);
    C := Parent(P)`Scheme;
    n := AmbientDimension(C);
    if IsAffine(C) then
	if n eq 1 then
	    printf "(%o)", S[1];
	else // n eq 2 then
	    printf "(%o, %o)", S[1], S[2];
	end if;
    else
	if n eq 1 then
	    printf "(%o : %o)", S[1], S[2];
	else // n eq 2 then
	    printf "(%o : %o : %o)", S[1], S[2], S[3];
	end if;
    end if;
end intrinsic;

// Other functions

intrinsic BaseRing(C::CrvGrp) -> Rng
    {}
    return BaseRing(C`Curve);
end intrinsic;

intrinsic BaseField(C::CrvGrp) -> Rng
    {}
    R := BaseRing(C);
    error if not IsField(R), "Base ring is not a field.";
    return R;
end intrinsic;

intrinsic Discriminant(C::CrvGrp) -> RngElt
    {}
    return C`Discriminant;
end intrinsic;

intrinsic IsAdditive(C::CrvGrp) -> BoolElt
    {}
    if not IsSingular(C) then 
	return false; 
    elif Discriminant(C) ne 0 then
	return false;
    end if;
    return not IsMultiplicative(C);
end intrinsic
    
intrinsic IsMultiplicative(C::CrvGrp) -> BoolElt
    {}
    if assigned C`GroupType then
	return C`GroupType eq "Multiplicative";
    end if;
    if not C`IsSingular then 
	return false; 
    end if;
    if not assigned C`GroupType then
	a1,a2,a3,a4,a6 := Explode(aInvariants(C)); 
	c4 := a1^4 + 8*a1^2*a2 - 24*a1*a3 + 16*a2^2 - 48*a4;
	if c4 eq 0 then
	    C`GroupType := "Additive";
	else 
	    C`GroupType := "Multiplicative";
	end if;
    end if;
    return C`GroupType eq "Multiplicative";
end intrinsic
    
intrinsic IsSplit(C::CrvGrp) -> BoolElt 
    {}
    error if not IsFieldType(BaseRing(C)),
	"Splitting type not defined over general rings.";
    error if not IsMultiplicative(C),
	"Curve must be of multiplicative type.";
    P := SingularPoints(C)[1];
    f := DefiningPolynomial(TangentCone(C`Curve,P));
    t := #Factorization(f);
    if t eq 2 then
	return true;
    else    
	return false;
    end if;
end intrinsic;

intrinsic IsProjective(C::CrvGrp) -> BoolElt 
    {}
    return Type(AmbientSpace(C)) eq Prj;
end intrinsic;

intrinsic IsAffine(C::CrvGrp) -> BoolElt
    {}
    return Type(AmbientSpace(C)) eq Aff;
end intrinsic;

intrinsic IsIdentity(P::PtGrp) -> BoolElt
    {}
    C := Parent(P)`Scheme;
    S := Eltseq(P);
    R := Universe(S);
    if AmbientDimension(C) eq 1 then
	if IsMultiplicative(C) then
	    if IsAffine(C) then
		return S eq [ R!1 ];
	    else
		return S eq [ R | 1,1 ];
	    end if;
	else
	    if IsAffine(C) then
		return S eq [ R!0 ];
	    else
		return S eq [ R | 0,1 ];
	    end if;
	end if;
    end if;
    return S eq [ R | 0,1,0 ];
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                            Parents                                 //
//                                                                    //
////////////////////////////////////////////////////////////////////////

intrinsic Parent(P::PtGrp) -> SetPtGrp
    {The parent of P.}
    return P`Parent;
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                   Membership and equality                          //
//                                                                    //
////////////////////////////////////////////////////////////////////////

intrinsic 'in'(P::., C::CrvGrp) -> BoolElt
    {Returns true if P defines a point on C.}
    if Type(P) notin {SeqEnum,Pt,PtGrp} then
	return false;
    end if;
    P := Eltseq(P);
    S := Universe(P);
    if Type(S) eq RngInt then
	P := [ BaseRing(C)!x : x in P ];
	S := BaseRing(C);
    end if;
    n := AmbientDimension(C);
    if n eq 2 and P eq [ S | 0,1,0 ] then
	return true;
    elif IsAffine(C) and #P ne n then
	return false;
    elif IsProjective(C) and #P ne n+1 then
	return false;
    end if;
    /*
    // Skip this test -- too restrictive.
    B := DefiningPolynomials(VoidLocus(C));
    if true or IsField(S) then
	if &and [ IsZero(Evaluate(f,P)) : f in B ] then
	    return false; // Singular point on curve.
	end if;
    else
	if S ne ideal< S | [ Evaluate(f,P) : f in B ] > then
	    return false; // Element meets singular locus.
	end if;
    end if;
    */
    return EvaluatePolynomial(C,Eltseq(P)) eq 0;
end intrinsic;

intrinsic IsOnCurve(C::CrvGrp,P::SeqEnum) -> BoolElt
    {}
    return P in C;
end intrinsic;

intrinsic 'eq'(P::PtGrp,Q::PtGrp) -> BoolElt
    {}
    C := Parent(P)`Scheme;
    if C ne Parent(Q)`Scheme then 
	return false;
    elif IsIdentity(P) then
	return IsIdentity(Q);
    elif IsAffine(C) then
	return Coordinates(P) eq Coordinates(Q);
    else 
	x1,y1,z1 := Explode(Coordinates(P) cat [0]);
	x2,y2,z2 := Explode(Coordinates(Q) cat [0]);
	return x1*y2 eq x2*y1 and x1*z2 eq x2*z1 and y1*z2 eq y2*z1;
    end if;
end intrinsic; 

intrinsic 'eq'(S1::SetPtGrp,S2::SetPtGrp) -> BoolElt
    {}
    if S2`Scheme ne S2`Scheme then 
	return false;
    end if;
    return S1`Ring cmpeq S2`Ring;
end intrinsic; 

intrinsic 'eq'(C1::CrvGrp,C2::CrvGrp) -> BoolElt
    {}
    if AmbientDimension(C1) eq 1 then
	if AmbientDimension(C2) ne 1 or 
	    IsAdditive(C1) xor IsAdditive(C2) then
	    print "Here.";
	    return false;
	end if;
	return true;
    elif AmbientDimension(C2) eq 1 then
	return false;
    end if;
    return C1`Curve eq C2`Curve;
end intrinsic; 

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                          Arithmetic                                //
//                                                                    //
////////////////////////////////////////////////////////////////////////

intrinsic DefiningPolynomial(C::CrvGrp) -> SeqEnum 
    {}
    return DefiningPolynomial(C`Curve);
end intrinsic;

intrinsic aInvariants(C::CrvGrp) -> SeqEnum 
    {}
    f := DefiningPolynomial(C); 
    R := Parent(f); 
    X := R.1; Y := R.2; Z := IsProjective(C) select R.3 else R!1;
    sgn := [1,-1,1,-1,-1];
    mon := [ X*Y*Z, X^2*Z, Y*Z^2, X*Z^2, Z^3 ]; 
    return [ sgn[i]*MonomialCoefficient(f,mon[i]) : i in [1..5] ];
end intrinsic;

intrinsic bInvariants(C::CrvGrp) -> SeqEnum 
    {}
    a1,a2,a3,a4,a6 := Explode(aInvariants(C));
    b8 := a1^2*a6 - a1*a3*a4 + a2*a3^2 + 4*a2*a6 - a4^2;
    return [ a1^2 + 4*a2, a1*a3 + 2*a4, a3^2 + 4*a6, b8 ];
end intrinsic;

intrinsic cInvariants(C::CrvGrp) -> SeqEnum 
    {}
    b2,b4,b6,b8 := Explode(bInvariants(C));
    return [ b2^2 - 24*b4, -b2^3 + 36*b2*b4 - 216*b6 ];
end intrinsic;

intrinsic FunctionField(C::CrvGrp) -> FldFun
    {}
    return C`function_field;
end intrinsic;

intrinsic DivisionPsi(C::CrvGrp,n::RngIntElt) -> FldFunElt
    {Returns the nth division polynomial, a function field element  
    defining the kernel of the multiplication by n map on E.} 
    
    K<y> := FunctionField(C);
    F<x> := BaseRing(K);
    a1,a2,a3,a4,a6 := Explode(aInvariants(C)); 
    b2,b4,b6,b8 := Explode(bInvariants(C)); 
    psi2 := 2*y + a1*x + a3; 
    if (n eq 0) then 
	return K!0; 
    elif (n eq 1) then 
	return K!1; 
    elif (n eq 2) then 
	return psi2; 
    elif (n eq 3) then 
	return (3*x^4 + b2*x^3 + 3*b4*x^2 + 3*b6*x + b8); 
    elif (n eq 4) then 
	return psi2*(2*x^6 + b2*x^5 + 5*b4*x^4 + 10*b6*x^3 + 10*b8*x^2  
	    + (b2*b8 - b4*b6)*x + b4*b8 - b6^2); 
    elif ((n mod 2) eq 0) then 
	m := n div 2; 
	return DivisionPsi(C,m)*( 
	    DivisionPsi(C,m+2)*DivisionPsi(C,m-1)^2 -  
	    DivisionPsi(C,m-2)*DivisionPsi(C,m+1)^2)/psi2; 
    else  
	m := n div 2; 
	return DivisionPsi(C,m+2)*DivisionPsi(C,m)^3 -  
	    DivisionPsi(C,m-1)*DivisionPsi(C,m+1)^3; 
    end if; 
end intrinsic; 

intrinsic DivisionPolynomial(C::CrvGrp,n::RngIntElt) -> RngUPolElt 
    {}
    E := C`GenericCurve;
    r := Rank(BaseRing(E));
    psi := DivisionPolynomial(E,n);
    coeffs := [ aInvariants(C)[i] : i in C`GenericIndices ];
    return PolynomialRing(BaseRing(C))!
	[ Evaluate(Numerator(x),coeffs) : x in Coefficients(psi) ];
end intrinsic;

intrinsic DivisionPolynomials(C::CrvGrp,n::RngIntElt) -> RngUPolElt 
    {}
    P := PolynomialRing(BaseRing(C));
    F<y> := FunctionField(C);
    coeffs := [ aInvariants(C)[i] : i in C`GenericIndices ];
    E := C`GenericCurve;
    psi, phi, omg := DivisionPolynomials(E,n);
    psii := [ P![ Evaluate(Numerator(c),coeffs) :
	c in Coefficients(Numerator(f)) ] : f in Coefficients(psi) ];
    phii := [ P![ Evaluate(Numerator(c),coeffs) :
	c in Coefficients(Numerator(f)) ] : f in Coefficients(phi) ];
    omgi := [ P![ Evaluate(Numerator(c),coeffs) :
	c in Coefficients(Numerator(f)) ] : f in Coefficients(omg) ];
    if #psii eq 1 then 
	psi := F!psii[1];
    else 
	psi := F!psii[1] + F!psii[2]*y;
    end if;   
    if #phii eq 1 then 
	phi := F!phii[1];
    else 
	phi := F!phii[1] + F!phii[2]*y;
    end if;   
    if #omgi eq 1 then 
	omg := F!omgi[1];
    else 
	omg := F!omgi[1] + F!omgi[2]*y;
    end if;   
    return psi, phi, omg;
    // Bug: "No addition algorithm."
    return &+[ F | (F!psii[i])*y^(i-1) : i in [1..#psii] ],
	&+[ F | (F!phii[i])*y^(i-1) : i in [1..#phii] ],
	&+[ F | (F!omgi[i])*y^(i-1) : i in [1..#omgi] ];
end intrinsic;

intrinsic Coordinate(P::PtGrp,i::RngIntElt) -> RngElt
    {The ith coordinate of P.}
    S := Coordinates(P);
    error if i notin [1..#S], "Invalid coordinate index.";
    return S[i];
end intrinsic;

intrinsic Coordinates(P::PtGrp) -> RngElt
    {The coordinates of P.}
    return Eltseq(P`Point);
end intrinsic;

intrinsic Eltseq(P::PtGrp) -> SeqEnum
    {}
    return Coordinates(P);
end intrinsic;

intrinsic ElementToSequence(P::PtGrp) -> SeqEnum
    {}
    return Coordinates(P);
end intrinsic;

intrinsic Identity(C::CrvGrp) -> PtGrp
    {The identity element of C.}
    return C!0;
end intrinsic;

intrinsic Identity(S::SetPtGrp) -> PtGrp
    {The identity element of C.}
    C := S`Scheme;
    A := AmbientSpace(C);
    Xpt := New(PtGrp);
    Xpt`Parent := S;
    if Dimension(A) eq 1 then
	if IsMultiplicative(C) then
	    if IsAffine(C) then
		Xpt`Point := A![1];
	    else
		Xpt`Point := A![1,1];
	    end if;
	else
	    if IsAffine(C) then
		Xpt`Point := A![0];
	    else
		Xpt`Point := A![0,1];
	    end if;
	end if;
    else
	Xpt`Point := [S`Ring|0,1,0];
    end if;
    return Xpt;
end intrinsic;

intrinsic '-'(P::PtGrp) -> PtGrp
    {The inverse of P.}
    PS := P`Parent;
    C := PS`Scheme;
    if P eq Identity(C) then
	return P;
    elif AmbientDimension(C) eq 1 then
	if IsMultiplicative(C) then
	    if IsAffine(C) then
		return PS!C![Coordinate(P,1)^-1];
	    else
		return PS!C![Coordinate(P,2),Coordinate(P,1)];
	    end if;
	else
	    if IsAffine(C) then
		return PS!C![-Coordinate(P,1)];
	    else
		return PS!C![-Coordinate(P,1),Coordinate(P,2)];
	    end if;
	end if;
    end if;
    S := Coordinates(P);
    a := aInvariants(C);
    if IsAffine(Parent(P)`Scheme) then
	S[2] := -S[2] - a[1]*S[1] - a[3];
	return PS!C!S;
    else
	S[2] := -S[2] - a[1]*S[1] - a[3]*S[3];
	return PS!C!S;
    end if;
end intrinsic;

intrinsic '-'(P::PtGrp,Q::PtGrp) -> PtGrp
    {P - Q.}
    require P`Parent eq Q`Parent :
	"Arguments must be in the same point set.";
    return P + (-Q);
end intrinsic;

intrinsic '+'(P::PtGrp,Q::PtGrp) -> PtGrp
    {}
    X := Parent(P);
    require Parent(Q) eq X : "Arguments must be in the same point set.";
    C := X`Scheme;
    R := BaseRing(C);
    O := Identity(C);
    if P eq O then
	return Q;
    elif Q eq O then
	return P;
    elif P eq -Q then
	return O;
    elif AmbientDimension(C) eq 1 then
	if IsMultiplicative(C) then
	    if IsAffine(C) then
		return X![Coordinate(P,1)*Coordinate(Q,1)];
	    else
		S := [ Coordinate(P,1)*Coordinate(Q,1),
		    Coordinate(P,2)*Coordinate(Q,2) ];
		if Type(R) in {RngInt,RngIntRes} then
		    S := [ x div m : x in S ] where m := GCD(S);
		end if;
		return X!S;
	    end if;
	else
	    if IsAffine(C) then
		return X![Coordinate(P,1)+Coordinate(Q,1)];
	    else
		S := [ Coordinate(P,1)*Coordinate(Q,2) +
		    Coordinate(P,2)*Coordinate(Q,1),
		    Coordinate(P,2)*Coordinate(Q,2) ];
		if Type(R) in {RngInt,RngIntRes} then
		    S := [ x div m : x in S ] where m := GCD(S);
		end if;
		return X!S;
	    end if;
	end if;
    end if;
    a1,a2,a3,a4,a6 := Explode(aInvariants(C));
    if IsAffine(C) then
	x1, y1 := Explode(Coordinates(P));
	x2, y2 := Explode(Coordinates(Q));
	if P eq Q then
	    psi2 := 2*y1 + a1*x1 + a3;
	    lambda := (x1*(3*x1 + 2*a2) + a4 - a1*y1)/psi2;
	    nu := (x1*(-x1^2 + a4) + 2*a6 - a3*y1)/psi2;
	else
	    lambda := (y2 - y1)/(x2 - x1);
	    nu := (y1*x2 - y2*x1)/(x2 - x1);
	end if;
	x3 := (lambda + a1)*lambda - a2 - x1 - x2;
	y3 := -(lambda + a1)*x3 - nu - a3;
	return X![x3,y3];
    else
	x1, y1, z1 := Explode(Coordinates(P));
	x2, y2, z2 := Explode(Coordinates(Q));
	if P eq Q then
	    mu := (2*y1 + a1*x1 + a3*z1)*z1^2;
	    lambda := (x1*(3*x1 + 2*a2*z1) + (a4*z1 - a1*y1)*z1)*z1;
	    nu := x1*(-x1^2 + a4*z1^2) + (2*a6*z1 - a3*y1)*z1^2;
	else
	    lambda := y2*z1 - y1*z2;
	    nu := y1*x2 - y2*x1;
	    mu := x2*z1 - x1*z2;
	end if;
	x3 := (lambda + a1*mu)*lambda*z1*z2 - (x1*z2 + x2*z1 + a2*z1*z2)*mu^2;
	y3 := -(lambda + a1*mu)*x3 - (nu + a3*mu)*mu^2*z1*z2;
	P := [mu*x3,y3,mu^3*z1*z2];
	if Type(Universe(P)) in {RngInt,RngIntRes} then
	    P := [ xi div m : xi in P ] where m := GCD(P);
	end if;
	return X!P;
    end if;
end intrinsic;

intrinsic '+:='(~P::PtGrp,Q::PtGrp)
    {}
    X := Parent(P);
    require Parent(Q) eq X : "Arguments must be in the same point set.";
    P`Point := (P+Q)`Point;
end intrinsic;

intrinsic '*'(n::RngIntElt,P::PtGrp) -> PtGrp
    {The nth multiple of P.}
    if n eq -1 then
	return -P;
    elif n eq 0 then
	return Identity(P`Parent);
    elif n eq 1 then
	return P;
    elif n lt 0 then
	n *:= -1; P := -P;
    end if;
    if n eq 2 then return P + P; end if;
    B := IntegerToSequence(n,2);
    Q := Identity(P`Parent);
    for i in [1..#B-1] do
	if B[i] eq 1 then
	    Q +:= P;
	end if;
	P := P + P;
    end for;
    Q +:= P;
    return Q;
end intrinsic;

intrinsic '*'(P::PtGrp,n::RngIntElt) -> PtGrp
    {The nth multiple of P.}
    return n*P;
end intrinsic;

intrinsic '*:='(~P::PtGrp,n::RngIntElt)
    {The nth multiple of P.}
    P`Point := (n*P)`Point;
end intrinsic;

////////////////////////////////////////////////////////////////////////

intrinsic BaseExtend(C::CrvGrp,R::Rng) -> CrvGrp
    {}
    require IsCoercible(R,BaseRing(C)!1) : "Illegal coercion.";
    T := [ R!x : x in aInvariants(C) ];
    return SingularCubicCurve(T);
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                          Morphisms                                 //
//                                                                    //
////////////////////////////////////////////////////////////////////////

intrinsic EvaluatePolynomial(C::CrvGrp,S::SeqEnum) -> RngElt
    {The defining polynomial evaluated at S.}
    f := DefiningPolynomial(C);
    n := Rank(Parent(f));
    require n eq #S : "Argument 2 must have length", n;
    return Evaluate(f,S);
end intrinsic;

intrinsic IsIsomorphic(C::CrvGrp,D::CrvGrp) -> BoolElt, MapCrvGrp
    {Return true and the isomorphism if D is to C.}
    if C eq D then
	return true, Identity(End(C));
    end if;
    if IsAdditive(C) and IsAdditive(D) then
	return true;
    elif IsMultiplicative(C) and IsMultiplicative(D)
	and not (IsSplit(C) xor IsSplit(D)) then
	return true;
    end if;
    return false;
end intrinsic;
