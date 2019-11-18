////////////////////////////////////////////////////////////////////////
//                                                                    //
//                         NEWTON HENSEL LIFTING                      //
//                             David Kohel                            //
//                                                                    //
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
//                        Accessory Functions                         //
////////////////////////////////////////////////////////////////////////

function MyGCD(f,g)
    while true do
	if g eq 0 then
	    return f; 
	elif f eq 0 then
	    return g;
	end if;
	if Degree(f) lt Degree(g) then
	    g mod:= f;
	else
	    f mod:= g;
	end if;
    end while;
end function;

function QuotientMod(f,g,m)
    m1 := MyGCD(g,m);
    while not IsUnit(m1) do
	error if f mod m1 ne 0, "Quotient undefined in Hensel lift.";
	    f div:= m1;
	    g div:= m1;
	    m1 := MyGCD(g,m);
	end while;
	m1, a, b := XGCD(g,m);
	u := 1/Eltseq(m1)[1];
	print Min([ Valuation(c) : c in Eltseq(u*(a*g mod m)-1) ]);
	return f*u*a;
    end function;

function ValMax(f,MaxInt)
    if #Eltseq(f) eq 0 then return MaxInt; end if;
    return Valuation(f);
end function;

////////////////////////////////////////////////////////////////////////
//                            Nth Roots                               //
////////////////////////////////////////////////////////////////////////

intrinsic Root(x::RngSerElt,n::RngIntElt) -> RngSerPuisElt
    {An n-th root of x.}

    if n eq 1 then return x; end if;
    PS := Parent(x); t := PS.1;
    m := Valuation(x);
    if x eq t^m then return t^(m/n); end if;
    PP := PolynomialRing(PS); X := PP.1;
    c, v, m := Coefficients(x); 
    if RelativePrecision(x) lt 0 then
	N := Max(m*(#c+v),20); 
    else
	N := Floor(RelativePrecision(x));
    end if;
    if Coefficient(x,v/m) eq One(BaseRing(PS)) then
	u0 := Coefficient(x,v/m);
    else
	u0 := Root(Coefficient(x,v/m),n);
    end if;
    return NewtonLift(X^n-x,u0*t^(v/(n*m)),N);
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                        Newton Polygons                             //
////////////////////////////////////////////////////////////////////////

intrinsic NewtonPolygon(f::RngUPolElt[RngSer]) -> SeqEnum
    {The Newton polygon of a polynomial over a series ring.}
    n := Degree(f);
    PP := Parent(f); X := PP.1;
    PS := BaseRing(PP); t := PS.1;
    MaxInt := 2^32;
    vals := [ ValMax(Coefficient(f,j),MaxInt) : j in [0..n] ];   
    j0 := 0; j1 := 0;
    newton := [ Parent([ RationalField() | ]) | ];
    while j0 lt n do
	slope := [ (vals[j+1] - vals[j0+1])/(j-j0) : j in [j0+1..n] ];
	m0 := Min(slope);
	j1 := Max([ j : j in [j0+1..n] | slope[j-j0] eq m0 ]);
	Append(~newton,[m0,j0,j1]);
	j0 := j1;
    end while;
    return newton;
end intrinsic;

intrinsic NewtonNormalization(
    f::RngUPolElt[RngSer],S::SeqEnum[RngElt]) -> RngUPolElt
    {}
    n := Degree(f);
    PP := Parent(f); X := PP.1;
    PS := BaseRing(PP); t := PS.1;
    m := S[1]; 
    j0 := Integers()!S[2];
    d := Denominator(m);
    a0 := Valuation(Coefficient(f,j0));
    G := t^(m*j0-a0)*Evaluate(f,t^(-m)*X);
    coeff := Coefficients(G);
    coeffseq := [ ];
    degseq := [ ];
    for j in [1..n+1] do
	coeffseq[j], nj, dj := Coefficients(coeff[j]);
	degseq[j] := nj/dj;
    end for;
    return &+[ PP | 
	t^(d*degseq[j]) * &+[ PS | coeffseq[j][k] * t^(k-1) 
	: k in [1..#coeffseq[j]] ] * X^(j-1) : j in [1..n+1] ];  
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                      Polynomial Root Finding                       //
////////////////////////////////////////////////////////////////////////

function RootsHelper(f)
    n := Degree(f);
    PP := Parent(f); X := PP.1;
    PS := BaseRing(PP); t := PS.1;
    R := BaseRing(PS);
    PR := PolynomialRing(R); x := PR.1;
    f_0 := &+[ Coefficient(Coefficient(f,j),0)*x^j : j in [0..n] ];
    return [ rts : rts in Roots(f_0) | rts[1] ne Zero(R) ];
end function;

intrinsic RootNormalization(
    f::RngUPolElt[RngSer],a0::RngSerElt) -> RngUPolElt
    {}
    n := Degree(f);
    PP := Parent(f); X := PP.1;
    PS := BaseRing(PP); t := PS.1;
    return &+[ a0^(-j)*Coefficient(f,j)*X^j : j in [0..n] ];
end intrinsic;

intrinsic RootsByNewtonLifting(
    f::RngUPolElt[RngSer],prec::RngIntElt) -> SeqEnum
    {The roots of the polynomial F over a series ring to precision prec.}

    PP := Parent(f); X := PP.1;
    PS := BaseRing(PP); t := PS.1;
    PSRts := [ PS | ];
    if Evaluate(f,0) eq 0 then
	while Evaluate(f,0) eq 0 do
	    f := f div X;
	end while;
	PSRts := [ Zero(PS) ];
    end if;
    NP := NewtonPolygon(f);
    for S in NP do
	s := S[1]; m := Denominator(s);
	G := NewtonNormalization(f,S);
	NRts := RootsHelper(G);
	for a0 in NRts do
	    x0 := NewtonLift(G,PS!a0[1],prec);
	    if Type(Parent(x0)) eq Type(PS) then
		PSRts := PSRts cat 
		    [ t^(-s)*Evaluate(x0,t^(1/m)) 
		    + O(t^((prec+1)/m)) ];
	    elif Type(x0) eq SeqEnum then
		PSRts := PSRts cat 
		    [ t^(-s)*Evaluate(y0,t^(1/m)) 
		    + O(t^((prec+1)/m)) : y0 in x0 ];
	    else 
		print x0; 
	    end if;
	end for;
    end for;
    return PSRts;
end intrinsic;

intrinsic Roots(
    f::RngUPolElt[RngSer],S::SeqEnum[RngSer],prec::RngIntElt) -> SeqEnum
    {The Hensel lift of a sequence of roots of a polynomial over
    a series ring.}

	PP := Parent(f); X := PP.1;
    PS := BaseRing(PP); t := PS.1;
    PSRts := [ PS | ];
    if Evaluate(f,0) eq 0 then
	while Evaluate(f,0) eq 0 do
	    f := f div X;
	end while;
	PSRts := [ Zero(PS) ];
    end if;
    m := S[1]; d := Denominator(m);
    G := NewtonNormalization(f,S);
    NRts := RootsHelper(G);
    for a0 in NRts do
	T := NewtonLift(G,a0[1],prec);
	PSRts := PSRts cat 
	    [ t^(-m)*Evaluate(x0,t^(1/d) + O(t^((prec+1)/d))) : x0 in T ];
    end for;
    return PSRts;
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                     Hensel Lifting of Series                       //
////////////////////////////////////////////////////////////////////////

/*
Should have some type checking and require statements. 

intrinsic InitialFactors(f::RngUPolElt) -> SeqEnum
{}
PS := BaseRing(Parent(f));
P := PolynomialRing(BaseRing(PS));
x := P.1;
n := Degree(f);
f_0 := &+[ Coefficient(Coefficient(f,j),0)*x^j : j in [0..n] ];
return [ fact : fact in Factorization(f_0) ];
end intrinsic;

*/

function NextIncrement(v0,v1,N)
    prec := N;
    minp := v0+2*v1+1;
    while prec gt 2*v0 do
	prec := Max((prec+1) div 2,minp);
    end while;
    return prec;
end function;

intrinsic NewtonLift(f::RngUPolElt[RngSer],x::RngSerElt,N::RngIntElt) -> RngElt
    {The Hensel lift of the root x to precision N.}
    x := Truncate(x);
    Df := Derivative(f);
    c0 := Evaluate(f,x);
    c1 := Evaluate(Df,x);
    v0 := ValMax(c0,N+1);
    v1 := ValMax(c1,N+1);
    require v0 gt 0 and v0 gt 2*v1 : "Argument 2 has insufficient precision.";
    t := BaseRing(Parent(f)).1;
    while true do
	// Current precision is v0, to be extended to 2v0.
	prec := NextIncrement(v0,v1,N);
	oerr := O(t^(prec+1));
	oerrnext := O(t^(2*prec+1));
	vprint Hensel : "v1 =", v1;
	vprint Hensel : "v0 =", v0;
	vprint Hensel : "Target prec =", prec;
	if prec ge N then
	    return Truncate(x - c0*(c1^-1)) + O(t^(N+1));
	end if;
	c0 := Truncate(c0) + oerrnext;
	c1 := Truncate(c1) + oerrnext;
	vtime Hensel, 2 : x := Truncate(x) - c0/c1 + oerrnext;
	vtime Hensel, 2 : c1 := Evaluate(Df,x + oerr);
	vtime Hensel, 2 : c0 := Evaluate(f,x + oerrnext);
	v0 := ValMax(c0,prec+1);
	v1 := ValMax(c1,prec+1);
    end while;
end intrinsic;

intrinsic NewtonLift(f::RngUPolElt[RngSer],g::RngUPolElt[RngSer],N::RngIntElt) -> RngElt
    {The Hensel lift of the factor g to precision N.}

    n := Degree(f);
    PP := Parent(f); X := PP.1;
    require Parent(g) eq PP :
	"Arguments 1 and 2 must have the same parent.";
    PS := BaseRing(PP); t := PS.1;
    R := BaseRing(PP);
    Df := Derivative(f);
    c0 := f mod g;
    c1 := Df mod g;
    v0 := Min( [N] cat [ ValMax(c,N) : c in Eltseq(c0) ] );
    v1 := Min( [N] cat [ ValMax(c,N) : c in Eltseq(c1) ] );
    require v0 gt 2*v1 : "Argument 2 has insufficient precision.";
    while v0 lt N do 
	vprint Hensel : "v0 =", v0;      
	vprint Hensel : "v1 =", v1;      
	dg := QuotientMod(c0,c1,g);
	vprint Hensel : "QuotientMod:", Min([N] cat
	    [ ValMax(c,N) : c in Eltseq((c1*dg-c0) mod g) ]);
	g +:= -dg;
	c0 := f mod g;
	c1 := Df mod g;
	v0 := Min([N] cat [ ValMax(c,N) : c in Eltseq(c0) ] );
	v1 := Min([N] cat [ ValMax(c,N) : c in Eltseq(c1) ] );
    end while;
    return g + O(t^(N+1));
end intrinsic;

