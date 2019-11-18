////////////////////////////////////////////////////////////////////////
//                                                                    //
//                           HENSEL LIFTING                           //
//                             David Kohel                            //
//                                                                    //
////////////////////////////////////////////////////////////////////////

declare verbose Hensel, 2;

/*
// Example.
P<x> := PolynomialRing(pAdicQuotientRing(2,64));
f := x^3 - 3814272*x^2 - 44544640241664*x + 135250282417024401408;
NewtonLift(f,x-450560,32);
*/

////////////////////////////////////////////////////////////////////////

function PrecisionSequence(n)
    precs := [ Integers() | ];
    while n gt 1 do
	Append(~precs,n);
	n := (n+1) div 2;
    end while;
    return Reverse(precs);
end function;

function QuotientMod(h,g,m)
    // Correct definition of QuotientMod?
    m1 := GCD(g,m);
    while m1 ne 1 do
       h div:= m1;
       g div:= m1;
       m1 := GCD(g,m);
    end while;
    return h*InverseMod(g,m);
end function;

function UnramifiedCover(K,n)
    // K must be a finite field.
    assert Type(K) eq FldFin;
    p := Characteristic(K);
    R := pAdicQuotientRing(p,n);
    f := PolynomialRing(R)!DefiningPolynomial(K);
    if AbsoluteDegree(f) eq 1 then return R; end if;
    return UnramifiedExtension(R,f);
end function;

////////////////////////////////////////////////////////////////////////
//                         NEWTON LIFTING                             //
////////////////////////////////////////////////////////////////////////

intrinsic NewtonLift(f::RngUPolElt,g::RngUPolElt,N::RngIntElt) -> RngUPolElt
    {The Hensel lift of the factor g to precision N.}
    P := Parent(f);
    require Parent(f) eq Parent(g) : "Parents of arguments differ";
    R := BaseRing(Parent(f));
    require Category(R) in {RngPadRes,RngPadResExt,RngSerLaur,RngSerPow} : 
       "Base ring of arguments must be a local ring or field";
    n1 := Min([ Valuation(a) : a in Eltseq(f mod g) ]);
    n2 := Min([ Valuation(a) : a in Eltseq(Derivative(f) mod g) ]);
    require n1 gt 2*n2 : "Argument 2 not liftable";
    // Make exact (this seems only to work for fields):
    df := Derivative(f);
    while n1 lt N do
	g -:= QuotientMod(f mod g,df mod g,g);    
	n1 := Min([ Valuation(a) : a in Eltseq(f mod g) ]);
	print n1;
    end while;
    return g;   
end intrinsic;

intrinsic NewtonLift(f::RngUPolElt,x::RngPadResElt,N::RngIntElt) -> RngPadResElt
    {The Hensel lift of the root x to precision N.}
    vprint Hensel : "Lifting to precision", N;
    R := BaseRing(Parent(f));
    precs := PrecisionSequence(Min(Precision(R),N));
    df := Derivative(f);
    for ni in precs do
	tyme := Cputime();
	Ri := ChangePrecision(R,ni);
	x := Ri!x;
	vprint Hensel, 1 : "Ring precision =", ni;
	vprint Hensel, 1 : "   Iteration =", Index(precs,ni);
	fx := Evaluate(PolynomialRing(Ri)!f,x);
	dfx := Evaluate(PolynomialRing(Ri)!df,x);
        v0 := Valuation(fx);
	v1 := Valuation(dfx);
	vprint Hensel, 2 : "   Valuation(f(x)) =", v0;
	vprint Hensel, 2 : "   Valuation(df(x)) =", v1;
	error if v0 le 2*v1, "Newton lifting criterion is not satified.";
	x -:= fx/dfx;
	vprint Hensel, 2 : "   Time:", Cputime(tyme);
    end for;
    return R!x;
end intrinsic; 

intrinsic NewtonLift(f::RngUPolElt,x::RngPadResExtElt,N::RngIntElt)
    -> RngPadResElt
    {The Hensel lift of the root x to precision N.}
    vprint Hensel : "Lifting to precision", N;
    S := BaseRing(Parent(f));
    bool, xi := IsCoercible(S,x);
    require bool :
	"Argument 2 must coerce into base ring of parent of argument 2.";
    precs := PrecisionSequence(Min(Precision(S),N));
    df := Derivative(f);
    for ni in precs do
	tyme := Cputime();
	Si := ChangePrecision(S,ni);
	Ri := BaseRing(Parent(DefiningPolynomial(Si)));
	vprint Hensel, 1 : "Ring precision =", ni;
	vprint Hensel, 1 : "   Iteration =", Index(precs,ni);
	xi := Si!Eltseq(xi);
	fx := Evaluate(PolynomialRing(Si)![ Si!Eltseq(c) : c in Eltseq(f) ],xi);
	dfx := Evaluate(PolynomialRing(Si)![ Si!Eltseq(c) : c in Eltseq(df) ],xi);
        v0 := Valuation(fx);
        v1 := Valuation(dfx);
	vprint Hensel, 2 : "   Valuation(f(x))  =", v0;
	vprint Hensel, 2 : "   Valuation(df(x)) =", v1;
	require v0 ge 2*v1+1 : "Newton lifting criterion must be satified.";
	xi +:= -fx/dfx;
	vprint Hensel, 2 : "   Time:", Cputime(tyme);
    end for;
    return S!Eltseq(xi);
end intrinsic; 

////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////

function CyclotomicLift(x,t,m)
    R := Parent(x);
    precs := PrecisionSequence(Min(Precision(R),m));
    for ni in precs do
	vprint Hensel, 2 : "   Newton precision:", ni;
	Ri := ChangePrecision(R,ni);
	x := Expand(Ri!x);
	u := x^(t-1);
	fx := x*u-1;
	dfx := t*u;
        v0 := Valuation(fx);
        v1 := Valuation(dfx);
	vprint Hensel, 2 : "      Valuation(f(x)) =", v0;
	vprint Hensel, 2 : "      Valuation(f'(x)) =", v1;
	error if v0 le 2*v1, "Newton lifting criterion is not satified.";
	x -:= fx/dfx;
    end for;
    return R!x;
end function;

////////////////////////////////////////////////////////////////////////
//              CYCLOTOMIC ROOTS AND GALOIS CONJUGATES                //
////////////////////////////////////////////////////////////////////////

intrinsic CyclotomicGenerator(L::RngPad : Precision := 16) -> RngPadElt
    {}
    prec := Min(Precision(L),Precision);
    P := PolynomialRing(L);
    X := P.1;
    FF, pi := ResidueClassField(L);
    q := #FF;
    x0 := FF.1@@pi;
    return CyclotomicLift(x0,q-1,prec);
end intrinsic;

intrinsic Conjugate(x::RngPadElt : Precision := 16) -> RngPadElt
    {}
    // Assumes that parent of x is unramified. 
    prec := Precision(x);
    if Type(prec) eq Infty then 
	prec := Precision eq 0 select 16 else Precision;
    elif Precision ne 0 and Precision lt prec then
	prec := Precision;
    end if;
    R := Parent(x);
    f := MinimalPolynomial(x);
    FF, pi := ResidueClassField(R); 
    p := Characteristic(FF);
    y := (pi(x)^p)@@pi;
    return NewtonLift(PolynomialRing(R)!f,y,prec);
end intrinsic;

intrinsic Conjugate(x::RngPadElt,i::RngIntElt : Precision := 16) -> RngPadElt
    {}
    // Assumes that parent of x is unramified. 
    prec := Precision(x);
    if Type(prec) eq Infty then 
	prec := Precision eq 0 select 16 else Precision;
    elif Precision ne 0 and Precision lt prec then
	prec := Precision;
    end if;
    R := Parent(x);
    f := MinimalPolynomial(x);
    FF, pi := ResidueClassField(R); 
    p := Characteristic(FF);
    y := (pi(x)^p^i)@@pi;
    return HenselLift(PolynomialRing(R)!f,y,prec);
end intrinsic;

intrinsic Conjugates(x::RngPadElt : Precision := 16) -> SeqEnum
    {The Galois conjugates of x.}
    prec := Precision(x);
    if Type(prec) eq Infty then 
	prec := Precision eq 0 select 16 else Precision;
    elif Precision ne 0 and Precision lt prec then
	prec := Precision;
    end if;
    R := Parent(x);
    f := MinimalPolynomial(x);
    return [ c[1] : c in Roots(PolynomialRing(R)!f) ];
end intrinsic;

intrinsic LocalConjugates(x::RngPadElt : Precision := 0) -> RngUPolElt
    {The conjugates of x under the Frobenius automorphism.}

    prec := Precision(x);
    if Type(prec) eq Infty then 
	prec := Precision eq 0 select 16 else Precision;
    elif Precision ne 0 and Precision lt prec then
	prec := Precision;
    end if;
    vprint Hensel, 2 : "Setting precision to ", prec;
    S := Parent(x);
    R := Universe(Eltseq(x));
    P := PolynomialRing(S);
    t := P.1;
    FF, pi := ResidueClassField(S);
    x0 := pi(x)@@pi;
    tyme := Cputime();
    z1 := CyclotomicLift(x0,#FF-1,prec);
    vprint Hensel : "Hensel lift time: ", Cputime(tyme);
    tyme := Cputime();
    deg := Degree(FF);
    p := Characteristic(FF);
    zconjs := [ z1 ];
    for i in [1..deg-1] do
	Append(~zconjs,zconjs[i]^p);
    end for; 
    vprint Hensel : "Cyclotomic conjugates time: ", Cputime(tyme);
    tyme := Cputime();
    M := Matrix(deg,deg,&cat[ Eltseq(zi) : zi in zconjs ]); 
    v := Vector(Eltseq(x));   
    u := Solution(M,v);
    vprint Hensel : "Linear algebra time: ", Cputime(tyme);
    tyme := Cputime();
    c := Eltseq(u);
    conjs := [ &+[ a[j]*zconjs[j] : j in [1..deg] ] 
        where a := (c[i..deg] cat c[1..i-1]) : i in [1..deg] ];
    vprint Hensel : "Argument conjugates time: ", Cputime(tyme);
    return conjs;
end intrinsic;
