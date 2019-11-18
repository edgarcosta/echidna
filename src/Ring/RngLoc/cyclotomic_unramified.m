////////////////////////////////////////////////////////////////////////
//                                                                    //
//                     Cyclotomic Lifting Polynomials                 //
//                              David Kohel                           //
//                                                                    //
////////////////////////////////////////////////////////////////////////

declare attributes RngPadResExt :
    IsCyclotomic,
    CyclotomicOrder;

declare verbose CyclotomicLift, 2;

////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////

function PrecisionSequence(n)
    precs := [ Integers() | ];
    while n gt 1 do
	Append(~precs,n);
	n := (n+1) div 2;
    end while;
    return Reverse(precs);
end function;

function MyInvmod(x,f)
    S := ext< BaseRing(Parent(f)) | f >;
    xinv := (S!Eltseq(x))^-1;
    return Parent(f)!Eltseq(xinv);
end function;

function MyModexp(x,m,f)
    y := Parent(x)!1;
    z := x;
    for i in IntegerToSequence(m,2) do
	if i eq 1 then
	    y *:= z;
	    y mod:= f;
	end if;
	z ^:= 2;
	z mod:= f;
    end for;
    return y;
end function;

////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////

intrinsic CyclotomicPolynomial(R::RngPadRes,m::RngIntElt : 
    Degree := 0) -> RngUPolElt
    {A cyclotomic polynomial of order m over R.}
    p := Prime(R);
    d := Degree ne 0 select Degree else Order(p,m);
    require m eq 1 or Modexp(p,d,m) eq 1 :
	"Degree must be the multiplicative order of the residue " *
	"characteristic of argument 1 modulo argument 2.";
    // Choose a polynomial to lift:
    P := PolynomialRing(R); x := P.1;
    e := 1;
    t := GCD(m,d);
    while t ne 1 do
	e *:= t;
	m div:= t;
	d div:= t;
	t := GCD(m,d);
    end while;
    f := P!Eltseq(DefiningPolynomial(FiniteField(p,d)));
    q := p^d;
    precs := PrecisionSequence(Precision(R));
    vprint CyclotomicLift : "Precision sequence:", precs;
    for i in [1..#precs] do
	S := ChangePrecision(R,Min(precs[i],Precision(R))); 
	P := PolynomialRing(S);
	f := P!f;
	x := P.1;
	tyme := Cputime();
	z := x-MyModexp(x,q,f);
	vprint CyclotomicLift : "Time:", Cputime(tyme);
	if z eq 0 then break; end if;
	vprint CyclotomicLift : "v =", v
	    where v := Min([ Valuation(c) : c in Eltseq(z) ]);
	f +:= z*Derivative(f) mod f;
    end for;
    if e eq 1 then
	return f;
    end if;
    return Evaluate(f,x^e);
end intrinsic;

////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////

intrinsic UnramifiedCyclotomicExtension(
    R::RngPadRes,f::RngIntElt : Order := 0) -> RngPadResExt
    {}
    p := Prime(R);
    m := Order eq 0 select p^f-1 else Order;
    g := CyclotomicPolynomial(R,m : Degree := f);
    S := ext< R | g >; 
    S`IsCyclotomic := true; 
    S`CyclotomicOrder := m;
    return S;
end intrinsic;

intrinsic CyclotomicOrder(R::RngPadResExt) -> RngIntElt
    {}
    require assigned R`CyclotomicOrder : 
	"Argument must be created as a cyclotomic extension";
    return R`CyclotomicOrder;
end intrinsic;

////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////

intrinsic FrobeniusImage(x::FldFinElt) -> FldFinElt
    {}
    return x^Characteristic(Parent(x));
end intrinsic;

intrinsic FrobeniusImage(x::RngPadResElt) -> RngPadResElt
    {}
    return x;
end intrinsic;

intrinsic FrobeniusImage(x::RngPadResExtElt) -> RngPadResExtElt
    {The image of x under the Frobenius automorphism.}
    R := Parent(x);
    if assigned R`IsCyclotomic then
	assert R`IsCyclotomic;
	p := Prime(R); f := Degree(R); m := CyclotomicOrder(R); 
	return &+[ c[i+1]*z^((i*p) mod m) : i in [0..f-1] ]
	    where c := Eltseq(x) where z := R.1;
    end if;
    return GaloisImage(x,1);
end intrinsic;

////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////

intrinsic TeichmuellerLift(R::RngPadRes,x::FldFinElt) -> FldFinElt
    {}
    require Parent(x) eq ResidueClassField(R) :
	"Argument 2 must lie in the residue class ring of argument 1.";
    if x eq 0 then
	return R!0;
    elif x eq 1 then
	return R!1;
    end if;
    n := Order(x);
    xi := R!x;
    ximn_m1 := xi^-n-1;
    i := 1;
    while ximn_m1 ne 0 do
	xi +:= (R!n)^-1*ximn_m1*xi;
	ximn_m1 := xi^-n-1;
    end while;
    return xi;
end intrinsic;

intrinsic TeichmuellerLift(R::RngPadResExt,x::FldFinElt) -> FldFinElt
    {}
    require Parent(x) eq ResidueClassField(R) :
	"Argument 2 must lie in the residue class ring of argument 1.";
    if x eq 0 then
	return R!0;
    elif x eq 1 then
	return R!1;
    end if;
    n := Order(x);
    xi := R!x;
    ximn_m1 := xi^-n-1;
    i := 1;
    while ximn_m1 ne 0 do
	xi +:= (R!n)^-1*ximn_m1*xi;
	ximn_m1 := xi^-n-1;
    end while;
    return xi;
end intrinsic;

////////////////////////////////////////////////////////////////////////
