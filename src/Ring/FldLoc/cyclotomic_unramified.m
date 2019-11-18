////////////////////////////////////////////////////////////////////////
//                                                                    //
//                     Cyclotomic Lifting Polynomials                 //
//                              David Kohel                           //
//                                                                    //
////////////////////////////////////////////////////////////////////////


declare verbose CyclotomicLift, 2;

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

intrinsic CyclotomicPolynomial(R::RngPadRes,m::RngIntElt : Degree := 0)
    -> RngUPolElt {A cyclotomic polynomial of order m over R.}
    p := Prime(R);
    if Degree ne 0 then
	d := Degree;
    else
	d := Order(p,m);
    end if;
    require Modexp(p,d,m) eq 1 : "Degree must be the multiplicative order" *
      " of the residue characteristic of argument 1 modulo argument 2.";
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
