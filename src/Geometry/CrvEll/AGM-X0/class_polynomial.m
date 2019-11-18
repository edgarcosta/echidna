declare verbose AGMClassPolynomial, 2;

////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////

function AGMInitialValues(j,p,n)
    prec := ((n+1) div 2)+1+(4 div p);
    case p:
    when 2: x := 1/j;
    when 3: x := 1/j;
    when 5: x := 1/j;
    when 7: x := 1/(j+1);
    when 13: x := 1/(j-5);
    end case;
    return x, prec; 
end function;

////////////////////////////////////////////////////////////////////////

intrinsic AGMClassPolynomial(j::FldFinElt,N::RngIntElt : 
    Precision := 0) -> RngUPolElt
    {Given a j-invariant of an ordinary elliptic curve and a level N,
    returns the p-adic factor of the class polynomial for j.}
    FF := Parent(j);
    p := Characteristic(FF);
    require N in {2,4,8,16,3,9,5,25,7,13} and N mod p eq 0 :
        "Argument 2 must be in {2,4,8,16,3,9,5,25,7,13} " *
        "and be divisible by the characteristic.";
    n := Degree(FF);
    x, prec := AGMInitialValues(j,p,n);  
    prec := Max([Precision,prec,16]); 
    x := AGMLift(N,x,prec);
    case N:
    when 2:
        x1 := 2^12*x; 
        x2 := 1 div x;
    when 4:
        x1 := 2^8*x; 
        x2 := 1 div x;
    when 8:
        x1 := 4*x; 
        x2 := (1-4*x) div (1+4*x);
    when 16:
        x1 := 2*x; 
        x2 := (1-2*x) div (1+2*x);
    when 3: 
        x1 := 729*x;
        x2 := 1 div x;
    when 9: 
        x1 := 27*x;
        x2 := 1 div x;
    else
        require false : "Level not yet treated.";
    end case;
    ZZ := Integers(); 
    return MinimalPolynomial(x1) * MinimalPolynomial(x2);
end intrinsic;

////////////////////////////////////////////////////////////////////////

/*
r := 7;
for jorbit in { { j^2^i : i in [0..r-1] } : j in GF(2,r) | j ne 0 } do
    P := HeegnerPoint(Representative(jorbit));
    print "D = ", Discriminant(MaximalOrder(Ring(Parent(P))));
    print P;
    print "Height:", Hauteur(P);
end for;
*/

intrinsic HeegnerPoint(j::FldFinElt) -> PtEll
    {}
    FF := Parent(j);
    p := Characteristic(FF);
    require p eq 2 and j ne 0 :
	"Argument must be a nonzero j-invariant " *
	"in a finite field of characteristic 2.";
    r := Degree(MinimalPolynomial(j));
    if r ne Degree(FF) then
	FF := FiniteField(p,r);
	j := FF!j;
    end if;
    t := Trace(EllipticCurveWithjInvariant(j));
    D := t^2-4*#Parent(j);
    K := NumberField(x^2-D)
	where x := PolynomialRing(Rationals()).1;
    AssignNames(~K,[ "d" * Sprint(Abs(D)) ]);
    d := K.1;
    PXYZ<X,Y,Z> := ProjectiveSpace(K,2);
    PUVW<U,V,W> := ProjectiveSpace(K,2);
    E := Curve(PXYZ,Y^2*Z-(4*X^3 + X*Z^2));
    C := Curve(PUVW,V^2*W^2-(U^4 - 4*U^3*W - 6*U^2*W^2 - 12*U*W^3 - 7*W^4));
    m := map< E->C | 
	[ 
	(Y*Z + X*Z + 2*X^2)/(X*(Z-2*X)), 
        (Z-2*X)/X - 8*(Y+2*X)*Z/(Z-2*X)^2,
	1
	],
	[
	(-U^4 + 4*U^3*W + 8*U^2*W^2 + 8*U*W^3 + V^2*W^2 - 2*V*W^3 - 3*W^4)/4,
    U^2*W^2 - 2*U*W^3 - V*W^3 + 3*W^4,
	U^2*W^2 + 6*U*W^3 - V*W^3 + 3*W^4
	] >;
    F := EllipticCurve([D^2*4,0]);
    n := map< E -> F | [d^2*X*Z,d^3*Y*Z,X^2] >;
    hD := AGMPlus32ClassPolynomial(j);
    vprint AGMClassPolynomial : hD;
    ZD := Scheme(C,Homogenization(Evaluate(hD,U),W));
    Infty := Scheme(PUVW,W);
    IrrCmp := [ zi : zi in PrimeComponents(ZD) | not zi subset Infty ];
    if #IrrCmp ne 2 then
	print hD;
	print IrrCmp;
	assert false;
    end if;
    z1, z2 := Explode(IrrCmp);
    p0 := Places(C![0,1,0])[1]; 
    p1 := Place(C,z1); 
    p2 := Place(C,z2); 
    J := PicardGroup(C,p0);
    pD := J!p1-J!p2;
    if pD eq J!0 then return F![0,1,0]; end if;
    ID := Ideal(Support(Divisor(pD))[1]);
    B := GroebnerBasis(ID);
    x1 := -MonomialCoefficient(B[1],W);
    y1 := -MonomialCoefficient(B[2],W);
    PD := C![x1,y1];
    return F(Rationals())!(PD@@m)@n;
end intrinsic;

intrinsic AGMPlus32ClassPolynomial(
    j::FldFinElt : Precision := 0) -> RngUPolElt
    {Given a j-invariant of an ordinary elliptic curve returns
    the p-adic factor of the class polynomial for j.}
    FF := Parent(j);
    p := Characteristic(FF);
    require p eq 2 and j ne 0 :
	"Argument must be a nonzero j-invariant " *
	"in a finite field of characteristic 2.";
    r := Degree(MinimalPolynomial(j));
    if r ne Degree(FF) then
	FF := FiniteField(p,r);
	j := FF!j;
    end if;
    jinvs := { { j^2^i : i in [0..r-1] } };
    t := TraceOfFrobenius(EllipticCurveWithjInvariant(j));
    D := t^2-4*p^r;
    Q := QuadraticForms(D);
    c := Conductor(Q);
    h := ClassNumber(Q);
    X := PolynomialRing(FF).1;
    m := h div r;
    q := 3;
    vprint AGMClassPolynomial : "Discriminant:", D; 
    vprint AGMClassPolynomial : "Class number:", h; 
    vprintf AGMClassPolynomial : "#Orbits = %o/%o\n", #jinvs, m;
    while #jinvs lt m do
	vprint AGMClassPolynomial : "Extending with prime", q;
	if KroneckerSymbol(D,q) ne -1 and c mod q ne 0 then
	    Phi := ClassicalModularPolynomial(q);
	    rts := Roots(Evaluate(Phi,[X,j]));
	    jinvs join:= { { z[1]^p^i : i in [0..r-1] } : z in rts };
	end if;
	q := NextPrime(q);
	vprintf AGMClassPolynomial : "#Orbits = %o/%o\n", #jinvs, m;
    end while;
    HD := 1;
    for jorbit in jinvs do
	ji := Representative(jorbit);
	xi, prec := AGMInitialValues(ji,p,r);  
	prec := Max([Precision,prec,16]); 
	x0 := AGMLift(16,xi,prec);
	x1 := GaloisImage(x0,1);
	y1 := x0*(4*x1^2 + 1);
	// Valuation(y1^2-4*x1^3-x1);
	u1 := (y1+x1*(1+2*x1)) div (x1*(1-2*x1));
	// v1 := ((1-2*x1) div x1) - (8*(y1 + 2*x1) div (1 - 2*x1)^2);
	// Valuation(u1^4 - 4*u1^3 - 6*u1^2 - 12*u1 - 7 - v1^2);
	HD *:= MinimalPolynomial(u1);
	vprintf AGMClassPolynomial : "Degree %o/%o\n", Degree(HD), h; 
    end for;
    function BalancedLift(c,m)
	c mod:= m;
	c1 := c-Sign(c)*m;
	return Abs(c) lt Abs(c1) select c else c1;
    end function; 
    return PolynomialRing(Integers())!
	[ BalancedLift(Integers()!c,2^(prec-2)) : c in Eltseq(HD) ];
end intrinsic;

intrinsic AGMClassPolynomial(
    S::[FldFinElt],N::RngIntElt : Precision := 0) -> RngUPolElt
    {Given a sequence of j-invariants...}
    p := Characteristic(Universe(S));
    require N in {2,4,8,16,3,9,5,25,7,13} and N mod p eq 0 :
        "Argument 2 must be in {2,4,8,16,3,9,5,25,7,13} " *
        "and be divisible by the characteristic.";
    prec := Max([Precision,16]); 
    ZZ := Integers(); 
    f := Eltseq(&*[
	AGMClassPolynomial(j,N : Precision := prec) : j in S ]);
    M := LLL(VerticalJoin(
	Matrix(#f,[ ZZ!f[i] : i in [1..#f] ]),
	p^(prec-4)*IdentityMatrix(ZZ,#f)));
    return PolynomialRing(ZZ)!Eltseq(M[1]);
end intrinsic;

