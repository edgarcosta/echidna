////////////////////////////////////////////////////////////////////////
//                                                                    //
//                       SATOH LIFTING ALGORITHM                      //
//                             David Kohel                            //
//                                                                    //
////////////////////////////////////////////////////////////////////////

declare verbose Satoh, 3;

forward VeluFrobeniusRoot, VeluCoefficients, TransitionScalar;
forward FGHLiftCycle, HenselLiftRoot, HenselLiftSquare;
forward CanonicalLiftjInvariants, CanonicalLiftwInvariants; 

intrinsic SatohFGHTrace(E::CrvEll) -> RngIntElt
    {The trace of Frobenius as computed by Satoh's algorithm.}
    FF := BaseRing(E);
    require Type(FF) eq FldFin : 
	"Base ring of argument must be a finite field.";
    r := Degree(FF);
    p := Characteristic(FF);
    require p in [2,3] : 
	"Algorithm implemented only for characteristics 2 and 3."; 
    require Degree(sub< BaseRing(E) | jInvariant(E) >) gt 2 : 
	"Argument's j-invariant must not lie in the field of degree 2.";
    // Analyze what minimum precision is needed. 
    prec := ((r+1) div 2)+8;
    E1, jInvs := CanonicalLiftjInvariants(jInvariant(E),prec);
    tyme := Cputime();
    vprint Satoh: "Begin Velu...";
    x0 := VeluFrobeniusRoot(E1,p);
    E2 := [1,0,0,-36*d0,-d0] where
	d0 := Parent(x0)!Eltseq((jInvs[2]-12^3)^-1);
    F1 := VeluCoefficients(E1,x0,p);
    u1 := TransitionScalar(E2,F1); 
    vprint Satoh : "Velu time:", Cputime(tyme);
    vprint Satoh, 2 : "RelativePrecision(u1) =", RelativePrecision(u1);
    m := p^Min(RelativePrecision(u1),prec);
    t := Integers()!Norm(p/u1) mod m;
    if t gt (m-t) then t -:= m; end if;
    vprint Satoh, 2 : "Trace = ", t;
    // Maybe chose the wrong twist for Velu construction...
    if true then
	P := Random(E);
	if (p^r+1-t)*P ne E!0 then
	    t *:= -1;
	    vprint AGM, 2: "Changing sign!";
	    assert (p^r+1-t)*P eq E!0;
	end if;
    end if;
    return t;
end intrinsic;

function HenselLiftRoot(f,x0,n)
    R := Parent(x0);
    x0 := Expand(x0) + O(UniformizingElement(R)^n);
    df := Derivative(f);
    for j in [1..Ceiling(Log(n)/Log(2))] do
	fx := Evaluate(f,x0);
	vprint Satoh, 2 : "RelativePrecision(fx) =", RelativePrecision(fx);
	vprint Satoh, 2 : "Valuation(fx) =", Valuation(fx);
	if RelativePrecision(fx) eq 0 then break j; end if;      
	dx := Evaluate(df,x0);
	vprint Satoh, 2 : "Valuation(dx) =", Valuation(dx);
	x0 +:= -fx/dx;
    end for;
    return x0;
end function;

function HenselLiftSquare(x2,x1,n)   
    R := Parent(x1);
    x1 := Expand(x1) + O(UniformizingElement(R)^n);
    for j in [1..Ceiling(Log(n)/Log(2))] do
	fx := x1^2-x2;
	if RelativePrecision(fx) eq 0 then break j; end if;      
	x1 +:= -(fx/2)*x1^-1;
    end for;
    return x1;
end function;

function VeluFrobeniusRoot(E1,p)
    R := Universe(E1);
    m := Precision(R);
    P := PolynomialRing(R); x := P.1;
    a1,a2,a3,a4,a6 := Explode(E1);
    b2 := a1^2 + 4*a2; b4 := a1*a3 + 2*a4; b6 := a3^2 + 4*a6;
    b8 := a1^2*a6 - a1*a3*a4 + a2*a3^2 + 4*a2*a6 - a4^2;
    if p eq 2 then
	psi := 4*x^3 + b2*x^2 + 2*b4*x + b6;
	x0 := HenselLiftRoot(psi,-b2/4,m); 
    elif p eq 3 then
	psi := 3*x^4 + b2*x^3 + 3*b4*x^2 + 3*b6*x + b8;
	x0 := HenselLiftRoot(psi,-b2/3,m); 
    end if;
    vprint Satoh, 2 : "RelativePrecision(x0) =", RelativePrecision(x0);
    vprint Satoh, 2 : "Valuation(x0) =", Valuation(x0);
    return x0;
end function;

function VeluCoefficients(E,x0,p)
    // E1 is the coefficient sequence of an elliptic curve
    a1,a2,a3,a4,a6 := Explode(E);
    b2 := a1^2 + 4*a2;
    if p eq 2 then
	y0 := -(a1*x0 + a3)/2;
	t := 3*x0^2 + 2*a2*x0 + a4 - a1*y0;
	w := x0*t;
    elif p eq 3 then
	n := 1;
	s1 := x0; s2 := 0; s3 := 0;
	b4 := a1*a3 + 2*a4;
	b6 := a3^2 + 4*a6;
	t := 6*(s1^2 - 2*s2) + b2*s1 + n*b4;
	w := 10*(s1^3 - 3*s1*s2 + 3*s3) + 2*b2*(s1^2 - 2*s2) 
	    + 3*b4*s1 + n*b6;
    end if;
    return [a1,a2,a3,a4-5*t,a6-b2*t-7*w];
end function;

function cInvariants(S)
    a1, a2,a3,a4,a6 := Explode(S);
    return [ a1^4 + 8*a1^2*a2 - 24*a1*a3 + 16*a2^2 - 48*a4,
	-a1^6 - 12*a1^4*a2 + 36*a1^3*a3 - 48*a1^2*a2^2
	+ 72*a1^2*a4 + 144*a1*a2*a3 - 64*a2^3
	+ 288*a2*a4 - 216*a3^2 - 864*a6 ];
end function;

function PrecisionSequence(n)
    precs := [ n ];
    while true do
	n := (n+1) div 2;
	if n eq 1 then break; end if;
	Append(~precs,n);
    end while;
    return Reverse(precs);
end function;

function TransitionScalar(S0,S1)
    R := Universe(S0);
    m := Precision(R);
    c0 := cInvariants(S0);
    c1 := cInvariants(S1);
    u2 := HenselLiftSquare(c1[1]/c0[1], c0[1]*c1[2]/(c1[1]*c0[2]), m);
    val, u1 := IsSquare(u2);
    if not val then error "Elliptic curves are not isomorphic"; end if;
    return HenselLiftSquare(u2,u1,RelativePrecision(u2));
end function;

function CanonicalLiftjInvariants(j,n)
    // {The canonical p-adic lift of the cycle of the
    // conjugate j-invariants of E.}
    FF := Parent(j);
    p := Characteristic(FF);
    r := Degree(FF);
    vprint Satoh: "Computing lifting rings.";
    Z := pAdicQuotientRing(p,n);
    S := CyclotomicUnramifiedExtension(Z,r);
    vprint Satoh: "Done computing lifting rings.";
    jInvs := [ S!j ];
    for i in [1..r-1] do
	Append(~jInvs,S!jInvs[i]^p);
    end for;
    Phi := ClassicalModularPolynomial(p);
    jInvs := FGHLiftCycle(Phi,Reverse(jInvs));
    K := CyclotomicUnramifiedExtension(pAdicField(p,n),r);
    w := K!Eltseq(1 div (jInvs[1]-12^3));
    return [1,0,0,-36*w,-w], jInvs;
end function;

function CanonicalLiftwInvariants(w,n)
    // {The canonical p-adic lift of the cycle of the
    // conjugate j-invariants of E.}
    FF := Parent(w);
    p := Characteristic(FF);
    r := Degree(FF);
    vprint Satoh: "Computing lifting rings.";
    Z := pAdicQuotientRing(p,n);
    S := CyclotomicUnramifiedExtension(Z,r);
    vprint Satoh: "Done computing lifting rings.";
    wInvs := [ S!w ];
    for i in [1..r-1] do
	Append(~wInvs,S!wInvs[i]^p);
    end for;
    Phi := ClassicalModularPolynomial(p);
    P<X,Y> := Parent(Phi);
    Phi := Numerator(Evaluate(Phi,[1/(X-12^3),1/(Y-12^3)]));
    wInvs := FGHLiftCycle(Phi,Reverse(wInvs));
    K := CyclotomicUnramifiedExtension(pAdicField(p,n),r);
    w := K!Eltseq(wInvs[1]);
    return [1,0,0,-36*w,-w], wInvs;
end function;

// Efficient version of HenselLift, implementing linear inversion 
// of matrix, following Fouquet, Gaudry, and Harley.

function FGHLiftCycle(Phi,jinvs)   
    S := Universe(jinvs);
    n := Precision(S);
    r := #Eltseq(jinvs);
    v := jinvs;
    precs := PrecisionSequence(n);
    vprint Satoh : "Computing lifts to precision:", n;
    vprintf Satoh : "Need %o iterations.\n", #precs;   
    total_tyme := Cputime();
    DPhi := Derivative(Phi,1);
    j := 1;
    for prec in precs do
	tyme := Cputime();
	vprint Satoh : "Iteration:", j;
	IndentPush();
	R := ChangePrecision(S,prec);
	ChangeUniverse(~v,R); 
	Fv := [ Evaluate(Phi,  [v[i],v[i mod r + 1] ]) : i in [1..r] ];
	if GetVerbose("Satoh") ge 3 then
	    print "Ring precision =", prec;
	    ord := Min([ Valuation(fx) : fx in Fv ]);
	    print "Valuation =", ord;
	end if;
	vprintf Satoh, 2 : "Step 1 (%o)\n", Cputime(tyme);
	Dx := [ Evaluate(DPhi, [v[i],v[i mod r + 1]]) : i in [1..r] ];
	vprintf Satoh, 2 : "Step 2 (%o)\n", Cputime(tyme);
	Dy := [ Evaluate(DPhi, [v[i mod r + 1],v[i]]) : i in [1..r] ];
	vprintf Satoh, 2 : "Step 3 (%o)\n", Cputime(tyme);
	InvDx := [ a^-1 : a in Dx ]; // Expensive step
	vprintf Satoh, 2 : "Step 4 (%o)\n", Cputime(tyme);
	Pv := [ Fv[i]*InvDx[i] : i in [1..r] ];
	Dv := [ Dy[i]*InvDx[i] : i in [1..r] ];
	f := Fv[r];
	m := Dy[r];
	vprintf Satoh, 2 : "Step 5 (%o)\n", Cputime(tyme);
	for i in [1..r-1] do
	    f +:= -m*Pv[i];
	    m *:= -Dv[i];
	    if m eq 0 then break i; end if;
	end for;
	m +:= Dx[r];
	f /:= m;
	Pv[r] := f; 
	vprintf Satoh, 2 : "Step 6 (%o)\n", Cputime(tyme);
	for i in [r-1..1 by -1] do
	    Pv[i] +:= -Dv[i]*Pv[i+1];
	end for;
	vprintf Satoh, 2 : "Step 7 (%o)\n", Cputime(tyme);
	for i in [1..r] do
	    v[i] +:= -Pv[i];         
	end for;
	IndentPop();
	j +:= 1;
    end for;
    vprint Satoh : "Total lift time:", Cputime(total_tyme);
    return Eltseq(v);
end function;


