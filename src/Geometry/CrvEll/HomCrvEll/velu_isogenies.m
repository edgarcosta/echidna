////////////////////////////////////////////////////////////////////////
//                                                                    //
//                            VELU ISOGENIES                          //
//                              David Kohel                           //
//                                                                    //
////////////////////////////////////////////////////////////////////////

forward OmegaOddDeg, OmegaOddDegChar2, OmegaOddDegChar2New;

////////////////////////////////////////////////////////////////////////

intrinsic VeluImageCurve(E::CrvEll,psi::RngUPolElt : 
    IsogenyDegree := 0) -> CrvEll
    {Returns codomain of the isogeny of Velu, defined with respect to
    the monic kernel polynomial psi.} 

    R := BaseRing(E); 
    S := Parent(psi); x := S.1;
    a1,a2,a3,a4,a6 := Explode(aInvariants(E)); 
    b2,b4,b6 := Explode(bInvariants(E)); 
    n := Degree(psi); 
    if IsogenyDegree eq 0 then
	e := Degree(GCD(psi,4*x^3+b2*x^2+2*b4*x+b6));
	deg := 2*n-e+1;  
    else 
	deg := IsogenyDegree;
    end if;
    s1 := -Coefficient(psi,n-1); 
    s2 := R!0; s3 := R!0; 
    if n ge 3 then 
	s2 := Coefficient(psi,n-2);  
	s3 := -Coefficient(psi,n-3); 
    elif n ge 2 then  
	s2 := Coefficient(psi,n-2);  
    end if; 
    p1 := s1; p2 := s1^2 - 2*s2; p3 := s1^3 - 3*s1*s2 + 3*s3; 
    t0 := 6*p2 + b2*p1 + n*b4; 
    w0 := 10*p3 + 2*b2*p2 + 3*b4*p1 + n*b6; 
    if IsOdd(deg) then 
	E1 := EllipticCurve([a1,a2,a3,a4-5*t0,a6-b2*t0-7*w0]); 
    else  
	assert Characteristic(R) ne 2;
	E1 := EllipticCurve([a1,a2,a3,a4-5*t0/2,a6-b2*t0/2-7*w0/2]); 
    end if; 
    return E1; 
end intrinsic;

intrinsic VeluIsogeny(E::CrvEll,psi::RngUPolElt :
    GeneralFormula := true, IsogenyDegree := 0) -> Map 
    {Returns the isogeny E -> F with kernel defined by psi,  
    such that the invariant differential on E pulls back to
    the invariant differential on F.} 
 
    R := BaseRing(E); 
    P := Parent(psi); X := P.1;
    require BaseRing(P) cmpeq R :
	"Argument 2 must be a polynomial over the base ring of argument 1.";
    a1, a2, a3, a4, a6 := Explode(aInvariants(E)); 
    b2, b4, b6 := Explode(bInvariants(E)); 
    n := Degree(psi);
    if IsogenyDegree eq 0 then
	e := Degree(GCD(psi,4*X^3 + b2*X^2 + 2*b4*X + b6));
	deg := 2*n-e+1;  
    else 
	deg := IsogenyDegree;
	e := 2*n+1-deg;
	require e in [0,1,3] : "Invalid value for parameter IsogenyDegree.";
    end if;
    // Symmetric sums
    s1 := -Coefficient(psi,n-1); 
    s2 := n ge 2 select Coefficient(psi,n-2) else R!0;
    s3 := n ge 3 select -Coefficient(psi,n-3) else R!0;
    // Power sums
    p1 := s1;
    p2 := s1^2 - 2*s2;
    p3 := s1^3 - 3*s1*s2 + 3*s3; 
    A := Ambient(AffinePatch(E,1)); x := A.1; y := A.2;
    psi := Evaluate(psi,x);
    psi2x := 4*x^3 + b2*x^2 + 2*b4*x + b6;
    if IsOdd(deg) then 
	t0 := (6*p2 + b2*p1 + n*b4); 
	w0 := (10*p3 + 2*b2*p2 + 3*b4*p1 + n*b6); 
	Dpsi := Derivative(psi,1);
	phi := (deg*x - 2*s1)*psi^2 +
	    psi2x*(Dpsi^2 - Derivative(Dpsi,1)*psi) - (6*x^2+b2*x+b4)*Dpsi*psi;
	if not GeneralFormula and Characteristic(R) ne 2 then 
	    Dphi := Derivative(phi,1);
	    psi2y := 2*y + a1*x + a3;
	    omg := y * Dphi * psi - psi2y * Dpsi * phi;
	    del := 0;
	    if a1 ne 0 then
		del +:= a1*(x*Dphi-phi);
	    end if;
	    if a3 ne 0 then
		del +:= a3*(Dphi-psi^2);
	    end if;
	    omg +:= del*psi/2;
	else
	    if Characteristic(R) ne 2 then
		omg := OmegaOddDeg(psi,phi,aInvariants(E),s1,n,x,y);
	    else
		omg := OmegaOddDegChar2(psi,phi,aInvariants(E),s1,n,x,y);
	    end if;
	end if;
    elif deg eq 2 then  
	x0 := s1;
	if a1 eq 0 and a3 eq 0 then
	    y0 := Parent(x0)!0;
	elif Characteristic(R) ne 2 then
	    y0 := -(a1*x0+a3)/2;
	else
	    y0 := Roots(P![-(x0^3+a2*x0^2+a4*x0+a6),a1*x0+a3,1])[1][1];
	end if; 
	t0 := 3*x0^2 + 2*a2*x0 + a4 - a1*y0;
	w0 := x0*t0;
	phi := x*psi + t0;
	omg := y*psi^2 - t0*(a1*psi + (y - y0));
    elif e eq 3 and deg eq 4 then
	if Characteristic(R) ne 2 then
	    t0 := (6*p2 + b2*p1 + n*b4)/2; 
	    w0 := (10*p3 + 2*b2*p2 + 3*b4*p1 + n*b6)/2;
	    phi := x^4 - s1*x^3 + (s1^2 - 2*s2)*x^2 
		- (s1*s2 - 8*s3)*x + (s2^2 - 3*s1*s3);
	    Dpsi := Derivative(psi,1);
	    Dphi := Derivative(phi,1);
	    omg := (2*y+a1*x+a3) * (Dphi*psi - phi*Dpsi)/2 
	    - (a1*phi + a3*psi)*psi/2;
	else
	    error "Multiplication by 2 in characteristic 2 not treated.";
	end if;
    else
	error "General even degree isogenies not treated.";
    end if; 
    F := EllipticCurve([a1,a2,a3,a4-5*t0,a6-b2*t0-7*w0]); 
    return Hom(E,F)![psi,phi,omg];
end intrinsic; 

function OmegaOddDeg(psi,phi,coeffs,s1,n,x,y)
    R := Parent(x); 
    a1, a2, a3, a4, a6 := Explode(coeffs);
    b2 := a1^2 + 4*a2;
    b4 := a1*a3 + 2*a4;
    b6 := a3^2 + 4*a6;
    psi2y := 2*y + a1*x + a3;
    psi2x := 4*x^3 + b2*x^2 + 2*b4*x + b6;
    D1psi2x := 6*x^2 + b2*x + b4;
    D2psi2x := 12*x + b2;
    Dpsi := Derivative(psi,1);
    D2psi := &+[ R | ((i*(i-1)) div 2)*
	MonomialCoefficient(psi,x^i)*x^(i-2) : i in [2..n] ];
    D3psi := &+[ R | ((i*(i-1)*(i-2)) div 2)*
	MonomialCoefficient(psi,x^i)*x^(i-3) : i in [3..n] ];
    L0 := n*psi^3;
    L1 := Dpsi*psi^2;
    L2 := (Dpsi^2 - 2*D2psi*psi)*psi;
    L3 := Dpsi^3 - 3*D2psi*Dpsi*psi + D3psi*psi^2;
    return
	- psi2y*(psi2x*L3 - 2*D1psi2x*L2 + D2psi2x*L1 - 4*L0)
	- y*(D1psi2x*L2 - D2psi2x*L1 + 6*L0 - psi^3)
        - a1*(phi-x*psi^2)*psi
	- a1*((x^3*L2-3*x^2*L1+2*x*L0+s1*psi^3) - a4*(x*L2-L1) - 2*a6*L2)
	- a3*(3*(x^2*L2-2*x*L1+L0) + 2*a2*(x*L2-L1) + a4*L2);
end function;    

function OmegaOddDegChar2(psi,phi,coeffs,s1,n,x,y)
    R := Parent(x); 
    a1, _, a3, a4 := Explode(coeffs);
    psi2y := a1*x + a3;
    Dpsi := Derivative(psi,1);
    D2psi := &+[ R | ((i*(i-1)) div 2)*
	MonomialCoefficient(psi,x^i)*x^(i-2) : i in [2..n] ];
    D3psi := &+[ R | ((i*(i-1)*(i-2)) div 2)*
	MonomialCoefficient(psi,x^i)*x^(i-3) : i in [3..n] ];
    L0 := n*psi^3;
    L1 := Dpsi*psi^2;
    L2 := Dpsi^2*psi;
    L3 := Dpsi^3 + D2psi*Dpsi*psi + D3psi*psi^2;
    return (a1*psi2y*L2 + a1^2*L1 + psi^3)*y
	+ psi2y^3*L3 + psi2y*(x^2+a4)*L2 + a1*(a1*psi2y + (x^2+a4))*L1 
	+ a1*(phi*psi + (x+s1)*psi^3) + a3*L0;
end function;    

intrinsic SchemeMorphism(f::Map) -> MapSch
    {}
    E1 := Domain(f);
    E2 := Codomain(f);
    require Type(E1) eq CrvEll and Type(E2) eq CrvEll :
       "Argument must be an isogeny of elliptic curves.";
    A := Ambient(E1);
    x := A.1; y := A.2; z := A.3;
    psi := Homogenization(Evaluate(IsogenyMapPsi(f),x),z);
    phi := Homogenization(Evaluate(IsogenyMapPhi(f),x),z);
    omg := Homogenization(Evaluate(IsogenyMapOmega(f),[x,y]),z);
    if IsOdd(Degree(f)) then
	return map< E1 -> E2 | [psi*phi,omg,psi^3*z] >;
    elif Degree(f) eq 2 then
	return map< E1 -> E2 | [psi*phi,omg,psi^2*z] >;
    end if;
    require false: "General even degree isogenies not treated.";
end intrinsic;

/*
intrinsic PhiLog(E0::CrvEll,psi0::FldFunElt)-> FldFunElt
    {}
    R := BaseRing(E0); 
    K := FunctionField(E0); 
    y := K.1;
    x := K!BaseField(K).1;
    F := FunctionField(R);
    if psi0 eq 1 then return K!0; end if; 
    S := Parent(Numerator(F!Eltseq(x)[1])); 
    X := S.1;
    a1, a2, a3, a4, a6 := Explode(aInvariants(E0)); 
    b2, b4, b6, b8 := Explode(bInvariants(E0)); 
    psi2 := 2*y + a1*x + a3; 
    Psi2 := 4*X^3 + b2*X^2 + 2*b4*X + b6; // a polynomial. 
    Psi0 := Numerator(F!Eltseq(psi0)[1]); // a polynomial.  
    Eta0 := GCD(Psi0,Psi2); 
    eta0 := K!Eta0;
    Rho0 := Psi0 div Eta0;
    rho0 := K!Rho0;
    if Degree(Eta0) eq 1 then
	x0 := Roots(Eta0)[1];
	y0 := Sqrt(-(x0^3 + a2*x0^2 + a4*x0 + a6));
	EtaLog := (3*x0^2 + 2*a2*x0 + a4 - a1*y0)/(x - x0);
    elif Degree(Eta0) eq 3 then
	s1 := Coefficient(Eta0,2);
	s2 := Coefficient(Eta0,1);
	DLogEta := Derivative(eta0)^2/eta0; 
	EtaLog := (3*x^2 - 2*s1*x + s2)*DLogEta - 3*(3*x - s1);
    else 
	EtaLog := K!0;
    end if;
    n := Degree(Rho0); 
    if n eq 0 then
	return EtaLog;
    end if;
    s1 := -Coefficient(Rho0,n-1); 
    DLogRho := Derivative(rho0)/rho0;
    DDLogRho := Derivative(rho0,2)/rho0 - DLogRho^2;
    return 2*n*x-2*s1 + EtaLog - psi2^2*DDLogRho - K!(6*X^2 + b2*X + b4)*DLogRho;
end intrinsic;

intrinsic PhiOmega(E::CrvEll,f::RngUPolElt)-> FldFunRatUElt
    {}
    return (Derivative(f)^2 - Derivative(f,2)*f)/f^2;
end intrinsic;
*/
