////////////////////////////////////////////////////////////////////////
//                                                                    //
//                 Divisors on Projective Plane Curves                //
//                                                                    //
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
//                       Simplified Divisor Constructors              //
////////////////////////////////////////////////////////////////////////

intrinsic Divisor(C::Crv,X::Sch) -> DivCrvElt
    {}
    require IsProjective(C) and Ambient(C) cmpeq Ambient(X) :
	"Argument 1 must be a projective curve.";
    require Ambient(C) cmpeq Ambient(X) :
	"Argument 2 must be in the same space as argument 1.";
    Z := Intersection(C,X);
    if IsEmpty(Z) then return DivisorGroup(C)!0; end if;
    require Dimension(Z) eq 0 :
	"Argument 2 must meet the curve of argument 1 " *
	"at a subscheme of dimension zero.";
    I := Ideal(Z);
    return Divisor(DivisorGroup(C),I);
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                       Simplified Divisor Constructors              //
////////////////////////////////////////////////////////////////////////

intrinsic Ideal(p::PlcCrvElt) -> RngMPol
    {The prime ideal of coordinate functions which vanish at p.}
    C := Curve(p);
    f, g := TwoGenerators(FunctionFieldPlace(p));
    K := FunctionField(C);
    L, m := AlgorithmicFunctionField(FunctionField(C));
    m := ProjectiveMap([f@@m,g@@m,1],Ambient(C));
    Z := Difference(Y,W)
	where Y := Scheme(Codomain(m),[C.1,C.2])@@m
	where W := BaseScheme(m);
    return Radical(Ideal(Z));
end intrinsic;

intrinsic Ideal(D::DivCrvElt) -> RngMPol
    {The ideal of coordinate functions which cuts out D.}
    plcs, vals := Support(D);
    require &and[ n gt 0 : n in vals ] :
	"Argument must be an effective divisor.";
    if #plcs eq 0 then
	return ideal< CoordinateRing(Ambient(Curve(D))) | 1 >;
    end if;
    return &*[ Ideal(plcs[i])^vals[i] : i in [1..#plcs] ];
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                    Alternate Printing Functions                    //
////////////////////////////////////////////////////////////////////////

intrinsic PrintPlace(p::PlcCrvElt)
    {}
    x, y := Explode(Basis(Ideal(p)));
    printf "(%o, %o)", x, y;
end intrinsic;

intrinsic PrintDivisor(D::DivCrvElt)
    {}
    fcns := Basis(Ideal(D));
    if #fcns eq 2 then
	printf "(%o, %o)\n", x, y where x, y := Explode(fcns);
    else
	print 0;
    end if;
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                     Evaluation and Valuation                       //
////////////////////////////////////////////////////////////////////////

intrinsic Evaluate(f::FldFunElt,P::PlcCrvElt) -> FldElt
    {}
    C := Curve(P);   
    require Parent(f) eq FunctionField(C) : 
	"Arguments must be defined with respect to the same curve."; 
    return Evaluate(f,FunctionFieldPlace(P));
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                          Functionality                             //
////////////////////////////////////////////////////////////////////////

intrinsic IntersectionDivisor(X::Crv,Y::Crv) -> DivCrvElt
    {Compute the intersection divisor of X and Y in Div(X).}
    
    K := BaseRing(X);
    require Type(K) eq FldFin :
	"Argument 1 must be defined over a finite field.";
    require Ambient(X) cmpeq Ambient(Y): 
	"Arguments must be curves in the same ambient space.";
    
    f := Polynomial(X); g := Polynomial(Y);
    require GCD(f,g) eq 1: "Arguments must meet transversally.";
    F := FunctionField(X);
    x := F.1; y := F.2;
    Div := DivisorGroup(X);
    DY := Div!0;
    g0 := Evaluate(g,[x,y,1]);
    Z0 := Zeros(g0);
    DY +:= Div ! &+[ Valuation(g0,Q)*Q : Q in Z0 ];
    z1 := 1/x; z2 := 1/y;
    g1 := Evaluate(g,[1,x*z2,z1]);
    Z1 := CommonZeros([ g1, z1, z2 ]);
    DY +:= Div ! &+[ Valuation(g1,Q)*Q : Q in Z1 ];
    return DY;
end intrinsic;

intrinsic 'ge'(D1::DivCrvElt,D2::DivCrvElt) -> BoolElt
    {True if and only if D1 is greater or equal than D2.}
    require Parent(D1) eq Parent(D2) : "Incompatible divisors";
    return IsEffective(D1-D2);
end intrinsic;

intrinsic 'gt'(D1::DivCrvElt,D2::DivCrvElt) -> BoolElt
    {True if and only if D1 is greater than D2.}
    require Parent(D1) eq Parent(D2) : "Incompatible divisors";
    if D1 eq D2 then return false; end if;
    return IsEffective(D1-D2);
end intrinsic;

intrinsic 'le'(D1::DivCrvElt,D2::DivCrvElt) -> BoolElt
    {True if and only if D1 is less than or equal to D2.}
    require Parent(D1) cmpeq Parent(D2):"Incompatible divisors";
    return IsEffective(D2-D1);
end intrinsic;

intrinsic 'lt'(D1::DivCrvElt,D2::DivCrvElt) -> BoolElt
    {True if and only if D1 is less than D2.}
    require Parent(D1) cmpeq Parent(D2):"Incompatible divisors";
    if D1 eq D2 then return false; end if;
    return IsEffective(D2-D1);
end intrinsic;
