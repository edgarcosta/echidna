////////////////////////////////////////////////////////////////////////
//                                                                    //
//                       ALGEBRA DECOMPOSITION                        //
//                            David Kohel                             //
//                                                                    //
////////////////////////////////////////////////////////////////////////

intrinsic Decomposition(A::AlgGrp) -> SeqEnum
    {}
    R := BaseRing(A);
    require IsField(R) : "Argument must be an algebra over a field.";
    require IsCoercible(A,1) : "Argument must be an algebra with unity.";
    idmpts := CentralPrimitiveIdempotents(A);
    return [ ideal< A | e > : e in idmpts ];
end intrinsic;

intrinsic Decomposition(A::AlgAss) -> SeqEnum
    {}
    R := BaseRing(A);
    require IsField(R) : "Argument must be an algebra over a field.";
    require IsCoercible(A,1) : "Argument must be an algebra with unity.";
    idmpts := CentralPrimitiveIdempotents(A);
    return [ ideal< A | e > : e in idmpts ];
end intrinsic;

intrinsic Decomposition(A::AlgMat) -> SeqEnum
    {}
    R := BaseRing(A);
    require IsField(R) : "Argument must be an algebra over a field.";
    require IsCoercible(A,1) : "Argument must be an algebra with unity.";
    idmpts := CentralPrimitiveIdempotents(A);
    return [ sub< A | { e*b : b in Basis(A) } > : e in idmpts ];
end intrinsic;

intrinsic IntegralSimpleQuotients(A::AlgMat) -> SeqEnum
    {}
    R := BaseRing(A);
    require Type(R) eq RngInt :
	"Argument must be an algebra over the integers.";
    K := BaseChange(A,Rationals()); 
    require IsCoercible(K,1) :
	"Argument must be an order in an algebra with unity.";
    idmpts := CentralPrimitiveIdempotents(K);
    gens := Generators(A); 
    return [ map< A->K | x :-> e*x > : e in idmpts ];
end intrinsic;

intrinsic IntegralSimpleQuotients(A::AlgGrp) -> SeqEnum
    {}
    R := BaseRing(A);
    require Type(R) eq RngInt :
	"Argument must be an algebra over the integers.";
    K := BaseChange(A,Rationals()); 
    require IsCoercible(K,1) :
	"Argument must be an order in an algebra with unity.";
    idmpts := CentralPrimitiveIdempotents(K);
    gens := Generators(A); 
    return [ map< A->K | x :-> e*K!Eltseq(x) > : e in idmpts ];
end intrinsic;

////////////////////////////////////////////////////////////////////////

function MergeIdempotents(idmpts,new_idmpts)
    mrg_idmpts := {@ Universe(idmpts) | @};
    for e in idmpts do
	for f in new_idmpts do
	    n := e*f;
	    if n ne 0 then
		Include(~mrg_idmpts,n);
	    end if;
	    n := e*(1-f);
	    if n ne 0 then
		Include(~mrg_idmpts,n);
	    end if;
	end for;
    end for;
    return mrg_idmpts;
end function;

function EvaluatePolynomial(f,a)
    n := Degree(f);
    return &+[ Coefficient(f,i)*a^i : i in [0..n] ];
end function;

function CPI(A)
    R := BaseRing(A);
    Z := Center(A);
    error if not Dimension(Z) ge 1,
	"Argument must be an algebra with unity.";
    if Dimension(Z) eq 1 then
	return {@ Z!1 @};
    end if;
    idmpts := {@ Z!1 @};
    PR := PolynomialRing(R); 
    for x in Basis(Z) do
	new_idmpts := {@ Z | @};
	fac := Factorization(MinimalPolynomial(x));
	dim := [ Degree(f[1]) : f in fac ]; 
	loc := [ f[1]^f[2] : f in fac ];
	num := #fac;
	if num gt 1 then
	    for i in [1..num] do
		uni := [ PR | 0 : j in [1..i-1] ] cat
    		    [ PR | 1] cat [ PR | 0 : j in [i+1..num] ];
   	        e := EvaluatePolynomial(CRT(uni,loc),x);
		idmpts := MergeIdempotents(idmpts,[e]);
	    end for;
	end if;
    end for;
    return {@ A!e : e in idmpts @};
end function;

intrinsic CentralPrimitiveIdempotents(A::AlgAss) -> SeqEnum
    {}
    require IsField(BaseRing(A)) :
	"Argument must be an algebra over a field.";
    return CPI(A);
end intrinsic;

intrinsic CentralPrimitiveIdempotents(A::AlgGrp) -> SeqEnum
    {}
    require IsField(BaseRing(A)) :
	"Argument must be an algebra over a field.";
    return CPI(A);
end intrinsic;

intrinsic CentralPrimitiveIdempotents(A::AlgMat) -> SeqEnum
    {}
    require IsField(BaseRing(A)) :
	"Argument must be an algebra over a field.";
    return CPI(A);
end intrinsic;

