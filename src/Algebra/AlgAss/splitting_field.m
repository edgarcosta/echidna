////////////////////////////////////////////////////////////////////////
//                                                                    //
//                            David Kohel                             //
//                                                                    //
////////////////////////////////////////////////////////////////////////

intrinsic PrimitiveElement(A::AlgAss) -> AlgAss
    {}
    require IsCommutative(A) and IsSimple(A) :  
	"Argument must be a commutative field.";
    n := Dimension(A);
    for x in Basis(A) do
	if Degree(MinimalPolynomial(x)) eq n then
	    return x;
	end if;
    end for;
    assert false;
end intrinsic;

////////////////////////////////////////////////////////////////////////

intrinsic SplittingField(A::AlgAss) -> AlgAss
    {}
    require IsField(BaseRing(A)) and IsSimpleXXX(A) : 
	"Argument must be a simple algebra over a field."; 
    if not assigned A`SplittingField then
	r := DimensionOfCenter(A);
	n := ReducedDegree(A);
	if r ne 1 then Z := Center(A); end if;
	for i in [1..Dimension(A)] do
	    x := A.i;
	    if Degree(MinimalPolynomial(x)) eq r*n then
		return sub< A | x >;
	    elif r ne 1 then
		K, m := sub< A | Basis(Z) cat [x] >;
		if Dimension(K) eq r*n then
		    return K, m;
		end if;
	    end if;
	end for;
	assert false;// "Not implemented.";
    end if;
    return A`SplittingField;
end intrinsic;

intrinsic ReducedDegree(A::AlgAss) -> SeqEnum
    {The degree of a minimal representation of the simple algebra A
    over its center.}
    require assigned A`AmbientAlgebra
	select IsSimpleXXX(A`AmbientAlgebra) else IsSimpleXXX(A) : 
	"Argument must be simple or an order in a simple algebra.";
    if assigned A`ReducedDegree then
	return A`ReducedDegree;
    elif assigned A`AmbientAlgebra then
	return ReducedDegree(A`AmbientAlgebra);
    end if;
    if not assigned A`ReducedDegree then
	A`ReducedDegree := Isqrt(Dimension(A) div DimensionOfCenter(A));
    end if;
    return A`ReducedDegree;
end intrinsic;

////////////////////////////////////////////////////////////////////////

