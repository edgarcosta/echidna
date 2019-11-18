////////////////////////////////////////////////////////////////////////
//                                                                    //
//                            David Kohel                             //
//                                                                    //
////////////////////////////////////////////////////////////////////////

intrinsic RamifiedPrimes(A::AlgAss) -> SeqEnum
    {}
    require Type(BaseRing(A)) in {RngInt,FldRat} : 
	"Argument must be defined over the integers or rationals.";
    if Type(BaseRing(A)) eq FldRat then
	if not assigned A`RamifiedPrimes then
	    A`RamifiedPrimes := RamifiedPrimes(MaximalOrder(A));
	end if;
	return A`RamifiedPrimes;
    end if;
    n := Dimension(A); 
    M := Matrix(n,[ ReducedTrace(x*y) : x, y in Basis(A) ]); 
    return [ p[1] : p in Factorization(Determinant(M)) ];
end intrinsic;

intrinsic RamifiedPrimes(A::AlgAss) -> SeqEnum
    {}
    require Type(BaseRing(A)) in {RngInt,FldRat} : 
	"Argument must be defined over the integers or rationals.";
    if Type(BaseRing(A)) eq FldRat then
	if not assigned A`RamifiedPrimes then
	    A`RamifiedPrimes := RamifiedPrimes(MaximalOrder(A));
	end if;
	return A`RamifiedPrimes;
    end if;
    M := Matrix(Dimension(A),[ ReducedTrace(x*y) : x, y in Basis(A) ]); 
    return PrimeDivisors(Determinant(M));
end intrinsic;

/*
intrinsic RamifiedPrimes(A::AlgGrp) -> SeqEnum
    {}
    require Type(BaseRing(A)) in {RngInt,FldRat} : 
	"Argument must be defined over the integers or rationals.";
    if Type(BaseRing(A)) eq FldRat then
	return RamifiedPrimes(MaximalOrder(A));
    end if;
    n := Dimension(A); 
    M := Matrix(n,[ ReducedTrace(x*y) : x, y in Basis(A) ]); 
    return [ p[1] : p in Factorization(Determinant(M)) ];
end intrinsic;
*/
