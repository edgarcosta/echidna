////////////////////////////////////////////////////////////////////////
//                                                                    //
//                            David Kohel                             //
//                                                                    //
////////////////////////////////////////////////////////////////////////

function MultiplicityOfFactor(f,e,x,deg)
    A := Parent(x);
    I := lideal< A | Evaluate(f^e,x) >;
    rel := Dimension(A)-Dimension(I);
    assert rel mod (Degree(f)*deg) eq 0;
    return rel div (Degree(f)*deg);
end function;

////////////////////////////////////////////////////////////////////////

intrinsic ReducedCharacteristicPolynomial(x::AlgAssElt) -> RngUPolElt
    {}
    A := Parent(x);
    require assigned A`AmbientAlgebra
	select IsSimpleXXX(A`AmbientAlgebra) else IsSimpleXXX(A) : 
	"Argument must be simple or an order in a simple algebra.";
    R := BaseRing(A); 
    dim := Dimension(A);
    if assigned A`AmbientAlgebra then
	M := A`AmbientBasisMatrix;
	A := A`AmbientAlgebra;
	x := A!Eltseq(VectorSpace(BaseRing(A),dim)!Eltseq(x)*M);
    end if;
    m := MinimalPolynomial(x);
    n := ReducedDegree(A);
    r := Degree(m);
    if r lt n then
	// Here we need to determine the multiplicities of the factors.
	m0 := Parent(m)!1;
	fact := Factorization(m);
	for i in [1..#fact] do
	    f := fact[i][1]; e := fact[i][2];
	    fact[i][2] := MultiplicityOfFactor(f,e,x,n);
	end for;
	m := &*[ f[1]^f[2] : f in fact ];
	assert Degree(m) eq n;
	r := n;
    end if;
    return PolynomialRing(R)!m;
end intrinsic;

////////////////////////////////////////////////////////////////////////

intrinsic ReducedNorm(x::AlgAssElt) -> SeqEnum
    {}
    A := Parent(x);
    require assigned A`AmbientAlgebra
	select IsSimpleXXX(A`AmbientAlgebra) else IsSimpleXXX(A) : 
	"Argument must be simple or an order in a simple algebra.";
    R := BaseRing(A); 
    dim := Dimension(A);
    if assigned A`AmbientAlgebra then
	M := A`AmbientBasisMatrix;
	A := A`AmbientAlgebra;
	x := A!Eltseq(VectorSpace(BaseRing(A),dim)!Eltseq(x)*M);
    end if;
    m := MinimalPolynomial(x);
    n := ReducedDegree(A);
    r := Degree(m);
    if r lt n then
	// Here we need to determine the multiplicities of the factors.
	m0 := Parent(m)!1;
	fact := Factorization(m);
	for i in [1..#fact] do
	    f := fact[i][1]; e := fact[i][2];
	    fact[i][2] := MultiplicityOfFactor(f,e,x,n);
	end for;
	m := &*[ f[1]^f[2] : f in fact ];
	assert Degree(m) eq n;
	r := n;
    end if;
    return ((-1)^r*R!Coefficient(m,0))^(n div r);
end intrinsic;

intrinsic ReducedTrace(x::AlgAssElt) -> SeqEnum
    {}
    A := Parent(x);
    require assigned A`AmbientAlgebra
	select IsSimpleXXX(A`AmbientAlgebra) else IsSimpleXXX(A) : 
	"Argument must be simple or an order in a simple algebra.";
    R := BaseRing(A); 
    dim := Dimension(A);
    if assigned A`AmbientAlgebra then
	M := A`AmbientBasisMatrix;
	A := A`AmbientAlgebra;
	x := A!Eltseq(VectorSpace(BaseRing(A),dim)!Eltseq(x)*M);
    end if;
    m := MinimalPolynomial(x);
    n := ReducedDegree(A);
    r := Degree(m);
    if r lt n then
	// Here we need to determine the multiplicities of the factors.
	m0 := Parent(m)!1;
	fact := Factorization(m);
	for i in [1..#fact] do
	    f := fact[i][1]; e := fact[i][2];
	    fact[i][2] := MultiplicityOfFactor(f,e,x,n);
	end for;
	m := &*[ f[1]^f[2] : f in fact ];
	assert Degree(m) eq n;
	r := n;
    end if;
    return -(n div r)*R!Coefficient(m,r-1);
end intrinsic;

intrinsic ReducedTraceMatrix(S::[AlgAssElt]) -> SeqEnum
    {}
    A := Universe(S);
    require assigned A`AmbientAlgebra
	select IsSimpleXXX(A`AmbientAlgebra) else IsSimpleXXX(A) : 
	"Argument must be simple or an order in a simple algebra.";
    return Matrix(#S,[ ReducedTrace(x*y) : x, y in S ]);
end intrinsic;

intrinsic ReducedTraceMatrix(A::AlgAss) -> SeqEnum
    {}
    require assigned A`AmbientAlgebra
	select IsSimpleXXX(A`AmbientAlgebra) else IsSimpleXXX(A) : 
	"Argument must be simple or an order in a simple algebra.";
    dim := Dimension(A);
    return Matrix(dim,[ ReducedTrace(x*y) : x, y in Basis(A) ]);
end intrinsic;

intrinsic Discriminant(A::AlgAss) -> RngElt
    {}
    require assigned A`AmbientAlgebra
	select IsSimpleXXX(A`AmbientAlgebra) else IsSimpleXXX(A) : 
	"Argument must be simple or an order in a simple algebra.";
    return Determinant(ReducedTraceMatrix(A));
end intrinsic;


