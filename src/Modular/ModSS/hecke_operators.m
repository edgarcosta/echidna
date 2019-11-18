import "curve_models.m" : RootsAfterSpecializeX;

////////////////////////////////////////////////////////////////////////
//                       Auxilliary Function                          //
////////////////////////////////////////////////////////////////////////

function Restrict(A,x)
    // Restriction of A to x.
    F := BaseRing(Parent(A));
    if Type(x) eq SeqEnum then
	B := x;
    else
	if Dimension(x) eq 0 then
	    return MatrixAlgebra(F,0)!0;
	end if;
	Z := Basis(x);
	V := RSpace(F, Degree(x));
	B := [V!Z[i] : i in [1..Dimension(x)]];
    end if; 
    S := RSpaceWithBasis(B);
    v := [Coordinates(S, S.i*A) : i in [1..#B]];
    return MatrixAlgebra(F,#B) ! (&cat v);
end function;

////////////////////////////////////////////////////////////////////////
//                         Hecke Operators                            //
////////////////////////////////////////////////////////////////////////

function ComputeHeckeOperatorBrandt(M,p)
    assert Type(M) eq ModSS;
    assert Type(p) eq RngIntElt;
    assert p ge 2 and IsPrime(p);
    return HeckeOperator(BrandtModule(M), p);
end function;

function ComputeHeckeOperatorMestre(M,p)
    assert Type(M) eq ModSS;
    assert Type(p) eq RngIntElt;
    assert p ge 2 and IsPrime(p);
    assert IsAmbientSpace(M);
    assert AuxiliaryLevel(M) mod p ne 0;
    
    S := SupersingularPoints(M);
    correspondence := HeckeCorrespondence(M,p);
    curve := ModularPolynomial(M);
    T := MatrixAlgebra(Integers(),Dimension(M))!0;
    for i in [1..#S] do
	P := S[i];
	for x in RootsAfterSpecializeX(correspondence,P[1]) do
	    y_val := RootsAfterSpecializeX(curve,x[1]);
	    assert #y_val le 1;
	    Q := <x[1], y_val[1][1]>;
	    n := Index(S, Q);
	    if n eq 0 then
		error "An error in ComputeHeckeOperatorMestre occured, which "*
		    "probably means that one of the polynomial tables is wrong."; 
	    end if;
	    T[i,n] +:= x[2];
	end for;
    end for;  
    return T; 
end function;

function HeckeOperatorPrimeIndex(M,p)
    assert Type(M) eq ModSS;
    assert Type(p) eq RngIntElt;
    assert p ge 1 and IsPrime(p);
    i := Index(M`hecke_primes,p);
    if i ne 0 then
	Tp := M`hecke_operators[i];
    else
	if UsesBrandt(M) then
	    Tp := ComputeHeckeOperatorBrandt(M,p);
	else
	    Tp := ComputeHeckeOperatorMestre(M,p);
	end if;
	Append(~M`hecke_primes,p);
	Append(~M`hecke_operators,Tp);
    end if;
    return Tp;
end function;

function ComputeHeckeOperator(M,n)
    assert Type(M) eq ModSS;
    assert Type(n) eq RngIntElt;
    assert n ge 1;
    
    fac := Factorization(n);
    if #fac eq 0 then
	return MatrixAlgebra(Integers(),Dimension(M))!1;
    elif #fac eq 1 then
	// T_{p^r} := T_p * T_{p^{r-1}} - eps(p)p^{k-1} T_{p^{r-2}}.
	p  := fac[1][1];
	r  := fac[1][2];
	T  := HeckeOperatorPrimeIndex(M,p) * ComputeHeckeOperator(M,p^(r-1))
	    - p* (r ge 2 select ComputeHeckeOperator(M,p^(r-2)) else 0);
    else  // T_m*T_r := T_{mr} and we know all T_i for i<n.
	m  := fac[1][1]^fac[1][2];
	T  := ComputeHeckeOperator(M,m)*ComputeHeckeOperator(M,n div m);
    end if;            
    return T;
end function;

intrinsic HeckeOperator(M::ModSS, n::RngIntElt) -> AlgMatElt
    {Hecke operator T_n.}
    require n ge 1 : "Argument 1 must be positive.";
    require GCD(AuxiliaryLevel(M),n) eq 1 or
	assigned M`uses_brandt and M`uses_brandt eq true:
	"Argument 2 must be coprime to the level of argument 1.";
    i := Index(M`hecke_primes,n);
    if i ne 0 then
	return M`hecke_operators[i];
    end if;
    if IsAmbientSpace(M) then
	Tn := ComputeHeckeOperator(M,n);
    else
	Tn := Restrict(ComputeHeckeOperator(AmbientSpace(M),n), RSpace(M));
    end if;
    return Tn;
end intrinsic;

intrinsic HeckeOperator(n::RngIntElt, x::ModSSElt) -> ModSSElt
    {Hecke operator applied to x:  T_n(x)}
    M := AmbientSpace(Parent(x));
    T := HeckeOperator(AmbientSpace(Parent(x)),n);
    return Parent(x)!(x`element*T);
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                       Atkin-Lehner Operators                       //
////////////////////////////////////////////////////////////////////////

function AtkinLehnerMestre(M, q)
    assert Type(M) eq ModSS;
    assert Type(q) eq RngIntElt;
    assert UsesMestre(M);
    assert IsAmbientSpace(M);
    p := Prime(M);
    N := AuxiliaryLevel(M);
    
    if q eq N and N eq 1 then
	return MatrixAlgebra(Integers(),Dimension(M))!1;
    end if;
    
    Wp := MatrixAlgebra(Integers(),Dimension(M))!0;
    S := SupersingularPoints(M);
    if q eq p then 
	for i in [1..Dimension(M)] do 
	    // Atkin-Lehner operator acts by -Frob_p.
	    Q := <S[i][1]^p, S[i][2]^p>;
	    j := Index(S, Q); assert j ne 0;
	    Wp[i,j] := -1;
	end for;
    elif q eq N then // N is one of 2, 3, 5, 7, or 13 (prime).
	for i in [1..Dimension(M)] do 
	    // This uses the structure of the Atkin-Lehner operator
	    // on this particular modular curve...
	    Q := <S[i][2], S[i][1]>;
	    j := Index(S, Q); assert j ne 0;
	    Wp[i,j] := 1;
	end for;
    else
	error "Argument must be prime.";
    end if;
    return Wp;
end function;

function AtkinLehnerBrandt(M, q)
    assert Type(M) eq ModSS;
    assert UsesBrandt(M);
    assert IsAmbientSpace(M);
    
    return AtkinLehnerOperator(BrandtModule(M),q);
end function;

intrinsic AtkinLehnerOperator(M::ModSS, q::RngIntElt) -> AlgMatElt
    {The Atkin-Lehner involution W_q, where q is either Prime(M) or
    AuxiliaryLevel(M).}
    require q in {Prime(M), AuxiliaryLevel(M)} :
	"Argument 2 must be either", Prime(M), "or", AuxiliaryLevel(M);
    if q notin M`atkin_lehner_primes then
	if IsAmbientSpace(M) then
	    if UsesMestre(M) then
		Wp := AtkinLehnerMestre(M,q);   
	    else
		Wp := AtkinLehnerBrandt(M,q);   
	    end if;
	else
	    Wp := Restrict(
		AtkinLehnerOperator(AmbientSpace(M),q),RSpace(M));
	end if;
	Append(~M`atkin_lehner_primes,q);
	Append(~M`atkin_lehner_operators,Wp);
    end if;
    i := Index(M`atkin_lehner_primes,q);
    return M`atkin_lehner_operators[i];
end intrinsic;

