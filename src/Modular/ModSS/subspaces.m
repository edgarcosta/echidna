////////////////////////////////////////////////////////////////////////
//                       Auxilliary Function                          //
////////////////////////////////////////////////////////////////////////

function CreateSubspace(M, V) 
    assert Type(M) eq ModSS;
    assert Type(V) eq ModTupRng;
    if V eq RSpace(M) then
	return M;
    end if;
    assert V subset RSpace(M);
    S := New(ModSS);
    S`p := Prime(M);
    S`auxiliary_level := AuxiliaryLevel(M);
    S`ambient_space := AmbientSpace(M);
    M`atkin_lehner_primes := [];
    M`atkin_lehner_operators := [];
    M`hecke_primes := [];
    M`hecke_operators := [];
    S`rspace := V;
    return S;
end function;

function LinearCombinations(Comb, B) 
    // Compute the linear combinations of the elements of B
    // defined by the elements of Comb.
    n := #B;
    if n eq 0 then
	return B;
    end if;
    return [Parent(B[1])|&+[B[i]*v[i] : i in [1..n]] : v in Comb];
end function;

function KernelOn(A, B)
    // Suppose B is a basis for an n-dimensional subspace
    // of some ambient space and A is an nxn matrix.
    // Then A defines a linear transformation of the space
    // spanned by B.  This function returns the
    // kernel of that transformation.
    if Type(B) eq ModTupRng then
	B := Basis(B);
    end if;
    n := #B;
    if n eq 0 then
	return sub<Universe(B)|0>;
    end if;
    assert Nrows(A) eq Ncols(A) and Nrows(A) eq n;
    K := Kernel(A);
    return sub<Universe(B) | LinearCombinations(Basis(K),B)>;
end function;

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
//                            Subspaces                               //
////////////////////////////////////////////////////////////////////////

intrinsic OrthogonalComplement(M::ModSS) -> ModSS
    {The orthogonal complement of M, with respect to the monodromy pairing.}
    A := RMatrixSpace(Integers(),Dimension(AmbientSpace(M)), Dimension(M))!0;
    w := MonodromyWeights(M);
    B := Basis(RSpace(M));
    for j in [1..#B] do
	for i in [1..Dimension(AmbientSpace(M))] do
	    A[i,j] := B[j][i]*w[i];
	end for;
    end for;   
    
    B := Basis(Kernel(A));
    V := RSpace(AmbientSpace(M));
    W := sub<V | [V!x : x in B]>;
    return CreateSubspace(AmbientSpace(M), W);
end intrinsic;

intrinsic EisensteinSubspace(M::ModSS) -> ModSS
    {The Eisenstein subspace of M.}
    if not assigned M`eisenstein_subspace then
	if not IsAmbientSpace(M) then
	    M`eisenstein_subspace := EisensteinSubspace(AmbientSpace(M)) meet M;
	else  // the orthogonal complement of the cuspidal subspace.
	    M`eisenstein_subspace := OrthogonalComplement(CuspidalSubspace(M));
	end if;
    end if;
    return M`eisenstein_subspace;
end intrinsic;


intrinsic CuspidalSubspace(M::ModSS) -> ModSS
    {The cuspidal subspace of M.}
    if not assigned M`cuspidal_subspace then
	if not IsAmbientSpace(M) then
	    M`cuspidal_subspace := CuspidalSubspace(AmbientSpace(M)) meet M;
	else
	    V := RSpace(M);
	    Zero := sub<V | [ V.1 - V.i : i in [2..Dimension(V)]] >;
	    M`cuspidal_subspace := CreateSubspace(M, Zero);
	end if;
    end if;
    return M`cuspidal_subspace;
end intrinsic;

function DecompositionHelper(M, pstart, pstop, Proof)
    assert Type(M) eq ModSS;
    assert Type(pstart) eq RngIntElt;
    assert Type(pstop) eq RngIntElt; 
    assert Type(Proof) eq BoolElt;
    if pstart gt pstop then
	return [M];
    end if;
    p := NextPrime(pstart-1);
    while UsesMestre(M) and AuxiliaryLevel(M) mod p eq 0 do
	print "Skipping p=", p, ".";
	p := NextPrime(p);   
    end while;
    if p gt pstop then
	return [M];
    end if;
    fp := CharacteristicPolynomial(HeckeOperator(M,p) : Al := "Modular", Proof := Proof);
    decomp := [];
    for F in Factorization(fp) do
	Append(~decomp, Kernel([<p, F[1]^F[2]>], M));
    end for; 
    p := NextPrime(p);
    return &cat [DecompositionHelper(Msmall, p, pstop, Proof) : Msmall in decomp];
end function;

intrinsic Decomposition(M::ModSS, stop::RngIntElt : Proof := true) -> SeqEnum
    {Decomposition of M with respect to the Hecke operators T_2, T_3, T_5, ..., T_stop.}
    return DecompositionHelper(M, 2, stop, Proof);
end intrinsic;

function Kernel_helper(M, W, polyprimes)
    for i in [1..#polyprimes] do
	vprint SupersingularModule : "Current dimension = ", Dimension(W);
	p  := polyprimes[i][1];
	f  := polyprimes[i][2];
	t  := Cputime();
	vprintf SupersingularModule: "Computing Ker(f(T_%o))\n", p;
	T  := Restrict(HeckeOperator(M, p), W);
	fT := Evaluate(f,T);
	K  := KernelOn(fT,W);
	W  := W meet K;
	vprintf SupersingularModule: "   (%o seconds.)", Cputime(t);
	if Dimension(W) eq 0 then
	    return W;
	end if;
    end for;
    vprint SupersingularModule : "Current dimension = ", Dimension(W);
    return W;
end function;

intrinsic Kernel(I::[Tup], M::ModSS) -> ModSS
    {The kernel of I on M.  This is the subspace of M obtained 
    by intersecting the kernels of the operators 
    f_n(T_\{p_n\}), where I is a sequence 
    [<p_1, f_1(x)>,...,<p_n,f_n(x)>] of pairs
    consisting of a prime number and a polynomial.}
    if #I eq 0 then
	return M;
    end if;
    exceptional_tp := I;
    p := I[1][1];
    f := I[1][2];
    t := Cputime();
    vprintf SupersingularModule : "Computing Ker(f(T_%o))\n", p;
    fT:= Evaluate(f, HeckeOperator(M,p));
    W := KernelOn(fT,RSpace(M));
    vprintf SupersingularModule : "   (%o seconds.)", Cputime(t);
    W := Kernel_helper(M, W, Remove(I,1));
    return CreateSubspace(M,W);
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                   Structure Arithmetic Functions                   //
////////////////////////////////////////////////////////////////////////

intrinsic 'eq'(M1::ModSS, M2::ModSS) -> BoolElt
    {}
    return Prime(M1) eq Prime(M2) and 
	AuxiliaryLevel(M1) eq AuxiliaryLevel(M2) and
	RSpace(M1) eq RSpace(M2) and
	( (UsesMestre(M1) and UsesMestre(M2)) or
	(UsesBrandt(M1) and UsesBrandt(M2)));
end intrinsic;

intrinsic '+'(M1::ModSS, M2::ModSS) ->  ModSS
    {}
    require AmbientSpace(M1) eq AmbientSpace(M2) :
	"Arguments 1 and 2 must have the same ambient space.";
    return CreateSubspace(AmbientSpace(M1), RSpace(M1) + RSpace(M2));
end intrinsic;    

intrinsic 'subset'(M1::ModSS, M2::ModSS) -> BoolElt
    {}
    return Prime(M1) eq Prime(M2) and 
	AuxiliaryLevel(M1) eq AuxiliaryLevel(M2) and
	RSpace(M1) subset RSpace(M2) and
	( (UsesMestre(M1) and UsesMestre(M2)) or (UsesBrandt(M1) and UsesBrandt(M2)));
end intrinsic;

intrinsic 'meet'(M1::ModSS, M2::ModSS) -> ModSS
    {}
    require AmbientSpace(M1) eq AmbientSpace(M2) :
	"Arguments 1 and 2 must have the same ambient space.";
    return CreateSubspace(AmbientSpace(M1), RSpace(M1) meet RSpace(M2));
end intrinsic;

