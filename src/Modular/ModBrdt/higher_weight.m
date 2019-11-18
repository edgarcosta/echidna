////////////////////////////////////////////////////////////////////////
//                                                                    //
//                    Higher Weight Brandt Modules                    //
//                            David Kohel                             //
//                                                                    //
////////////////////////////////////////////////////////////////////////

import "brandt_modules.m" : NormGrams;

////////////////////////////////////////////////////////////////////////
//                                                                    //
////////////////////////////////////////////////////////////////////////

function OrthogonalBasis(H,B1)
    V := NormSpace(H);
    U1 := sub< V | [ V!Eltseq(x) : x in B1 ] >;
    U2 := OrthogonalComplement(V, U1);
    B2 := Basis(U2);
    d2 := [ LCM([ Denominator(a) : a in Eltseq(x) ]) : x in B2 ];
    return B1 cat [ H | d2[i]*B2[i] : i in [1..#B2] ];
end function;

function OrthogonalVector(H,B1)
    V := NormSpace(H);
    U1 := sub< V | [ V!Eltseq(x) : x in B1 ] >;
    U2 := OrthogonalComplement(V, U1);
    u := U2.1;
    return H!(LCM([ Denominator(a) : a in Eltseq(u) ])*u);
end function;

intrinsic MatrixRepresentation(H::AlgQuat) -> AlgMatElt
    {}

    f := MinimalPolynomial(H.1);
    K := NumberField(f);
    conj := func< x | Trace(x) - x >;
    B1 := [ H!1, H.1 ];
    u := OrthogonalVector(H,B1);
    B := B1 cat [ u, H.1*u ];
    M := Matrix(4,4,&cat[ Eltseq(x) : x in B ])^-1;
    VQ := VectorSpace(RationalField(),4);
    CK := CartesianPower(K,2);
    pi := hom< H -> CK | x :-> <K!v[1..2],K!v[3..4]> 
    where v := Eltseq((VQ!Eltseq(x))*M) >; 
    M2K := MatrixAlgebra(K,2);
    n := Norm(B[3]);
    return hom< H -> M2K | 
    x :-> M2K ! [ v[1], v[2], -n*conj(v[2]), conj(v[1]) ] where v := pi(x) >;
end intrinsic;

intrinsic MatrixRepresentation(H::AlgQuat,r::RngIntElt) -> AlgMatElt
    {}
    h := MatrixRepresentation(H);
    K := BaseRing(Codomain(h));
    P4<x1,x2,x3,x4> := PolynomialRing(K,4);
    MSP := MatrixAlgebra(P4,2);
    B := Basis(H);
    X := [ MSP!P4.i : i in [1..4] ];
    M := &+[ (MSP!Eltseq(h(B[i])))*X[i] : i in [1..4] ];
    P<X,Y> := PolynomialRing(P4,2);
    SymMons := [ X^(r-i)*Y^i : i in [0..r] ];
    ImgMons := [ Evaluate(mj, 
        [ M[1,1]*X+M[1,2]*Y, 
        M[2,1]*X + M[2,2]*Y ]) : mj in SymMons ];
    MP := MatrixAlgebra(P4,r+1) ! &cat [ 
        [ MonomialCoefficient(mi,mj) : mj in SymMons ] : mi in ImgMons ];
    MK := MatrixAlgebra(K,r+1);
    return hom< H -> MK | 
    x :-> MK![ Evaluate(mij,c) : mij in Eltseq(MP) ] 
        where c := Eltseq(x) >;
end intrinsic;

intrinsic ThetaSeries(f::RngMPolElt,L::Lat : Precision := 100)
    -> RngSerElt {}
    require Rank(Parent(f)) eq 4 : "Bad";
    K := BaseRing(Parent(f));
    P<q> := LaurentSeriesRing(K);
    s := 2;
    b1 := Ceiling(s*Sqrt(Precision)/Norm(L.1));
    b2 := Ceiling(s*Sqrt(Precision)/Norm(L.2));
    b3 := Ceiling(s*Sqrt(Precision)/Norm(L.3));
    b4 := Ceiling(s*Sqrt(Precision)/Norm(L.4));
    // printf "b1 = %o, b2 = %o, b3 = %o, b4 = %o\n", b1, b2, b3, b4;
    return &+[ Evaluate(f,[x1,x2,x3,x4]) * q^Norm(L![x1,x2,x3,x4]) 
        : x1 in [-b1..b1], x2 in [-b2..b2], 
        x3 in [-b3..b3], x4 in [-b4..b4] ] + O(q^(Precision+1));
end intrinsic;

intrinsic SphericalMatrix(H::AlgQuat,r::RngIntElt) -> AlgMatElt
    {}
    h := MatrixRepresentation(H);
    K := BaseRing(Codomain(h));
    P4<x1,x2,x3,x4> := PolynomialRing(K,4);
    MSP := MatrixAlgebra(P4,2);
    B := Basis(H);
    X := [ MSP!P4.i : i in [1..4] ];
    M := &+[ (MSP!Eltseq(h(B[i])))*X[i] : i in [1..4] ];
    P<X,Y> := PolynomialRing(P4,2);
    SymMons := [ X^(r-i)*Y^i : i in [0..r] ];
    ImgMons := [ Evaluate(mj, 
        [ M[1,1]*X+M[1,2]*Y, 
        M[2,1]*X + M[2,2]*Y ]) : mj in SymMons ];
    return MatrixAlgebra(P4,r+1) ! &cat [ 
        [ MonomialCoefficient(mi,mj) : mj in SymMons ] : mi in ImgMons ];
end intrinsic;

intrinsic BrandtModule(G::SymAlgQuat,R::RngOrd,r::RngIntElt) 
    -> ModBrdt {} 
    require r mod 2 eq 0 and r ge 2 : 
        "Argument 3 must be even and positive.";
    A := Order(G,1);
    M := New(ModBrdt);
    M`IsFull := true;
    M`BaseRing := R;
    M`Degree := r;
    M`RamifiedPrimes := RamifiedPrimes(QuaternionAlgebra(A));
    M`Conductor := Level(A);
    M`FullLevelIndex := LevelIndices(A)[3];
    M`NormGrams, M`AutoNums := NormGrams(A);
    M`ThetaPrecision := 0;
    M`ThetaSeries := [ LaurentSeriesRing(R) | ];
    M`HeckePrimes := [ Integers() | ];
    h := (#M`AutoNums)*(r+1);
    MatR := MatrixAlgebra(R,h);
    M`HeckeOperators := [ MatR | ];
    M`Module := RSpace(R,h);
    M`DecompositionIdeal := {@ @};
    return M;
end intrinsic;

intrinsic Weight(M::ModBrdt) -> RngIntElt
    {}
    return 2;
end intrinsic;
