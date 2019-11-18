////////////////////////////////////////////////////////////////////////
//                                                                    //
//                           ORTHOGONALITY                            //
//                            David Kohel                             //
//                            April 2000                              //
//                                                                    //
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                       ORTHOGONAL COMPLEMENTS                       //
//                                                                    //
////////////////////////////////////////////////////////////////////////

intrinsic OrthogonalComplement(L::Lat) -> Lat
    {}
    A := LatticeWithGram(InnerProductMatrix(L));
    require L subset A :
	"Argument must be contained in its ambient lattice.";
    if Dimension(L) eq 0 then return A; end if;
    K := Kernel(Transpose(BasisMatrix(L)*InnerProductMatrix(L)));
    return sub< A | Basis(K) >;
end intrinsic;

intrinsic OrthogonalComplement(x::LatElt) -> Lat
    {}
    L := Parent(x);
    if x eq 0 then return L; end if;
    K := Kernel(Matrix(1,Eltseq(x*InnerProductMatrix(L))));
    return sub< L | Basis(K) >;
end intrinsic;

intrinsic OrthogonalComplement(S::[LatElt]) -> Lat
    {Lattice orthogonal to the given vector, vector sequence, or subspace.}
    L := Universe(S);
    N := sub< L | S >;
    if Dimension(N) eq 0 then return L; end if;
    K := Kernel(Transpose(BasisMatrix(N)*InnerProductMatrix(N)));
    return sub< L | Basis(K) >;
end intrinsic;

intrinsic OrthogonalComplement(L::Lat) -> Lat
    {}
    A := LatticeWithGram(InnerProductMatrix(L));
    require L subset A :
	"Argument must be contained in its ambient lattice.";
    if Dimension(L) eq 0 then return A; end if;
    K := Kernel(Transpose(BasisMatrix(L)*InnerProductMatrix(L)));
    return sub< A | Basis(K) >;
end intrinsic;

intrinsic OrthogonalComplement(U::ModTupRng) -> ModTupRng
    {}
    if Dimension(U) eq 0 then return Generic(U); end if;
    K := Kernel(Transpose(BasisMatrix(U)*InnerProductMatrix(U)));
    return sub< Generic(U) | Basis(K) >;
end intrinsic;

intrinsic OrthogonalComplement(u::ModTupRngElt) -> ModTupRng
    {}
    U := Parent(u);
    if u eq 0 then return Generic(U); end if;
    M := InnerProductMatrix(U);
    return U meet
	sub< Generic(U) | Basis(Kernel(Matrix(1,Eltseq(u*M)))) >;
end intrinsic;

intrinsic OrthogonalComplement(S::[ModTupRngElt]) -> ModTupRng
    {Space orthogonal to the given vector, vector sequence, or subspace.}
    return OrthogonalComplement(sub< Universe(S) | S >);
end intrinsic;

intrinsic OrthogonalComplement(V::ModTupRng,U::ModTupRng) -> ModTupRng
    {}
    return V meet OrthogonalComplement(U);
end intrinsic;

intrinsic OrthogonalComplement(V::ModTupRng,u::ModTupRngElt) -> ModTupRng
    {}
    require u in Generic(V) : "Incompatible arguments";
    return V meet OrthogonalComplement(u);
end intrinsic;

intrinsic OrthogonalComplement(V::ModTupRng,S::[ModTupRngElt]) -> ModTupRng
    {Subspace of V orthogonal to the second argument.}
    require Generic(Universe(S)) eq Generic(V) : "Incompatible arguments";
    return V meet OrthogonalComplement(S);
end intrinsic;

