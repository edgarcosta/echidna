////////////////////////////////////////////////////////////////////////
//                                                                    //
//                         Creation functions                         //
//                                                                    //
////////////////////////////////////////////////////////////////////////

import "decomposition.m": Submodule;

intrinsic MonodromyWeights(M::ModBrdt) -> SeqEnum
    {}
    return [ e div 2 : e in A`AutoNums ] where A := AmbientModule(M);
end intrinsic;

////////////////////////////////////////////////////////////////////////

intrinsic OrthogonalComplement(N::ModBrdt) -> ModBrdt
    {}
    U := OrthogonalComplement(N`Module);
    return Submodule(AmbientModule(N),Basis(U));
end intrinsic;

intrinsic OrthogonalComplement(M::ModBrdt,S::[ModBrdt]) -> ModBrdt
    {}
    if #S eq 0 then return M; end if;
    U := M`Module;
    for N in S do
	require AmbientModule(N) eq AmbientModule(M) :
	    "Argument 2 must consist of submodules " *
	    "in the ambient module of argument 1.";
	U := OrthogonalComplement(U,U meet N`Module);
    end for;
    return Submodule(M,Basis(U));
end intrinsic;

intrinsic OrthogonalComplement(M::ModBrdt,S::[ModBrdtElt]) -> ModBrdt
    {The orthogonal complement to N or the sequence S inside
    of a common ambient space M.}
    if #S eq 0 then return M; end if;
    U := M`Module;
    require AmbientModule(Universe(S)) eq AmbientModule(M) :
	"Argument 2 must consist of elements " *
	"in the ambient module of argument 1.";
    V := sub< AmbientModule(M)`Module | [ Eltseq(v) : v in S ] >;
    U := OrthogonalComplement(U,U meet V);
    return Submodule(M,Basis(U));
end intrinsic;

////////////////////////////////////////////////////////////////////////

intrinsic CongruenceGroup(N::ModBrdt) -> GrpAb
    {}
    X := CuspidalSubspace(AmbientModule(N));
    require N subset X : "Argument must be a cuspidal module.";
    P := OrthogonalComplement(N) meet X;
    Q, m := quo< X`Module | N`Module + P`Module >;
    A := AbelianGroup(Moduli(Q)); 
    return A, map< X->A | x :-> A!Eltseq(m(x`Element)) >;
end intrinsic;

intrinsic CongruenceGroup(X::ModBrdt,N::ModBrdt) -> GrpAb
    {The congruence group of N in X, i.e. group X/(N+N^*);
    if not specified then X is the ambient cuspidal module.}
    require N subset X : "Argument 2 must be a submodule of argument 1";
    P := OrthogonalComplement(N) meet X;
    Q, m := quo< X`Module | N`Module + P`Module >;
    A := AbelianGroup(Moduli(Q)); 
    return A, map< X->A | x :-> A!Eltseq(m(x`Element)) >;
end intrinsic;

////////////////////////////////////////////////////////////////////////

intrinsic ComponentGroup(N::ModBrdt) -> GrpAb
    {}
    R := BaseRing(N);
    require R cmpeq Integers() : 
	"Argument must be defined over the integers.";
    require IsCuspidal(N) : "Argument must be a cuspidal space.";
    if Dimension(N) eq 0 then return AbelianGroup([]); end if;
    M := Lattice(CuspidalSubspace(AmbientModule(N)));
    n := Dimension(N);
    L := Lattice(N);
    Lstar := Dual(L);
    U := Matrix(
	[ [ R | InnerProduct(u,v) : u in Basis(L) ] : v in Basis(Lstar) ])^-1;
    imgs := [ Vector(
	[ R | InnerProduct(u,v) : u in Basis(L) ])*U : v in Basis(M) ];
    XimgL := sub< Lstar |
	[ &+[ w[i]*Lstar.i : i in [1..n] ] : w in imgs ] >;
    return A, B where A := Lstar/XimgL where B := XimgL/L;
end intrinsic;

intrinsic ComponentGroup(X::ModBrdt,N::ModBrdt) -> GrpAb
    {The component group of an optimal quotient of X isogenous to N;
    if not specified then X is the ambient cuspidal module.}
    R := BaseRing(N);
    require R cmpeq Integers() : 
	"Argument must be defined over the integers.";
    require IsCuspidal(X) : "Argument must be a cuspidal space.";
    require N subset X :
	"Argument 2 must be a submodule of argument 1";
    if Dimension(X) eq 0 then return AbelianGroup([]); end if;
    n := Dimension(N);
    L := Lattice(N);
    Lstar := Dual(L);
    M := Lattice(X);
    U := Matrix(
	[ [ R | InnerProduct(u,v) : u in Basis(L) ] : v in Basis(Lstar) ])^-1;
    imgs := [ Vector(
	[ R | InnerProduct(u,v) : u in Basis(L) ])*U : v in Basis(M) ];
    XimgL := sub< Lstar |
	[ &+[ w[i]*Lstar.i : i in [1..n] ] : w in imgs ] >;
    return A, B where A := Lstar/XimgL where B := XimgL/L;
end intrinsic;

////////////////////////////////////////////////////////////////////////

intrinsic qExpansionCongruenceGroup(M::ModBrdt,n::RngIntElt) -> GrpAb
    {The subgroup measuring congruences of the q-expansion basis
    to precision n in its saturation.}
    require BaseRing(M) cmpeq Integers() :
	"Argument 1 must be defined over the integers.";
    require IsCuspidal(M) : "Argument must be cuspidal.";
    if Dimension(M) eq 0 then return AbelianGroup([]); end if;
    B := qExpansionBasis(M,n+1);
    S := [ [ Integers() | Coefficient(f,i) : i in [0..n-1] ] :  f in B ];
    D := SmithForm(Matrix(S));
    return AbelianGroup([ D[i,i] : i in [1..Min(#B,n)] | D[i,i] gt 1 ]);
end intrinsic;
