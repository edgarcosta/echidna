//////////////////////////////////////////////////////////////////////////////
//                                                                          // 
//  Copyright (C) 2007 David Kohel <kohel@maths.usyd.edu>                   //
//                                                                          //
//  Distributed under the terms of the GNU General Public License (GPL)     //
//                  http://www.gnu.org/licenses/                            //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

function ScaledMinkowskiVector(x,r,s : Precision := 128)
    n := r+2*s;
    S := Conjugates(x : Precision := Precision);
    sq2 := Sqrt(RealField(Universe(S))!2);
    return [ Re(S[k]) : k in [1..r] ] cat &cat[ [ sq2*Re(S[k]), sq2*Im(S[k]) ] : k in [r+1..n by 2] ];
end function;

intrinsic MinkowskiLattice(R::RngOrd : Precision := 128) -> Lat, Map
    {The real lattice L given by the image of R under the Minkowski map, with
    inner product given by the T2-norm on the number field, followed by the
    isomorphism R -> L.}
    require Type(BaseRing(R)) eq RngInt :
	"Base ring of argument must be the integers";
    r, s := Signature(R);
    n := r+2*s;
    L := LatticeWithBasis(Matrix(n,&cat[
	ScaledMinkowskiVector(R!x,r,s : Precision := Precision) : x in Basis(R) ]) );
    return L, hom< R->L | x :-> &+[ S[i]*L.i : i in [1..n] ] where S is Eltseq(x) >;
end intrinsic;

intrinsic MinkowskiLattice(I::RngOrdIdl : Precision := 128) -> Lat, Map
    {The real lattice L given by the image of I under the Minkowski map, with
    inner product given by the T2-norm on the number field, followed by the
    isomorphism I -> L.}
    R := Order(I);
    require Type(BaseRing(R)) eq RngInt : "Base ring of argument must be the integers";
    r, s := Signature(R);
    n := r+2*s;
    L := LatticeWithBasis(Matrix([
	ScaledMinkowskiVector(R!x,r,s : Precision := 128) : x in Basis(I) ]) );
    QQ := RationalField();
    function f(x)
	error if x notin I, "Argument is not in domain";
	return &+[ S[i]*L.i : i in [1..n] ] where S is
	    Eltseq(Solution(MatrixAlgebra(QQ,n)!BasisMatrix(I),Vector(QQ,n,Eltseq(x))));
    end function;
    return L, hom< R->L | x :-> f(x) >;
end intrinsic;

intrinsic MinkowskiLattice(I::RngOrdFracIdl : Precision := 128) -> Lat, Map
    {The real lattice L given by the image of I under the Minkowski map, with
    inner product given by the T2-norm on the number field, followed by the
    isomorphism I -> L.}
    R := Order(I);
    F := FieldOfFractions(R);
    require Type(BaseRing(R)) eq RngInt : "Base ring of argument must be the integers";
    r, s := Signature(R);
    n := r+2*s;
    L := LatticeWithBasis(Matrix([
	ScaledMinkowskiVector(F!x,r,s : Precision := Precision) : x in Basis(I) ]) );
    QQ := RationalField();
    function f(x)
	error if x notin I, "Argument is not in domain";
	return &+[ S[i]*L.i : i in [1..n] ] where S is
	    Eltseq(Solution(MatrixAlgebra(QQ,n)!BasisMatrix(I),Vector(QQ,n,Eltseq(x))));
    end function;
    return L, map< F->L | x :-> f(x) >;
end intrinsic;

intrinsic MinkowskiSpace(F::FldAlg : Precision := 128) -> Lat, Map
    {The Minkowski vector space V of F, as a real vector space, with inner product
    given by the T2-norm on F, followed by the embedding F -> V.}
    require Type(BaseField(F)) eq FldRat :
	"Base field of argument must be the rationals";
    r, s := Signature(F);
    n := r+2*s;
    V := KSpaceWithBasis(Matrix([
	ScaledMinkowskiVector(k,r,s : Precision := Precision) : k in Basis(F) ]) );
    return V, hom< F->V | x :-> &+[ S[i]*V.i : i in [1..n] ] where S is Eltseq(x) >;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

function minkowski_reduction(I,prec)
    SetKantPrecision(Max(GetKantPrecision(),prec));
    O := Order(I);
    K := NumberField(O);
    n := Degree(K); 
    J := I^-1;
    B := Basis(J);
    if IsCMField(K) then
	c := ComplexConjugation(K);
	M := Matrix(n,[ Trace(x*c(y)) : x, y in B ]);
	_, U := MinkowskiGramReduction(M : Canonical);
    else
	L := MinkowskiLattice(J : Precision := prec);
	_, U := LLL(L);
    end if;
    x := &+[ U[1,j]*B[j] : j in [1..n] ];
    return ideal< O | [ x * y : y in Basis(I) ] >, x;
end function;

intrinsic MinkowskiReduction(I::RngOrdIdl : Precision := 128) -> RngOrdIdl, FldOrdElt
    {}
    return minkowski_reduction(I,Precision);
end intrinsic;

intrinsic MinkowskiReduction(I::RngOrdFracIdl : Precision := 128) -> RngOrdIdl, FldOrdElt
    {An reduced ideal in the class of I with minimal (?) norm.}
    return minkowski_reduction(I,Precision);
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

