//////////////////////////////////////////////////////////////////////////////
//                                                                          // 
//               Ramified Primes and Discriminant Sequences                 //
//  Copyright (C) 2000 David Kohel <kohel@maths.usyd.edu>                   //
//                                                                          //
//  Distributed under the terms of the GNU General Public License (GPL)     //
//                  http://www.gnu.org/licenses/                            //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

intrinsic IsRamified(K::AlgQuat,p::RngIntElt) -> BoolElt
   {True if and only if p is a ramified prime in K, where K 
   must be a quaternion algebra over the rationals.}
   require IsPrime(p) : "Argument 2 must be prime.";
   return p in RamifiedPrimes(K);
end intrinsic;

intrinsic IsDefinite(K::AlgQuat) -> BoolElt
   {True if and only if K is ramified at infinity, where K 
   must be a quaternion algebra over the rationals.}
   return (#RamifiedPrimes(K) mod 2) eq 1; 
end intrinsic;
 
intrinsic IsIndefinite(K::AlgQuat) -> BoolElt
   {True if and only if K is split at infinity, where K 
   must be a quaternion algebra over the rationals.}
   return (#RamifiedPrimes(K) mod 2) eq 0; 
end intrinsic;
 
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

intrinsic Conductor(A::AlgQuatOrd) -> RngIntElt
    {The conductor of the quaternion order, defined to be the index in
    a maximal order of its quaternion algebra.}
    require Type(BaseRing(A)) eq RngInt :
        "Argument must be defined over the integers.";
    return Level(A);
end intrinsic;

intrinsic LevelIndices(A::AlgQuatOrd) -> RngIntElt
    {}
    require BaseRing(A) cmpeq Integers():  //and Norm(A) eq 1 : 
	"Argument must be an order over the integers.";
    D := Discriminant(A);
    if assigned A`FullLevelIndex then
	M := Conductor(A);
	R := A`FullLevelIndex;
    else
	O := MaximalSuperOrder(A);
	G := quo< AbelianGroup([0,0,0,0]) |
	    [ Eltseq(O!x) : x in Basis(A) ] >;
	I := AbelianInvariants(G);
	if #I eq 0 then
	    M := 1; R := 1;
	elif #I le 2 then
	    M := &*I; R := 1;
	elif #I eq 3 then
	    M := &*I; R := GCD(I);
	end if;
	A`FullLevelIndex := R;
    end if;
    return [ D, M div R^3, R ];
end intrinsic;

intrinsic FullLevelIndex(A::AlgQuatOrd) -> RngIntElt
    {}
    if not assigned A`FullLevelIndex then
	I := LevelIndices(A);
	A`FullLevelIndex := I[3];
    end if;
    return A`FullLevelIndex;
end intrinsic;

/////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////

intrinsic RamifiedPrimes(a::RngIntElt,b::RngIntElt :
    MakeSquareFree := true) -> SeqEnum
    {}
    if MakeSquareFree then  
        a := SquareFree(a); b := SquareFree(b);
    end if;
    vprintf Quaternion : "RamifiedPrimes(%o,%o):\n", a, b;
    if &or [ IsSquare(x) : x in {a,b,a+b} ] then
        return [ Integers() | ];
    end if;
    c := GCD(a,b);
    if c ne 1 then
        p := Factorization(c)[1][1];
        vprint Quaternion : "";
        prms := RamifiedPrimes(p,-(b div p))
            cat RamifiedPrimes(a div p,b);
        return Sort( [ p : p in { x : x in prms } |
            (#[ i : i in [1..#prms] | prms[i] eq p ] mod 2) eq 1 ] );
    end if;
    prms := [ Integers() | ];
    S1 := PrimeDivisors(a);
    vprint Quaternion : "  S1 =", S1;
    for p in S1 do
        vprint Quaternion : "  p =", p;
        if p eq 2 and (b mod 4) eq 3 then
            vprintf Quaternion :
                "    Case p = 2 and b = %o == 3 mod 4\n", b;
            if KroneckerSymbol(a+b,p) eq -1 then
                vprintf Quaternion :
                    "    (a+b,p) = (%o,%o) = -1", a+b, p;
                vprintf Quaternion : " appending p = %o\n", p;
                Append(~prms,p);
            end if;
        elif KroneckerSymbol(b,p) eq -1 then
            vprintf Quaternion :
                "    Case p ne 2 or b = %o == 1 mod 4\n", b;
            vprintf Quaternion : "      (b,p) = (%o,%o) = -1", b, p;
            vprintf Quaternion : " appending p = %o\n", p;
	    Append(~prms,p);
	end if;
    end for;
    S2 := PrimeDivisors(b);
    vprint Quaternion : "  S2 =", S2;
    for q in S2 do
	vprint Quaternion : "  q =", q;
	if q eq 2 and (a mod 4) eq 3 then
	    vprintf Quaternion :
		"    Case q = 2 and a = %o == 3 mod 4\n", a;
	    if KroneckerSymbol(a+b,q) eq -1 then
		vprintf Quaternion :
		    "      (a+b,q) = (%o,%o) = -1", a+b, q;
		vprintf Quaternion : " appending q = %o\n", q;
		Append(~prms,q);
	    end if;
	elif KroneckerSymbol(a,q) eq -1 then
	    vprintf Quaternion :
		"    Case q ne 2 or a = %o == 1 mod 4\n", a;
	    vprintf Quaternion : "      (a,q) = (%o,%o) = -1", a, q;
	    vprintf Quaternion : " appending q = %o\n", q;
	    Append(~prms,q);
	end if;
    end for;
    if 2 notin prms and (a mod 4) eq 3 and (b mod 4) eq 3 then
	vprint Quaternion : "  r = 2";
	vprintf Quaternion : "    Case a = %o == 3 mod 4", a;
	vprintf Quaternion : "       and b = %o == 3 mod 4;", b;
	vprintf Quaternion : " appending p = 2\n";
	Append(~prms,2);
    end if;
    vprint Quaternion : "  Returning ", prms;
    vprint Quaternion : "";
    return Sort(prms);
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//                        Discriminant Functionality                        //
//////////////////////////////////////////////////////////////////////////////

function MatrixMinor(M,I,J)
    return Matrix([ [ M[i,j] : j in J ] : i in I ]);
end function;

intrinsic DiscriminantSequence(O::AlgQuatOrd) -> SeqEnum 
    {The sequence of 2x2 minors of the norm form on O with respect
    to a reduced basis for O.}   
    require Type(BaseRing(O)) eq RngInt : 
	"Argument must be an order over the integers.";
    if IsDefinite(QuaternionAlgebra(O)) then
	M := ReducedGramMatrix(O);
    else
	M := GramMatrix(O);
    end if;
    S := [ [2,2], [3,3], [4,4], [2,3], [2,4], [3,4] ];
    return [ (MatrixMinor(M,[1,X[1]],[1,X[2]])) : X in S ];
    return [ Determinant(MatrixMinor(M,[1,X[1]],[1,X[2]])) : X in S ];
end intrinsic;

intrinsic DiscriminantSequence(B::[AlgQuatOrdElt]) -> SeqEnum 
    {The sequence of 2x2 minors of the norm form on the sequence
    of elements of B.}   
    M := Matrix(4,[ Norm(x+y)-Norm(x)-Norm(y) : x, y in B ]);
    S := [ [2,2], [3,3], [4,4], [2,3], [2,4], [3,4] ];
    return [ Determinant(MatrixMinor(M,[1,X[1]],[1,X[2]])) : X in S ];
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//                  Constructor from Discriminant Data                      //
//////////////////////////////////////////////////////////////////////////////

intrinsic QuaternionOrderWithGram(M::AlgMatElt) -> AlgQuatOrd 
    {A quaternion order in an algebra over Q with norm Gram matrix M.}
    require BaseRing(Parent(M)) cmpeq Integers() :
	"Argument must be a matrix over the integers.";
    D1 := Determinant(MatrixMinor(M,[1,2],[1,2]));
    D2 := Determinant(MatrixMinor(M,[1,3],[1,3]));
    D3 := Determinant(MatrixMinor(M,[1,4],[1,4]));
    T1 := Determinant(MatrixMinor(M,[1,2],[1,3]));
    t1 := M[1,2]; t2 := M[1,3]; t3 := M[1,4];
    K := QuaternionAlgebra(-D1,-D2,-T1);
    B := Basis(K);
    B[2] +:= K!(t1-(D1 mod 2))/2;
    B[3] +:= K!(t2-(D2 mod 2))/2;
    M0 := Matrix(4,[Norm(x+y)-Norm(x)-Norm(y) : x, y in B ]);
    MQ := MatrixAlgebra(RationalField(),4)!M;
    w0 := Vector([ MQ[1,4], MQ[2,4], MQ[3,4] ]); 
    v0, V0 := Solution(Submatrix(M0,1,1,4,3),w0);
    v1 := Basis(V0)[1];
    a := InnerProduct(v1*M0,v1);
    b := InnerProduct(v1*M0,v0);
    c := InnerProduct(v0*M0,v0);
    f0 := a*X^2 + 2*b*X + c - M[4,4]
	where X := PolynomialRing(RationalField()).1;
    if f0 ne 0 then
	v0 +:= Roots(f0)[1][1]*v1;
    end if;
    B[4] := &+[ v0[i]*B[i] : i in [1..4] ];
    return QuaternionOrder(B);
end intrinsic;

