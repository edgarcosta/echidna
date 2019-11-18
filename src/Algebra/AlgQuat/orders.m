//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//                         Quaternion Orders                                //
//  Copyright (C) 2006 David Kohel <kohel@maths.usyd.edu>                   //
//                                                                          //
//  Distributed under the terms of the GNU General Public License (GPL)     //
//                  http://www.gnu.org/licenses/                            //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

forward IntBasisClosure, PolyBasisClosure;
forward LLLAlgQuat, LLLSeq;

//////////////////////////////////////////////////////////////////////////////
//                       Auxiliary Random Functions                         //
//////////////////////////////////////////////////////////////////////////////

function RandomElement(A,S)
   return A![ Random(S) : i in [1..4] ];
end function;

intrinsic MaximalOrder(K::AlgQuat) -> AlgQuatOrd
    {A maximal quaternion order in K.}
    require Type(BaseField(K)) eq FldRat :
        "Argument must be a quaternion algebra over the rationals.";
    ZZ := Integers();
    V := NormSpace(K);
    N := ZZ!Discriminant(K);
    D := Isqrt(ZZ!Determinant(GramMatrix(V)));
    m := D div N;
    B := Basis(K);
    fact := [ p[1] : p in Factorization(m) ];
    while #fact ne 0 do
	p := fact[1];
	FF := FiniteField(p);
	B1 := Basis(Kernel(
	    Matrix(4,[FF|Trace(x*Conjugate(y)) : x, y in B])));
	if p eq 2 then
	    X := [ &+[ (ZZ!v[i])*B[i] : i in [1..4] ] : v in B1 ];
	    for c in CartesianPower({0,1},#B1) do
		if &or [ c[i] eq 1 : i in [1..#B1] ] then
		    z := &+[ c[i]*X[i] : i in [1..#B1] ];
		    if ZZ!Norm(z) mod 4 eq 0 then
			break c;
		    end if;
		end if;
	    end for;
	elif #B1 eq 1 then
	    z := &+[ (ZZ!B1[1][i])*B[i] : i in [1..4] ];
	else
	    // The inner product of elements in B1 with all other elements
	    // in B1 is divisible by p.  Now we need to solve for a linear
	    // combination z whose norm (i.e. inner product with itself) is
	    // divisible by p^2, so that z/p is integral.
	    X := [ &+[ (ZZ!v[i])*B[i] : i in [1..4] ] : v in B1 ];
	    T := Matrix(#X,
		[ FF | ZZ!(Trace(x*Conjugate(y))/p) : x, y in X ]);
	    B2 := Basis(Kernel(T));
	    if #B2 ne 0 then
		z := &+[ (ZZ!B2[1][i])*X[i] : i in [1..#X] ];
	    elif #B1 eq 2 then
		assert #X eq 2;
		P := PolynomialRing(GF(p));
		f := T[1,1]*P.1^2 + 2*T[1,2]*P.1 + T[2,2];
		z := (ZZ!r)*X[1] + X[2] where r := Roots(f)[1][1];
	    else // T defines Gram matrix of a nonsingular conic
		assert #B1 eq 3;
		assert #X eq 3;
		P2 := ProjectiveSpace(GF(p),2);
		C := Conic(P2,&+[ T[i,j]*P2.i*P2.j : i, j in [1..3] ]);
		s := Eltseq(RationalPoint(C));
		z := &+[ (ZZ!s[i])*X[i] : i in [1..3] ];
	    end if;
	end if;
	B := LLLAlgQuat(B cat [z/p]);
	m div:= p;
	if (m mod p) ne 0 then
	    Exclude(~fact,p);
	end if;
    end while;
    return QuaternionOrder([ K | u*x : x in B ]) where u is B[1]^-1;
end intrinsic;

intrinsic MaximalSuperOrder(A::AlgQuatOrd) -> AlgQuatOrd
    {A maximal quaternion superorder order of A.}
    K := QuaternionAlgebra(A);
    require Type(BaseField(K)) eq FldRat :
        "Argument must be a quaternion order over the integers.";
    //if assigned A`MaximalOrderBasis then
    //	return QuaternionOrder([ K!x : x in A`MaximalOrderBasis ]);
    //end if;
    m := Conductor(A);
    B := Basis(A);
    ZZ := Integers();
    fact := [ p[1] : p in Factorization(m) ];
    while #fact ne 0 do
	p := fact[1];
	FF := FiniteField(p);
	B1 := Basis(Kernel(
	    Matrix(4,[FF|Trace(x*Conjugate(y)) : x, y in B])));
	if p eq 2 then
	    X := [ &+[ (ZZ!v[i])*B[i] : i in [1..4] ] : v in B1 ];
	    for c in CartesianPower({0,1},#B1) do
		if &or [ c[i] eq 1 : i in [1..#B1] ] then
		    z := &+[ c[i]*X[i] : i in [1..#B1] ];
		    if ZZ!Norm(z) mod 4 eq 0 then
			break c;
		    end if;
		end if;
	    end for;
	elif #B1 eq 1 then
	    z := &+[ (ZZ!B1[1][i])*B[i] : i in [1..4] ];
	else
	    // The inner product of elements in B1 with all other elements
	    // in B1 is divisible by p.  Now we need to solve for a linear
	    // combination z whose norm (i.e. inner product with itself) is
	    // divisible by p^2, so that z/p is integral.
	    X := [ &+[ (ZZ!v[i])*B[i] : i in [1..4] ] : v in B1 ];
	    T := Matrix(#X,
		[ FF | ZZ!(Trace(x*Conjugate(y))/p) : x, y in X ]);
	    B2 := Basis(Kernel(T));
	    if #B2 ne 0 then
		z := &+[ (ZZ!B2[1][i])*X[i] : i in [1..#X] ];
	    elif #B1 eq 2 then
		assert #X eq 2;
		P := PolynomialRing(GF(p));
		f := T[1,1]*P.1^2 + 2*T[1,2]*P.1 + T[2,2];
		z := (ZZ!r)*X[1] + X[2] where r := Roots(f)[1][1];
	    else // T defines Gram matrix of a nonsingular conic
		assert #B1 eq 3;
		assert #X eq 3;
		P2 := ProjectiveSpace(GF(p),2);
		C := Conic(P2,&+[ T[i,j]*P2.i*P2.j : i, j in [1..3] ]);
		s := Eltseq(RationalPoint(C));
		z := &+[ (ZZ!s[i])*X[i] : i in [1..3] ];
	    end if;
	end if;
	B := LLLAlgQuat(B cat [z/p]);
	m div:= p;
	if (m mod p) ne 0 then
	    Exclude(~fact,p);
	end if;
    end while;
    O := QuaternionOrder([ K | u*x : x in B ]) where u is B[1]^-1;
    A`MaximalOrderBasis := [ Eltseq(K!x) : x in Basis(O) ];
    return O;
end intrinsic;

intrinsic SuperOrder(A::AlgQuatOrd,m::RngIntElt) -> AlgQuatOrd
    {A maximal quaternion superorder order of A.}
    K := QuaternionAlgebra(A);
    require Type(BaseField(K)) eq FldRat :
        "Argument must be a quaternion order over the integers.";
    if m eq Conductor(A) then
	return MaximalSuperOrder(A);
    end if;
    B := Basis(A);
    ZZ := Integers();
    fact := [ p[1] : p in Factorization(m) ];
    while #fact ne 0 do
	p := fact[1];
	FF := FiniteField(p);
	B1 := Basis(Kernel(
	    Matrix(4,[FF|Trace(x*Conjugate(y)) : x, y in B])));
	if p eq 2 then
	    X := [ &+[ (ZZ!v[i])*B[i] : i in [1..4] ] : v in B1 ];
	    for c in CartesianPower({0,1},#B1) do
		if &or [ c[i] eq 1 : i in [1..#B1] ] then
		    z := &+[ c[i]*X[i] : i in [1..#B1] ];
		    if ZZ!Norm(z) mod 4 eq 0 then
			break c;
		    end if;
		end if;
	    end for;
	elif #B1 eq 1 then
	    z := &+[ (ZZ!B1[1][i])*B[i] : i in [1..4] ];
	else
	    // The inner product of elements in B1 with all other elements
	    // in B1 is divisible by p.  Now we need to solve for a linear
	    // combination z whose norm (i.e. inner product with itself) is
	    // divisible by p^2, so that z/p is integral.
	    X := [ &+[ (ZZ!v[i])*B[i] : i in [1..4] ] : v in B1 ];
	    T := Matrix(#X,
		[ FF | ZZ!(Trace(x*Conjugate(y))/p) : x, y in X ]);
	    B2 := Basis(Kernel(T));
	    if #B2 ne 0 then
		z := &+[ (ZZ!B2[1][i])*X[i] : i in [1..#X] ];
	    elif #B1 eq 2 then
		assert #X eq 2;
		P := PolynomialRing(GF(p));
		f := T[1,1]*P.1^2 + 2*T[1,2]*P.1 + T[2,2];
		z := (ZZ!r)*X[1] + X[2] where r := Roots(f)[1][1];
	    else // T defines Gram matrix of a nonsingular conic
		assert #B1 eq 3;
		assert #X eq 3;
		P2 := ProjectiveSpace(GF(p),2);
		C := Conic(P2,&+[ T[i,j]*P2.i*P2.j : i, j in [1..3] ]);
		s := Eltseq(RationalPoint(C));
		z := &+[ (ZZ!s[i])*X[i] : i in [1..3] ];
	    end if;
	end if;
	B := LLLAlgQuat(B cat [z/p]);
	m div:= p;
	if (m mod p) ne 0 then
	    Exclude(~fact,p);
	end if;
    end while;
    return QuaternionOrder([ K | u*x : x in B ]) where u is B[1]^-1;
end intrinsic;

intrinsic SuperOrders(A::AlgQuatOrd,m::RngIntElt) -> AlgQuatOrd
    {The quaternion superorders containing A with index m.}
    K := QuaternionAlgebra(A);
    M := Conductor(A);
    require Type(BaseField(K)) eq FldRat :
        "Argument must be a quaternion order over the integers.";
    require M mod m eq 0 :
	"Argument 2 must divide conductor of argument 1.";
    ZZ := Integers();
    fact := [ p[1] : p in Factorization(m) ];
    /*
    Quaternion orders are no longer hashable, so we need instead
    to classify them by embedding matrices in order to remove
    redundancies:
    O := QuaternionOrder(-71,-23,1);
    SuperOrders(O,24);
    #{ HermiteForm(RMatrixSpace(ZZ,4,4)!(24*Matrix([ Eltseq(A!x) : x in Basis(S) ]))) : S in B };
    */
    superords := [ A ];
    while #fact ne 0 do
	newsupords := [ ];
	p := fact[1];
	FF := FiniteField(p);
	for R in superords do
	    divelts := [];
	    B := Basis(R);
	    B1 := Basis(Kernel(
		Matrix(4,[FF|Trace(x*Conjugate(y)) : x, y in B])));
	    if p eq 2 then
		X := [ &+[ (ZZ!v[i])*B[i] : i in [1..4] ] : v in B1 ];
		for c in CartesianPower({0,1},#B1) do
		    if &or [ c[i] eq 1 : i in [1..#B1] ] then
			z := &+[ c[i]*X[i] : i in [1..#B1] ];
			if ZZ!Norm(z) mod 4 eq 0 then
			    Append(~divelts,z);
			    // break c;
			end if;
		    end if;
		end for;
	    elif #B1 eq 1 then
		z := &+[ (ZZ!B1[1][i])*B[i] : i in [1..4] ];
		Append(~divelts,z);
	    else
		// The inner product of elements in B1 with all other
		// elements in B1 is divisible by p.  Now we need to
		// solve for a linear combination z whose norm (i.e.
		// inner product with itself) is divisible by p^2, so
		// that z/p is integral.
		X := [ &+[ (ZZ!v[i])*B[i] : i in [1..4] ] : v in B1 ];
		T := Matrix(#X,
		    [ FF | ZZ!(Trace(x*Conjugate(y))/p) : x, y in X ]);
		B2 := Basis(Kernel(T));
		if #B2 ne 0 then
		    PP := RationalPoints(ProjectiveSpace(GF(p),#B2-1));
		    for P in PP do
			z := &+[ ZZ!(P[j]*B2[j][i])*X[i] : i in [1..#X], j in [1..#B2] ];
			Append(~divelts,z);
		    end for;
		elif #B1 eq 2 then
		    assert #X eq 2;
		    P := PolynomialRing(GF(p));
		    f := T[1,1]*P.1^2 + 2*T[1,2]*P.1 + T[2,2];
		    if T[1,1] eq 0 then
		    	Append(~divelts,X[1]);
		    end if;
		    for r in Roots(f) do
			Append(~divelts,(ZZ!r[1])*X[1] + X[2]);
		    end for;
		else // T defines Gram matrix of a nonsingular conic
		    assert #B1 eq 3;
		    assert #X eq 3;
		    P2 := ProjectiveSpace(GF(p),2);
		    C := Conic(P2,&+[ T[i,j]*P2.i*P2.j : i, j in [1..3] ]);
		    for P in RationalPoints(C) do
			z := &+[ (ZZ!P[i])*X[i] : i in [1..3] ];
			Append(~divelts,z);
		    end for;
		end if;
	    end if;
	    for z in divelts do
		bool, O := IsQuaternionOrder([ K | u*x : x in B0 ])
		    where u is B0[1]^-1 where B0 := LLLAlgQuat(B cat [z/p]);
		if bool then
		    Append(~newsupords,O);
		end if;
	    end for;
	end for;
	m div:= p;
	if (m mod p) ne 0 then Exclude(~fact,p); end if;
	superords := newsupords;
    end while;
    return superords;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////

intrinsic IMT(A::AlgQuatOrd,B::AlgQuatOrd) -> AlgQuatOrd
   {}
   // internal intersection function -- called by 'meet'
   K := QuaternionAlgebra(A);
   require QuaternionAlgebra(B) eq K :
      "Orders have different quotient algebras";
   R := BaseRing(A); 
   require Type(R) in {RngInt,RngUPol} : 
      "Base ring is of not of integral type";
   BA := [ K!x : x in Basis(A) ];
   BB := [ K!x : x in Basis(B) ];
   d := LCM([ LCM([ Denominator(a) : a in Eltseq(x) ]) 
      : x in BA cat BB ]);
   M := RSpace(R,4);
   N := sub< M | [ M!Eltseq(d*x) : x in BA ] > meet
        sub< M | [ M!Eltseq(d*x) : x in BB ] >;
   S := LLLAlgQuat( [ (K!Eltseq(x))/d : x in Basis(N) ] ); 
   return QuaternionOrder([ K | S[1]^-1*x : x in S ]);
end intrinsic; 

intrinsic QuaternionOrder(S::[AlgQuatElt] : IsBasis := false) 
    -> AlgQuatOrd
    {Quaternion order generated by S, preserving S if it constitutes
    a basis with initial element 1.}

    A := Universe(S);
    k := BaseField(A); 
    if Type(k) eq FldRat then
	if not IsBasis then
	    test, S := IntBasisClosure(S);
	    require #S eq 4 : "Argument does not generate an order.";  
	    require test : "Argument not closed under multiplication.";  
	    S := [ r*x : x in S ] where r := S[1]^-1; 
	end if;
	R := Integers();
    elif Type(k) eq FldFunRat then
	if not IsBasis then
	    test, S := PolyBasisClosure(S);
	    require #S eq 4 : "Argument does not generate an order.";  
	    require test : "Argument not closed under multiplication.";  
	end if;
	R := PolynomialRing(BaseRing(k));
    else
	require false :
	    "Base ring must be specified for order creation.";
    end if;
    require #S eq 4 : "Argument does not define an order.";
    return QuaternionOrder(R,S);
end intrinsic;

intrinsic IsQuaternionOrder(S::[AlgQuatElt] : IsBasis := false) 
    -> BoolElt, AlgQuatOrd
    {Quaternion order generated by S, preserving S if it constitutes
    a basis with initial element 1.}

    A := Universe(S);
    k := BaseField(A); 
    if Type(k) eq FldRat then
	if not IsBasis then
	    test, S := IntBasisClosure(S);
	    if not test or #S ne 4 then return false, _; end if;
	    S := [ r*x : x in S ] where r := S[1]^-1; 
	end if;
	R := Integers();
    elif Type(k) eq FldFunRat then
	if not IsBasis then
	    test, S := PolyBasisClosure(S);
	    if not test or #S ne 4 then return false, _; end if;
	end if;
	R := PolynomialRing(BaseRing(k));
    else
	return false, _;
    end if;
    if #S ne 4 then return false, _; end if;
    return true, QuaternionOrder(R,S);
end intrinsic;

intrinsic QuaternionOrder(K::AlgQuat,M::RngIntElt) -> AlgQuatOrd
    {Returns a quaternion order of level M in K.}

    require Type(BaseField(K)) eq FldRat :
	"Argument must be quaternion algebra over the rationals."; 
    M := Abs(M);
    N := Integers()!Discriminant(K);
    N1 := GCD(M,N);
    M1 := M div N1;
    O := MaximalOrder(K);
    R := O;
    if N1 ne 1 then
	require Max([ Valuation(M,p) : p in RamifiedPrimes(K) ]) le 1 :
	    "Argument 2 can be divisible by at most " * 
	    "the first power of a ramified prime.";
	P := lideal< R | [ R | N1 ] cat [ x*y-y*x : x,y in Basis(R) ] >;
	R := QuaternionOrder([ K!x : x in Basis(P) ]); 
    end if;
    fact := Factorization(M1);   
    for p in fact do 
	repeat 
	    x := RandomElement(R,[-p[1] div 2..p[1] div 2]);
	    D := Trace(x)^2 - 4*Norm(x);
	until KroneckerSymbol(D,p[1]) eq 1; 
	P := PolynomialRing(FiniteField(p[1])); 
	X := P.1;      
	a := Integers()!Roots(X^2 - Trace(x)*X + Norm(x))[1][1];
	I := lideal< R | [ R | p[1]^p[2], (x-a)^p[2] ]>;
	R := R meet RightOrder(I); 
    end for;
    R`MaximalOrderBasis := [ Eltseq(x) : x in Basis(O) ]; 
    return R;
end intrinsic;

intrinsic QuaternionOrder(N::RngIntElt) -> AlgQuatOrd
    {Returns a maximal order in the rational quaternion algebra
    of discriminant N.}
    prms := PrimeDivisors(N);
    require #prms mod 2 eq 1 : 
        "Argument 1 must be a product of an odd number of primes.";
    require Max([ Valuation(N,p) : p in prms ]) le 1 :
        "Argument 1 can have valuation at most 1 at each prime.";
    return MaximalOrder(QuaternionAlgebra(N));
end intrinsic;

intrinsic QuaternionOrder(S::[RngIntElt]) -> AlgQuatOrd
    {Given a sequence S = [N,M,R], returns a quaternion order of conductor
    MR^3 of the form Z+R*O for an order O of conductor M in the rational
    quaternion algebra of (squarefree) discriminant N.}

    require #S ne 0 and #S le 3 : 
	"Argument 1 must be nonempty sequence of length at most 3.";
    N := S[1];
    M := #S ge 2 select S[2] else 1;
    R := #S eq 3 select S[3] else 1;
    prms := PrimeDivisors(N);
    require #prms mod 2 eq 1 : 
	"Argument 1 must be a product of an odd number of primes.";
    require Max([ Valuation(N,p) : p in prms ]) le 1 :
	"Argument 1 can have valuation at most 1 at each prime.";
    require Max([ Valuation(M,p) : p in prms ]) le 1 :
	"Argument 2 can have valuation at most 1 " * 
	"at each prime divisor of argument 2.";
    O := QuaternionOrder(QuaternionAlgebra(N),M);
    if R ne 1 then
	O := sub< O | [ 1 ] cat [ R*x : x in Basis(O) ] >;
	O`FullLevelIndex := R;
    end if;
    return O;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//                      Coordinates in a given order                        //
//////////////////////////////////////////////////////////////////////////////

intrinsic Coordinates(O::AlgQuatOrd[RngInt],x::AlgQuatOrdElt) -> SeqEnum
    {The coordinates of x in terms of the basis of O.}
    if Parent(x) eq O then
        return Eltseq(x);
    end if;
    bool, x := IsCoercible(O,x);
    require bool : "Argument 2 must be an element of argument 1.";
    return Eltseq(x);
end intrinsic;

intrinsic Coordinates(I::AlgQuatOrdIdl[RngInt],x::AlgQuatElt) -> SeqEnum
    {The coordinates of x in terms of the basis of I.}
    A := QuaternionAlgebra(Order(I));
    require A cmpeq Parent(x) :
        "Argument 2 must be an element of the quaternion algebra of argument 1.";
    U := Matrix([ Eltseq(y) : y in Basis(I) ]);
    v := Vector(Eltseq(x))*U^-1;
    bool, v := CanChangeUniverse(Eltseq(v),IntegerRing());
    require bool : "Argument 2 is not in argument 1.";
    return v;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//                         Some Basis Reduction                             //
//////////////////////////////////////////////////////////////////////////////

function LLLSeq(B)
    // {An LLL reduced basis of the sublattice generated by B.}
    V := Universe(B);
    if Category(V) eq Lat then
	print "LAT";
	return Basis(LLL(sub< V | B >));
    elif Category(V) in { ModTupFld, ModTupRng } then
	N := LLL( Matrix(B) );
	return [ N[i] : i in [1..Rank(N)] ];
    end if;
    error if false, "Invalid universe of argument";
end function;

function LLLAlgQuat(S)
    K := Universe(S);
    error if not Type(BaseRing(K)) eq FldRat,
       "Basis reduction valid only over the integers";
    if IsDefinite(K) then
        L := LatticeWithGram( MatrixAlgebra(BaseField(K),4) !
	    [ Trace(x*Conjugate(y)) : x, y in Basis(K) ] );
	T := [ Eltseq(x) : x in S ];
	n := LCM([ Denominator(a) : a in &cat T ]);
	M := LLL(sub< L | [ L!Eltseq(n*a) : a in S ] >);
	return [ (K!Eltseq(x))/n : x in Basis(M) ];
    else
        V := RSpace(Integers(),4);
        T := &cat[ Eltseq(x) : x in S ];
        n := LCM([ Denominator(a) : a in T ]);
        M := Matrix(4,[ Integers() | n*a : a in T ]);
        U := sub< V | [ M[i] : i in [1..Nrows(M)] ] >;
        one := V![n,0,0,0];
        if one in U and GCD(Coordinates(U,one)) eq 1 then
            W, pi := quo< U | one >;
            B := [ one ] cat [ v@@pi : v in Basis(W) ];
        else
            B := Basis(U);
        end if;
        return [ (K!Eltseq(B[i]))/n : i in [1..Rank(U)] ];
    end if;
end function;

//////////////////////////////////////////////////////////////////////////////

function IntBasisClosure(S)
    // Sequence of elements over the rationals!!!
    A := Universe(S);
    V := KSpace(RationalField(),4);
    if not &or [ x eq A!1 : x in S ] then
	S := [ A!1 ] cat S;
    end if;
    S := LLLAlgQuat(S);
    // Problems if #S > 4 seen...
    if #S lt 4 then
	S := LLLAlgQuat([ x*y : x, y in S ]);
	if #S lt 4 then
	    return false, S;
	end if;
    end if;
    assert #S eq 4;
    M := Matrix([ Eltseq(x) : x in S ]);
    Minv := M^-1;
    k := 1;
    while k lt 4 do
	T := [ (V!Eltseq(x*y))*Minv : x, y in S ];
	bool := &and
	    [ &and[ Denominator(a) eq 1 : a in Eltseq(v) ] : v in T ];
	if bool then
	    return true, S;
	end if;
	S := LLLAlgQuat([ A!Eltseq(v*M) : v in LLLSeq(T) ]);  
	k +:= 1;
    end while;
    return false, S;
end function;

function PolyBasisClosure(S)
    // over k(x)
    A := Universe(S);
    F := BaseField(A);
    k := BaseRing(F);
    error if not IsField(k),
	"Base ring of function field must be a field.";
    M := RSpace(PolynomialRing(k),4);
    if not &or [ x eq A!1 : x in S ] then
	S := [ A!1 ] cat S;
    end if;
    g := F!LCM(&cat[ [ Denominator(a) : a in Eltseq(x) ] : x in S ]);
    T := [ M!Eltseq(g*x) : x in S ];
    S := [ A![ f/g : f in Eltseq(v) ] : v in Basis(sub< M | T >) ]; 
    if #S gt 4 then
	S := [ A![ f/g : f in Eltseq(v) ] : v in Basis(sub< M | T >) ]; 
    elif #S lt 4 then
	S := [ x*y : x, y in S ];
	g := F!LCM(&cat[
	    [ Denominator(a) : a in Eltseq(x) ] : x in S ]);
	T := [ M!Eltseq(g*x) : x in S ];
	S := [ A![ f/g : f in Eltseq(v) ] : v in Basis(sub< M | T >) ];
	if #S lt 4 then return false, S; end if;
    end if;
    V := KSpace(F,4); 
    N := Matrix([ Eltseq(x) : x in S ])^-1;
    k := 1;
    while k le 3 do
	X := [ (V!Eltseq(x*y))*N : x, y in S ];
	bool := &and [ &and [ Denominator(a) eq 1 : 
	    a in Eltseq(v) ] : v in X ];
	if bool then return true, S; end if;
	S := [ x*y : x, y in S ];
	g := F!LCM(&cat[
	    [ Denominator(a) : a in Eltseq(x) ] : x in S ]);
	T := [ M!Eltseq(g*x) : x in S ];
	S := [ A![ f/g : f in Eltseq(v) ] : v in Basis(sub< M | T >) ];
	k +:= 1;
    end while;
    return false, S;
end function;

