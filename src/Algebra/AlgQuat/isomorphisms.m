//////////////////////////////////////////////////////////////////////////////
//                                                                          // 
//                      ISOMORPHISM OF QUATERNIONS                          //
//                  -- ALGEBRAS, ORDERS, AND IDEALS --                      //
//  Copyright (C) 2001 David Kohel <kohel@maths.usyd.edu>                   //
//                                                                          //
//  Distributed under the terms of the GNU General Public License (GPL)     //
//                  http://www.gnu.org/licenses/                            //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

//////////////////////////////////////////////////////////////////////////////
//                     Isomorphism testing of Algebras                      //
//////////////////////////////////////////////////////////////////////////////

intrinsic IsIsomorphic(K::AlgQuat,L::AlgQuat : Isomorphism := false) -> BoolElt, Map
    {True if K is isomorphic to L.}
    require {Type(BaseField(K)), Type(BaseField(L))} eq {FldRat} :
	"Base field of arguments must be the rationals.";
    if not Isomorphism then
	return Discriminant(K) eq Discriminant(L);
    end if;
    PP := ProjectiveSpace(Rationals(),2);
    BK := Basis(K)[[2..4]];
    TK := [ Trace(x)/2 : x in BK ];
    XK := [ BK[i] - TK[i] : i in [1..3] ];
    fK := &+[ Trace(Conjugate(XK[i])*XK[j])*PP.i*PP.j : i, j in [1..3] ];
    CK := Conic(PP,fK);
    BL := Basis(L)[[2..4]];
    TL := [ Trace(x)/2 : x in BL ];
    XL := [ BL[i] - TL[i] : i in [1..3] ];
    fL := &+[ Trace(Conjugate(XL[i])*XL[j])*PP.i*PP.j : i, j in [1..3] ];
    CL := Conic(PP,fL);
    vprint Quaternion, 2 : "  Finding isomorphism of conics.";
    bool, m := IsIsomorphic(CK,CL);
    if not bool then
	print "Failed to find isomorphism between conics:";
	PP<X,Y,Z> := PP;
	print CK;
	print CL;
	assert false;
    end if;
    vprint Quaternion, 2 : "  Found isomorphism of conics.";
    c := Rationals()!(Evaluate(fL,DefiningPolynomials(m))/fK);
    issq, a := IsSquare(c); assert issq;
    polys := DefiningPolynomials(m);
    M0 := Matrix([[
	MonomialCoefficient(f,PP.i)/a : i in [1..3] ] : f in polys ]);
    UK := Matrix([[1,0,0,0],[-TK[1],1,0,0],[-TK[2],0,1,0],[-TK[3],0,0,1]]);
    UL := Matrix([[1,0,0,0],[-TL[1],1,0,0],[-TL[2],0,1,0],[-TL[3],0,0,1]]);
    QQ := Rationals();
    M1 := VerticalJoin(Matrix(4,[QQ|1,0,0,0]),
	HorizontalJoin(Matrix(1,[QQ|0,0,0]),M0));
    return bool, hom< K->L | UK^-1*Transpose(M1)*UL >;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//                  Isomorphism testing of Orders and Ideals                //
//////////////////////////////////////////////////////////////////////////////

intrinsic IsIsomorphic(A::AlgQuatOrd,B::AlgQuatOrd) -> BoolElt, Map
    {True if and only if A and B are isomorphic as algebras.}
    
    K := QuaternionAlgebra(A);
    require K cmpeq QuaternionAlgebra(B) : 
	"Arguments must be orders in the same algebra.";
    require Type(BaseRing(A)) eq RngInt :
	"Arguments must be orders in a quaternion algebra over Q.";
    require IsDefinite(K) :
	"Arguments must be orders in a definite quaternion algebra.";
    MA := ReducedGramMatrix(A);
    MB := ReducedGramMatrix(B);
    // This requires that the corresponding reduced Gram matrices 
    // are reduced to a canonical representative!!!
    val := MA eq MB;
    // Returning the isomorphism gives a small overhead; this would
    // be minimized by putting this in the kernel and checking whether 
    // a second argument is asked for.  Here we omit this step and 
    // just return the boolean value.
    return val; 
    if val then
	h, t := Isomorphism(A,B);
	return val, h, t;
    end if;
    return false, _, _;
end intrinsic;

intrinsic IsLeftIsomorphic(I::AlgQuatOrd,J::AlgQuatOrd) -> BoolElt
    {True if and only if I is isomorphic to J as an ideal over a 
    common left order.}
    
    K := QuaternionAlgebra(I);
    require K cmpeq QuaternionAlgebra(J) : 
	"Arguments must be ideals in the same algebra.";
    require Type(BaseRing(I)) eq RngInt :
	"Arguments must be ideals in a quaternion algebra over Q.";
    require IsDefinite(K) :
	"Arguments must be ideals in a definite quaternion algebra.";
    require LeftOrder(I) eq LeftOrder(J) : 
	"Arguments must have the same left order.";
    if Norm(J)*ReducedGramMatrix(I) ne Norm(I)*ReducedGramMatrix(J) then
	return false, _, _;
    end if;
    MA := ReducedGramMatrix(RightOrder(I));
    IJ := Conjugate(I)*J;
    MIJ := ReducedGramMatrix(IJ);
    val := MIJ eq Norm(I)*Norm(J)*MA;
    if val then
	t := ReducedBasis(IJ)[1]/Norm(I);
	Q := [ x*t : x in Basis(I) ];
	h := hom< I -> J | x :-> &+[ x[i]*Q[i] : i in [1..4] ] >;
	return true, h, t;
    end if;
    return false, _, _;
end intrinsic;

intrinsic IsRightIsomorphic(I::AlgQuatOrd,J::AlgQuatOrd) -> BoolElt
    {True if and only if I is isomorphic to J as an ideal over a 
    common right order.}
    
    K := QuaternionAlgebra(I);
    require K cmpeq QuaternionAlgebra(J) : 
	"Arguments must be ideals in the same algebra.";
    require Type(BaseRing(I)) eq RngInt :
	"Arguments must be ideals in a quaternion algebra over Q.";
    require IsDefinite(K) :
	"Arguments must be ideals in a definite quaternion algebra.";
    require RightOrder(I) eq RightOrder(J) : 
	"Arguments must have the same right order.";
    if Norm(J)*ReducedGramMatrix(I) ne Norm(I)*ReducedGramMatrix(J) then
	return false, _, _;
    end if;
    MA := ReducedGramMatrix(LeftOrder(I));
    IJ := I*Conjugate(J);
    MIJ := ReducedGramMatrix(IJ);
    val := MIJ eq Norm(I)*Norm(J)*MA;
    if val then
	t := ReducedBasis(IJ)[1]/Norm(I);
	Q := [ t*x : x in Basis(I) ];
	h := hom< I -> J | x :-> &+[ x[i]*Q[i] : i in [1..4] ] >;
	return true, h, t;
    end if;
    return false, _, _;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//                             Isomorphisms                                 //
//////////////////////////////////////////////////////////////////////////////

intrinsic Isomorphism(A::AlgQuatOrd,B::AlgQuatOrd) -> Map
    {}
    K := QuaternionAlgebra(A);
    require K eq QuaternionAlgebra(B) : 
	"Arguments must be orders in the same algebra.";
    L := LatticeWithGram(GramMatrix(A));
    M := LatticeWithGram(GramMatrix(B));
    val, T := IsIsometric(L,M);
    require val : "Arguments must be isomorphic.";
    Q := [ A!Eltseq(T[i]) : i in [1..4] ];
    // Ensure that 1 :-> 1.
    uB := Eltseq(B!1);
    uA := &+[ uB[i]*Q[i] : i in [1..4] ];
    if uA ne 1 then
	vprintf QuaternionIsomorphism : 
	    "Lattice isometry off by unit u = %o of argument 1.\n", Q[1];
	vprint QuaternionIsomorphism : 
	    "MinimalPolynomial(u) =", MinimalPolynomial(Q[1]);
	Q := [ uA*x : x in Q ];
	T := Matrix(4,&cat[ Eltseq(x) : x in Q ]);
    end if;
    S := T^-1;
    print "S =", S;
    P := [ B!Eltseq(S[i]) : i in [1..4] ];
    print "P =", P;
    print "Universe(P) =", Universe(P);
    U := BasisMatrix(A)^-1*S*BasisMatrix(B);
    print "U =", U;
    h := hom< A->B |
	x :-> &+[ x[i]*P[i] : i in [1..4] ],
	y :-> &+[ y[i]*Q[i] : i in [1..4] ] >;
    print "Images:", [ h(x) : x in Basis(A) ];
    // Ensure that h is a homomorphism, not an anti-homomorphism.
    if h(A.1)*h(A.2) ne h(A.1*A.2) then
	vprint QuaternionIsomorphism :
	    "Isometry not an isomorphism, taking conjugates.";
	Q := [ Conjugate(x) : x in Q ];
	T := Matrix(4,&cat[ Eltseq(x) : x in Q ]);
	S := T^-1;
	P := [ B!Eltseq(S[i]) : i in [1..4] ];
	h := hom< A->B |
	    x :-> &+[ x[i]*P[i] : i in [1..4] ], 
	    y :-> &+[ y[i]*Q[i] : i in [1..4] ] >;
	U := BasisMatrix(A)^-1*S*BasisMatrix(B);
    end if;
    fac := Factorization(CharacteristicPolynomial(U));
    if GetVerbose("QuaternionIsomorphism") ge 1 then
	printf "Factored charpoly: \n%o\n", fac;
    end if;
    // Characteristic polynomial is (X-1)^2*G(X). 
    if #fac eq 1 then 
	// Characteristic polynomial of U is (X-1)^4, return identity.
	x := K ! 1;
    elif Degree(fac[2][1]) eq 1 then
	V := Kernel(U-1);
	x := K!Basis(V)[2];
	x -:= K!Trace(x)/2;
	x *:= K!Denominator(Norm(x));   
    else 
	chi := fac[2][1];
	V1 := Kernel(U-1);
	V2 := Kernel(Evaluate(chi,U));
	if GetVerbose("QuaternionIsomorphism") ge 1 then
	    printf "Kernel(U-1) =\n%o\n", V1;
	    print "chi =", chi;
	    print "Kernel(Evaluate(chi,U)) =", Kernel(Evaluate(chi,U));
	end if;
	// Let x be a non-central element of Kernel(U-1),
	// y any element of Kernel(chi(U)), and z = y*U.
	// Solve for c such that (x+c)^-1*y*(x + c) = z.
	// ==> c*(y-z) = (x*z - y*x).
	x := K!Basis(V1)[2];
	y := K!Basis(V2)[1];
	z := K!(Basis(V2)[1]*U);
	x +:= (x*z-y*x)/(y-z);
	x *:= K!Denominator(Norm(x));   
    end if;
    if GetVerbose("QuaternionIsomorphism") ge 1 then
	print "x =", x;
	print "minipoly(x) =", MinimalPolynomial(x);
	print [ x^-1*y*x in B : y in Basis(A) ];      
	assert &and[ x^-1*y*x in B : y in Basis(A) ];      
    end if;
    return h, x;
end intrinsic;

intrinsic LeftIsomorphism(I::AlgQuatOrdIdl,J::AlgQuatOrdIdl)
    -> Map, AlgQuatElt
    {}
    K := QuaternionAlgebra(I);
    require K cmpeq QuaternionAlgebra(J) : 
	"Arguments must be ideals in the same algebra.";
    require Type(BaseRing(I)) eq RngInt :
	"Arguments must be ideals in a quaternion algebra over Q.";
    require IsDefinite(K) :
	"Arguments must be ideals in a definite quaternion algebra.";
    require LeftOrder(I) eq LeftOrder(J) : 
	"Arguments must have the same left order.";
    val, h, t := IsLeftIsomorphic(I,J);
    require val : "Arguments must be isomorphic as left ideals.";
    return h, t;
end intrinsic;

intrinsic RightIsomorphism(I::AlgQuatOrdIdl,J::AlgQuatOrdIdl) -> Map, AlgQuatElt
    {}
    K := QuaternionAlgebra(I);
    require K cmpeq QuaternionAlgebra(J) : 
	"Arguments must be ideals in the same algebra.";
    require Type(BaseRing(I)) eq RngInt :
	"Arguments must be ideals in a quaternion algebra over Q.";
    require IsDefinite(K) :
	"Arguments must be ideals in a definite quaternion algebra.";
    require RightOrder(I) eq RightOrder(J) : 
	"Arguments must have the same right order.";
    val, h, t := IsRightIsomorphic(I,J);
    require val : "Arguments must be isomorphic as right ideals.";
    return h, t;
end intrinsic;

