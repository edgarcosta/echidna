////////////////////////////////////////////////////////////////////////
//                                                                    //
//                            David Kohel                             //
//                                                                    //
////////////////////////////////////////////////////////////////////////

declare verbose AlgebraOrder, 1;

////////////////////////////////////////////////////////////////////////

intrinsic AmbientAlgebra(A::AlgAss) -> BoolElt
    {True iff A is an integral order in a ***simple*** algebra.}
    require IsOrder(A) : 
	"Argument must be an integral order of a simple algebra.";
    return A`AmbientAlgebra;
end intrinsic;

////////////////////////////////////////////////////////////////////////

/*
function pMultiplicationKernel(B,p)
    bool, Q := CanChangeUniverse(StructureConstants(B),Integers());
    if not bool then error "Basis is nonintegral."; end if;
    n := #B;
    FF := FiniteField(p);
    V := VectorSpace(FF,n); 
    U := VectorSpace(FF,Binomial(n,2));
    //
    function ext2(x,y)
	v := U!0;
	for i in [1..n-1] do
	    for j in [i+1..n] do
		k := ((2*n-i)*(i-1)) div 2 + j-i;
		v[k] := x[i]*y[j]-x[j]*y[i];
	    end for;
	end for;
	return v;
    end function;
    //
    BM := Matrix([ Eltseq(x) : x in B ]); 
    //
    K := V;
    for y in B do
	Vects := [ U | ]; 
	for x in B do 
	    bool, vx := IsConsistent(BM,Vector(Eltseq(x))); assert bool;
	    bool, Bx := CanChangeUniverse(Eltseq(vx),Integers()); assert bool;	
	    bool, vxy := IsConsistent(BM,Vector(Eltseq(x*y))); assert bool;	
	    bool, Bxy := CanChangeUniverse(Eltseq(vxy),Integers()); assert bool;
	    Append(~Vects,ext2(V!Bx,V!Bxy));
	end for;
	K meet:= Kernel(Matrix(Vects));
	if Dimension(K) eq 0 then
	    return K;
	else
	    vprint AlgebraOrder : "  Kernel dimension:", Dimension(K);
	end if;
    end for;
    Vects := [ V | ]; 
    for v in Basis(K) do 
	x := &+[ Integers()!c[i]*B[i] : i in [1..n] ] where c := Eltseq(v);
	bool, vx2 := IsConsistent(BM,Vector(Eltseq(x^2))); assert bool;
	bool, Bx2 := CanChangeUniverse(Eltseq(vx2),Integers()); assert bool;
	Append(~Vects,vx2);
    end for;
    K := sub< K | [ &+[ c[i]*K.i : i in [1..Dimension(K)] ] : 
	c in Basis(Kernel(Matrix(Vects))) ] >; 
    vprint AlgebraOrder : "  Self kernel dimension:", Dimension(K);
    Vects := [ U | ]; 
    for v in Basis(K) do 
	x := &+[ Integers()!c[i]*B[i] : i in [1..n] ] where c := Eltseq(v);
	print MinimalPolynomial(x);
	bool, vx := IsConsistent(BM,Vector(Eltseq(x))); assert bool;
	bool, Bx := CanChangeUniverse(Eltseq(vx),Integers()); assert bool;	
	bool, vx2 := IsConsistent(BM,Vector(Eltseq(x^2))); assert bool;	
	bool, Bx2 := CanChangeUniverse(Eltseq(vx2),Integers()); assert bool;
	assert &and[ c mod p eq 0 : c in Bx2 ];
	Append(~Vects,ext2(V!Bx,V![ c div p : c in Bx2 ]));
    end for;
    K := sub< K | [ &+[ c[i]*K.i : i in [1..Dimension(K)] ] : 
	c in Basis(Kernel(Matrix(Vects))) ] >; 
    vprint AlgebraOrder : "  Self double kernel dimension:", Dimension(K);
    return K;
end function;
*/

function IsIntegralExtendor(B,x)
    return CanChangeUniverse(StructureConstants(B cat [x]),Integers());
end function;

function pIntegralExtendor(B,p)
    A := Universe(B); 
    C := B;
    for i in [1..Isqrt(#B)-1] do
	C := &cat[ [ B[i]*C[j]-C[j]*B[i] : i in [1..#B-1] ] : j in [1..#C] ];
	M := LLL(Matrix([ Eltseq(x) : x in C ])); 
	C := &cat[ [ x*A!M[i] : i in [1..Rank(M)] ] : x in B ];
	M := LLL(Matrix([ Eltseq(x) : x in C ])); 
	C := &cat[ [ A!M[i]*y : i in [1..Rank(M)] ] : y in B ];
	M := LLL(Matrix([ Eltseq(x) : x in C ])); 
	C := [ A!M[i] : i in [1..Rank(M)] ];
    end for;
    vprint AlgebraOrder : "  Commutator basis dimension:", #C;
    V := VectorSpace(FiniteField(p),#B);
    U := VectorSpace(FiniteField(p),#C);
    Vects := [ U | ]; 
    BM := Matrix([ Eltseq(x) : x in B ]); 
    VC := [ Vector(Eltseq(y)) : y in C ];
    for v in VC do
	Append(~Vects,U!Eltseq(Solution(BM,v)));
    end for;
    K := sub< U | Vects >;
    vprint AlgebraOrder : "  Commutator basis dimension mod pS:", Dimension(K);
    for u in K do
	if u ne 0 then
	    x := (1/p)*&+[ Integers()!u[i]*C[i] : i in [1..#C] ];
	    if IsIntegralExtendor(B,x) then
		vprint AlgebraOrder : "  x =", x;
		vprint AlgebraOrder : "  pol =", MinimalPolynomial(x);
		return x;
	    end if;
	end if;
    end for;
    vprint AlgebraOrder : "  No extension";
    return 0;
end function;

function pMaximalIntegralBasis(B,p)
    A := Universe(B);
    n := Dimension(A); assert #B eq n;
    x := pIntegralExtendor(B,p);
    while x eq 0 do
	vprint AlgebraOrder :
	    "Found nontrivial p-multiplication kernel at p =", p;
	N := LLL(Matrix([ Eltseq(y) : y in B ] cat [ Eltseq(x) ]));
	B := [ A!N[i] : i in [1..n] ];
	x := pIntegralExtendor(B,p);
    end while;
    return B;
end function;

////////////////////////////////////////////////////////////////////////

intrinsic IntegralOrder(A::AlgAss) -> AlgAss
    {An integral suborder of A.}
    require IsUnitary(A) : "Argument 1 must be a unitary algebra.";
    require BaseRing(A) cmpeq Rationals() :
	"Base ring of argument must be the rationals.";
    bool, Q := CanChangeUniverse(StructureConstants(A),Integers());
    require bool : "Argument must have integral structure constants.";
    n := Dimension(A);
    ZA := AssociativeAlgebra< Integers(), n | Q >;
    ZA`AmbientAlgebra := A;
    ZA`AmbientBasisMatrix := IdentityMatrix(Rationals(),n);
    return ZA, hom< ZA->A | x :-> A!Eltseq(x) >;
end intrinsic;

intrinsic IntegralOrder(A::AlgGrp) -> AlgGrp
    {The integral group subalgebra of A.}
    require IsUnitary(A) : "Argument 1 must be a unitary algebra.";
    require BaseRing(A) cmpeq Rationals() :
	"Base ring of argument must be the rationals.";
    ZG := GroupAlgebra(Integers(),Group(A)); 
    // ZA`AmbientAlgebra := A;
    // ZA`AmbientBasisMatrix := IdentityMatrix(Rationals(),n);
    return ZG, hom< ZG->A | x :-> A!Eltseq(x) >;
end intrinsic;

////////////////////////////////////////////////////////////////////////

intrinsic MaximalOrder(A::AlgAss) -> AlgAss
    {A maximal order of A.}
    require IsUnitary(A) : "Argument 1 must be a unitary algebra.";
    require BaseRing(A) cmpeq Rationals() :
	"Base ring of argument must be the rationals.";
    M := LLL(Matrix([ Eltseq(x) : x in [ A!1 ] cat Basis(A) ]));
    B := [ A!M[i] : i in [1..Dimension(A)] ];
    // Need to ensure that this is an integral basis!!!
    disc := Determinant(Matrix(#B,[ ReducedTrace(x*y) : x, y in B ]));
    vprint AlgebraOrder : "Discriminant:", disc;
    for p in PrimeDivisors(Integers()!disc) do
	vprint AlgebraOrder : "Computing p-maximal basis at p =", p;
	B := pMaximalIntegralBasis(B,p);
    end for;
    ZA := AssociativeAlgebra< Integers(), #B | StructureConstants(B) >;
    ZA`AmbientAlgebra := A;
    ZA`AmbientBasisMatrix := Matrix([ Eltseq(x) : x in B ]);
    return ZA, hom< ZA->A | x :-> &+[ x[i]*B[i] : i in [1..#B] ] >;
end intrinsic;

intrinsic pMaximalOrder(A::AlgAss,p::RngIntElt) -> AlgAss
    {A p-maximal order of A.}
    require IsUnitary(A) : "Argument 1 must be a unitary algebra.";
    require BaseRing(A) cmpeq Rationals() : 
	"Base ring of argument 1 must be the rationals.";
    B := pMaximalIntegralBasis([ A!1 ] cat Basis(A),p);
    ZA := AssociativeAlgebra< Integers(), #B | StructureConstants(B) >; 
    ZA`AmbientAlgebra := A;
    ZA`AmbientBasisMatrix := Matrix([ Eltseq(x) : x in B ]);
    return ZA, hom< ZA->A | x :-> &+[ x[i]*B[i] : i in [1..#B] ] >;
end intrinsic;

////////////////////////////////////////////////////////////////////////

intrinsic AlgebraOrder(S::[AlgAssElt]) -> AlgAss
    {An order in an associative algebra generated by S.}
    A := Universe(S);
    require IsUnitary(A) : "Argument 1 must be a unitary algebra.";
    require BaseRing(A) cmpeq Rationals() : 
	"Base ring of argument 1 must be the rationals.";
    S := [ A!1 ] cat S;
    M := LLL(Matrix([ Eltseq(x) : x in S ])); 
    B := [ A!M[i] : i in [1..Rank(M)] ];
    StrCnts := StructureConstants(B);
    bool, StrCnts := CanChangeUniverse(StrCnts,Integers());
    if not bool then
	M := LLL(Matrix([ Eltseq(x*y) : x, y in B ])); 
	B := [ A!M[i] : i in [1..Rank(M)] ];
	StrCnts := StructureConstants(B);
	bool, StrCnts := CanChangeUniverse(StrCnts,Integers());
    end if;
    require bool :
	"Argument must form a multiplicatively closed integral order.";
    ZA := AssociativeAlgebra< Integers(), #B | StrCnts >;
    ZA`AmbientAlgebra := A;
    ZA`AmbientBasisMatrix := Matrix([ Eltseq(x) : x in B ]);
    return ZA, hom< ZA->A | x :-> &+[ x[i]*B[i] : i in [1..#B] ] >;
end intrinsic;


