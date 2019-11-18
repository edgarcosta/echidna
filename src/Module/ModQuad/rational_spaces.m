////////////////////////////////////////////////////////////////////////
//                                                                    //
//                     RATIONAL QUADRATIC SPACES                      //
//                            David Kohel                             //
//                            April 2000                              //
//                                                                    //
////////////////////////////////////////////////////////////////////////

/*
// Example representing 0:
V := RSpace(QQ,4,DiagonalMatrix(Mat(QQ,4),[2,5,17,-86]));
*/

declare verbose Isometry, 2;

////////////////////////////////////////////////////////////////////////

function RationalSquareFree(x)
    if Type(x) eq RngIntElt then return SquareFree(x); end if;
    return SquareFree(Numerator(x))*SquareFree(Denominator(x));
end function;

////////////////////////////////////////////////////////////////////////

function IsIsotropicCoeffs(S)
    if 0 in S then return true; end if;
    n := #S;
    if Abs(&+[ Sign(x) : x in S ]) eq n then
	return false;
    end if;  
    if n eq 2 then
	return IsSquare(-S[1]/S[2]);
    elif n eq 3 then
	S := [ x  div m : x in S ] where m is GCD(S);
	d := &*S;
	prms := Sort(SetToSequence(
	    SequenceToSet(&cat[ PrimeDivisors(x) : x in S ]))); 
	for p in prms do
	    if HilbertSymbol(-1,-d,p) ne 
		&*(&cat[ [ HilbertSymbol(S[i],S[j],p) 
		: j in [i+1..n] ] : i in [1..n-1] ]) then 
	        return false;
	    end if;
	end for;
	return true;
    elif n eq 4 then
	S := [ x  div m : x in S ] where m is GCD(S);
	prms := Sort(SetToSequence(
	    SequenceToSet([2] cat &cat[ PrimeDivisors(x) : x in S ]))); 
	d := &*S;
	for p in prms do
	    while d mod p^2 eq 0 do d div:= p^2; end while; 
	    if KroneckerSymbol(d,p) eq 1 and HilbertSymbol(-1,-1,p) ne
		&*(&cat[ [ HilbertSymbol(S[i],S[j],p) 
		: j in [i+1..n] ] : i in [1..n-1] ]) then 
	        return false;
	    end if;
	end for;
	return true;
    end if;
    return true;
end function;

////////////////////////////////////////////////////////////////////////

intrinsic Determinant(V::ModTupFld) -> FldRatElt
    {}
    return Determinant(GramMatrix(V));
end intrinsic;

////////////////////////////////////////////////////////////////////////

intrinsic Radical(V::ModTupFld) -> BoolElt
    {The subspace orthogonal to V.}
    B := Basis(V);
    C := Basis(Kernel(GramMatrix(V)));
    return sub< V | [ &+[ c[i]*B[i] : i in [1..#B] ] : c in C ] >;
end intrinsic;

////////////////////////////////////////////////////////////////////////

intrinsic IsNonsingular(V::ModTupFld) -> BoolElt
    {Returns true if V is singular.}
    require Type(BaseRing(V)) eq FldRat :
	"Argument must be defined over the rationals";
    return Determinant(GramMatrix(V)) ne 0;
end intrinsic;

intrinsic IsSingular(V::ModTupFld) -> BoolElt
    {Returns true if V is singular.}
    return Determinant(GramMatrix(V)) eq 0;
end intrinsic;

intrinsic IsDefinite(V::ModTupFld) -> BoolElt
    {Returns true if V is definite.}
    require Type(BaseRing(V)) eq FldRat :
	"Argument must be defined over the rationals";
    M := GramMatrix(V);
    if Determinant(M) eq 0 then
	return false;
    end if;
    if IsPositiveDefinite(Sign(M[1,1])*M) then
	return true;
    end if;
    return false;
end intrinsic;

intrinsic IsSemiDefinite(V::ModTupFld) -> BoolElt
    {Returns true if V is definite.}
    require Type(BaseRing(V)) eq FldRat :
	"Argument must be defined over the rationals";
    M := GramMatrix(V);
    if Determinant(M) eq 0 then
	U, pi := quo< V | Radical(V) >;
	m := Dimension(U); 
	B := [ (U.i)@@pi : i in [1..m] ];
	M := MatrixAlgebra(BaseRing(V),m)!
	    [ InnerProduct(B[i]*M,B[j]) : i in [1..m], j in [1..m] ];
    end if;
    if IsPositiveDefinite(Sign(M[1,1])*M) then
	return true;
    end if;
    return false;
end intrinsic;

intrinsic IsIndefinite(V::ModTupFld) -> BoolElt
    {Returns true if V is indefinite.}
    require Type(BaseRing(V)) eq FldRat :
	"Argument must be defined over the rationals";
    return not IsSemiDefinite(V);
end intrinsic;

////////////////////////////////////////////////////////////////////////

intrinsic Signature(V::ModTupFld) -> SeqEnum
    {}   
    require Type(BaseRing(V)) eq FldRat :
	"Argument must be defined over the rationals";
    require IsNonsingular(V) : "Argument must be nonsingular";
    n := Dimension(V);
    M := OrthogonalizeGram(GramMatrix(V));
    s := &+[ Sign(M[i,i]) : i in [1..n] ];
    return [ (n + s) div 2, (n - s) div 2 ];
end intrinsic;

////////////////////////////////////////////////////////////////////////

intrinsic IsIsotropic(V::ModTupFld) -> BoolElt
    {Returns true if and only if V represents zero.}
    require Type(BaseRing(V)) eq FldRat :
	"Argument must be defined over the rationals";
    if IsDefinite(V) then return false; end if;
    n := Dimension(V);
    M := OrthogonalizeGram(GramMatrix(V));
    return IsIsotropicCoeffs(
	[ Numerator(M[i,i])*Denominator(M[i,i]) : i in [1..n]]);
end intrinsic;

function IsometryBasis(U,V)
    // A basis for V, giving an isometry U -> V.
    a := Norm(U.1); 
    n := Numerator(a);
    m := Denominator(a);
    v := Representation(V,n*m)/m;
    vprint Isometry : "v =", v; 
    if Dimension(V) eq 1 then
	return [ v ];
    else 
	U1 := OrthogonalComplement(U,U.1);   
	V1 := OrthogonalComplement(V,v);   
	vprint Isometry : "U1 =", U1;
	vprint Isometry : "V1 =", V1;
	return [ v ] cat IsometryBasis(U1,V1);
    end if;
end function; 

intrinsic Isometry(U::ModTupFld,V::ModTupFld) -> BoolElt
    {An isometry U -> V of inner product spaces; error if none exists.}
    require Type(BaseRing(U)) eq FldRat and 
	Type(BaseRing(V)) eq FldRat :
	"Arguments must be defined over the rationals";
    require IsIsometric(U,V) : "Arguments are not isometric";
    B := IsometryBasis(U,V);     
    return hom< U -> V | u :-> &+[ u[i]*B[i] : i in [1..#B] ] >;
end intrinsic;

////////////////////////////////////////////////////////////////////////

intrinsic IsIsometric(U::ModTupFld,V::ModTupFld) -> BoolElt
    {True if and only if U and V are isometric inner product spaces
    over Q.}
    
    require Type(BaseRing(U)) eq FldRat and 
        Type(BaseRing(V)) eq FldRat :
	"Arguments must be defined over the rationals";
    n := Dimension(U);
    if Dimension(V) ne n then
	return false;   
    end if;
    D1 := RationalSquareFree(Determinant(GramMatrix(U)));
    D2 := RationalSquareFree(Determinant(GramMatrix(V)));
    if D1 ne D2 then
	return false;   
    end if;
    M1 := OrthogonalizeGram(GramMatrix(U));
    d1 := [ RationalSquareFree(M1[i,i]) : i in [1..n] ];
    s1 := &+[ Sign(x) : x in d1 ];
    M2 := OrthogonalizeGram(GramMatrix(V));
    d2 := [ RationalSquareFree(M2[i,i]) : i in [1..n] ];
    s2 := &+[ Sign(x) : x in d2 ];
    if s1 ne s2 then
	return false;
    end if;
    prms := Sort(SetToSequence(
	SequenceToSet([2] cat &cat[ PrimeDivisors(x) : x in d1 ]))); 
    for p in prms do
	c1 := &*(&cat[ [ HilbertSymbol(d1[i],d1[j],p) 
	    : j in [i+1..n] ] : i in [1..n] ]);  
	c2 := &*(&cat[ [ HilbertSymbol(d2[i],d2[j],p) 
	    : j in [i+1..n] ] : i in [1..n] ]);  
	if c1 ne c2 then
	    return false;   
	end if;      
    end for;
    return true;
end intrinsic;
