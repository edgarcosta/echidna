//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//        Witt Rings                                                        //
//        Copyright (C) 2013 David Kohel <David.Kohel@univ-amu.fr>          //
//                                                                          //
//  Distributed under the terms of the GNU General Public License (GPL)     //
//                                                                          //
//                  http://www.gnu.org/licenses/                            //
//                                                                          //
//        All rights granted to distribute under the GPL, version 2,        //
//          or (at your option) any later version of the license.           //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

/*
Created by David Kohel, 2011
Changes:
2003: Update and patches of Claus Fieker.
2005: Extensions to characteristic 0.
*/

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//                          Attribute declarations                          //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

declare type RngWittNew[RngWittNewElt];

declare attributes RngWittNew:
    BaseRing,
    Prime,
    Length,
    CoAddition,
    CoInverse,
    CoMultiplication,
    LocalRingMap;

declare attributes RngWittNewElt:
    Parent,
    Element;

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//                            Creation functions                            //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

MyExactQuotient := ExactQuotient;

/*
function MyExactQuotient(f,m)
    if Type(f) eq RngMPolElt then
	cffs := Coefficients(f);
	mons := Monomials(f);
	return &+[ ExactQuotient(cffs[i],m)*mons[i] : i in [1..#mons] ];
    end if;
    return ExactQuotient(f,m);
end function;
*/

function CoAddn(X,Y,p,n)
    A := [ X[1] + Y[1] ];
    for i in [1..n-1] do
	A[i+1] := MyExactQuotient(
	    - &+[ p^(j-1)*A[j]^(p^(i+1-j)) : j in [1..i] ] 
	    + &+[ p^(j-1)*X[j]^(p^(i+1-j)) : j in [1..i+1] ] 
	    + &+[ p^(j-1)*Y[j]^(p^(i+1-j)) : j in [1..i+1] ], p^i);
    end for;
    return A;
end function; 

function CoInvs(X,p,n)
    I := [ -X[1] ];
    if p eq 2 then
	Y := [ -1 : i in [1..n] ];
    else
	Y := [ -1 ] cat [ 0 : i in [1..n-1] ];
    end if;
    for i in [1..n-1] do
	I[i+1] := MyExactQuotient(
	    - &+[ p^(j-1)*I[j]^(p^(i+1-j)) : j in [1..i] ]  
	    + &+[ p^(j-1)*X[j]^(p^(i+1-j)) : j in [1..i+1] ]        
	    * &+[ p^(j-1)*Y[j]^(p^(i+1-j)) : j in [1..i+1] ], p^i);
    end for;
    return I;
end function; 

function CoMult(X,Y,p,n)
    M := [ X[1] * Y[1] ]; 
    for i in [1..n-1] do
	M[i+1] := MyExactQuotient(
	    - &+[ p^(j-1)*M[j]^(p^(i+1-j)) : j in [1..i] ] + 
	    &+[ p^(j-1)*X[j]^(p^(i+1-j)) : j in [1..i+1] ] *       
	    &+[ p^(j-1)*Y[j]^(p^(i+1-j)) : j in [1..i+1] ], p^i);
    end for;
    return M;
end function; 

intrinsic WittRing(R::.,n::RngIntElt :
    ResidueCharacteristic := 0,
    MinimalPrecision := false,
    UniversalComputation := true) -> RngWittNew
    {The ring of Witt vectors of length n over R.}
    if ResidueCharacteristic ne 0 then
	//require p mod ResidueCharacteristic eq 0 :
	//    "ResidueCharacteristic must divide the ring charateristic.";
	p := ResidueCharacteristic;
    else
	q := Characteristic(R);
	require q ne 0 :  
	    "The parameter ResidueCharacteristic must be prime.";
	bool, p := IsPrimePower(q);
	require bool :  
	    "The parameter ResidueCharacteristic must be prime.";
    end if;
    require IsPrime(p) :
	"The parameter ResidueCharacteristic must be prime.";
    W := New(RngWittNew);
    W`BaseRing := R;
    W`Prime := p;
    W`Length := n;
    if UniversalComputation then
	if MinimalPrecision then
	    S := pAdicQuotientRing(p,n);
	else
	    S := Integers();
	end if;
	P1 := PolynomialRing(S,n);
	AssignNames(~P1,
	    [ "X" cat IntegerToString(i) : i in [0..n-1] ] );
	P2 := PolynomialRing(S,2*n);
	AssignNames(~P2,
	    [ "X" cat IntegerToString(i) : i in [0..n-1] ] cat 
	    [ "Y" cat IntegerToString(i) : i in [0..n-1] ] );
	X := [ P2.i : i in [1..n] ]; 
	Y := [ P2.i : i in [n+1..2*n] ]; 
	U := [ P1.i : i in [1..n] ]; 
	W`CoAddition := CoAddn(X,Y,p,n);
	W`CoInverse := CoInvs(U,p,n);
	W`CoMultiplication := CoMult(X,Y,p,n);
    end if;
    h := hom< R -> W | x :-> x*(W!1) >;
    return W, h;   
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//                              Coercions                                   //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

function WittCreateElt(W, S)
    x := New(RngWittNewElt);
    x`Parent := W;
    x`Element := S;
    return x;
end function;

intrinsic IsCoercible(W::RngWittNew,S::.) -> BoolElt, RngWittNewElt
    {}
    if Type(S) eq RngWittNewElt then
	if Parent(S) eq W then return true, S; end if;
    elif Type(S) eq RngIntElt then
	p := W`Prime;
	if S eq -1 and p eq 2 then
	    R := W`BaseRing;
	    U := [ R!-1 : i in [1..Length(W)] ];   
	    return true, WittCreateElt(W,U);
	elif S in {-1,0,1} then
	    R := W`BaseRing; 
	    Z := [ R | 0 : i in [1..Length(W)-1] ];
	    return true, WittCreateElt(W, [R!S] cat Z); 
	end if;
	return true, S*(W!1); 
    elif ISA(Type(S),RngElt) then
	R := W`BaseRing;
	bool, S := IsCoercible(R,S);
	if bool then
	    Z := [ R | 0 : i in [1..Length(W)-1] ];
	    return true, WittCreateElt(W, [R!S] cat Z); 
	end if;
    elif Type(S) eq SeqEnum then
	R := W`BaseRing; 
	bool, S := CanChangeUniverse(S, R);
	if bool and #S eq Length(W) then
	    return true, WittCreateElt(W, S);
	end if;
    end if;
    return false, "Illegal coercion.";
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//                                  Printing                                //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

intrinsic Print(W::RngWittNew, level::MonStgElt)
    {}
    printf "Witt ring of length %o over %o", Length(W), BaseRing(W);
end intrinsic;

intrinsic Print(x::RngWittNewElt, level::MonStgElt)
    {}
    S := x`Element;
    if ISA(Type(Universe(S)),Rng) then
	printf "%o", Vector(x`Element);
    else
	s := "(";
	for i in [1..#S-1] do
	    s *:= Sprintf("%o, ", S[i]);
	end for;
	s *:= Sprint(S[#S]) * ")";
	printf "%o", s;
    end if;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//                         Membership and Equality                          //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

intrinsic 'in'(x::., X::RngWittNew) -> BoolElt
    {Returns true if x is in X.}
    if Type(x) eq RngWittNewElt then
	return x`Parent eq X;
    end if;
    return false;
end intrinsic;

intrinsic Parent(x::RngWittNewElt) -> RngWittNew
    {}
    return x`Parent;
end intrinsic;

intrinsic 'eq' (W::RngWittNew,V::RngWittNew) -> BoolElt
    {}
    return W`BaseRing cmpeq V`BaseRing and W`Length eq V`Length;
end intrinsic;

intrinsic 'eq' (x::RngWittNewElt,y::RngWittNewElt) -> BoolElt
    {}
    return Parent(x) eq Parent(y) and x`Element eq y`Element;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//                           Attribute Access Functions                     //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

intrinsic BaseRing(W::RngWittNew) -> Rng
    {The defining ring of W.}
    return W`BaseRing;
end intrinsic;

intrinsic BaseField(W::RngWittNew) -> Rng
    {The defining ring of W.}
    return W`BaseRing;
end intrinsic;

intrinsic Length(W::RngWittNew) -> Rng
    {The length of the finite Witt ring W.}
    return W`Length;
end intrinsic;

intrinsic Eltseq(x::RngWittNewElt) -> SeqEnum
    {}
    return x`Element;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//                         Arithmetic and Functionality                     //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

intrinsic Unity(W::RngWittNew) -> RngWittNewElt 
    {The identity element of R.}
    return W!1;
end intrinsic;

intrinsic Zero(W::RngWittNew) -> RngWittNewElt
    {The zero element of R.}
    return W!0;
end intrinsic;

intrinsic Inverse(x::RngWittNewElt) -> RngWittNewElt
    {}
    W := Parent(x);
    n := Length(W);
    if assigned W`CoInverse then
	A := W`CoInverse;
	inv := [ Evaluate(A[i],x`Element) : i in [1..n] ];
	return WittCreateElt(W,inv);
    end if;
    return -x;
end intrinsic;

intrinsic '-' (x::RngWittNewElt) -> RngWittNewElt
    {}
    return (Parent(x)!-1)*x;
end intrinsic;

intrinsic '-' (x::RngWittNewElt,y::RngIntElt) -> RngWittNewElt
    {}
    return x + Parent(x)!-y;
end intrinsic;

intrinsic '-' (x::RngIntElt,y::RngWittNewElt) -> RngWittNewElt
    {}
    return Parent(y)!x - y;
end intrinsic;

intrinsic '-' (x::RngWittNewElt,y::RngWittNewElt) -> RngWittNewElt
    {}
    W := Parent(x);
    require W eq Parent(y): "Arguments have different parents.";
    return x + (-y);
end intrinsic;

intrinsic '+' (x::RngWittNewElt,y::RngIntElt) -> RngWittNewElt
    {}
    return x + Parent(x)!y;
end intrinsic;

intrinsic '+' (x::RngIntElt,y::RngWittNewElt) -> RngWittNewElt
    {}
    return Parent(y)!x + y;
end intrinsic;

intrinsic '+' (x::RngWittNewElt,y::RngWittNewElt) -> RngWittNewElt
    {}
    W := Parent(x);
    require W eq Parent(y): "Arguments have different parents.";
    n := Length(W);
    X := x`Element;
    Y := y`Element;
    if assigned W`CoAddition then
	A := W`CoAddition;
	sum := [ Evaluate(A[i],X cat Y) : i in [1..n] ];
    else
	p := W`Prime;
	sum := CoAddn(X,Y,p,n);
    end if;
    return WittCreateElt(W,sum);
end intrinsic;

intrinsic '*' (x::RngWittNewElt,n::RngIntElt) -> RngWittNewElt
    {}
    return n*x;
end intrinsic;

intrinsic '*' (n::RngIntElt,x::RngWittNewElt) -> RngWittNewElt
    {}
    if n lt 0 then
	return -((-n)*x);
    elif n eq 0 then
	return Parent(x)!0;
    elif n eq 1 then
	return x;
    elif n eq 2 then
	return x + x;
    elif n eq Parent(x)`Prime then
	return Frobenius(Verschiebung(x));
    end if;
    b := IntegerToSequence(n,2);
    y := Parent(x)!0;
    for i in [1..#b] do
	y := y + b[i]*x;
	x := 2*x; 
    end for;
    return y;
end intrinsic;

intrinsic '*' (x::RngWittNewElt,y::RngWittNewElt) -> RngWittNewElt
    {}
    W := Parent(x);
    require W eq Parent(y): "Arguments have different parents.";
    n := Length(W);
    X := x`Element;
    Y := y`Element;
    if assigned W`CoMultiplication then
	M := W`CoMultiplication;
	prod := [ Evaluate(M[i],X cat Y) : i in [1..n] ];
    else
	p := W`Prime;
	prod := CoMult(X,Y,p,n);
    end if;
    return WittCreateElt(W,prod);
end intrinsic;

intrinsic '^' (x::RngWittNewElt,n::RngIntElt) -> RngWittNewElt
    {}
    require n ge 0: "Argument 2 must be positive.";
    if n eq 0 then 
	return Parent(x)!1;
    elif n eq 1 then 
	return x;
    elif n eq 2 then
	return x*x;
    end if;
    b := IntegerToSequence(n,2);
    y := x^b[1]; 
    for i in [2..#b] do 
	x := x^2;  
	if b[i] eq 1 then
	    y := x*y;
	end if;
    end for;
    return y;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//                                 Morphisms                                //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

intrinsic ArtinSchreier(W::RngWittNew) -> Map
    {}
    return hom< W -> W | x :-> Frobenius(x)-x >;
end intrinsic;

intrinsic ArtinSchreier(x::RngWittNewElt) -> RngWittNewElt
    {}
    p := Parent(x)`Prime;
    return Frobenius(x)-x;
end intrinsic;

intrinsic Frobenius(W::RngWittNew) -> Map
    {}
    p := W`Prime;
    return hom< W -> W | x :-> [ c^p : c in Eltseq(x) ] >;
end intrinsic;

intrinsic Frobenius(x::RngWittNewElt) -> RngWittNewElt
    {}
    W := Parent(x);
    p := W`Prime;
    return W![ c^p : c in Eltseq(x) ];
end intrinsic;

intrinsic Verschiebung(W::RngWittNew) -> Map
    {}
    n := Length(W);
    return hom< W->W | x :-> 
	[ 0 ] cat [ c[i] : i in [1..n-1] ] where c := Eltseq(x) >;
end intrinsic;

intrinsic Verschiebung(e::RngWittNewElt) -> RngWittNewElt
    {}
    W := Parent(e);
    n := Length(W);
    S := [ 0 ] cat [ c[i] : i in [1..n-1] ] where c := Eltseq(e);
    return WittCreateElt(W,S);
end intrinsic;
