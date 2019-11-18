//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//        Copyright (C) 2012 David Kohel <David.Kohel@univ-amu.fr>          //
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
//
chi1 := x^4 - 13*x^3 + 545*x^2 - 4979*x + 146689;
A1 := EquationOrder(chi1);
A1_dagger := ComplementaryModule(A1);
ComplementaryModule(A1_dagger) eq ideal< A1 | 1 >;
O1 := MaximalOrder(A1);
O1_dagger := ComplementaryModule(O1);
ComplementaryModule(O1_dagger) eq ideal< O1 | 1 >;
// Construct a non-Gorenstein order:
B1 := sub< O1 | [ 2*x : x in Basis(O1) ] >;
IsGorenstein(B1);
//
chi2 := x^4 - 2*x^3 - 831*x^2 - 2048*x + 1048576;
A2 := EquationOrder(chi2);
A2_dagger := ComplementaryModule(A2);
ComplementaryModule(A2_dagger) eq ideal< A2 | 1 >;
O2 := MaximalOrder(A2);
O2_dagger := ComplementaryModule(O2);
ComplementaryModule(O2_dagger) eq ideal< O2 | 1 >;
//
// Construct a non-Gorenstein order:
B2 := sub< O2 | [ 2*x : x in Basis(O2) ] >;
EndomorphismRing(B2);
*/

intrinsic EndomorphismRing(A::RngOrd) -> RngOrd
    {}
    return A;
end intrinsic;

intrinsic EndomorphismRing(I::RngOrdFracIdl) -> RngOrd
    {}
    B := Basis(ColonIdeal(I,I));
    return Order(B);
end intrinsic;

intrinsic IsInvertible(I::RngOrdFracIdl) -> BoolElt
    {}
    unit_ideal := Parent(I)!1;
    return ColonIdeal(unit_ideal,I)*I eq unit_ideal;
end intrinsic;

intrinsic DualIdeal(I::RngOrdFracIdl) -> RngOrdFracIdl
    {}
    return ColonIdeal(Parent(I)!1,I);
end intrinsic;

intrinsic Codifferent(O::RngOrd) -> RngOrdFracIdl
    {The codifferent of O.}
    return Codifferent(ideal< O | 1 >);
end intrinsic;

intrinsic ComplementaryModule(A::RngOrd) -> RngOrdFracIdl
    {}
    B := Basis(A);
    K := FieldOfFractions(A);
    M := Matrix(RationalField(),[ [ Trace(x*y) : y in B ] : x in B ]);
    N := M^-1;
    return ideal< A | [ K!Eltseq(N[i]) : i in [1..Nrows(N)] ] >;
end intrinsic;

intrinsic ComplementaryModule(I::RngOrdFracIdl) -> RngOrdFracIdl
    {}
    A := Order(I);
    B := Basis(I);
    M := Matrix(RationalField(),[ [ Trace(x*y) : y in B ] : x in B ]);
    N := M^-1;
    C := [ &+[ N[i,j]*B[j] : j in [1..#B] ] : i in [1..#B] ];
    // This assumes the endomorphism ring of I^\dagger is A = End(I).
    return ideal< A | C >;
end intrinsic;

intrinsic ComplementaryBasis(A::RngOrd) -> SeqEnum
    {}
    ZZ := IntegerRing();
    A_dagger := ComplementaryModule(A);
    B := Basis(A);
    B_dagger := Basis(A_dagger);
    _, U := HermiteForm(Matrix([ [ ZZ | Trace(x*y) : x in B ] : y in B_dagger ]));
    return [ &+[ U[i,j]*B_dagger[j] : j in [1..#B] ] : i in [1..#B] ];
end intrinsic;

intrinsic ComplementaryBasis(I::RngOrdFracIdl) -> SeqEnum
    {}
    ZZ := IntegerRing();
    I_dagger := ComplementaryModule(I);
    B := Basis(I);
    B_dagger := Basis(I_dagger);
    _, U := HermiteForm(Matrix([ [ ZZ | Trace(x*y) : x in B ] : y in B_dagger ]));
    return [ &+[ U[i,j]*B_dagger[j] : j in [1..#B] ] : i in [1..#B] ];
end intrinsic;

intrinsic IsRelativeProjective(O::RngOrd) -> BoolElt
    {Returns true if the quartic CM order O is relatively projective over its real subring.}
    /*
    Use the exact sequence 0 -> R -> O -> P -> 0 where P is the image
    of x |-> x - \bar{x} in S = O + \bar{O}, with kernel the real
    subring R of O.  Then O is free as an R-module if and only if the
    quotient O/R \isom P is projective. 
    */
    K := NumberField(O);
    require IsCMField(K) : "Argument must be a CM field.";
    require Degree(K) eq 4 : "Argument must be a quartic CM field.";
    F := TotallyRealSubfield(K);
    s := ComplexConjugation(K);
    X := Basis(O);
    // Construct the smallest symmetric order S containing O:
    Y := [ s(x) : x in X ];
    S := &and [ y in O : y in Y ] select O else Order(X cat Y);
    M := Kernel(Matrix(IntegerRing(),[ Eltseq(S!(x-s(x))) : x in X ]));
    Z := [ S!O!Eltseq(x) : x in Basis(M) ];
    if IsMaximal(Order([ F!K!z : z in Z ])) then
	// O is a f.g. R-module with R Dedekind:
	return true;
    end if;
    V := RSpace(Integers(),Degree(K));
    // Construct P as a submodule of S (not generally saturated in V):
    P := sub< V | [ V!Eltseq(S!(x-s(x))) : x in X ] >;
    W := [ S!Eltseq(x) : x in Basis(P) ];
    // Above V is the underlying module of S (of rank 2*deg),
    // and below V is used as the underlying module of the
    // deg x deg matrices -- these ranks coincide for deg = 2.
    U := sub< V | [ V!&cat[ Eltseq(Coordinates(P,V!Eltseq(y*z))) : y in W ] : z in Z ] >;
    return U eq Saturation(U);
end intrinsic;

intrinsic IsRelativeProjective(O::RngOrd,F::FldNum) -> BoolElt
    {Given an order O in a field K with subfield F such that [K:F] = 2,
    returns true if O is relatively projective over O meet F.}
    /*
    Use the exact sequence 0 -> R -> O -> P -> 0 where P is the image
    of x |-> x - \bar{x} in S = O + \bar{O}, with kernel the real
    subring R of O.  Then O is free as an R-module if and only if the
    quotient O/R \isom P is projective. 
    */
    K := NumberField(O);
    require Degree(K) eq 2*Degree(F) : "Argument 1 must be an order in a quadratic extension of argument 2.";
    bool, BF := CanChangeUniverse(Basis(F),K); 
    require CanChangeUniverse(Basis(F),K) : "Argument 1 must be an order in a quadratic extension of argument 2.";
    G := Automorphisms(K);
    s := [ g : g in G | &and [ g(x) in F : x in BF ] ][1];
    for g in G do
	s := g;
	if &and [ g(x) eq x : x in Basis(K) ] then continue; end if;
	if &and [ g(x) eq x : x in BF ] then break; end if;
    end for;
    X := Basis(O);
    // Construct the smallest symmetric order S containing O:
    Y := [ s(x) : x in X ];
    S := &and [ y in O : y in Y ] select O else Order(X cat Y);
    M := Kernel(Matrix(IntegerRing(),[ Eltseq(S!(x-s(x))) : x in X ]));
    Z := [ S!O!Eltseq(x) : x in Basis(M) ];
    if IsMaximal(Order([ F!K!z : z in Z ])) then
	// O is a f.g. R-module with R Dedekind:
	return true;
    end if;
    V := RSpace(Integers(),Degree(K));
    // Construct P as a submodule of S (not generally saturated in V):
    P := sub< V | [ V!Eltseq(S!(x-s(x))) : x in X ] >;
    W := [ S!Eltseq(x) : x in Basis(P) ];
    // Above V is the underlying module of S (of rank 2*deg),
    // and below V is used as the underlying module of the
    // deg x deg matrices -- these ranks coincide for deg = 2.
    U := sub< V | [ V!&cat[ Eltseq(Coordinates(P,V!Eltseq(y*z))) : y in W ] : z in Z ] >;
    return U eq Saturation(U);
end intrinsic;

intrinsic IsGorenstein(O::RngOrd) -> BoolElt
    {Returns true if O is a Gorenstein order.}
    unit_ideal := 2*ideal< O | 1/2 >; // create the unit fractional ideal
    O_dagger := ComplementaryModule(O);
    O_dagger_dual := ColonIdeal(unit_ideal,O_dagger);
    return unit_ideal eq ideal< O | [ x*y : x in Basis(O_dagger), y in Basis(O_dagger_dual) ] >;
end intrinsic;
