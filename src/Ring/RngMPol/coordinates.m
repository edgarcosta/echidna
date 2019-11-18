//////////////////////////////////////////////////////////////////////////////
//                                                                          //
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
This gives the K-coordinates of polynomials in the span of a sequence of
polynomials over K.  Sometimes we also want to compute the K-coordinates of
n-tuples (f_1,...,f_n) in the K-linear span of a sequence of such tuples
(e.g. when the latter is a basis of forms of degree d defining a morphism).
*/

intrinsic Coordinates(X::SeqEnum[RngMPolElt],B::SeqEnum[RngMPolElt],I::RngMPol) -> SeqEnum
    {Returns a sequence of vectors (over the base ring) expressing
    the polynomials of X in terms of the polynomials in B modulo
    the ideal I, followed by the kernel of relations in B.}
    X := NormalForm(X,I);
    B := NormalForm(B,I);
    mons := SetToSequence(&join[ SequenceToSet(Monomials(g)) : g in B cat X ]);
    K := BaseRing(Universe(mons));
    V := VectorSpace(K,#mons);
    M := Matrix([ V![ MonomialCoefficient(g,m) : m in mons ] : g in B ]);
    S := [ ];
    for f in X do
        v := V![ MonomialCoefficient(f,m) : m in mons ];
        bool, u := IsConsistent(M,v);
        require bool : "Coordinate " * Sprint(Index(X,f)) *
            " of argument 1 is not in the space spanned by argument 2.";
        Append(~S,u);
    end for;
    return S, Kernel(M);
end intrinsic;

intrinsic Coordinates(f::RngMPolElt,B::SeqEnum[RngMPolElt],I::RngMPol) -> SeqEnum, Any
    {Returns a sequence of vectors (over the base ring) expressing f
    in terms of the polynomials in B modulo the ideal I, followed by
    the kernel of relations in B.}
    f := NormalForm(f,I);
    B := NormalForm(B,I);
    mons := SetToSequence(&join[ SequenceToSet(Monomials(g)) : g in B cat [f] ]);
    K := BaseRing(Universe(mons));
    V := VectorSpace(K,#mons);
    M := Matrix([ V![ MonomialCoefficient(g,m) : m in mons ] : g in B ]);
    v := V![ MonomialCoefficient(f,m) : m in mons ];
    bool, u := IsConsistent(M,v);
    require bool : "Argument 1 is not in the space spanned by argument 2.";
    return u, Kernel(M);
end intrinsic;

intrinsic VectorCoordinates(
    x::SeqEnum[RngMPolElt],B::SeqEnum[SeqEnum[RngMPolElt]],I::RngMPol) -> SeqEnum, Any
    {Returns a sequence of vectors (over the base ring) expressing the n-tuple x
    in terms of the sequence of n-tuples of polynomials in B modulo the ideal I,
    followed by the kernel of relations in B.}
    n := #x;
    require &and [ n eq #S : S in B ] :
        "Elements of argument 2 must have the same length as argument 1.";
    x := NormalForm(x,I);
    B := [ NormalForm(S,I) : S in B ];
    mons := SetToSequence(&join[ SequenceToSet(Monomials(S[j])) : S in B cat [x], j in [1..n] ]);
    K := BaseRing(Universe(mons));
    V := VectorSpace(K,n*#mons);
    M := Matrix([ V!&cat[ [ MonomialCoefficient(g,m) : m in mons ] : g in S ] : S in B ]);
    v := V!&cat[ [ MonomialCoefficient(f,m) : m in mons ] : f in x ];
    bool, u := IsConsistent(M,v);
    require bool : "Argument 1 is not in the span of argument 2.";
    return u, Kernel(M);
end intrinsic;

intrinsic VectorCoordinates(
    X::SeqEnum[SeqEnum[RngMPolElt]],
    B::SeqEnum[SeqEnum[RngMPolElt]],I::RngMPol) -> SeqEnum, Any
    {}
    n := #X[1];
    require &and [ n eq #S : S in X ] :
        "Elements of argument 1 must all have the same length.";
    require &and [ n eq #S : S in B ] :
        "Elements of argument 2 must have the same length as elements of argument 1.";
    X := [ NormalForm(S,I) : S in X ];
    B := [ NormalForm(S,I) : S in B ];
    mons := SetToSequence(&join[ SequenceToSet(Monomials(S[j])) : S in B cat X, j in [1..n] ]);
    K := BaseRing(Universe(mons));
    V := VectorSpace(K,n*#mons);
    M := Matrix([ V!&cat[ [ MonomialCoefficient(g,m) : m in mons ] : g in S ] : S in B ]);
    S := [ ];
    for x in X do
        v := V!&cat[ [ MonomialCoefficient(f,m) : m in mons ] : f in x ];
        bool, u := IsConsistent(M,v);
        require bool : "Coordinate " * Sprint(Index(X,x)) *
            " of argument 1 is not in the space spanned by argument 2.";
        Append(~S,u);
    end for;
    return S, Kernel(M);
end intrinsic;

