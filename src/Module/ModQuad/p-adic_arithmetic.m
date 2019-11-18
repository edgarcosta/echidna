//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//        Copyright (C) 2014 David Kohel <David.Kohel@univ-amu.fr>          //
//                                                                          //
//  Distributed under the terms of the GNU General Public License (GPL)     //
//                                                                          //
//                  http://www.gnu.org/licenses/                            //
//                                                                          //
//        All rights granted to distribute under the GPL, version 2,        //
//          or (at your option) any later version of the license.           //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

intrinsic pAdicDualSpace(x::ModTupRngElt[RngInt],p::RngIntElt,m::RngIntElt) -> ModTupRng
    {Given an element x of an integral quadratic module M, and
    prime p, and exponent m, return the submodule of elements y
    of M such that <x,y> = 0 mod p^m.}
    M := Parent(x);
    n := Rank(M);
    A := GramMatrix(M);
    B := Transpose(Matrix([ &+[ x[i] * A[i] : i in [1..n] ] ]));
    R := pAdicQuotientRing(p,m);
    Mat := RMatrixSpace(R,n,1);
    N := Kernel(Mat!B);
    return sub< M | [ M!v : v in Basis(N) ] cat [ p^m*u : u in Basis(M) ] >;
end intrinsic;

intrinsic pAdicDualSpace(N::ModTupRng[RngInt],p::RngIntElt,m::RngIntElt) -> ModTupRng
    {Given an integral quadratic submodule N of M, a prime p,
    and an exponent m, return the submodule of elements y
    such that <x,y> = 0 mod p^m for all x in N.}
    M := AmbientModule(N);
    n := Degree(N);
    A := InnerProductMatrix(N);
    B := Transpose(Matrix([ &+[ x[i] * A[i] : i in [1..n] ] : x in Basis(N) ]));
    R := pAdicQuotientRing(p,m);
    Mat := RMatrixSpace(R,n,Rank(N));
    return sub< M | [ M!v : v in Basis(Kernel(Mat!B)) ] cat [ p^m*u : u in Basis(M) ] >;
end intrinsic;

intrinsic pAdicTangentNeighborhood(x::ModTupRngElt[RngInt],
    p::RngIntElt,m::RngIntElt,r::RngIntElt) -> ModTupRng
    {Given a vector x in an integral quadratic module M,
    a prime p, and precision m, and a radius r, return
    the submodule ZZ*x + p^r N, where N is the p-adic dual
    subspace of x in M.}
    D := pAdicDualSpace(x,p,m);
    return sub< Parent(x) | [ x ] cat [ p^r*y : y in Basis(D) ] >;
end intrinsic;

intrinsic pAdicTangentNeighborhood(N::ModTupRng[RngInt],
    p::RngIntElt,m::RngIntElt,r::RngIntElt) -> ModTupRng
    {Given a submodule N of an integral quadratic module M,
    a prime p, and precision m, and a radius r, return
    the submodule N + p^r T, where T is the p-adic dual 
    space of N.}
    M := AmbientModule(N);
    T := pAdicDualSpace(N,p,m);
    return sub< M | Basis(N) cat [ p^r*y : y in Basis(T) ] >;
end intrinsic;

