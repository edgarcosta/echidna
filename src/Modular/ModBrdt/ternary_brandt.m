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

function HasHenselLift(v,p)
    // Given a vector v with (v,v) = 0 mod p (or 4 = p^2), 
    // determines whether there exists an p-adic lifting, 
    // and if so returns a vector of norm divisible by p^2 
    // (or 8 when p = 2).
    // 
    // For p = 2, a vector of norm divisible by 4 is changed by 
    // a vector in 2*L such that the norm is divisible by 8.
    //
    // For p > 2 a vector of norm divisible by p is changed by 
    // a vector in p*L such that the norm is divisible by p^2.
    // Returns false if v does not lift p-adically.
    // 
    n := Norm(v);
    if n mod p ne 0 then return false, _; end if;
    if p eq 2 then
	if n mod 4 ne 0 then return false, _; end if;
	if n mod 8 ne 0 then
	    B := [ b : b in Basis(Parent(v)) | (v,b) mod 2 eq 1 ];
	    if #B eq 0 then return false, _; end if;
	    return true, v + 2*B[1];
	end if;
    else
	if n mod p^2 ne 0 then
	    B := [ b : b in Basis(Parent(v)) | (v,b) mod p ne 0 ];
            if #B eq 0 then return false, _; end if;
	    return true, v - (n*Modinv(2*(v,B[1]),p) mod p^2)*B[1]; 
	end if;
   end if;
   return true, v;
end function;

function GoodReduction(L1)
    ZZ := IntegerRing();
    QQ := RationalField();
    PP<X,Y,Z> := ProjectiveSpace(QQ,2);
    XX := [X,Y,Z];
    A1 := GramMatrix(L1);
    f1 := &+[ A1[i,j]*XX[i]*XX[j] : i, j in [1..3] ];
    C0, m0 := MinimalModel(Conic(PP,f1));
    f0 := Universe(XX)!DefiningPolynomial(C0);
    A0 := Parent(A1)!0;
    for i in [1..3] do
        A0[i,i] := 2*MonomialCoefficient(f0,XX[i]^2);
        for j in [i+1..3] do
            A0[i,j] := MonomialCoefficient(f0,XX[i]*XX[j]);
            A0[j,i] := A0[i,j];
        end for;
    end for;
    c0 := GCD([ ZZ!c : c in Eltseq(A0) ]);
    A0 *:= 1/c0;
    //L0 := LatticeWithGram(A0);
    U0 := Matrix(m0);
    return C0, A0, U0;
end function;

function pIsotropicSublattice(L,p)
    ZZ := IntegerRing();
    FF := FiniteField(p);
    MatF := MatrixAlgebra(FF,3);
    N := Kernel(MatF!GramMatrix(L));
    return sub< L | [ p*L.i : i in [1..3] ] cat [ L![ ZZ!c : c in Eltseq(v) ] : v in Basis(N) ] >;
end function;

function AtkinLehnerMatrix(G)
    return 1;
end function;

function HeckeMatrix2(G)
    // The quadratic form is singular -- use bilinear form.
    return 0;
end function;

intrinsic HeckeMatrix(G::SymGen,ell::RngIntElt) -> AlgMatElt
    {}
    if ell eq 2 then return HeckeMatrix2(G); end if;
    error if Determinant(G) mod ell eq 0, "Prime is not nonsingular.";
    ZZ := IntegerRing();
    FF := FiniteField(ell);
    RepsG := Representatives(G);
    Grams := {@ MinkowskiGramReduction(GramMatrix(Li) : Canonical) : Li in RepsG @};
    PP<X,Y,Z> := ProjectiveSpace(FF,2); XX := [X,Y,Z];
    BB := [ ];
    for Lk in RepsG do
        Ak := GramMatrix(Lk);
        fell := &+[ Ak[i,j]*XX[i]*XX[j] : i, j in [1..3] ];
        Ck := Conic(PP,fell);
        u := [ 0 : i in [1..#G] ];
        Pnts := RationalPoints(Ck);
        for P in Pnts do
            v := Lk![ ZZ!x : x in Eltseq(P) ];
            bool, v := HasHenselLift(v,ell); assert bool;
            A := GramMatrix(Neighbor(Lk,v,ell));
            A := MinkowskiGramReduction(A : Canonical);
            u[Index(Grams,A)] +:= 1;
        end for;
        Append(~BB,u);
    end for;
    return Matrix(BB);
end intrinsic;

intrinsic OrientedHeckeMatrix(G::SymGen,p::RngIntElt,ell::RngIntElt) -> AlgMatElt
    {}
    MatZ := MatrixAlgebra(IntegerRing(),3);
    error if Determinant(G) mod ell eq 0, "Prime is not nonsingular.";
    RepsG := [ Li : Li in Representatives(G) | #AutomorphismGroup(Li) eq 2 ];
    Grams := {@ MinkowskiGramReduction(GramMatrix(Li) : Canonical) : Li in RepsG @};
    ZZ := IntegerRing();
    FF := FiniteField(ell);
    PP<X,Y,Z> := ProjectiveSpace(FF,2); XX := [X,Y,Z];
    O := pOrientations(G,p);
    BB := [ ];
    for Li in RepsG do
        ti := O[Li];
        Ai := GramMatrix(Li);
        fell := &+[ Ai[i,j]*XX[i]*XX[j] : i, j in [1..3] ];
        Ci := Conic(PP,fell);
        u := [ 0 : i in [1..#RepsG] ];
        for Pij in RationalPoints(Ci) do
            vij := Li![ ZZ!x : x in Eltseq(Pij) ];
            bool, vij := HasHenselLift(vij,ell); assert bool;
            Lj := Neighbor(Li,vij,ell);
            // The basis matrix is encoded in Lj.i, but we need its determinant:
            Tj := BasisMatrix(Lj);
            if Determinant(Tj) lt 0 then sgn := -1; else sgn := 1; end if;
            Aj, Uj := MinkowskiGramReduction(GramMatrix(Lj) : Canonical);
            if Determinant(Uj) lt 0 then Uj *:= -1; end if;
            j := Index(Grams,Aj); if j eq 0 then continue; end if;
            vj := 1@@O[RepsG[j]]; // Preimage vj -> 1 
            uj := sgn * &+[ cj[i]*Lj.i : i in [1..3] ] where cj := Eltseq(vj*Uj);
            assert Norm(vj) eq Norm(uj);
            chi := 1/ell*ti(Li!(ell*uj));
            if chi^2 ne 1 then print chi; assert false; end if;
            u[j] +:= chi eq 1 select 1 else -1;
        end for;
        Append(~BB,u);
    end for;
    return Matrix(BB);
end intrinsic;

intrinsic DiscriminantGenus(N::RngIntElt,M::RngIntElt) -> RngIntElt
    {}
    O := QuaternionOrder(N,M);
    G := Genus(DiscriminantModule(O));
    Grams := [ MinkowskiGramReduction(GramMatrix(L) : Canonical) : L in Representatives(G) ];
    RepsG := [ LatticeWithGram(A) : A in Grams ];
    G`Representative := RepsG[1];
    G`Representatives := RepsG;
    return G;
end intrinsic;

intrinsic Orientations(G::SymGen) -> Assoc
    {}
    L := Representative(G);
    O := AssociativeArray(Parent(L));
    MatQ := MatrixAlgebra(RationalField(),3);
    RepsG := Representatives(G);
    Grams := [ MinkowskiGramReduction(GramMatrix(L) : Canonical) : L in RepsG ];
    i := 1;
    while Grams[i][1,1] in {3,4} do
        i +:= 1;
    end while;
    O[RepsG[i]] := MatQ!1;
    Frontier := { RepsG[i] };
    KnownGrams := { Grams[i] };
    ell := 3;
    while Determinant(G) mod ell eq 0 do ell := NextPrime(ell); end while;
    while #Frontier ne 0 do
        NewFrontier := {};
        //print "Frontier size:", #Frontier;
        for M in Frontier do
            Ai := MatQ!GramMatrix(M);
            for N in Neighbors(M,ell) do
                Bj := MatQ!GramMatrix(N);
                Aj, Uj := MinkowskiGramReduction(Bj : Canonical);
                if Aj notin KnownGrams then
                    Include(~KnownGrams,Aj);
                    if Index(Grams,Aj) eq 0 then
                        print Grams;
                        print "Aj:"; print Aj;
                    end if;
                    j := Index(Grams,Aj); assert j ne 0;
                    Lj := RepsG[j];
                    Include(~NewFrontier,Lj);
                    Tj :=  MatQ!Uj * BasisMatrix(N) * O[M];
                    if Determinant(Tj) lt 0 then Tj *:= -1; end if;
                    O[Lj] :=  Tj;
                end if;
            end for;
        end for;
        Frontier := NewFrontier;
    end while;
    return O;
end intrinsic;

intrinsic pOrientations(G::SymGen,p::RngIntElt) -> Assoc
    {}
    ZZ := IntegerRing();
    QQ := RationalField();
    FF := FiniteField(p);
    MatZ := MatrixAlgebra(ZZ,3);
    MatQ := MatrixAlgebra(QQ,3);
    RepsG := Representatives(G);
    oOrient := Orientations(G);
    pOrient := AssociativeArray(Universe(RepsG));
    i := 1;
    while oOrient[RepsG[i]] ne MatQ!1 do
        i +:= 1;
    end while;
    L := RepsG[i];
    N := BasisMatrix(pIsotropicSublattice(L,p));
    X, m := quo< L | N >; assert #X eq p;
    u := [ FF!Eltseq(m(v))[1] : v in Basis(L) ];
    j := [ i : i in [1..3] | u[i] ne 0 ][1];
    c := u[j]^-1;
    u := [ c*u[i] : i in [1..3] ];
    v1 := L.j;
    VQ := VectorSpace(QQ,3);
    for Lj in RepsG do
        Tj := oOrient[Lj];
        vj := VQ!Eltseq(v1)*Tj^-1;
        dj := LCM([ Denominator(c) : c in Eltseq(vj) ]);
        vj := Lj!(dj*vj);
        pOrient[Lj] := map< Lj->FF |
            v :-> &+[ u[i]*vTj[i] : i in [1..3] ] where vTj := VQ!Eltseq(v)*Tj, a :-> ZZ!(a/dj)*vj >;
    end for;
    return pOrient;
end intrinsic;



    
