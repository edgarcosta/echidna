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

intrinsic SudokuExamples() -> SeqEnum
    {A sequence of defining matrices for hard Sudoku puzzles.}
    // The example from Sage documentation:
    ZZ := IntegerRing();
    // No. 1: David Filmer's Unsolvable #49
    A1 := Matrix(ZZ,9,[
        0,0,2,8,0,0,0,0,0, 0,3,0,0,6,0,0,0,7, 1,0,0,0,0,0,0,4,0,
        6,0,0,0,9,0,0,0,0, 0,5,0,6,0,0,0,0,9, 0,0,0,0,5,7,0,6,0,
        0,0,0,3,0,0,1,0,0, 0,7,0,0,0,6,0,0,8, 4,0,0,0,0,0,0,2,0]);
    // No. 2: David Filmer's Unsolvable #28
    A2 := Matrix(ZZ,9,[
        6,0,0,0,0,8,9,4,0, 9,0,0,0,0,6,1,0,0, 0,7,0,0,4,0,0,0,0,
        2,0,0,6,1,0,0,0,0, 0,0,0,0,0,0,2,0,0, 0,8,9,0,0,2,0,0,0,
        0,0,0,0,6,0,0,0,5, 0,0,0,0,0,0,0,3,0, 8,0,0,0,0,1,6,0,0]);
    // No. 3: The world's hardest (UK Telegraph) by Arto Inala
    A3 := Matrix(ZZ,9,[
        8,0,0,0,0,0,0,0,0, 0,0,3,6,0,0,0,0,0, 0,7,0,0,9,0,2,0,0,
        0,5,0,0,0,7,0,0,0, 0,0,0,0,4,5,7,0,0, 0,0,0,1,0,0,0,3,0,
        0,0,1,0,0,0,0,6,8, 0,0,8,5,0,0,0,1,0, 0,9,0,0,0,0,4,0,0]);
    // No. 4: Escargot by Arto Inala (???)
    A4 := Matrix(ZZ,9,[
        1,0,0,0,0,0,7,0,0, 0,0,7,1,0,9,0,0,0, 6,8,0,0,7,0,0,0,0,
        0,0,1,0,9,0,6,0,0, 0,0,0,3,0,0,0,2,0, 0,4,0,0,0,0,0,0,3,
        0,0,8,0,6,0,1,0,0, 5,0,0,0,0,0,0,4,0, 0,0,0,0,0,2,0,0,5]);
    // No. 4: Escargot by Arto Inala (???)
    A5 := Matrix(ZZ,9,[
        1,0,0,0,0,7,0,9,0, 0,3,0,0,2,0,0,0,8, 0,0,9,6,0,0,5,0,0,
        0,0,5,3,0,0,9,0,0, 0,1,0,0,8,0,0,0,2, 6,0,0,0,0,4,0,0,0,
        3,0,0,0,0,0,0,1,0, 0,4,1,0,0,0,0,0,7, 0,0,7,0,0,0,3,0,0]);
    // More challenging Sudoku:
    A6 := Matrix(ZZ,9,[
        0,0,2,5,0,0,0,0,7, 0,5,0,0,3,0,0,2,0, 6,0,0,0,0,1,3,0,0,
        7,0,0,0,0,5,1,0,0, 0,1,0,0,9,0,0,7,0, 0,0,3,8,0,0,0,0,5,
        0,0,6,9,0,0,0,0,2, 0,8,0,0,6,0,0,3,0, 5,0,0,0,0,2,4,0,0]);
    // Wikipedia's brute force hard puzzle (doesn't seem too hard)
    A7 := Matrix(ZZ,9,[
        0,0,0,0,0,0,0,0,0, 0,0,0,0,0,3,0,8,5, 0,0,1,0,2,0,0,0,0,
        0,0,0,5,0,7,0,0,0, 0,0,4,0,0,0,1,0,0, 0,9,0,0,0,0,0,0,0,
        5,0,0,0,0,0,0,7,3, 0,0,2,0,1,0,0,0,0, 0,0,0,0,4,0,0,0,9]);
    // Sudoku from Sage examples (trivial)
    A8 := Matrix(ZZ,9,[
        5,0,0, 0,8,0, 0,4,9, 0,0,0, 5,0,0, 0,3,0, 0,6,7, 3,0,0, 0,0,1,
        1,5,0, 0,0,0, 0,0,0, 0,0,0, 2,0,8, 0,0,0, 0,0,0, 0,0,0, 0,1,8,
        7,0,0, 0,0,4, 1,5,0, 0,3,0, 0,0,2, 0,0,0, 4,9,0, 0,5,0, 0,0,3]);
    A9 := Matrix(ZZ,9,[
        0,0,6, 0,2,0, 0,5,0, 5,7,0, 0,0,0, 2,0,0, 0,0,0, 0,0,4, 0,8,0,
        6,0,0, 0,1,3, 0,0,9, 0,0,0, 0,9,0, 0,0,0, 3,0,0, 6,7,0, 0,0,4,
        0,8,0, 2,0,0, 0,0,0, 0,0,5, 0,0,0, 0,1,3, 0,6,0, 0,5,0, 7,0,0]);
    return [A1,A2,A3,A4,A5,A6,A7,A8,A9];
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

function SudokuMaskField(n)
    assert n gt 1;
    if n eq 6 then q := 7; else q := n; end if;
    if q in {2,3,5,7} then
        FF := FiniteField(q);
        ff := AssociativeArray({1..n});
        for a in [1..n] do ff[a] := FF!a; end for;
        gg := AssociativeArray(FF);
        for a in [1..n-1] do gg[FF!a] := a; end for;
        gg[FF!0] := q;
    elif q in {4,8,9} then
        FF<w> := FiniteField(q); s := PrimitiveElement(FF);
        ff := AssociativeArray({1..n});
        ff[q] := FF!0;
        for a in [1..q-1] do ff[a] := s^a; end for;
        gg := AssociativeArray(FF);
        gg[FF!0] := q;
        for a in [1..q-1] do gg[s^a] := a; end for;
    end if;
    return ff, gg;
end function;

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

intrinsic SudokuMaskingMatrix(A::AlgMatElt,a::RngIntElt) -> AlgMatElt
    {The 1-masking matrix with entries a -> 1 and b != a -> 2
    and 0's (unknown) remaining 0.}
    dsquare := Degree(Parent(A));
    require a ge 1 and a le dsquare:
        "Argument 2 must be between 1 and " * Sprint(dsquare) * ".";
    ZZ := IntegerRing();
    B := MatrixAlgebra(ZZ,dsquare)!0;
    for i,j in [1..dsquare] do
        case A[i,j]:
        when 0:
            B[i,j] := 0; // do nothing
        when a:
            B[i,j] := 1;
        else
            B[i,j] := 2;
        end case;
    end for;
    return B;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
// Helper functions for Sudoku mask update
//////////////////////////////////////////////////////////////////////////////

intrinsic PruneMask1(B::AlgMatElt) -> AlgMatElt
    {Assumes B is a masking matrix with entries 0,1,2,
    multiplicities 1 for 1 in each row, column, and
    deg x deg block.}
    dsquare := Degree(Parent(B));
    bool, deg := IsSquare(dsquare);
    require bool : "Argument 1 must be a matrix of square degree.";
    for i,j in [1..dsquare] do
        if B[i,j] eq 1 then
            // Clear row:
            for l in [1..dsquare] do
                if l ne j then
                    B[i,l] := B[i,l] eq 1 select 1 else 2;
                end if;
            end for;
            // Clear column:
            for k in [1..dsquare] do
                if k ne i then
                    B[k,j] := B[k,j] eq 1 select 1 else 2;
                end if;
            end for;
        end if;
    end for;
    // Clear deg x deg blocks:
    for i1,j1 in [0..dsquare-deg by deg] do
        if 1 in { B[i0+i1,j0+j1] : i0,j0 in [1..deg] } then
            for i0,j0 in [1..deg] do
                if B[i0+i1,j0+j1] ne 1 then
                    B[i0+i1,j0+j1] := B[i0+i1,j0+j1] eq 1 select 1 else 2;
                end if;
            end for;
        end if;
        I := {}; J := {};
        for i0, j0 in [1..deg] do
            if B[i0+i1,j0+j1] ne 2 then
                Include(~I,i0+i1);
                Include(~J,j0+j1);
            end if;
        end for;
        if #I eq 1 then
            // Set all row entries outside of the block to 2
            i := Representative(I);
            for j in [1..dsquare] do
                if (j-1) - ((j-1) mod deg) ne j1 then
                    B[i,j] := B[i,j] eq 1 select 1 else 2;
                end if;
            end for;
        end if;
        if #J eq 1 then
            // Set all col entries outside of the block to 2
            j := Representative(J);
            for i in [1..dsquare] do
                if (i-1) - ((i-1) mod deg) ne i1 then
                    B[i,j] := B[i,j] eq 1 select 1 else 2;
                end if;
            end for;
        end if;
    end for;
    return B;
end intrinsic;

function PruneQuad1Rows(B)
    dsquare := Degree(Parent(B)); bool, deg := IsSquare(dsquare);
    error if not bool, "Argument must be a matrix of square degree.";
    I := {};
    for i in [1..dsquare] do
        ex := [ j : j in [1..dsquare] | B[i,j] eq 0 ];
        if #ex eq 2 then Include(~I,<i,ex>); end if;
    end for;
    for S in Subsets(I,2) do
        ij1, ij2 := Explode(SetToSequence(S));
        if ij1[2] eq ij2[2] then
            i1 := ij1[1];
            i2 := ij2[1];
            j1, j2 := Explode(ij1[2]);
            for i in [1..dsquare] do
                if i notin {i1,i2} then
                    B[i,j1] := 2;
                    B[i,j2] := 2;
                end if;
            end for;
        end if;
    end for;
    return B;
end function;

intrinsic PruneQuad1(B::AlgMatElt) -> AlgMatElt
    {Given a 1-masking matrix B such that there is at most
    one 1 in each row, column and block, and "pruned" such
    that if such a 1 appears the remaining entries are 2.
    Find configurations I = [i1,i2] and J = [j1,j2] such
    that all entries in I x J are unknown (= 0), and
    set entries in the rows I and columns J, outside I x J,
    to 2 (opposing option).}
    return Transpose(PruneQuad1Rows(Transpose(PruneQuad1Rows(B))));
end intrinsic;

function UniqueSubs1(B)
    // INPUT: A pruned 1-masking matrix -- any row, column, or block
    // containing a 1 has only 2's.
    // OUTPUT: The matrix with any isolated 0's converted to 1's.
    dsquare := Degree(Parent(B)); bool, deg := IsSquare(dsquare);
    error if not bool, "Argument must be a matrix of square degree.";
    // Assume any row or column with a 1 is already pruned, so look for a lone 0:
    for i,j in [1..dsquare] do
        if B[i,j] eq 0 then
            if #[ k : k in [1..dsquare] | B[k,j] ne 2 ] eq 1 then
                // Unique substitution of 1 in row:
                B[i,j] := 1;
                // Prune column:
                for l in [1..dsquare] do
                    if l ne j then B[i,l] := 2; end if;
                end for;
                // Prune block:
                i1 := deg*((i-1) div deg);
                j1 := deg*((j-1) div deg);
                for i0, j0 in [1..deg] do
                    if i0+i1 ne i or j0+j1 ne j then B[i0+i1,j0+j1] := 2; end if;
                end for;
            end if;
            if #[ l : l in [1..dsquare] | B[i,l] ne 2 ] eq 1 then
                // Unique substitution of 1 in column:
                B[i,j] := 1;
                // Prune row:
                for k in [1..dsquare] do
                    if k ne i then B[k,j] := 2; end if;
                end for;
                // Prune block:
                i1 := deg*((i-1) div deg);
                j1 := deg*((j-1) div deg);
                for i0, j0 in [1..deg] do
                    if i0+i1 ne i or j0+j1 ne j then B[i0+i1,j0+j1] := 2; end if;
                end for;
            end if;
        end if;
    end for;
    // Assume any block with a 1 is already pruned, so look for a lone 0:
    for i1, j1 in [0..dsquare-deg by deg] do
        if #{ [i0,j0] : i0, j0 in [1..deg] | B[i0+i1,j0+j1] eq 0 } eq 1 then
            // Unique substitution of 1 in block:
            for i0, j0 in [1..deg] do
                if B[i0+i1,j0+j1] eq 0 then
                    B[i0+i1,j0+j1] := 1;
                    // Prune row:
                    for i in [1..dsquare] do
                        if i ne i0+i1 then B[i,j0+j1] := 2; end if;
                    end for;
                    // Prune col:
                    for j in [1..dsquare] do
                        if j ne j0+j1 then B[i0+i1,j] := 2; end if;
                    end for;
                end if;
            end for;
        end if;
    end for;
    return B;
end function;

intrinsic PruneOrientedQuad1(B) -> SetEnum
    {}
    // Make lists of unknown distinguished pairs
    // in rows, columns, or blocks
    dsquare := Degree(Parent(B)); bool, deg := IsSquare(dsquare);
    require bool : "Argument must be a matrix of square degree.";
    E := {@ @};
    for i in [1..dsquare] do
        ee := {@ [i,j] : j in [1..dsquare] | B[i,j] eq 0 @};
        if #ee eq 2 then Include(~E,ee); end if;
    end for;
    for j in [1..dsquare] do
        ee := {@ [i,j] : i in [1..dsquare] | B[i,j] eq 0 @};
        if #ee eq 2 then Include(~E,ee); end if;
    end for;
    for i1, j1 in [0..dsquare-deg by deg] do
        ee := {@ [i0+i1,j0+j1] : i0,j0 in [1..deg] | B[i0+i1,j0+j1] eq 0 @};
        if #ee eq 2 then Include(~E,ee); end if;
    end for;
    V := &join E;
    A := MatrixAlgebra(IntegerRing(),#V)!0;
    for ee in E do
        i := Index(V,ee[1]);
        j := Index(V,ee[2]);
        A[i,j] := 1; A[j,i] := 1;
    end for;
    n := #V;
    S1 := &join[ Parent({@[[1,2]]@}) |
        {@ [V[i],V[j]] : j in [i+1..n] | A[i,j] ne 0 @} : i in [1..n-1] ];
    for k in [3,5] do
        Ak := A^k; // Construct the adjacency map for vertices at distance k.
        Sk := &join[ {@ [ V[i],V[j] ] : j in [i+1..n] | Ak[i,j] ne 0 @} : i in [1..n-1] ];
        Sk := {@ ee : ee in Sk | ee notin S1 and
            ee[1][1] ne ee[2][1] and
            ee[1][2] ne ee[2][2] @};
        for ee in Sk do
            v1 := ee[1]; v2 := ee[2];
            i1, j1 := Explode(v1);
            i2, j2 := Explode(v2);
            if i1 eq i2 or j1 eq j2 then continue; end if;
            B[i1,j2] := 2;
            B[i2,j1] := 2;
        end for;
        S1 join:= Sk;
    end for;
    return B, A;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

intrinsic SudokuMaskUpdate(B::AlgMatElt) -> AlgMatElt
    {}
    dsquare := Degree(Parent(B)); bool, deg := IsSquare(dsquare);
    require bool : "Argument must be a matrix of square degree.";
    B := UniqueSubs1(PruneMask1(B));
    B := UniqueSubs1(PruneQuad1(B));
    B := UniqueSubs1(PruneOrientedQuad1(B));
    return B;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

intrinsic ApplySudokuMask(A::AlgMatElt,B::AlgMatElt,a::RngIntElt) -> AlgMatElt
    {}
    dsquare := Degree(Parent(B));
    for i,j in [1..dsquare] do
        if B[i,j] eq 1 then A[i,j] := a; end if;
    end for;
    return A;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

intrinsic SudokuUpdate(A::AlgMatElt) -> AlgMatElt
    {Recursively update}
    dsquare := Degree(Parent(A)); bool, deg := IsSquare(dsquare);
    require bool : "Argument 1 must be a matrix of square degree.";
    change := false;
    for a in [1..dsquare] do
        B := SudokuMaskUpdate(SudokuMaskingMatrix(A,a));
        N := ApplySudokuMask(A,B,a);
        if A ne N then
            A := N; change := true;
            //printf "nums (a = %o): %o\n", a, {* c : c in Eltseq(A) | c ne 0 *};
        end if;
    end for;
    if change then
        return SudokuUpdate(A);
    else
        return A;
    end if;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

intrinsic SudokuExtensions(A::AlgMatElt) -> SeqEnum
    {The possible Sudoku extensions using an incomplete entry of highest multiplicity.}
    dsquare := Degree(Parent(A)); bool, deg := IsSquare(dsquare);
    require bool : "Argument 1 must be a matrix of square degree.";
    counts := {* c : c in Eltseq(A) | c ne 0 *};
    if #counts eq dsquare^2 then return [A]; end if;
    mm := [ Multiplicity(counts,i) mod dsquare : i in [1..dsquare] ];
    mi, k := Maximum(mm);
    return SudokuExtensions(A,k);
end intrinsic;

intrinsic SudokuExtensions(A::AlgMatElt,k::RngIntElt) -> SeqEnum
    {The possible Sudoku extensions of entry k.}
    dsquare := Degree(Parent(A));
    require 1 le k and k le dsquare :
        "Argument 2 must be between 1 and " * Sprint(k) * ".";
    Bk := SudokuMaskUpdate(SudokuMaskingMatrix(A,k));
    return [ SudokuUpdate(ApplySudokuMask(A,B,k)) : B in SudokuMaskSplittings(Bk) ];
end intrinsic;

intrinsic SudokuExtensions(A::AlgMatElt,S::SetEnum[SeqEnum[RngIntElt]]) -> SeqEnum
    {The possible Sudoku extensions using an incomplete entry of highest multiplicity.}
    dsquare := Degree(Parent(A)); bool, deg := IsSquare(dsquare);
    require bool : "Argument 1 must be a matrix of square degree.";
    counts := {* c : c in Eltseq(A) | c ne 0 *};
    if #counts eq dsquare^2 then return [A]; end if;
    Scounts := {* A[ij[1],ij[2]] : ij in S | A[ij[1],ij[2]] ne 0 *};
    mm := [ Multiplicity(counts,i) eq dsquare
        select 0 else Multiplicity(Scounts,i) : i in [1..dsquare] ];
    mi, k := Maximum(mm);
    return SudokuExtensions(A,k,S);
end intrinsic;

intrinsic SudokuExtensions(A::AlgMatElt,k::RngIntElt,S::SetEnum[SeqEnum[RngIntElt]]) -> SeqEnum
    {The possible Sudoku extensions of entry k.}
    dsquare := Degree(Parent(A));
    require 1 le k and k le dsquare :
        "Argument 2 must be between 1 and " * Sprint(k) * ".";
    Bk := SudokuMaskUpdate(SudokuMaskingMatrix(A,k));
    return [ SudokuUpdate(ApplySudokuMask(A,B,k)) : B in SudokuMaskSplittings(Bk,S) ];
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

intrinsic SudokuMaskIdeal(B::AlgMatElt : Coordinates := false) -> RngMPol
    {Given a 1-masking matrix that has been pre-processed so
    that if there were a 1 in a row, column, or block, then
    there is no 0 (and conversely), returns the ideal of Sudoku
    relations for the partition [[1],[2..n]].}
    dsquare := Degree(Parent(B)); bool, deg := IsSquare(dsquare);
    require bool : "Argument must be a matrix of square degree.";
    I0 := [ i : i in [1..dsquare] | 0 in Eltseq(B[i]) ];
    J0 := [ j : j in [1..dsquare] | 0 in Eltseq(C[j]) ] where C := Transpose(B);
    S0 := {@ [i,j] : i in I0, j in J0 | B[i,j] eq 0 @};
    n := 2;
    if Type(Coordinates) eq BoolElt then
        ff := SudokuMaskField(n);
    else
        ff := Coordinates;
    end if;
    require Type(ff) eq Assoc :
        "Parameter \"Coordinates\" must be an associative array.";
    require Universe(ff) eq {1,2} :
        "Universe of \"Coordinates\" must be the set {1,2}.";
    require Keys(ff) eq {1..n} :
        "Keys of \"Coordinates\" must be the set {1,2}.";
    FF := Parent(ff[1]);
    P := PolynomialRing(FF,#S0);
    AssignNames(~P,[ "X" * Sprint(ij[1]) * Sprint(ij[2]) : ij in S0 ]);
    B := [ (P.k-ff[1])*(P.k-ff[2]) : k in [1..#S0] ];
    R<x> := PolynomialRing(P);
    // Row relations:
    for i in I0 do
        IJ0 := [ ij : ij in S0 | ij[1] eq i ];
        if #IJ0 eq 0 then continue; end if;
        charpoly := (x-ff[1])*(x-ff[2])^(#IJ0-1);
        fij := &*[ x - P.Index(S0,ij) : ij in IJ0 ];
        B cat:= Eltseq(fij - charpoly);
    end for;
    // Column relations:
    for j in J0 do
        IJ0 := [ ij : ij in S0 | ij[2] eq j ];
        if #IJ0 eq 0 then continue; end if;
        charpoly := (x-ff[1])*(x-ff[2])^(#IJ0-1);
        fij := &*[ x - P.Index(S0,ij) : ij in IJ0 ];
        B cat:= Eltseq(fij - charpoly);
    end for;
    // Block relations:
    for i,j in [0..dsquare-deg by deg] do
        IJ0 := [ ij : ij in S0 | (ij[1]-i) in [1..deg] and (ij[2]-j) in [1..deg] ];
        if #IJ0 eq 0 then continue; end if;
        charpoly := (x-ff[1])*(x-ff[2])^(#IJ0-1);
        fij := &*[ x - P.Index(S0,ij) : ij in IJ0 ];
        B cat:= Eltseq(fij - charpoly);
    end for;
    return ideal< P | B >, S0;
end intrinsic;

intrinsic SudokuMaskIdeal(B::AlgMatElt,I::SeqEnum[RngIntElt],J::SeqEnum[RngIntElt] :
    Coordinates := false) -> RngMPol
    {Given a 1-masking matrix that has been pre-processed so
    that if there were a 1 in a row, column, or block, then
    there is no 0 (and conversely), returns the ideal of Sudoku
    relations for the partition [[1],[2..n]].}
    dsquare := Degree(Parent(B));  bool, deg := IsSquare(dsquare);
    require bool : "Argument must be a matrix of square degree.";
    I0 := [ i : i in I | 0 in Eltseq(B[i]) ];
    J0 := [ j : j in J | 0 in Eltseq(C[j]) ] where C := Transpose(B);
    S0 := {@ [i,j] : i in I0, j in J0 | B[i,j] eq 0 @};
    n := 2;
    if Type(Coordinates) eq BoolElt then
        ff := SudokuMaskField(n);
    else
        ff := Coordinates;
    end if;
    require Type(ff) eq Assoc :
        "Parameter \"Coordinates\" must be an associative array.";
    require Universe(ff) eq {1..n} :
        "Universe of \"Coordinates\" must be the set {1..#P}.";
    require Keys(ff) eq {1..n} :
        "Keys of \"Coordinates\" must be the set {1..#P}.";
    FF := Parent(ff[1]);
    P := PolynomialRing(FF,#S0);
    AssignNames(~P,[ "X" * Sprint(ij[1]) * Sprint(ij[2]) : ij in S0 ]);
    rels := [ (P.k-ff[1])*(P.k-ff[2]) : k in [1..#S0] ];
    R<x> := PolynomialRing(P);
    Iset := SequenceToSet(I);
    Jset := SequenceToSet(J);
    if Jset eq {1..dsquare} then
        // Row relations:
        for i in I0 do
            IJ0 := [ ij : ij in S0 | ij[1] eq i ];
            if #IJ0 eq 0 then continue; end if;
            charpoly := (x-ff[1])*(x-ff[2])^(#IJ0-1);
            fij := &*[ x - P.Index(S0,ij) : ij in IJ0 ];
            rels cat:= Eltseq(fij - charpoly);
        end for;
    end if;
    if Iset eq {1..dsquare} then
        // Column relations:
        for j in J0 do
            IJ0 := [ ij : ij in S0 | ij[2] eq j ];
            if #IJ0 eq 0 then continue; end if;
            charpoly := (x-ff[1])*(x-ff[2])^(#IJ0-1);
            fij := &*[ x - P.Index(S0,ij) : ij in IJ0 ];
            rels cat:= Eltseq(fij - charpoly);
        end for;
    end if;
    // Block relations:
    for i1, j1 in [0..dsquare-deg by deg] do
        if not {i1+1..i1+deg} subset Iset then continue; end if;
        if not {j1+1..j1+deg} subset Jset then continue; end if;
        IJ0 := [ ij : ij in S0 | (ij[1]-i1) in [1..deg] and (ij[2]-j1) in [1..deg] ];
        if #IJ0 eq 0 then continue; end if;
        charpoly := (x-ff[1])*(x-ff[2])^(#IJ0-1);
        fij := &*[ x - P.Index(S0,ij) : ij in IJ0 ];
        rels cat:= Eltseq(fij - charpoly);
    end for;
    rels := [ rel : rel in SequenceToSet(rels) | rel ne 0 ];
    return ideal< P | rels >, S0;
end intrinsic;

intrinsic SudokuMaskIdeal(B::AlgMatElt,S::SetEnum[SeqEnum] : Coordinates := false) -> RngMPol
    {Given a 1-masking matrix that has been pre-processed so
    that if there were a 1 in a row, column, or block, then
    there is no 0 (and conversely), returns the ideal of Sudoku
    relations for the partition [[1],[2..n]].}
    dsquare := Degree(Parent(B));  bool, deg := IsSquare(dsquare);
    require bool : "Argument must be a matrix of square degree.";
    S0 := {@ [i,j] : i, j in [1..dsquare] | [i,j] in S and B[i,j] eq 0 @};
    I0 := [ ij[1] : ij in S0 ];
    J0 := [ ij[2] : ij in S0 ];
    n := 2;
    if Type(Coordinates) eq BoolElt then
        ff := SudokuMaskField(n);
    else
        ff := Coordinates;
    end if;
    require Type(ff) eq Assoc :
        "Parameter \"Coordinates\" must be an associative array.";
    require Universe(ff) eq {1..n} :
        "Universe of \"Coordinates\" must be the set {1..#P}.";
    require Keys(ff) eq {1..n} :
        "Keys of \"Coordinates\" must be the set {1..#P}.";
    FF := Parent(ff[1]);
    P := PolynomialRing(FF,#S0);
    AssignNames(~P,[ "X" * Sprint(ij[1]) * Sprint(ij[2]) : ij in S0 ]);
    rels := [ (P.k-ff[1])*(P.k-ff[2]) : k in [1..#S0] ];
    R<x> := PolynomialRing(P);
    // Row relations:
    for i in I0 do
        IJ0 := [ ij : ij in S0 | ij[1] eq i ];
        // Make sure the only unknowns of the row are in S
        if #IJ0 eq 0 then
            continue; // no unknown in S
        elif #[ [i,j] : j in [1..dsquare] | B[i,j] eq 0 ] gt #IJ0 then
            continue; // another unknown outside S
        end if;
        charpoly := (x-ff[1])*(x-ff[2])^(#IJ0-1);
        fij := &*[ x - P.Index(S0,ij) : ij in IJ0 ];
        rels cat:= Eltseq(fij - charpoly);
    end for;
    // Column relations:
    for j in J0 do
        IJ0 := [ ij : ij in S0 | ij[2] eq j ];
        // Make sure the only unknowns of the column are in S
        if #IJ0 eq 0 then
            continue; // no unknown in S
        elif #[ [i,j] : i in [1..dsquare] | B[i,j] eq 0 ] gt #IJ0 then
            continue; // another unknown outside S
        end if;
        charpoly := (x-ff[1])*(x-ff[2])^(#IJ0-1);
        fij := &*[ x - P.Index(S0,ij) : ij in IJ0 ];
        rels cat:= Eltseq(fij - charpoly);
    end for;
    // Block relations:
    for i1, j1 in [0..dsquare-deg by deg] do
        IJ0 := [ [i0+i1,j0+j1] :  i0, j0 in [1..deg] | [i0+i1,j0+j1] in S0 ];
        // Make sure the only unknowns of the block are in S
        if #IJ0 eq 0 then
            continue; // no unknown in S
        elif #[ [i0+i1,j0+j1] : i0, j0 in [1..deg] | B[i0+i1,j0+j1] eq 0 ] gt #IJ0 then
            continue; // another unknown outside S
        end if;
        charpoly := (x-ff[1])*(x-ff[2])^(#IJ0-1);
        fij := &*[ x - P.Index(S0,ij) : ij in IJ0 ];
        rels cat:= Eltseq(fij - charpoly);
    end for;
    rels := [ rel : rel in SequenceToSet(rels) | rel ne 0 ];
    return ideal< P | rels >, S0;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

intrinsic SudokuMaskSplittings(B::AlgMatElt) -> AlgMatElt
    {}
    ZZ := IntegerRing();
    ff, gg := SudokuMaskField(2);
    I, S0 := SudokuMaskIdeal(B : Coordinates := ff);
    V := Variety(I);
    Masks := [ Parent(B) | ];
    dsquare := Degree(Parent(B));
    counts := {* 0^^dsquare, 1, 2^^(dsquare-1) *};
    for m in V do
        M := B;
        for k in [1..#m] do
            i, j := Explode(S0[k]);
            M[i,j] := gg[m[k]];
        end for;
        if &and[ {* M[i,j] : j in [1..dsquare] *} subset counts : i in [1..dsquare] ] then
            Append(~Masks,M);
        end if;
    end for;
    return Masks;
end intrinsic;

intrinsic SudokuMaskSplittings(
    B::AlgMatElt,I::SeqEnum[RngIntElt],J::SeqEnum[RngIntElt]) -> AlgMatElt
    {}
    ZZ := IntegerRing();
    ff, gg := SudokuMaskField(2);
    I, S0 := SudokuMaskIdeal(B,I,J : Coordinates := ff);
    V := Variety(I);
    Masks := [ Parent(B) | ];
    dsquare := Degree(Parent(B));
    for i in [1..dsquare] do
        if &and[ B[i,j] eq 2 : j in [1..dsquare] ] then return Masks; end if;
    end for;
    for m in V do
        M := B;
        for k in [1..#m] do
            i, j := Explode(S0[k]);
            M[i,j] := gg[m[k]];
        end for;
        Append(~Masks,M);
    end for;
    return Masks;
end intrinsic;

intrinsic SudokuMaskSplittings(B::AlgMatElt,S::SetEnum[SeqEnum[RngIntElt]]) -> AlgMatElt
    {}
    ZZ := IntegerRing();
    ff, gg := SudokuMaskField(2);
    FF := Parent(ff[1]);
    I, S0 := SudokuMaskIdeal(B,S : Coordinates := ff);
    V := Variety(I);
    Masks := [ Parent(B) | ];
    dsquare := Degree(Parent(B));
    for i in [1..dsquare] do
        if &and[ B[i,j] eq 2 : j in [1..dsquare] ] then return Masks; end if;
    end for;
    for m in V do
        M := B;
        for k in [1..#m] do
            i, j := Explode(S0[k]);
            M[i,j] := gg[m[k]];
        end for;
        Append(~Masks,M);
    end for;
    return Masks;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

intrinsic IsDisjointSudoku(B1::AlgMatElt,B2::AlgMatElt) -> BoolElt
    {Given two complete (no zeros) 1-masking matrices of the same degrees,
    return true if and only if the positions of their 1 are disjoint.}
    dsquare := Degree(Parent(B1));
    require Parent(B1) eq Parent(B2) : "Arguments must have the same degree.";
    Mults := {* 1^^1, 2^^(dsquare-1) *};
    require &and[ {* c : c in Eltseq(B1[i]) *} eq Mults : i in [1..dsquare] ] :
        "Argument 1 must be a complete 1-masking matrix.";
    require &and[ {* c : c in Eltseq(B2[i]) *} eq Mults : i in [1..dsquare] ] :
        "Argument 2 must be a complete 1-masking matrix.";
    for i, j in [1..dsquare] do
        if B1[i,j] eq 1 and B2[i,j] eq 1 then return false; end if;
    end for;
    return true;
end intrinsic;

intrinsic SudokuMaskIntersection(B1::AlgMatElt,B2::AlgMatElt) -> AlgMatElt
    {Given two 1-masking matrices of the same degrees, construct the
    intersection mask -- with zero entries where the masks disagree.}
    MatZ := Parent(B1);
    require MatZ eq Parent(B2) : "Arguments must have the same degree.";
    dsquare := Degree(MatZ);
    return Parent(B1)![ B2[i,j] eq B1[i,j] select B1[i,j] else 0 : i, j in [1..dsquare] ];
end intrinsic;

intrinsic SudokuMaskIntersection(S::SeqEnum[AlgMatElt]) -> AlgMatElt
    {Given a sequence of 1-masking matrices of the same degrees,
    construct the intersection mask -- with zero entries where
    the masks disagree.}
    MatZ := Universe(S);
    dsquare := Degree(MatZ);
    if #S eq 0 then return MatZ!0; end if;
    B0 := S[1];
    for i, j in [1..dsquare] do
        c := B0[i,j];
        for B1 in S do
            if B1[i,j] ne c then B0[i,j] := 0; break; end if;
        end for;
    end for;
    return B0;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
// Higher multiplicity masking matrices
//////////////////////////////////////////////////////////////////////////////

function PruneSudokuMask(B,n) // B::AlgMatElt,n::RngIntElt) -> AlgMatElt
    dsquare := Degree(Parent(B)); bool, deg := IsSquare(dsquare);
    error if not bool, "Argument must be a matrix of square degree.";
    S := {1..n};
    for i in [1..dsquare] do
        if S subset { B[i,j] : j in [1..dsquare] } then
            for j in [1..dsquare] do
                if B[i,j] notin S then B[i,j] := n+1; end if;
            end for;
        end if;
        if S subset { B[j,i] : j in [1..dsquare] } then
            for j in [1..dsquare] do
                if B[j,i] notin S then B[j,i] := n+1; end if;
            end for;
        end if;
    end for;
    for i1, j1 in [0..dsquare-deg by deg] do
        if S subset { B[i0+i1,j0+j1] : i0, j0 in [1..deg] } then
            for i0, j0 in [1..deg] do
                if B[i0+i1,j0+j1] notin S then B[i0+i1,j0+j1] := n+1; end if;
            end for;
        end if;
    end for;
    return B;
end function;

function UniqueSudokuSubs(B,n)
    dsquare := Degree(Parent(B)); bool, deg := IsSquare(dsquare);
    error if not bool, "Argument must be a matrix of square degree.";
    S := {1..n};
    for i,j in [1..dsquare] do
        if B[i,j] eq 0 then
            ex := [ k : k in [1..dsquare] | B[k,j] eq 0 ];
            if #ex eq 1 then
                k := ex[1];
                T := { B[l,j] : l in [1..dsquare] | l ne k };
                Exclude(~T,0); assert #T eq n-1;
                B[k,j] := [ a : a in [1..n] | a notin T ][1];
            end if;
            ex := [ l : l in [1..dsquare] | B[i,l] eq 0 ];
            if #ex eq 1 then
                l := ex[1];
                T := { B[i,m] : m in [1..dsquare] | m ne l };
                Exclude(~T,0); assert #T eq n-1;
                B[i,l] := [ a : a in [1..n] | a notin T ][1];
            end if;
        end if;
    end for;
    for i1, j1 in [0..dsquare-deg by deg] do
        ex := [ [i0,j0] : i0, j0 in [1..deg] | B[i0+i1,j0+j1] eq 0 ];
        if #ex eq 1 then
            i0, j0 := Explode(ex[1]);
            T := { B[k0+i1,l0+j1] : k0, l0 in [1..deg] | [k0,l0] ne [i0,j0] };
            Exclude(~T,0); assert #T eq n-1;
            B[i0+i1,j0+j1] := [ a : a in [1..n] | a notin T ][1];
        end if;
    end for;
    return B;
end function;

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

intrinsic SudokuMaskUpdate(B::AlgMatElt,n::RngIntElt) -> RngMPol
    {}
    return UniqueSudokuSubs(PruneSudokuMask(B,n),n);
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

intrinsic SudokuMaskIdeal(B::AlgMatElt,n::RngIntElt) -> RngMPol
    {Given a Sudoku n-masking matrix (a_1->1,...,a_n->n
    and all other a's->n+1), return the relations ideal.}
    dsquare := Degree(Parent(B));
    bool, deg := IsSquare(dsquare);
    require bool : "Argument 1 must have square degree.";
    if Type(Coordinates) eq BoolElt then
        ff := SudokuMaskField(n);
    else
        ff := Coordinates;
    end if;
    require Type(ff) eq Assoc :
        "Parameter \"Coordinates\" must be an associative array.";
    require Universe(ff) eq {1..n} :
        "Universe of \"Coordinates\" must be the set {1..#P}.";
    require Keys(ff) eq {1..n} :
        "Keys of \"Coordinates\" must be the set {1..#P}.";
    FF := Parent(ff[1]);
    S0 := {@ [i,j] : i, j in [1..dsquare] | B[i,j] eq 0 @};
    I0 := {@ ij[1] : ij in S0 @}; J0 := {@ ij[2] : ij in S0 @};
    P := PolynomialRing(FF,#S0);
    AssignNames(~P,[ "X" * Sprint(ij[1]) * Sprint(ij[2]) : ij in S0 ]);
    gens := [ &*[ P.k - ff[a] : a in [1..n+1] ] : k in [1..#S0] ];
    R<x> := PolynomialRing(P);
    // Row relations:
    for i in I0 do
        IJ0 := [ ij : ij in S0 | ij[1] eq i ];
        aa := { B[i,j] : j in [1..dsquare] }; Exclude(~aa,n+1);
        charpoly := &*[ R | x - ff[a] : a in [1..n] | a notin aa ]
            * (x - ff[n+1])^(#IJ0-(n+1-#aa));
        fij := &*[ x - P.Index(S0,ij) : ij in IJ0 ];
        gens cat:= Eltseq(fij - charpoly);
    end for;
    // Column relations:
    for j in J0 do
        IJ0 := [ ij : ij in S0 | ij[2] eq j ];
        aa := { B[i,j] : i in [1..dsquare] }; Exclude(~aa,n+1);
        charpoly := &*[ R | x - ff[a] : a in [1..n] | a notin aa ]
            * (x - ff[n+1])^(#IJ0-(n+1-#aa));
        fij := &*[ x - P.Index(S0,ij) : ij in IJ0 ];
        gens cat:= Eltseq(fij - charpoly);
    end for;
    // Block relations:
    for i1, j1 in [0..dsquare-deg by deg] do
        IJ0 := [ ij : ij in S0 | (ij[1]-i1) in [1..deg] and (ij[2]-j1) in [1..deg] ];
        if #IJ0 eq 0 then continue; end if;
        aa := { B[i0+i1,j0+j1] : i0, j0 in [1..deg] }; Exclude(~aa,n+1);
        charpoly := &*[ R | x - ff[a] : a in [1..n] | a notin aa ]
            * (x - ff[n+1])^(#IJ0-(n+1-#aa));
        fij := &*[ x - P.Index(S0,ij) : ij in IJ0 ];
        gens cat:= Eltseq(fij - charpoly);
    end for;
    return ideal< P | gens >, S0;
end intrinsic;

intrinsic SudokuMaskSplittings(B::AlgMatElt,n::RngIntElt) -> SeqEnum
    {}
    ZZ := IntegerRing();
    ff, gg := SudokuMaskField(n+1);
    I, S0 := SudokuMaskIdeal(B,n : Coordinates := ff);
    Masks := [ Parent(B) | ];
    dsquare := Degree(Parent(B));
    counts := {* 0^^dsquare *} join {* i : i in [1..n] *} join {* (n+1)^^(dsquare-n) *};
    for m in Variety(I) do
        M := B;
        for k in [1..#m] do
            i, j := Explode(S0[k]);
            M[i,j] := gg[m[k]];
        end for;
        if &and[ {* M[i,j] : j in [1..dsquare] *} subset counts : i in [1..dsquare] ] then
            Append(~Masks,M);
        end if;
    end for;
    return Masks;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

intrinsic ApplySudokuMask(A::AlgMatElt,B::AlgMatElt,I::SeqEnum[RngIntElt]) -> AlgMatElt
    {Apply the n-masking matrix B to Sudoko matrix A,
    using the inverse sequence I = [a_1,..,a_n].}
    dsquare := Degree(Parent(A));
    bool, deg := IsSquare(dsquare);
    require bool : "Argument must be a matrix of square degree.";
    require Parent(A) eq Parent(B) : "Arguments 1 and 2 must in the same matrix space.";
    for i,j in [1..dsquare] do
        k := B[i,j];
        if k ge 1 and k le #I then
            A[i,j] := I[k];
        end if;
    end for;
    return A;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
/*
SDK := SudokuExamples();

function SudokuResolutions(A)
    print {* c : c in Eltseq(A) | c ne 0 *};
    Aseq := [ A ];
    for k in [1..9] do
        tyme := Cputime();
        Aseq := &cat[ SudokuExtensions(A) : A in Aseq ];
        printf "  %3o: Num extensions: %4o [%o]\n",
            k, #Aseq, Cputime(tyme);
        if #Aseq eq 1 and 0 notin Eltseq(Aseq[1]) then
            break;
        end if;
    end for;
    return Aseq;
end function;

for i in [1..#SDK] do
    print "i =", i;
    Aseq := SudokuResolutions(SDK[i]);
end for;
*/

//////////////////////////////////////////////////////////////////////////////
// Masking matrices with partitions
//////////////////////////////////////////////////////////////////////////////

intrinsic SudokuMaskingMatrix(A::AlgMatElt,P::SeqEnum[SetEnum]) -> AlgMatElt
    {}
    ZZ := IntegerRing();
    dsquare := Degree(Parent(A));
    require &join[ S : S in P ] cmpeq {1..dsquare} :
        "Argument 2 must be a partition of {1.." * Sprint(dsquare) * "}";
    require &and[ &and[ #(P[i] meet P[j]) eq 0 : j in [i+1..#P] ] : i in [1..#P-1] ] :
        "Argument 2 must be a sequence of disjoint sets.";
    // Construct the inverse of the partition:
    InvP := AssociativeArray(ZZ);
    InvP[0] := 0;
    for i in [1..#P] do
        for j in P[i] do
            InvP[j] := i;
        end for;
    end for;
    return Parent(A)![ [ InvP[A[i,j]] : j in [1..dsquare] ] : i in [1..dsquare] ];
end intrinsic;

function UniquePartitionMaskSubs(B,P)
    dsquare := Degree(Parent(B)); bool, deg := IsSquare(dsquare);
    error if not bool, "Argument 1 must have square degree.";
    // Compute the positions of the zeros:
    S := {@ [i,j] : i, j in [1..dsquare] | B[i,j] eq 0 @};
    I := {@ ij[1] : ij in S @}; J := {@ ij[2] : ij in S @};
    // Compute the partition multiplicities:
    nn := [ #Ai : Ai in P ]; n := #P;
    // Row relations:
    for i in I do
        aa := {* B[i,j] : j in [1..dsquare] *};
        ex := [ nn[a] - Multiplicity(aa,a) : a in [1..n] ];
        cc := [ ex[a] eq 0 select 0 else 1 : a in [1..n] ];
        if &+cc ne 1 then continue; end if;
        //printf "Row %2o cc: %o\n", i, cc;
        a := Index(cc,1);
        for j in [1..dsquare] do
            if B[i,j] eq 0 then B[i,j] := a; end if;
        end for;
    end for;
    // Column relations:
    for j in J do
        aa := {* B[i,j] : i in [1..dsquare] *};
        ex := [ nn[a] - Multiplicity(aa,a) : a in [1..n] ];
        cc := [ ex[a] eq 0 select 0 else 1 : a in [1..n] ];
        if &+cc ne 1 then continue; end if;
        //printf "Col %2o cc: %o\n", j, cc;
        a := Index(cc,1);
        for i in [1..dsquare] do
            if B[i,j] eq 0 then B[i,j] := a; end if;
        end for;
    end for;
    // Block relations:
    for i1, j1 in [0..dsquare-deg by deg] do
        aa := {* B[i0+i1,j0+j1] : i0, j0 in [1..deg] *};
        ex := [ nn[a] - Multiplicity(aa,a) : a in [1..n] ];
        cc := [ ex[a] eq 0 select 0 else 1 : a in [1..n] ];
        if &+cc ne 1 then continue; end if;
        //printf "Blk (%2o,%2o) cc: %o\n", i1, j1, cc;
        a := Index(cc,1);
        for i0, j0 in [1..deg] do
            if B[i0+i1,j0+j1] eq 0 then B[i0+i1,j0+j1] := a; end if;
        end for;
    end for;
    return B;
end function;

intrinsic SudokuMaskUpdate(B::AlgMatElt,P::SeqEnum[SetEnum]) -> RngMPol
    {}
    dsquare := Degree(Parent(B)); bool, deg := IsSquare(dsquare);
    require bool : "Argument 1 must be a matrix of square degree.";
    require &join[ S : S in P ] cmpeq {1..dsquare} :
        "Argument 2 must be a partition of {1.." * Sprint(dsquare) * "}";
    require &and[ &and[ #(P[i] meet P[j]) eq 0 : j in [i+1..#P] ] : i in [1..#P-1] ] :
        "Argument 2 must be a sequence of disjoint sets.";
    return UniquePartitionMaskSubs(B,P);
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

intrinsic SudokuMaskIdeal(B::AlgMatElt,P::SeqEnum[SetEnum] : Coordinates := false) -> RngMPol
    {Given a Sudoku P-masking matrix (A_1->1,...,A_n->n), return the relations ideal.}
    dsquare := Degree(Parent(B)); bool, deg := IsSquare(dsquare);
    require bool : "Argument 1 must have square degree.";
    require &join[ S : S in P ] cmpeq {1..dsquare} :
        "Argument 2 must be a partition of {1.." * Sprint(dsquare) * "}";
    require &and[ &and[ #(P[i] meet P[j]) eq 0 : j in [i+1..#P] ] : i in [1..#P-1] ] :
        "Argument 2 must be a sequence of disjoint sets.";
    ZZ := IntegerRing();
    n := #P;
    nn := [ #Ai : Ai in P ];
    if Type(Coordinates) eq BoolElt then
        ff := SudokuMaskField(n);
    else
        ff := Coordinates;
    end if;
    require Type(ff) eq Assoc :
        "Parameter \"Coordinates\" must be an associative array.";
    require Universe(ff) eq {1..n} :
        "Universe of \"Coordinates\" must be the set {1..#P}.";
    require Keys(ff) eq {1..n} :
        "Keys of \"Coordinates\" must be the set {1..#P}.";
    FF := Parent(ff[1]);
    S := {@ [i,j] : i, j in [1..dsquare] | B[i,j] eq 0 @};
    I := {@ ij[1] : ij in S @}; J := {@ ij[2] : ij in S @};
    P := PolynomialRing(FF,#S);
    AssignNames(~P,[ "X" * Sprint(ij[1]) * Sprint(ij[2]) : ij in S ]);
    gens := [ &*[ P.ij - ff[a] : a in [1..n] ] : ij in [1..#S] ];
    R<x> := PolynomialRing(P);
    // Row relations:
    for i in I do
        IJ := [ ij : ij in S | ij[1] eq i ];
        aa := {* B[i,j] : j in [1..dsquare] *};
        mm := [ Multiplicity(aa,a) : a in [1..n] ];
        charpoly := &*[ R | (x - ff[a])^(nn[a]-mm[a]) : a in [1..n] ];
        fij := &*[ x - P.Index(S,ij) : ij in IJ ];
        assert Degree(charpoly) eq Degree(fij);
        gens cat:= Eltseq(fij - charpoly);
    end for;
    // Column relations:
    for j in J do
        IJ := [ ij : ij in S | ij[2] eq j ];
        aa := {* B[i,j] : i in [1..dsquare] *};
        mm := [ Multiplicity(aa,a) : a in [1..n] ];
        charpoly := &*[ R | (x - ff[a])^(nn[a]-mm[a]) : a in [1..n] ];
        fij := &*[ x - P.Index(S,ij) : ij in IJ ];
        assert Degree(charpoly) eq Degree(fij);
        gens cat:= Eltseq(fij - charpoly);
    end for;
    // Block relations:
    for i1, j1 in [0..dsquare-deg by deg] do
        IJ := [ ij : ij in S | (ij[1]-i1) in [1..deg] and (ij[2]-j1) in [1..deg] ];
        if #IJ eq 0 then continue; end if;
        aa := {* B[i0+i1,j0+j1] : i0, j0 in [1..deg] *};
        mm := [ Multiplicity(aa,a) : a in [1..n] ];
        charpoly := &*[ R | (x - ff[a])^(nn[a]-mm[a]) : a in [1..n] ];
        fij := &*[ x - P.Index(S,ij) : ij in IJ ];
        assert Degree(charpoly) eq Degree(fij);
        gens cat:= Eltseq(fij - charpoly);
    end for;
    return ideal< P | gens >, S;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

intrinsic SudokuMaskSplittings(B::AlgMatElt,P::SeqEnum[SetEnum]) -> SeqEnum
    {}
    ZZ := IntegerRing();
    ff, gg := SudokuMaskField(#P);
    I, S0 := SudokuMaskIdeal(B,P : Coordinates := ff);
    Masks := [ Parent(B) | ];
    dsquare := Degree(Parent(B));
    counts := {* 0^^dsquare *} join {* i^^#P[i] : i in [1..#P] *};
    for i in [1..dsquare] do
        if &and[ B[i,j] eq 2 : j in [1..dsquare] ] then return Masks; end if;
    end for;
    for m in Variety(I) do
        M := B;
        for k in [1..#m] do
            i, j := Explode(S0[k]);
            M[i,j] := gg[m[k]];
        end for;
        if &and[ {* M[i,j] : j in [1..dsquare] *} subset counts : i in [1..dsquare] ] then
            Append(~Masks,M);
        end if;
    end for;
    return Masks;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

intrinsic SudokuMaskNormalization(B::AlgMatElt) -> AlgMatElt, SeqEnum
    {Returns a normalized representative of the 1-masking matrix B.}
    require SequenceToSet(Eltseq(B)) subset {0,1,2} :
        "Argument must be a 1-masking matrix (with entries in {0,1,2}).";
    dsquare := Degree(Parent(B)); bool, deg := IsSquare(dsquare);
    require bool : "Argument 1 must have square degree.";
    function mysort(list)
        n := #list;
        G := SymmetricGroup(n);
        new_indx := [1..n];
        new_list := list;
        for k in [1..n] do
            A, i := Max(new_list[[k..n]]);
            I := [1..k-1] cat [i+k-1] cat [ j+k-1 : j in [1..n-k+1] | j ne i];
            new_list := new_list[I];
            new_indx := new_indx[I];
        end for;
        return new_list, G!new_indx;
    end function;
    mats := [ ];
    nums := [ ];
    for i1 in [0..dsquare-deg by deg] do
        mati := [ ];
        numi := [ ];
        for j1 in [0..dsquare-deg by deg] do
            A := Submatrix(B,i1+1,j1+1,3,3);
            S := {* c : c in Eltseq(A) *};
            Append(~mati,A);
            Append(~numi,[ Multiplicity(S,k) : k in [1,2,0] ]);
        end for;
        Append(~mats,mati);
        Append(~nums,numi);
    end for;
    for k in [1..deg-1] do
        max_nums := [];
        max_indx := [];
        for i in [1..deg-k+1] do
            numi, j := Max(nums[i+k-1][[k..deg]]);
            Append(~max_nums,numi);
            Append(~max_indx,j);
        end for;
        _, g := mysort(max_nums);
        j := max_indx[1^g];
        I := [1..k-1] cat [ k+i^g-1 : i in [1..deg-k+1] ];
        J := [1..k-1] cat [j+k-1] cat [ k+l-1 : l in [1..deg-k+1] | l ne j ];
        nums := [ numi[J] : numi in nums ][I];
        mats := [ mati[J] : mati in mats ][I];
    end for;
    _, g := mysort([ nums[i][[i..deg] cat [1..i-1]] : i in [1..deg] ]);
    I := [1..deg]^g;
    mats := [ mati[I] : mati in mats ][I];
    B := VerticalJoin([ HorizontalJoin(mats[i]) : i in [1..deg] ]);
    for k in [1..deg] do
        M := mats[k,k];
        IJ := [ [i,j] : i, j in [deg*(k-1)+1..deg*k] | B[i,j] eq 1 ];
        I := [ ij[1] : ij in IJ ];
        J := [ ij[2] : ij in IJ ];
        I cat:= [ i : i in [deg*(k-1)+1..deg*k] | i notin I ];
        J cat:= [ j : j in [deg*(k-1)+1..deg*k] | j notin J ];
        I := [1..deg*(k-1)] cat I cat [deg*k+1..dsquare];
        J := [1..deg*(k-1)] cat J cat [deg*k+1..dsquare];
        B := Transpose(Matrix([ B[i] : i in I ]));
        B := Transpose(Matrix([ B[j] : j in J ]));
    end for;
    return B;
end intrinsic;
