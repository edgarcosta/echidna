////////////////////////////////////////////////////////////////////////
//                                                                    //
//                   CANONICAL 2-ADIC JORDAN BLOCK FORM               //
//                            David Kohel                             //
//                       Created November 1999                        //
//                       Last modified May 2000                       //
//                                                                    //
////////////////////////////////////////////////////////////////////////

ZZ := Integers();
QQ := Rationals();

Diags := [[1],[3],[5],[7]];
NSplt := [2,1,1,2]; Split := [2,1,1,4];

////////////////////////////////////////////////////////////////////////

forward
    DiagonalizingReduction, NonDiag0Reduction, NonDiag1Reduction,
    Diag0Term2Reduction, Diag0Term4Reduction,
    Diag1Term2Reduction, Diag1Term3Reduction, Diag1Term4Reduction,
    Diag2Term2Reduction, Diag2Term3Reduction;

////////////////////////////////////////////////////////////////////////

import "genus_common.m" : LatticeContent, RLattice, UnitSquareClass;

////////////////////////////////////////////////////////////////////////

function Find2RootVector(L)
    n := Rank(L);
    for i in [1..n] do
        if (ZZ!Norm(L.i) mod 2) eq 1 then
            return L.i;
        end if;
    end for;
    for i in [1..n] do
        if (ZZ!(L.i,L.i) mod 4) ne 0 then
            return L.i;
        end if;
        for j in [i+1..n] do
            if IsOdd(ZZ!(L.i,L.j)) then
                if (ZZ!((L.j,L.j) + 2*(L.i,L.j)) mod 4) ne 0 then
                    return L.i + L.j;
                end if;
                return L.j;
            end if;
        end for;
    end for;
end function;

function twoAdicDiagonals(L)
    TYPE := Type(L);
    dim := Rank(L);
    K := Rationals();
    if dim eq 1 then
        return [K|UnitSquareClass((L.1,L.1),2)], [Parent([K|])|];
    end if;
    c := LatticeContent(L);
    if c notin {QQ|0,1} then
        L := RLattice(TYPE,(1/c)*GramMatrix(L));
    end if;
    c := UnitSquareClass(c,2);
    q := 2^Valuation(c,2);
    u := Find2RootVector(L);
    n := ZZ!Norm(u);
    G, f := quo< L | u >;
    B := [ g@@f : g in Generators(G) ];
    if IsOdd(n) then
        B1 := [ ];
        B := [ n*v-(u,v)*u : v in B ];
        t := 1;
    else
        m := n div 2;
        B1 := [ v : v in B | IsOdd(ZZ!(u,v)) ];
        if #B1 eq 0 then
            B := [ m*w-(ZZ!(u,w) div 2)*u : w in B ];
            t := 1;
        else
            v := B1[1];
            B := [ m*(w-v)-(ZZ!(u,w-v) div 2)*u : w in B1 | w ne v ] cat
                [ m*w-(ZZ!(u,w) div 2)*u : w in B | w notin B1 ];
            t := (u,v);
            d := t^2-(u,u)*(v,v);
            B := [ d*w-(v,w)*((u,v)*u-(u,u)*v) : w in B ];
            t := 2;
        end if;
    end if;
    if dim eq t then /* t equals 2 */
        D := -(((u,u)*(v,v)-(u,v)^2) mod 8);
        if D eq -3 then
            return [K|], [[K|2*q,q,q,2*q]];
        else
            return [K|], [[K|2*q,q,q,4*q]];
        end if;
    end if;
    A := Matrix(dim-t,[ (B[i],B[j]) : i,j in [1..dim-t] ]);
    M := RLattice(TYPE,c*A);
    if t eq 1 then
        D1, D2 := twoAdicDiagonals(M);
        Insert(~D1,1,UnitSquareClass(c*(u,u),2));
        return &cat[ Sort([ a : a in D1 | Valuation(a,2) eq i ]) :
            i in {@ Valuation(a,2) : a in D1 @} ], D2;
    else /* t equals 2 */
        D1, D2 := twoAdicDiagonals(M);
        D := -(((u,u)*(v,v)-(u,v)^2) mod 8);
        if D eq -3 then
            Insert(~D2,1,[K|2*q,q,q,2*q]);
        else /* D eq -7 */
            Insert(~D2,1,[K|2*q,q,q,4*q]);
        end if;
        D1 := &cat[ Sort([ a : a in D1 | Valuation(a,2) eq i ]) :
            i in {@ Valuation(a,2) : a in D1 @} ];
        return D1, D2;
    end if;
end function;

////////////////////////////////////////////////////////////////////////
//                  Canonical 2-Adic Jordan Form                      //
////////////////////////////////////////////////////////////////////////

function Jordan2Reduction(L)
    // L is a lattice representing a 2-adic Jordan decomposition.
    // D are integer sequences representing the Jordan blocks,
    // Valid blocks are:
    //    [1], [3], [5], [7], [2,1,1,2], [2,1,1,4].
    // I are the scales, log base 2.
    TYPE := Type(L);
    M := GramMatrix(L);
    I := [ IntegerRing() | ];
    D := [ Parent(I) |  ];
    n := Degree(Parent(M));
    i := 1;
    while i le n do
        if i lt n and M[i,i+1] ne 0 then
            k := Valuation(M[i,i+1],2);
            q := 2^k;
            r := Max([0] cat [ j : j in [1..#I] | I[j] le k ]);
            Insert(~I,r+1,k);
            Insert(~D,r+1,[ IntegerRing() |
                M[i,i]/q, M[i,i+1]/q, M[i+1,i]/q, M[i+1,i+1]/q ] );
            i +:= 2;
        else
            k := Valuation(M[i,i],2);
            q := 2^k;
            Append(~I,k);
            Append(~D,[ IntegerRing() | M[i,i]/q ]);
            i +:= 1;
        end if;
    end while;
    DiagonalizingReduction(~D,~I);
    ScaleVals := {@ i : i in I @};
    repeat
        stable := true;
        for i0 in ScaleVals do
            I0 := [ j : j in [1..#I] | I[j] eq i0 ];
            I1 := [ j : j in [1..#I] | I[j] eq i0+1 ];
            NonDiag0Reduction(~D,~stable,I0);
            NonDiag1Reduction(~D,~stable,I0,I1);
        end for;
    until stable;
    repeat
        stable := true;
        for i0 in ScaleVals do
            I0 := [ j : j in [1..#I] | #D[j] eq 1 and I[j] eq i0   ];
            I1 := [ j : j in [1..#I] | #D[j] eq 1 and I[j] eq i0+1 ];
            I2 := [ j : j in [1..#I] | #D[j] eq 1 and I[j] eq i0+2 ];
            Diag0Term2Reduction(~D,~stable,I0);
            Diag0Term4Reduction(~D,~stable,I0);
            Diag1Term2Reduction(~D,~stable,I0,I1);
            Diag1Term3Reduction(~D,~stable,I0,I1);
            Diag1Term4Reduction(~D,~stable,I0,I1);
            Diag2Term2Reduction(~D,~stable,I0,I2);
            Diag2Term3Reduction(~D,~stable,I0,I1,I2);
        end for;
    until stable;
    D := &cat[ Sort([ D[j] : j in [1..#D] | #D[j] eq 1 and I[j] eq i0 ])
        cat Sort([ D[j] : j in [1..#D] | #D[j] eq 4 and I[j] eq i0 ])
        : i0 in ScaleVals ];
    // Since the zero lattice doesn't exist, must manually
    // initialize a lattice.
    t := #D[1] eq 1 select 1 else 2;
    L := RLattice(TYPE,2^I[1]*Matrix(t,D[1]));
    for i in [2..#D] do
        t := #D[i] eq 1 select 1 else 2;
        L := DirectSum(L,RLattice(TYPE,2^I[i]*Matrix(t,D[i])));
    end for;
    return L;
end function;

// BEGIN REDUCTION ALGORITHMS:

procedure DiagonalizingReduction(~D,~I)
    for i0 in I do
        I0 := [ j : j in [1..#I] | I[j] eq i0 ];
        E0 := [ D[i] : i in I0 ];
        for R in Diags do
            while Split in E0 and R in E0 do
                k := I0[Index(E0,Split)];
                D[k] := R;
                Insert(~D,k,[7*R[1] mod 8]);
                Insert(~I,k,i0);
                I0 := [ j : j in [1..#I] | I[j] eq i0 ];
                E0 := [ D[j] : j in I0 ];
            end while;
            while NSplt in E0 and R in E0 do
                j := I0[Index(E0,R)];
                k := I0[Index(E0,NSplt)];
                u03 := 3*R[1] mod 8;
                D[j] := [u03];
                D[k] := [u03];
                Insert(~D,k,[u03]);
                Insert(~I,k,i0);
                I0 := [ j : j in [1..#I] | I[j] eq i0 ];
                E0 := [ D[j] : j in I0 ];
            end while;
        end for;
    end for;
end procedure;

/*

// Diagonalizing relations (0-increment):
[
    u1*x7 - x3^2*x1,
    u1*x5 - x3*x1^2,
    u1*x3 - x5*x3^2,
    u1*x1 - x5*x3*x1,
    u0*x7 - x5*x1^2,
    u0*x5 - x7*x3^2,
    u0*x3 - x1^3,
    u0*x1 - x3^3,
    ];

*/

procedure NonDiag0Reduction(~D,~stable,I0)
    Split := [2,1,1,4];
    NSplt := [2,1,1,2];
    IS := [ j : j in I0 | D[j] eq Split ];
    while #IS ge 2 do
        j := IS[1]; Exclude(~IS,j);
        k := IS[1]; Exclude(~IS,k);
        D[j] := NSplt;
        D[k] := NSplt;
        stable := false;
    end while;
end procedure;

/*
// 0-increment non-diagonalizable relations:
[
    u1^2 - u0^2
    ];
*/

procedure Diag0Term2Reduction(~D,~stable,I0)
    if #I0 lt 2 then return; end if;
    for R in [[5],[7]] do
        J0 := [ j : j in I0 | D[j] eq R ];
        while #J0 ge 2 do
            j := J0[1]; Exclude(~J0,j);
            k := J0[1]; Exclude(~J0,k);
            u05 := (5*R[1]) mod 8;
            D[j] := [u05];
            D[k] := [u05];
            stable := false;
        end while;
    end for;
    E0 := [ D[j] : j in I0 ];
    while [5] in E0 and [7] in E0 do
        j := I0[Index(E0,[5])];
        k := I0[Index(E0,[7])];
        D[j] := [1];
        D[k] := [3];
        E0 := [ D[i] : i in I0 ];
        stable := false;
    end while;
    while [1] in E0 and [7] in E0 do
        j := I0[Index(E0,[1])];
        k := I0[Index(E0,[7])];
        D[j] := [3];
        D[k] := [5];
        E0 := [ D[i] : i in I0 ];
        stable := false;
    end while;
end procedure;

/*
// 0-increment 2-term diagonalized relations:
[
    x7^2 - x3^2,
    x7*x5 - x3*x1,
    x7*x1 - x5*x3,
    x5^2 - x1^2,
    ];
*/

procedure Diag0Term4Reduction(~D,~stable,I0)
    E0 := [ D[j] : j in I0 ];
    J3 := [ j : j in I0 | D[j] eq [3] ];
    i7 := Index(E0,[7]);
    while #J3 ge 3 and i7 ne 0 do
        for i in [1..3] do
            D[J3[1]] := [1];
            Remove(~J3,1);
        end for;
        D[I0[i7]] := [5];
        stable := false;
        i7 := Index(E0,[7]);
    end while;
    while #J3 ge 4 do
        for i in [1..4] do
            D[J3[1]] := [1];
            Remove(~J3,1);
        end for;
        stable := false;
    end while;
end procedure;

/*
// 0-increment 4-term diagonalized relations:
[
    x7*x3^3 - x5*x1^3,
    x3^4 - x1^4
    ];
*/

procedure NonDiag1Reduction(~D,~stable,I0,I1)
    E0 := [ D[j] : j in I0 ];
    E1 := [ D[j] : j in I1 ];
    for R in Diags do
        while Split in E0 and R in E1 do
            j0 := Index(E0,Split);
            j1 := Index(E1,R);
            u05 := (5*R[1]) mod 8;
            D[I0[j0]] := NSplt; E0[j0] := NSplt;
            D[I1[j1]] := [u05]; E1[j1] := [u05];
            stable := false;
        end while;
        while R in E0 and Split in E1 do
            j0 := Index(E0,R);
            j1 := Index(E1,Split);
            u05 := 5*R[1] mod 8;
            D[I0[j0]] := [u05]; E0[j0] := [u05];
            D[I1[j1]] := NSplt; E1[j1] := NSplt;
            stable := false;
        end while;
    end for;
end procedure;

/*
// 1-increment non-diagonalizable relations:
[
    u1*y7 - u0*y3,
    u1*y5 - u0*y1,
    u1*y3 - u0*y7,
    u1*y1 - u0*y5,
    v1*x7 - v0*x3,
    v1*x5 - v0*x1,
    v1*x3 - v0*x7,
    v1*x1 - v0*x5
    ];
*/

procedure Diag1Term2Reduction(~D,~stable,I0,I1)
    Unreduced3 := [ [7,7], [7,3], [3,7], [3,3] ];
    Unreduced7 := [ [7,5], [7,1], [5,7], [5,3] ];
    E0 := [ D[j] : j in I0 ];
    E1 := [ D[j] : j in I1 ];
    for P in Unreduced3 do
        u0, u1 := Explode(P);
        while [u0] in E0 and [u1] in E1 do
            i0 := Index(E0,[u0]);
            i1 := Index(E1,[u1]);
            u03 := (3*u0) mod 8;
            u13 := (3*u1) mod 8;
            D[I0[i0]] := [u03]; E0[i0] := [u03];
            D[I1[i1]] := [u13]; E1[i1] := [u13];
            stable := false;
        end while;
    end for;
    for P in Unreduced7 do
        u0, u1 := Explode(P);
        while [u0] in E0 and [u1] in E1 do
            i0 := Index(E0,[u0]);
            i1 := Index(E1,[u1]);
            u07 := (7*u0) mod 8;
            u17 := (7*u1) mod 8;
            D[I0[i0]] := [u07]; E0[i0] := [u07];
            D[I1[i1]] := [u17]; E1[i1] := [u17];
            stable := false;
        end while;
    end for;
end procedure;

/*
// 1-increment 2-term relations:
[
    x7*y7 - x5*y5,
    x7*y5 - x1*y3,
    x7*y3 - x5*y1,
    x7*y1 - x1*y7,
    x5*y7 - x3*y1,
    x5*y3 - x3*y5,
    x3*y7 - x1*y5,
    x3*y3 - x1*y1,
    ];
*/

procedure Diag1Term3Reduction(~D,~stable,I0,I1)
    if #I0 le 1 and #I1 le 1 then return; end if;
    Unreduced3 := [ [7,7], [7,3], [3,7], [3,3] ];
    Unreduced7 := [ [7,5], [7,1], [5,7], [5,3] ];
    E0 := [ D[j] : j in I0 ];
    E1 := [ D[j] : j in I1 ];
    i5 := Index(E0,[5]);
    if i5 ne 0 then
        i1 := Index(E0,[1]);
        i3 := Index(E0,[3]);
        j1 := Index(E1,[1]);
        j5 := Index(E1,[5]);
        if i3 ne 0 and j5 ne 0 then
            D[I0[i5]] := [1];
            D[I0[i3]] := [1];
            D[I1[j5]] := [3];
            stable := false;
        elif i3 ne 0 and j1 ne 0 then
            D[I0[i5]] := [1];
            D[I0[i3]] := [1];
            D[I1[j1]] := [7];
            stable := false;
        elif i1 ne 0 and j5 ne 0 then
            D[I0[i5]] := [3];
            D[I0[i1]] := [3];
            D[I1[j5]] := [1];
            stable := false;
        elif i1 ne 0 and j1 ne 0 then
            D[I0[i5]] := [3];
            D[I0[i1]] := [3];
            D[I1[j1]] := [5];
            stable := false;
        elif j5 ne 0 and j1 ne 0 then
            D[I0[i5]] := [1];
            D[I1[j1]] := [3];
            D[I1[j5]] := [3];
            stable := false;
        elif j1 ne 0 then
            E1[j1] := [3];
            j2 := Index(E1,[1]);
            if j2 ne 0 then
                D[I0[i5]] := [1];
                D[I1[j1]] := [3];
                D[I1[j2]] := [7];
                stable := false;
            end if;
        end if;
    end if;
end procedure;

/*
// 1-increment 3-term relations:
[
    x5*x3*y5 - x1^2*y3,
    x5*x3*y1 - x1^2*y7,
    x5*x1*y5 - x3^2*y1,
    x5*x1*y1 - x3^2*y5,
    x5*y5*y1 - x1*y3^2,
    x5*y1^2 - x1*y7*y3,
    ];
*/

procedure Diag1Term4Reduction(~D,~stable,I0,I1)
    if #I0 le 2 and #I1 le 1 then return; end if;
    if #I0 le 1 and #I1 le 2 then return; end if;
    E0 := [ D[j] : j in I0 ];
    E1 := [ D[j] : j in I1 ];
    I3 := [ j : j in [1..#E0] | E0[j] eq [3] ];
    if #I3 ge 3 then
        i1, i2, i3 := Explode(I3);
        j1 := Index(E1,[1]);
        j5 := Index(E1,[5]);
        if j5 ne 0 then
            D[I0[i1]] := [1];
            D[I0[i2]] := [1];
            D[I0[i3]] := [1];
            D[I1[j5]] := [7];
            stable := false;
        elif j1 ne 0 then
            D[I0[i1]] := [1];
            D[I0[i2]] := [1];
            D[I0[i3]] := [1];
            D[I1[j1]] := [3];
            stable := false;
        end if;
    elif #I3 ge 2 then
        i1, i2 := Explode(I3);
        j1 := Index(E1,[1]);
        j5 := Index(E1,[5]);
        if j1 ne 0 and j5 ne 0 then
            D[I0[i1]] := [1];
            D[I0[i2]] := [1];
            D[I1[j1]] := [3];
            D[I1[j5]] := [7];
            stable := false;
        elif j1 ne 0 then
            E1[j1] := [3];
            j2 := Index(E1,[1]);
            if j2 ne 0 then
                D[I0[i1]] := [1];
                D[I0[i2]] := [1];
                D[I1[j1]] := [3];
                D[I1[j2]] := [3];
                stable := false;
            end if;
        end if;
    elif #I3 eq 1 then
        i1 := I3[1];
        J1 := [ j : j in [1..#I1] | E1[j] eq [1] ];
        if #J1 ge 3 then
            j1, j2, j3 := Explode(J1);
            D[I0[i1]] := [1];
            D[I1[j1]] := [3];
            D[I1[j2]] := [3];
            D[I1[j3]] := [3];
            stable := false;
        elif #J1 ge 2 then
            j1, j2 := Explode(J1);
            j5 := Index(E1,[5]);
            if j5 ne 0 then
                D[I0[i1]] := [1];
                D[I1[j1]] := [3];
                D[I1[j2]] := [3];
                D[I1[j5]] := [7];
                stable := false;
            end if;
        end if;
    end if;
end procedure;

/*
// 1-increment 4-term relations:
[
    x3^3*y5 - x1^3*y7,
    x3^3*y1 - x1^3*y3,
    x3^2*y5*y1 - x1^2*y7*y3,
    x3^2*y1^2 - x1^2*y3^2,
    x3*y5*y1^2 - x1*y7*y3^2,
    x3*y1^3 - x1*y3^3,
    ];
*/

procedure Diag2Term2Reduction(~D,~stable,I0,I2)
    if #I0 eq 0 or #I2 eq 0 then return; end if;
    E0 := [ D[i] : i in I0 ];
    E2 := [ D[i] : i in I2 ];
    i5 := Index(E0,[5]);
    i7 := Index(E0,[7]);
    while i7 ne 0 or i5 ne 0 do
        if i7 ne 0 then
            D[I0[i7]] := [3]; E0[i7] := [3];
            i7 := Index(E0,[7]);
        else
            D[I0[i5]] := [1]; E0[i5] := [1];
            i5 := Index(E0,[5]);
        end if;
        if [7] in E2 then
            D[I2[Index(E2,[7])]] := [3];
        elif [5] in E2 then
            D[I2[Index(E2,[5])]] := [1];
        elif [3] in E2 then
            D[I2[Index(E2,[3])]] := [7];
        elif [1] in E2 then
            D[I2[Index(E2,[1])]] := [5];
        end if;
        E2 := [ D[i] : i in I2 ];
        stable := false;
    end while;
end procedure;

/*
// 2-increment 2-term relations:
[
    x7*z7 - x3*z3,
    x7*z5 - x3*z1,
    x7*z3 - x3*z7,
    x7*z1 - x3*z5,
    x5*z7 - x1*z3,
    x5*z5 - x1*z1,
    x5*z3 - x1*z7,
    x5*z1 - x1*z5,
    ];
*/

procedure Diag2Term3Reduction(~D,~stable,I0,I1,I2)
    E0 := [ D[i] : i in I0 ];
    i3 := Index(E0,[3]);
    if i3 eq 0 then return; end if;
    E1 := [ D[i] : i in I1 ];
    E2 := [ D[i] : i in I2 ];
    j1 := Index(E1,[1]);
    j5 := Index(E1,[5]);
    k1 := Index(E2,[1]);
    k5 := Index(E2,[5]);
    while i3 ne 0 and j5 ne 0 and (k1 ne 0 or k5 ne 0) do
        E0[i3] := [1]; D[I0[i3]] := [1];
        E1[j5] := [3]; D[I1[j5]] := [3];
        if k5 ne 0 then
            E2[k5] := [1]; D[I2[k5]] := [1];
            k5 := Index(E2,[5]);
        else
            E2[k1] := [5]; D[I2[k1]] := [5];
            k1 := Index(E2,[1]);
        end if;
        i3 := Index(E0,[3]);
        j5 := Index(E1,[5]);
        stable := false;
    end while;
    while i3 ne 0 and j1 ne 0 and #E2 ne 0 do
        E0[i3] := [1]; D[I0[i3]] := [1];
        if [7] in E2 then
            k7 := Index(E2,[7]);
            E1[j1] := [5]; D[I1[j1]] := [5];
            E2[k7] := [1]; D[I2[k7]] := [1];
        elif [5] in E2 then
            k5 := Index(E2,[5]);
            E1[j1] := [1]; D[I1[j1]] := [1];
            E2[k5] := [7]; D[I2[k5]] := [7];
        elif [3] in E2 then
            k3 := Index(E2,[3]);
            E1[j1] := [5]; D[I1[j1]] := [5];
            E2[k3] := [5]; D[I2[k3]] := [5];
        elif [1] in E2 then
            k1 := Index(E2,[1]);
            E1[j1] := [1]; D[I1[j1]] := [1];
            E2[k1] := [3]; D[I2[k1]] := [3];
        end if;
        i3 := Index(E0,[3]);
        j1 := Index(E1,[1]);
        stable := false;
    end while;
end procedure;

/*
// 2-increment 3-term relations:
[
    x3*y5*z5 - x1*y3*z1,
    x3*y5*z1 - x1*y3*z5,

    x3*y1*z7 - x1*y5*z1,
    x3*y1*z5 - x1*y1*z7,
    x3*y1*z3 - x1*y5*z5,
    x3*y1*z1 - x1*y1*z3
    ];
*/


