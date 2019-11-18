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

function HasClassNumberOne(D)
    if D in [ -3, -4, -7, -8, -11, -12, -16, -19, -27, -28, -43, -67, -163 ] then
        return true;
    else
        return false;
    end if;
end function;

function ClassNumberOneRepresentationNumber(D,n : Primitive := false)
    // Assume D is one of the 13 class number one discriminants.
    if D eq -3 then
        nreps := 6;
    elif D eq -4 then
        nreps := 4;
    else
        nreps := 2;
    end if;
    for prm in Factorization(n) do
        chi := KroneckerSymbol(D,prm[1]);
        if chi eq 1 then
            if Primitive then
                nreps *:= 2;
            else
                nreps *:= prm[2] + 1;
            end if;
        elif chi eq 0 then
            if Primitive and prm[2] gt 1 then
                return 0;
            end if;
        elif chi eq -1 then
            if Primitive or prm[2] mod 2 eq 1 then
                return 0;
            end if;
        end if;
    end for;
    return nreps;
end function;

intrinsic RepresentationNumber(L::Lat,n::RngIntElt : Primitive := false) -> RngIntElt
    {The n-th representation number of the lattice L.}
    require IsIntegral(L): "Argument 1 must be an integral lattice.";
    require n ge 0: "Argument 2 must be an positive integer.";
    if n eq 0 then
        return 1;
    end if;
    dim := Dimension(L);
    if dim eq 0 then
        return 0;
    end if;
    A := GramMatrix(L);
    m := GCD(Eltseq(A));
    if n mod m ne 0 then
        return 0;
    end if;
    if dim eq 1 then
        if Primitive then
            return n eq m select 2 else 0;
        else
            return IsSquare(n div m) select 2 else 0;
        end if;
    end if;
    if m gt 1 then
        n div:= m;
        A div:= m;
        L := LatticeWithGram(A);
    end if;
    if IsEven(L) and n mod 2 ne 0 then
        return 0;
    end if;
    S, B := SuccessiveMinima(L);
    for k in [1..dim] do
        if S[k] gt n then
            if k eq 1 then
                return 0; 
            elif k eq 2 then
                if n mod S[1] eq 0 then
                    bool, m := IsSquare(n div S[1]);
                    if not bool then
                        return 0;
                    elif Primitive and m gt 1 then
                        return 0;
                    else // m eq 1 or not Primitive 
                        return 2;
                    end if;
                else
                    return 0;
                end if;
            end if;
            dim := k-1;
            A := Matrix(dim,[ InnerProduct(B[i],B[j]) : i,j in [1..dim] ]);
            L := LatticeWithGram(A);
        end if;
    end for;
    /* Now A has content 1, dim is at least 2, and n > 0. */
    if dim eq 2 then
        if IsEven(L) then
            D := -Determinant(L);
        else
            D := -4*Determinant(L);
        end if;
        if HasClassNumberOne(D) then
            print "HERE";
            if IsEven(L) then
                return ClassNumberOneRepresentationNumber(D,n div 2 : Primitive := Primitive);
            else
                return ClassNumberOneRepresentationNumber(D,n : Primitive := Primitive);
            end if;
        end if;
    end if;
    t := ThetaSeries(L,n);
    if Primitive then
        n1, n2 := SquarefreeFactorization(n);
        return &+[ MoebiusMu(n2 div m2)*Coefficient(t,n1 * m2^2) : m2 in Divisors(n2) ];
    else
        return Coefficient(t,n);
    end if;
end intrinsic;
