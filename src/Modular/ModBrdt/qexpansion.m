////////////////////////////////////////////////////////////////////////
//                                                                    //
//                          David Kohel                               //
//                q-Expansion Bases for Brandt Modules                //
//                                                                    //
////////////////////////////////////////////////////////////////////////

import "hecke_operators.m" : ExtendHecke;

forward EchelonSeries, ValuationOrder;

intrinsic ThetaSeries(
    u::ModBrdtElt, v::ModBrdtElt, prec::RngIntElt) -> RngSerElt
    {The value of the theta series pairing.}
    M := Parent(u);
    require M eq Parent(v) : "Arguments have different parents.";
    A := AmbientModule(M);
    if M ne A then
        return ThetaSeries(A!u, A!v, prec);
    end if;
    h := Dimension(M);
    if A`HeckePrecision lt prec then 
        ExtendHecke(A,prec); 
    end if;
    PS := Universe(A`ThetaSeries);  
    f := PS!0;
    c1 := Eltseq(u); c2 := Eltseq(v);
    for i in [1..h] do
        k := Binomial(h+1,2) - Binomial(h-i+2,2) + 1;
        c := c1[i]*c2[i];
        if c ne 0 then f +:= c1[i]*c2[i]*A`ThetaSeries[k]; end if;
        for j in [i+1..h] do
            k := Binomial(h+1,2) - Binomial(h-i+2,2) + j-i+1;
            c := c1[i]*c2[j] + c1[j]*c2[i];
            if c ne 0 then f +:= c*A`ThetaSeries[k]; end if;
        end for;
    end for;
    return f + O(PS.1^(prec+1));
end intrinsic;

intrinsic qExpansionBasis(M::ModBrdt,n::RngIntElt) -> SeqEnum
    {}
    B := Basis(M);
    P := PowerSeriesRing(BaseRing(M));
    S := &cat[ Parent([P|]) | 
        [ P!ThetaSeries(B[i],B[j],n) : i in [1..j] ] : j in [1..#B] ];
    return EchelonSeries(S,n);
end intrinsic;

intrinsic qExpansionBasis(B::[ModBrdtElt],n::RngIntElt) -> SeqEnum
    {}
    P := PowerSeriesRing(BaseRing(Universe(B)));
    S := &cat[ Parent([P|]) | 
        [ P!ThetaSeries(B[i],B[j],n) : i in [1..j] ] : j in [1..#B] ];
    return EchelonSeries(S,n);
end intrinsic;

function EchelonSeries(B,n)
    // Returns the echelonized power series spanning the same space.
    if #B eq 0 then return B; end if;
    P := Universe(B);
    R := BaseRing(P);
    M := Matrix(R,[ [ Coefficient(f,j) : j in [0..n-1] ] : f in B ]);
    M := EchelonForm(M); 
    return [ P | P!Eltseq(M[i])+O(P.1^n) : i in [1..Rank(M)] ];
end function;
