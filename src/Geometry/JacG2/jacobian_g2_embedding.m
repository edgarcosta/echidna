//////////////////////////////////////////////////////////////////////////////
//                                                                          // 
//  Formal Group Embedding                                                  //
//  Copyright (C) 2004 Geordie Williamson                                   //
//                     David Kohel <kohel@maths.usyd.edu>                   //
//                                                                          //
//  Distributed under the terms of the GNU General Public License (GPL)     //
//                  http://www.gnu.org/licenses/                            //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

forward FindUpperCoordinatesFld, FindUpperCoordinatesSeq; 
forward FindLowerCoordinatesFld, FindLowerCoordinatesFromUpper;

//////////////////////////////////////////////////////////////////////////////

intrinsic JacobianG2FormalGroupRelations(ff::[RngElt]) -> SeqEnum
    {
    This is a function for testing purposes only -- it returns generic
    relations which can be used for determining the embedding of the formal
    group in the Jacobian.  NB: The returned solving sequence requires
    the solution of two square roots (bug?).  
    INPUT: A sequence of polynomial coefficients.\n
    OUTPUT: A sequence of generic relations which determine s_i in terms of
    the (s_13, s_14, s_15) = (s_14, s_15, 1)?
    }
    a, JacRels := JacobianRelations(ff);
    
    M := Universe(JacRels);
    F := BaseRing(M);

    // New polynomial ring "near the origin":
    S<S01, S02, S03, S04, S05, S06, S07, 
        S08, S09, S10, S11, S12, S13, S14, S15> := PolynomialRing(F, 15);

    // The dehomogenisation homomorphism:
    dehomog := hom < M->S |
	1, S01, S02, S03, S04, S05, S06, S07, S08, S09, S10, S11, S12, S13, S14, S15 >;
    
    JacRels := [ dehomog(JacRels[i]) : i in [1..#JacRels]];
    
    require IsField(F): "Base ring must be a field";
    
    MonList := [ S.i : i in [1..15]];
    
    for i in [1..15] do
        MonList cat:= [ S.i*S.j : j in [i..15]];
    end for;
    
    V := VectorSpace(F, #MonList);
    
    RelsMat := [];
    
    for i in [1..#JacRels] do
        Mons := Monomials(JacRels[i]);
        Coeffs := Coefficients(JacRels[i]);
        RelsMat[i] := &+[Coeffs[j]*V.(Index(MonList,Mons[j])) : j in [1..#Mons]];
    end for;
    
    RelsMat := Matrix(RelsMat);
    
    // SS stands for "Solving Sequence":
    // (there are a few different possibilities:)
    SS := [15, 14, 13, 12, 11, 10, 4, 5, 3, 2, 9, 8, 7, 6, 1];
    // SS := [15, 14, 13, 12, 11, 10, 5, 4, 3, 8, 6, 7, 9, 2, 1];
    
    ReturnSequence := [ <15,0,false>, <14,0,false>, <13,0,false> ];
    // We return a sequence in which each entry has the form:
    // < index, relation, true/false>;
    // Where index s_i that it is possible to solve for, relation is the 
    // relation from which it is possible to derive s_i and true/false
    // indicates whether or not it is necessary to evaluate a square root:
    
    // We start from 4 since we already know s15, s14 and s13:
    for CurrentSS in [4..15] do
    
        // We first list all the monomials that can appear in our relation:
        WantedMons := [];
        for i in [1..CurrentSS-1] do
            for j in [1..i] do
                WantedMons cat:= [V.Index(MonList,S.SS[i]*S.SS[j])];
            end for;
        end for;
        // Monomials of the form S.CurrentIndex*S.j with j ne CurrentIndex:
        WantedMons cat:= [V.Index(MonList,S.SS[CurrentSS]*S.SS[j]) : j in [1..CurrentSS-1]];
        // Monomials of the form S.j with S.j already known or equal to S.CurrentIndex;
        WantedMons cat:= [V.Index(MonList,S.SS[j]) : j in [1..CurrentSS]];
        
        // We then create the corresponding space:
        WantedSpace := sub < V | WantedMons >;
        // ... and intersect it with the relations:
        WantedSpace :=  WantedSpace meet Image(RelsMat);
        
        // We now need to find an element in the WantedSpace that
        // contains a term of the form S.CurrentIndex*S.j for some j > CurrentIndex.
        
        NeededMons := [V.Index(MonList, S.SS[CurrentSS]*S.SS[j]): j in [1..CurrentSS-1]] cat
            [V.Index(MonList, S.SS[CurrentSS])];
        
        M := Transpose(Matrix(NeededMons));
        
        B := Basis(WantedSpace);
        
        PossibleRelations := [];
        // Stored as 1/size so that we can do an easy maximum:
        RelationSizes := [Rationals() | ];
        for i in [1..#B] do
            if B[i]*M eq 0 then
                RelationSizes[i] := 0;
            else
                sol := Solution(RelsMat, B[i]);
                sol := Eltseq(sol);
                PossibleRelations[i] := &+[sol[i]*JacRels[i] : i in [1..#JacRels]];
                RelationSizes[i] := 1/#Coefficients(PossibleRelations[i]);
            end if;
        end for;
        
        if not IsEmpty(PossibleRelations) then
            // We want the relation that is crudely the smallest:
            _, x := Maximum(RelationSizes);
            ReturnSequence[CurrentSS] := <SS[CurrentSS], PossibleRelations[x], false>;
            continue CurrentSS;
        end if;
        
        // We are here if, regrettably(!), we need to evaluate a square root:
        
        // We add the square term to both wanted and needed:
        WantedMons cat:= [ V.Index(MonList, S.SS[CurrentSS]*S.SS[CurrentSS])];
        NeededMons cat:= [ V.Index(MonList, S.SS[CurrentSS]*S.SS[CurrentSS])];
        
        WantedSpace := Image(RelsMat) meet sub < V | WantedMons >;
        B := Basis(WantedSpace);
        
        M := Transpose(Matrix(NeededMons));
        
        PossibleRelations := [];
        RelationSizes := [Rationals() | ];
        for i in [1..#B] do
            if B[i]*M eq 0 then
                RelationSizes[i] := 0;
                continue;
            else
                sol := Solution(RelsMat, B[i]);
                sol := Eltseq(sol);
                PossibleRelations[i] := &+[sol[i]*JacRels[i] : i in [1..#JacRels]];
                RelationSizes[i] := 1/#Coefficients(PossibleRelations[i]);
            end if;
        end for;
        // We want the relation that is crudely the "smallest":
        _, x := Maximum(RelationSizes);
        ReturnSequence[CurrentSS] := <SS[CurrentSS], PossibleRelations[x], true>;
    end for;
    return ReturnSequence;
end intrinsic;

intrinsic JacobianG2FormalEmbedding(K::Fld : Precision := 8) -> SeqEnum
    {}
    F<f0,f1,f2,f3,f4,f5,f6> := FunctionField(K,7 : Global); 
    return JacobianG2FormalEmbedding([f0,f1,f2,f3,f4,f5,f6] : Precision := Precision);
end intrinsic;

intrinsic JacobianG2FormalEmbedding(ff::[RngElt] : Precision := 8) -> RngMSerElt 
    {}
    _ , JacRels := JacobianG2Relations(ff);
    require #ff eq 7 : "Argument must have length 7.";
    F := Universe(ff);
    // We pick up the global object:
    P<X00,X01,X02,X03,X04,X05,X06,X07,
	X08,X09,X10,X11,X12,X13,X14,X15> := PolynomialRing(F,16 : Global);
    // We first need to find the 13 relations that express the
    // s_i in terms of other s_j. These are of the form X00*Xij - ...
    // New polynomial ring "near the origin":
    R<S01, S02, S03, S04, S05, S06, S07, 
	S08, S09, S10, S11, S12, S13, S14, S15> := PolynomialRing(F, 15);

    // The dehomogenisation homomorphism:
    dehomog := hom < P->R |
	1, S01, S02, S03, S04, S05, S06, S07, S08, S09, S10, S11, S12, S13, S14, S15>;
    
    // We already know S01 and S02. We want to find expressions for the others:
    sRel := []; sRel[1] := S01; sRel[2] := S02;
    CurRel := 1;
    for sIndex in [3..15] do
        errChk := CurRel;
        while HomogeneousComponent(dehomog(JacRels[CurRel]), 1) ne R.sIndex do
            CurRel := CurRel ne #JacRels select (CurRel + 1) else 1;
            if CurRel eq errChk then // We've cycled through without finding our Si
                require true: "Error: couldn't find an expression for Si in the relations.";
            end if;
        end while;
        sRel[sIndex] := -HomogeneousComponent(dehomog(JacRels[CurRel]),2);
    end for;
    // We now need to recursively generate the power series:
    Coef<S1,S2> := PolynomialRing(F, 2);
    R<X> := PowerSeriesRing(Coef);
    s := [BigO(X^2) : i in [1..15]];
    s[1] := X*S1; s[2] := X*S2;
    // Not sure whether this is quite right:
    steps := Ceiling(1/2*(Precision))-1;
    // This is probably pretty inefficient:
    for k in [1..steps] do
        s := [ Evaluate(sRel[i], s) : i in [1..15]];
    end for;
    return s;
end intrinsic;

function FindUpperCoordinatesFld(K, prec) 
    /*
    Returns the last three projective coordinates (ie u13, u14 and u15)
    when (1:s1:s2:..) is added to (1:t1:t2:..) on the Jacobian
    corresponding to the curve y^2 = f0 + f1*X + .. + f6*X^6 over K.
    */
    F<f0,f1,f2,f3,f4,f5,f6> := FunctionField(K,7 : Global); 
    return FindUpperCoordinatesSeq([f0,f1,f2,f3,f4,f5,f6],prec);
end function;

// If c = a + b on the Jacobian this intrinsic calculates approximations 
// for c13, c14 and c15 as power series in K[[s1,s2,t1,t2]];

function FindUpperCoordinatesSeq(ff,prec)
    /*
    Returns the last three projective coordinates (ie u13, u14 and u15)
    when (1:s1:s2:..) is added to (1:t1:t2:..) on the Jacobian
    corresponding to the curve ff.
    */
    
    // Precision less than 6 gives errors:
    prec := Maximum(prec, 6);
    // Almost nothing works unless we're over a field!:
    error if not IsField(Universe(ff)), "The elements of Argument 1 must belong to a field";
    error if #ff ne 7, "Argument 1 must have length 7";
    
    // The field that we are working over:
    F := Universe(ff);
    f0, f1, f2, f3, f4, f5, f6 := Explode(ff);
    
    T<s01, s02, s03, s04, s05, s06, s07, s08, s09, s10, s11, s12, s13, s14, s15, 
    t01, t02, t03, t04, t05, t06, t07, t08, t09, t10, t11, t12, t13, t14, t15> := PolynomialRing(F, 30) ;
    
    // These functions give the cubic that meets the curve at the two sets of points
    // given corresponding to (a01,..,a15) and (b01,..,b15). (See Flynn's article)
    a := [];
    // mu:
    mu := s10*t15 + t10*s15 - s14*t11 - t14*s11 + s13*(t12 + t13) + t13*(s12+ s13);
    // alpha:
    alpha := s07*t15 + t07*s15 + s13*t09 + t13*s09 - s14*t08 - t14*s08;
    // beta:
    beta := -s06*t15 - t06*s15 + s08*(t12 + t13) + t08*(s12 + s13) - s11*t09 - t11*s09;
    // gamma
    gamma := s06*t14 + t06*s14 - s07*(t12 + t13) - t07*(s12 + s13) + s09*t10 + t09*s10;
    // delta
    delta := -s06*t13 - t06*s13 + s07*t11 + t07*s11 - s08*t10 - t08*s10;
    
    // These formulas are lifted straight from Flynn's article:
    c13 := s15^2*t15^2*(delta^2 - f0*mu^2);
    c14 := s13*t13*(s15*t15*(f5*mu^2 - 2*alpha*beta) - (s15*t14 + s14*t15)*(alpha^2 - f6*mu^2));
    c15 := s13*t13*s15*t15*(alpha^2 - f6*mu^2);
    
    PowSer := JacobianG2FormalEmbedding(ff : Precision := prec);
    
    Coeffs<S1,S2,T1,T2> := PolynomialRing(F,4);
    P<X> := PowerSeriesRing(Coeffs);
    
    Q := Universe(PowSer);
    B := BaseRing(Q);
    f := hom< B -> Coeffs | [S1, S2] >;
    g := hom< B -> Coeffs | [T1, T2] >;
    
    s1 := S1*X; s2 := S2*X; t1 := T1*X; t2 := T2*X;
    
    aLocalSeries := [];
    for i in [1..#PowSer] do
        seq, val := Eltseq(PowSer[i]);
        p := RelativePrecision(PowSer[i]);
        aLocalSeries[i] := elt< P | val, [f(seq[j]) : j in [1..#seq]], p>;
    end for;
    
    bLocalSeries := [];
    for i in [1..#PowSer] do
        seq, val := Eltseq(PowSer[i]);
        p := RelativePrecision(PowSer[i]);
        bLocalSeries[i] := elt< P | val, [g(seq[j]) : j in [1..#seq]], p>;
    end for;

    LocalSeries := aLocalSeries cat bLocalSeries;
    
    // We now evaluate our exact projective expressions for c13, c14 and c15
    // at the series approximations for s1,..,s15 and t1,..,t15:
    cp13 := Evaluate(c13, LocalSeries);
    cp14 := Evaluate(c14, LocalSeries);
    cp15 := Evaluate(c15, LocalSeries);
    
    // We could return cp13, cp14, cp15 now, but it is neater if we 
    // divide out by any common factors and multiply by a factor of (s2 + t2)^2
    // Flynn uses (s2 + t2)^2/((s1^2*t1^2*s2^8*t2^8(s1*t2 - s2*t1)^4));
    
    seq13 := Eltseq(cp13); seq14 := Eltseq(cp14); seq15 := Eltseq(cp15);
    DivRenorm := GreatestCommonDivisor(seq13 cat seq14 cat seq15);
    DivRenorm := DivRenorm*X^(TotalDegree(DivRenorm));

    DivRenorm := P!1;

    MultRenorm := P!1;
    MultRenorm := (s2 + t2)^2;
    
    // MultRenorm := (s1+t1)^8*(s2 + t2)^6*s1^4*s2^4*t1^4*t2^4*(s1*t2-s2*t1)^4;
    
    cp13 := P!(MultRenorm*cp13/DivRenorm);
    cp14 := P!(MultRenorm*cp14/DivRenorm);
    cp15 := P!(MultRenorm*cp15/DivRenorm);
    return [cp13, cp14, cp15];
end function;

function FindLowerCoordinatesFld(K,prec) // -> SeqEnum
    /*
    Given the last three projective coordinates for a point on the Jacobian of
    a generic curve over k, attempt to find the coordinates of all the other points.
    If successful this function returns the first two coordinates (ie s1 and s2).
    */
    F<f0,f1,f2,f3,f4,f5,f6> := FunctionField(K,7);
    return FindLowerCoordinatesFromUpper([f0,f1,f2,f3,f4,f5,f6], FindUpperCoordinatesFld(K,prec));
end function;

function FindLowerCoordinatesFromUpper(ff, UpperCoords)
    /*
    Given the last three projective coordinates for a point on the Jacobian of
    a curve given by ff, attempt to find the coordinates of all the other points.
    If successful this function returns the first two coordinates (ie s1 and s2).
    */
    SolvingSequence := JacobianG2FormalGroupRelations(ff);
    // The polynomial ring in X01, X02, X03 etc:
    M := Parent(SolvingSequence[5][2]);
    
    // The "multivariate power series ring" R[s1,s2,t1,t2][[X]]:
    P := Universe(UpperCoords);
    X := P.1;
    
    Coeffs := BaseRing(P);
    s1 := Coeffs.1*X; s2 := Coeffs.2*X; t1 := Coeffs.3*X; t2 := Coeffs.4*X;
    
    // We need the power series ring over the function field
    // to use the SquareRoot intrinsic below:    
    BiggerCoeffs := FieldOfFractions(Coeffs);
    Q := PowerSeriesRing(BiggerCoeffs);
    
    // SExpand stores the power series expansion for each s_i:
    SExpand := [P | 1 : i in [1..16]];

    // FindUpperCoordinates() has given us s13, s14 and s15:
    
    SExpand[0 + 1] := s1^2*t1^2*s2^8*t2^8*(s2*t1 - s1*t2)^4;
    
    SExpand[13+1] := UpperCoords[1];
    SExpand[14+1] := UpperCoords[2];
    SExpand[15+1] := UpperCoords[3];
    
    for Step in SolvingSequence do
        CurrentIndex, Relation, IsSquare := Explode(Step);
        printf "Attempting to calculate s%o using the following relation:\n%o\n", CurrentIndex, Relation;
        if not IsSquare then
            top, bottom := Explode(Terms(Relation, M.(CurrentIndex+1)));
            bottom := ExactQuotient(bottom, M.(CurrentIndex+1));
            top := Evaluate(top, SExpand); bottom := Evaluate(bottom, SExpand);
            result := Q!(-top / bottom);
        else
            printf "(Note: We must evaluate a square root)\n";
            c, b, a := Explode(Terms(Relation, M.(CurrentIndex+1)));
            error if not b eq 0, "Unexpected quadratic! (rather than just a square root)";
            a := ExactQuotient(a, (M.(CurrentIndex+1))^2);
            a := Evaluate(a, SExpand); c := Evaluate(c, SExpand);
            // We need to write a SquareRoot function as this generic
            // intrinsic doesn't working in characteristic not equal to 0.
            result := SquareRoot(Q!(-c/a));
        end if;
        // We must clear any denominators:
        seq := Eltseq(result);
        denom := &*[Denominator(seq[i]) : i in [1..#seq]];
        denom := ExactQuotient(denom, GCD([Denominator(seq[i]) : i in [1..#seq]]));
        denom := denom*X^TotalDegree(denom);
        // Update all the other coordinates:
        for i in {1..16} do
            SExpand[i] *:= denom;
        end for;
        SExpand[CurrentIndex+1] := P!(denom*result);
        printf "Finished (Relative precision: %o. Denominator: %o).\n\n", 
            RelativePrecision(SExpand[CurrentIndex+1]), Eltseq(denom)[1];
    end for;
    return [SExpand[0+1], SExpand[1+1], SExpand[2+1]], SExpand;
end function;
