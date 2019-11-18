//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//                  BRANDT MODULE DATABASE CONSTRUCTORS                     //
//                                                                          //
//  Copyright (C) 2007 David Kohel <kohel@maths.usyd.edu>                   //
//                                                                          //
//  Distributed under the terms of the GNU General Public License (GPL)     //
//                  http://www.gnu.org/licenses/                            //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////


//////////////////////////////////////////////////////////////////////////////
//                          Accessory Function                              //
//////////////////////////////////////////////////////////////////////////////

function LevelPairs(N)
    fac := Factorization(N);
    S := [ Parent([ Integers() | ]) | ];
    for k in [1..#fac by 2] do
        for T in Subsets(SequenceToSet(fac),k) do
            if &and[ pp[2] le 2 : pp in T ] then
                D := &*[ pp[1] : pp in T ];
                Append(~S,[D,N div D]);
            end if;
        end for;
    end for;
    return Sort(S);
end function;

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

intrinsic BuildBrandtModuleDatabase(Dat::DBUser,S::[RngIntElt] :
    LevelOne := false)
    {Build the database of Brandt modules for all levels (D,m) 
    with D*m in S.}
    require Dat`DBIdentifier eq "Brandt module" :
        "Argument 1 must be the database of Brandt modules.";
    DBQA := QuaternionAlgebraDatabase(); 
    for N in S do
        vprintf Brandt : "Level N = %o\n", N; 
        for L in LevelPairs(N) do
            D, m := Explode(L);
            if (m eq 1 or not LevelOne) then
                if [D,m] in Dat then 
                    vprintf Brandt : 
                        "  Already computed (D,m) = (%o,%o)\n", D, m; 
                else
                    if [D,m] in DBQA then
                        vprintf Brandt : "  Found (D,m) = (%o,%o) " *
                            "in quaternion database\n", D, m;
                        Q := QuaternionIdealClasses(DBQA,D,m);
                        vprint Brandt :
                            "  ClassNumber:", ClassNumber(Q);
                    else
                        vprintf Brandt :
                            "  Computing (D,m) = (%o,%o)\n", D, m; 
                        tyme := Cputime();
                        A := QuaternionOrder(D,m);
                        Q := QuaternionIdealClasses(A : Reduce);
                        if [D,m] notin DBQA then
                            Write(DBQA,Q : Overwrite);
                        end if;
                        vprintf Brandt :
                            "  Quaternion ideals time: %o\n", Cputime(tyme);
                        vprint Brandt :
                            "  ClassNumber:", ClassNumber(Q);
                    end if;
                    tyme := Cputime();
                    M := BrandtModule(Q : ComputeGrams);
                    printf "  Brandt modules time: %o\n", Cputime(tyme);
                    Write(Dat,M);
                    print "  Dimension =", Dimension(M);
                end if;
            end if;
        end for;
    end for;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//                     DECOMPOSITION DATABASE CONSTRUCTOR                   //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

intrinsic BuildBrandtDecompositionDatabase(
    Dat::DBUser,S::SeqEnum[SeqEnum[RngIntElt]] :
    HeckeBound := 0,
    Sort := true,
    ThetaSeries := false,
    UseBrandtDatabase := true,
    UseHeckeAlgebraDatabase := true,
    UseQuaternionDatabase := true,
    Overwrite := false)
    {Build the decomposition database for Brandt modules
    of levels (D,m) with [D,m] in S.}
    
    require Dat`DBIdentifier eq "Brandt decomposition" :
        "Argument 1 must be the database of Brandt decompositions.";
    require &and[ #L eq 2 : L in S ] : 
        "Argument 2 must consist of level pairs.";
    DBBM := BrandtModuleDatabase();
    DBHA := HeckeAlgebraDatabase();
    DBQA := QuaternionAlgebraDatabase();
    BoolModBrdt := UseBrandtDatabase;
    BoolAlgHck := UseHeckeAlgebraDatabase;
    BoolAlgQuat := UseQuaternionDatabase;
    for L in S do
        D, m := Explode(L);
        if not Overwrite and [D,m] in Dat then
            printf "  Already computed (D,m) = (%o,%o)\n", D, m; 
        else
            tyme := Cputime();
            if BoolModBrdt and [D,m] in DBBM then 
                printf "  Found BrandtModule(%o,%o) " *
                    "in Brandt database.\n", D, m; 
                M := BrandtModule(DBBM,D,m);
            elif BoolAlgQuat and [D,m] in DBQA then
                printf "  Found BrandtModule(%o,%o) " *
                    "in quaternion database.\n", D, m; 
                Q := QuaternionIdealClasses(DBQA,D,m);
                M := BrandtModule(Q);
                // Haven't computed gram matrices...
                // Write(DBBM,M : Overwrite);
            else
                printf "  Computing QuaternionIdealClasses(%o,%o).\n",
                    D, m;
                Q := QuaternionIdealClasses(D,m);
                Write(DBQA,Q : Overwrite);
                M := BrandtModule(Q);
                // Haven't computed gram matrices...
                // Write(DBBM,M : Overwrite);
            end if;
            if HeckeBound eq 0 then
                HckBnd := Level(M);
            else
                HckBnd := Min(Level(M),HeckeBound);
            end if;
            if BoolAlgHck then
                h := Dimension(M);
                for q in AtkinLehnerPrimes(M) do 
                    e := Valuation(m,q);
                    if D mod q eq 0 and e eq 1 then
                        if <[D,m],"U",q> notin DBHA then
                            BuildHeckeAlgebraDatabase(DBHA,[[D,m]],1);
                        end if;
                        if not assigned M`CharacterPrimes then
                            M`CharacterPrimes := [];
                            M`CharacterPermutations := [];
                        end if;
                        U := CharacterOperator(DBHA,[D,m],q);
                        pi := [ Index(Eltseq(U[i]),1) : i in [1..h] ];
                        Append(~M`CharacterPrimes,q);
                        Append(~M`CharacterPermutations,pi);
                    end if;
                    if <[D,m],"W",q> notin DBHA then
                        BuildHeckeAlgebraDatabase(DBHA,[[D,m]],1);
                    end if;
                    if not assigned M`AtkinLehnerPermutations then
                        M`AtkinLehnerPermutations := [];
                    end if;
                    W := AtkinLehnerOperator(DBHA,[D,m],q);
                    pi := [ Index(Eltseq(W[i]),x) : i in [1..h] ]
                        where x := D mod q eq 0 select -1 else 1;
                    Append(~M`AtkinLehnerPermutations,pi);
                    k := Index(AtkinLehnerPrimes(M),q);
                    assert M`AtkinLehnerPermutations[k] eq pi;
                end for;
                p := 2;
                while p le HckBnd do
                    if <[D,m],"T",p> in DBHA then
                        T := HeckeOperator(DBHA,[D,m],p);
                        Append(~M`HeckePrimes,p);
                        Append(~M`HeckeOperators,T);
                        M`HeckePrecision := p;
                        p := NextPrime(p);
                    else
                        p := HckBnd+1;
                    end if;
                end while;
            end if;
            printf "  Brandt module time: %o\n", Cputime(tyme);
            print "  Dimension =", Dimension(M);
            prms := PrimeDivisors(m);
            if not assigned M`ConductorPrimes then
                M`ConductorPrimes := prms;
            end if;
            if not assigned M`DegeneracyIndices then
                M`DegeneracyIndices := [];
            end if;
            DBBQ := BrandtDegeneraciesDatabase();
            h := Dimension(M);
            tyme := Cputime();
            for k in [1..#prms] do
                p := prms[k];
                if <[D,m],p> in DBBQ then
                    _, degen_indxs :=
                        DegeneracyMaps(DBBQ,[D,m],p);
                else
                    _, degen_indxs, degen_isoms :=
                        DegeneracyMaps(M,p);
                    Write(DBBQ,[D,m,1],p,
                        degen_indxs,degen_isoms);
                end if;
                M`DegeneracyIndices[k] := degen_indxs;
            end for;
            print "  Brandt degeneracies time:", Cputime(tyme);
            X := NewSubspace(CuspidalSubspace(M));
            dcmp := Decomposition(X,HckBnd : Proof := false, 
                ThetaSeries := ThetaSeries, Sort := Sort);
            Write(Dat,[D,m,1],dcmp : Overwrite := Overwrite);
            if assigned M`NormGrams and [D,m] notin DBBM then
                Write(DBBM,M);
            end if;
            printf "  Decomposition time: %o\n", Cputime(tyme);
            print "  NewSubspace dimensions =",
                [ Dimension(N) : N in dcmp ];
        end if;
    end for;
end intrinsic;

intrinsic BuildBrandtDecompositionDatabase(
    Dat::DBUser,S::[RngIntElt] :
    HeckeBound := 0,
    LevelOne := false, 
    Sort := true,
    SquareFree := false,
    ThetaSeries := false,
    UseBrandtDatabase := true,
    UseHeckeAlgebraDatabase := true,
    UseQuaternionDatabase := true,
    Overwrite := false)
    {Build the decomposition database for Brandt modules
    of levels (D,m) with D*m in S.}
    
    require Dat`DBIdentifier eq "Brandt decomposition" :
        "Argument 1 must be the database of Brandt decompositions.";
    DBBM := BrandtModuleDatabase();
    DBHA := HeckeAlgebraDatabase();
    DBQA := QuaternionAlgebraDatabase();
    BoolModBrdt := UseBrandtDatabase;
    BoolAlgHck := UseHeckeAlgebraDatabase;
    BoolAlgQuat := UseQuaternionDatabase;
    if SquareFree then
        S := [ N : N in S | IsSquarefree(N) ];
    end if;
    for N in S do
        printf "Level N = %o\n", N; 
        for L in LevelPairs(N) do
            D, m := Explode(L);
            if (m eq 1 or not LevelOne) then
                if not Overwrite and [D,m] in Dat then
                    printf "  Already computed (D,m) = (%o,%o)\n", D, m; 
                else
                    tyme := Cputime();
                    if BoolModBrdt and [D,m] in DBBM then 
                        printf "  Found BrandtModule(%o,%o) " *
                            "in Brandt database.\n", D, m; 
                        M := BrandtModule(DBBM,D,m);
                    elif BoolAlgQuat and [D,m] in DBQA then
                        printf "  Found BrandtModule(%o,%o) " *
                            "in quaternion database.\n", D, m; 
                        Q := QuaternionIdealClasses(DBQA,D,m);
                        M := BrandtModule(Q);
                        // Haven't computed gram matrices...
                        // Write(DBBM,M : Overwrite);
                    else
                        printf "  Computing QuaternionIdealClasses(%o,%o).\n",
                            D, m;
                        Q := QuaternionIdealClasses(D,m);
                        Write(DBQA,Q : Overwrite);
                        M := BrandtModule(Q);
                        // Haven't computed gram matrices...
                        // Write(DBBM,M : Overwrite);
                    end if;
                    if HeckeBound eq 0 then
                        HckBnd := Level(M);
                    else
                        HckBnd := Min(Level(M),HeckeBound);
                    end if;
                    if BoolAlgHck then
                        h := Dimension(M);
                        for q in AtkinLehnerPrimes(M) do 
                            e := Valuation(m,q);
                            if D mod q eq 0 and e eq 1 then
                                if <[D,m],"U",q> notin DBHA then
                                    BuildHeckeAlgebraDatabase(DBHA,[[D,m]],1);
                                end if;
                                if not assigned M`CharacterPrimes then
                                    M`CharacterPrimes := [];
                                    M`CharacterPermutations := [];
                                end if;
                                U := CharacterOperator(DBHA,[D,m],q);
                                pi := [ Index(Eltseq(U[i]),1) : i in [1..h] ];
                                Append(~M`CharacterPrimes,q);
                                Append(~M`CharacterPermutations,pi);
                            end if;
                            if <[D,m],"W",q> notin DBHA then
                                BuildHeckeAlgebraDatabase(DBHA,[[D,m]],1);
                            end if;
                            if not assigned M`AtkinLehnerPermutations then
                                M`AtkinLehnerPermutations := [];
                            end if;
                            W := AtkinLehnerOperator(DBHA,[D,m],q);
                            pi := [ Index(Eltseq(W[i]),x) : i in [1..h] ]
                                where x := D mod q eq 0 select -1 else 1;
                            Append(~M`AtkinLehnerPermutations,pi);
                            k := Index(AtkinLehnerPrimes(M),q);
                            assert M`AtkinLehnerPermutations[k] eq pi;
                        end for;
                        p := 2;
                        while p le HckBnd do
                            if <[D,m],"T",p> in DBHA then
                                T := HeckeOperator(DBHA,[D,m],p);
                                Append(~M`HeckePrimes,p);
                                Append(~M`HeckeOperators,T);
                                M`HeckePrecision := p;
                                p := NextPrime(p);
                            else
                                p := HckBnd+1;
                            end if;
                        end while;
                    end if;
                    printf "  Brandt module time: %o\n", Cputime(tyme);
                    print "  Dimension =", Dimension(M);
                    prms := PrimeDivisors(m);
                    if not assigned M`ConductorPrimes then
                        M`ConductorPrimes := prms;
                    end if;
                    if not assigned M`DegeneracyIndices then
                        M`DegeneracyIndices := [];
                    end if;
                    DBBQ := BrandtDegeneraciesDatabase();
                    h := Dimension(M);
                    tyme := Cputime();
                    for k in [1..#prms] do
                        p := prms[k];
                        if <[D,m],p> in DBBQ then
                            _, degen_indxs :=
                                DegeneracyMaps(DBBQ,[D,m],p);
                        else
                            _, degen_indxs, degen_isoms :=
                                DegeneracyMaps(M,p);
                            Write(DBBQ,[D,m,1],p,
                                degen_indxs,degen_isoms);
                        end if;
                        M`DegeneracyIndices[k] := degen_indxs;
                    end for;
                    print "  Brandt degeneracies time:", Cputime(tyme);
                    X := NewSubspace(CuspidalSubspace(M));
                    dcmp := Decomposition(X,HckBnd : Proof := false, 
                        ThetaSeries := ThetaSeries, Sort := Sort);
                    Write(Dat,[D,m,1],dcmp : Overwrite := Overwrite);
                    if assigned M`NormGrams and [D,m] notin DBBM then
                        Write(DBBM,M);
                    end if;
                    printf "  Decomposition time: %o\n", Cputime(tyme);
                    print "  NewSubspace dimensions =",
                        [ Dimension(N) : N in dcmp ];
                end if;
            end if;
        end for;
    end for;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//                   BRANDT DEGENERACY DATABASE CONSTRUCTOR                 //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

intrinsic BuildBrandtDegeneraciesDatabase(
    Dat::DBUser,S::SeqEnum[SeqEnum[RngIntElt]] : 
    Overwrite := false)
    {}
    require Dat`DBIdentifier eq "Brandt degeneracies" :
        "Argument 1 must be the database of Brandt degeneracies.";
    require &and[ #L eq 2 : L in S ] : 
        "Argument 2 must consist of level pairs.";
    DBQA := QuaternionAlgebraDatabase();
    for L in S do
        D, m := Explode(L);
        prms := PrimeDivisors(m);
        if m eq 1 then
            // Do nothing
        elif not Overwrite and &and[ <[D,m],p> in Dat : p in prms ] then
            vprintf Brandt :
                "  Already computed degeneracies for " *
                "(D,m) = (%o,%o).\n", D, m;
        else
            tyme := Cputime();
            Q := QuaternionIdealClasses(DBQA,D,m);
            vprint Brandt : "  ClassNumber:", ClassNumber(Q);
            for p in prms do
                if Overwrite or <[D,m],p> notin Dat then
                    _, degen_indxs, degen_isoms :=
                        DegeneracyMaps(Q,p);
                    Write(Dat,[D,m,1],p,degen_indxs,degen_isoms :
                        Overwrite := Overwrite);
                end if;
            end for;
            printf "  Time for (D,m) = (%o,%o): %o\n",
                D, m, Cputime(tyme);;
        end if;
    end for;
end intrinsic;

intrinsic BuildBrandtDegeneraciesDatabase(Dat::DBUser,S::[RngIntElt] : 
    Overwrite := false)
    {}
    require Dat`DBIdentifier eq "Brandt degeneracies" :
        "Argument 1 must be the database of Brandt degeneracies.";
    DBQA := QuaternionAlgebraDatabase();
    for N in S do
        vprintf Brandt : "Level N = %o\n", N; 
        for L in LevelPairs(N) do
            D, m := Explode(L);
            prms := PrimeDivisors(m);
            if m eq 1 then
                // Do nothing
            elif not Overwrite and &and[ <[D,m],p> in Dat : p in prms ] then
                vprintf Brandt :
                    "  Already computed degeneracies for " *
                    "(D,m) = (%o,%o).\n", D, m;
            else
                tyme := Cputime();
                Q := QuaternionIdealClasses(DBQA,D,m);
                vprint Brandt : "  ClassNumber:", ClassNumber(Q);
                for p in prms do
                    if Overwrite or <[D,m],p> notin Dat then
                        _, degen_indxs, degen_isoms :=
                            DegeneracyMaps(Q,p);
                        Write(Dat,[D,m,1],p,degen_indxs,degen_isoms :
                            Overwrite := Overwrite);
                    end if;
                end for;
                printf "  Time for (D,m) = (%o,%o): %o\n",
                    D, m, Cputime(tyme);;
            end if;
        end for;
    end for;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//                     HECKE ALGEBRA DATABASE CONSTRUCTOR                   //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

intrinsic BuildHeckeAlgebraDatabase(
    Dat::DBUser,S::SeqEnum[SeqEnum[RngIntElt]],B::RngIntElt :
    UseBrandtDatabase := true,
    UseQuaternionDatabase := true,
    Overwrite := false)
    {}
    require Dat`DBIdentifier eq "Hecke algebra" :
        "Argument 1 must be the database of Hecke algebras.";
    require &and[ #L in {2,3} : L in S ] :  
        "Argument 2 must be a sequence of sequences of level 2 or 3.";
    DBBM := BrandtModuleDatabase();
    DBQA := QuaternionAlgebraDatabase();
    BoolModBrdt := UseBrandtDatabase;
    BoolAlgQuat := UseQuaternionDatabase;
    for L in S do
        D, m := Explode(L);
        c := #L eq 2 select 1 else L[3]; assert c eq 1;
        tyme := Cputime();
        if BoolModBrdt and [D,m] in DBBM then 
            printf "  Found BrandtModule(%o,%o) " *
                "in Brandt database.\n", D, m; 
            M := BrandtModule(DBBM,D,m);
            if GCD(D,m) ne 1 and [D,m] in DBQA then
                Q := QuaternionIdealClasses(DBQA,D,m);
                M`LeftIdeals := LeftIdealClasses(Q);
            end if;
        elif BoolAlgQuat and [D,m] in DBQA then
            printf "  Found QuaternionIdealClases(%o,%o) " *
                "in quaternion database.\n", D, m; 
            Q := QuaternionIdealClasses(DBQA,D,m);
            M := BrandtModule(Q);
            // Haven't computed gram matrices...
            //Write(DBBM,M : Overwrite);
        else
            printf "  Computing QuaternionIdealClasses(%o,%o).\n", D, m;
            Q := QuaternionIdealClasses(D,m);
            Write(DBQA,Q : Overwrite);
            printf "  Computing BrandtModule(%o,%o).\n", D, m; 
            M := BrandtModule(Q);
            // Haven't computed gram matrices...
            // Write(DBBM,M : Overwrite);
        end if;
        printf "  Brandt module time: %o\n", Cputime(tyme);
        print "  Dimension =", Dimension(M);
        HckBnd := B;
        for p in AtkinLehnerPrimes(M) do 
            e := Valuation(m,p);
            if not Overwrite and <[D,m,c],"W",p> in Dat then
                printf "  Already computed W_%o(%o,%o)\n", p, D, m;
            else
                W := AtkinLehnerOperator(M,p);
                Write(Dat,M,"W",W,p : Overwrite := Overwrite);
            end if;
            if D mod p eq 0 and e eq 1 then
                if not Overwrite and <[D,m,c],"U",p> in Dat then
                    printf "  Already computed U_%o(%o,%o)\n", p, D, m;
                else
                    U := CharacterOperator(M,p);
                    Write(Dat,M,"U",U,p : Overwrite := Overwrite);
                end if;
            end if;
        end for;
        for p in Reverse(Primes([1..B])) do 
            if not Overwrite and <[D,m,c],"T",p> in Dat then
                printf "  Already computed T_%o(%o,%o)\n", p, D, m;
                break p;
            else
                T := HeckeOperator(M,p);
                Write(Dat,M,"T",T,p : Overwrite := Overwrite);
            end if;
        end for;
        printf "  Hecke operators time: %o\n", Cputime(tyme);
    end for;
end intrinsic;

intrinsic BuildHeckeAlgebraDatabase(
    Dat::DBUser,S::[RngIntElt],B::RngIntElt : 
    LevelOne := false, 
    SquareFree := false,
    ThetaSeries := false,
    UseBrandtDatabase := true,
    UseQuaternionDatabase := true,
    Overwrite := false)
    {Build the Hecke operator database for Brandt modules
    of levels (D,m) with D*m in S.}
    
    require Dat`DBIdentifier eq "Hecke algebra" :
        "Argument 1 must be the database of Hecke algebras.";
    DBBM := BrandtModuleDatabase();
    DBQA := QuaternionAlgebraDatabase();
    BoolModBrdt := UseBrandtDatabase;
    BoolAlgQuat := UseQuaternionDatabase;
    if SquareFree then
        S := [ N : N in S | IsSquarefree(N) ];
    end if;
    for N in S do
        printf "Level N = %o\n", N; 
        for L in LevelPairs(N) do
            D, m := Explode(L); c := 1;
            if (m eq 1 or not LevelOne) then
                tyme := Cputime();
                if BoolModBrdt and [D,m] in DBBM then 
                    printf "  Found BrandtModule(%o,%o) " *
                        "in Brandt database.\n", D, m; 
                    M := BrandtModule(DBBM,D,m);
                    if GCD(D,m) ne 1 and [D,m] in DBQA then
                        Q := QuaternionIdealClasses(DBQA,D,m);
                        M`LeftIdeals := LeftIdealClasses(Q);
                    end if;
                elif BoolAlgQuat and [D,m] in DBQA then
                    printf "  Found BrandtModule(%o,%o) " *
                        "in quaternion database.\n", D, m; 
                    Q := QuaternionIdealClasses(DBQA,D,m);
                    M := BrandtModule(Q);
                else
                    printf "  Computing BrandtModule(%o,%o).\n", D, m; 
                    M := BrandtModule(QuaternionOrder(D,m));
                end if;
                printf "  Brandt module time: %o\n", Cputime(tyme);
                print "  Dimension =", Dimension(M);
                HckBnd := B;
                for p in AtkinLehnerPrimes(M) do 
                    if D mod p ne 0 or Valuation(m,p) eq 0 then
                        if not Overwrite and <[D,m,c],"W",p> in Dat then
                            printf "  Already computed W_%o(%o,%o)\n", p, D, m;
                        else
                            W := AtkinLehnerOperator(M,p);
                            Write(Dat,M,"W",W,p : Overwrite := Overwrite);
                        end if;
                    else
                        assert Valuation(m,p) eq 1;
                        if not Overwrite and <[D,m,c],"U",p> in Dat then
                            printf "  Already computed U_%o(%o,%o)\n", p, D, m;
                        else
                            assert IsPrime(p);
                            U := CharacterOperator(M,p);
                            Write(Dat,M,"U",U,p : Overwrite := Overwrite);
                        end if;
                    end if;
                end for;
                for p in Reverse(Primes([1..B])) do 
                    if not Overwrite and <[D,m,c],"T",p> in Dat then
                        printf "  Already computed T_%o(%o,%o)\n", p, D, m;
                        break p;
                    else
                        T := HeckeOperator(M,p);
                        Write(Dat,M,"T",T,p : Overwrite := Overwrite);
                    end if;
                end for;
                printf "  Hecke operators time: %o\n", Cputime(tyme);
            end if;
        end for;
    end for;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//                     QUATERNION DATABASE CONSTRUCTOR                      //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

intrinsic BuildQuaternionDatabase(
    Dat::DBUser,S::[RngIntElt] : LevelOne := false, Overwrite := false)
    {Build the database of quaternions for all levels (D,m) with D*m in S.}
    require Dat`DBIdentifier eq "Quaternion algebra" :
        "Argument 1 must be the database of quaternions.";
    RR := RealField(20);
    for N in S do
        printf "Level N = %o\n", N; 
        for L in LevelPairs(N) do
            D, m := Explode(L);
            if (m eq 1 or not LevelOne) then
                if not Overwrite and [D,m] in Dat then
                    printf "  Already computed (D,m) = (%o,%o)\n", D, m; 
                else
                    printf "  Computing (D,m) = (%o,%o)\n", D, m; 
                    tyme := Cputime();
                    G := QuaternionIdealClasses(D,m : Reduce);
                    Write(Dat,G : Overwrite := Overwrite);
                    print "  Class number =", ClassNumber(G);
                    printf "  Ideal classes time: %o\n", Cputime(tyme);
                end if;
            end if;
        end for;
    end for;
end intrinsic;

