////////////////////////////////////////////////////////////////////////
//                                                                    //
//                   Brandt Module Decompositions                     //
//                           David Kohel                              //
//                      Created September 2000                        //
//                                                                    //
////////////////////////////////////////////////////////////////////////

import "hecke_operators.m" : ExtendHecke;
import "brandt_ideals.m" : ExtendAdjacencyHecke;
import "brandt_modules.m" : NormGramsOrder;

forward HeckeSort, DimensionSort;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                          Decomposition                             //
//                                                                    //
////////////////////////////////////////////////////////////////////////

function Submodule(M,S)
    // {}
    X := sub< M`Module | S >;
    if X eq M`Module then return M; end if;
    N := New(ModBrdt);
    N`AmbientModule := AmbientModule(M);
    N`Module := X;
    N`IsFull := N`Module cmpeq AmbientModule(M)`Module;
    N`RamifiedPrimes := M`RamifiedPrimes;
    N`Conductor := M`Conductor;
    if not assigned M`FullLevelIndex then
        printf "  Assigning FullLevelIndex to parent in Submodule " *
            "of dimension %o and degree %o!\n", Dimension(M), Degree(M);
        M`FullLevelIndex := 1;
    end if;
    N`FullLevelIndex := M`FullLevelIndex;
    N`BaseRing := M`BaseRing;
    N`HeckePrecision := 0;
    N`HeckePrimes := [ Integers() | ];
    N`HeckeOperators := [ Mat | ]
        where Mat := MatrixAlgebra(N`BaseRing,Dimension(N`Module));
    // Set some decomposition data in case it doesn't get set later.
    if assigned M`DecompositionIdeal then
        N`DecompositionIdeal := M`DecompositionIdeal;
    else
        print "Warning: DecompositionIdeal not assigned.";
        M`DecompositionIdeal := {@ @};
        N`DecompositionIdeal := {@ @};
    end if;
    N`HeckeDegree := 0;
    return N;
end function;

intrinsic EisensteinSubspace(M::ModBrdt) -> ModBrdt
    {}
    // Should be modified for Brandt modules or non-Eichler orders
    // nonmaximal at primes dividing the discriminant.
    if M`IsFull then
        D := Discriminant(M);
        m := Conductor(M);
        if GCD(D,m) eq 1 then
            r := LCM(M`AutoNums);  
            eis := M`Module ! [ r div w : w in M`AutoNums ];
            E := Submodule(M,[eis]);
	    E`HeckeDegree := 1;
            E`IsIndecomposable := true;
        else  
            h := Dimension(M);
            if assigned M`NormGrams then
                GenSeq := [
                    Genus(LatticeWithGram(A)) : A in M`NormGrams[1..h] ];
            else
                NormGrams := [
                    1/Norm(I)*GramMatrix(I) : I in M`LeftIdeals ];
                GenSeq := [
                    Genus(LatticeWithGram(A)) : A in NormGrams ];
            end if;
            GenSet := [ GenSeq[1] ];
            for H in GenSeq do
                if &and [ G ne H : G in GenSet ] then
                    Append(~GenSet,H);
                end if;
            end for;   
            inds := [ [ i : i in [1..h] |
                G eq GenSeq[i] ] : G in GenSet ];
            B := [ M`Module | ];
            for I in inds do
                r := LCM([ M`AutoNums[i] : i in I ]);  
                eis := M`Module ! [ (i in I select r else 0)
                    div M`AutoNums[i] : i in [1..h] ];
                Append(~B,eis);
            end for;
            E := Submodule(M,B);
            E`IsIndecomposable := false;
        end if;  
        // Let's just put in some dummy data here:
        E`DecompositionIdeal := {@ @};
        return E;
    end if;
    return M meet EisensteinSubspace(AmbientModule(M));
end intrinsic;

intrinsic IsEisenstein(M::ModBrdt) -> BoolElt
    {Returns true if and only if M is contained in the Eisenstein 
    subspace of its abmient module.}
    return M subset EisensteinSubspace(AmbientModule(M));
end intrinsic;

intrinsic CuspidalSubspace(M::ModBrdt) -> ModBrdt
    {}
    // Should be modified for Brandt modules or non-Eichler orders
    // nonmaximal at primes dividing the discriminant.
    if M`IsFull then
        D := Discriminant(M);
        m := Conductor(M);
        if GCD(D,m) eq 1 then
            g := Dimension(M);
            B := [ X | X.i-X.(i+1) : i in [1..g-1] ] where X := M`Module;
            S := Submodule(M,B);
            if Dimension(S) eq 1 then
                S`HeckeDegree := 1;
                S`IsIndecomposable := true;
            end if;
        else   
            h := Dimension(M);
            if assigned M`NormGrams then
                GenSeq := [
                    Genus(LatticeWithGram(A)) : A in M`NormGrams[1..h] ];
            else
                NormGrams := [
                    1/Norm(I)*GramMatrix(I) : I in M`LeftIdeals ];
                GenSeq := [
                    Genus(LatticeWithGram(A)) : A in NormGrams ];
            end if;
            GenSet := [ GenSeq[1] ];
            for H in GenSeq do
                if &and [ G ne H : G in GenSet ] then
                    Append(~GenSet,H);
                end if;
            end for;   
            inds := [
                [ i : i in [1..h] | G eq GenSeq[i] ] : G in GenSet ];
            B := [ M`Module | ];
            for I in inds do
                B cat:= [ M`Module | 
                    Eltseq(M.I[i]-M.I[i+1]) : i in [1..#I-1] ];
            end for;
            S := Submodule(M,B);
            S`IsIndecomposable := false;
        end if;
        // Let's just put in some dummy data here:
        S`DecompositionIdeal := {@ @};
        return S;
    end if;
    return M meet CuspidalSubspace(AmbientModule(M));
end intrinsic;

intrinsic IsCuspidal(M::ModBrdt) -> BoolElt
    {Returns true if and only if M is contained in the cuspidal
    subspace of its abmient module.}
    return M subset CuspidalSubspace(AmbientModule(M));
end intrinsic;

intrinsic NewSubspaceDecomposition(M::ModBrdt,B::RngIntElt : 
    Anemic := false, Proof := false, 
    ThetaSeries := false, Sort := false ) -> SeqEnum
    {}
    return Decomposition(NewSubspace(M),B : 
	Anemic := Anemic, Proof := Proof, 
	ThetaSeries := ThetaSeries, Sort := Sort);
end intrinsic;
    
intrinsic Decomposition(M::ModBrdt,B::RngIntElt : 
    Anemic := false, Proof := false, 
    ThetaSeries := false, Sort := false ) -> SeqEnum
    {Decomposition of M with respect to the Hecke operators T_p 
    for p up to the bound B.}
    require Characteristic(BaseRing(M)) notin {2,3} :
        "The characteristic of the base ring of " *
        "argument 1 must be different from 2 and 3.";
    A := AmbientModule(M);
    if (not assigned A`NormGrams) and ThetaSeries then
        vprint Brandt : "  Computing gram matrices.";
        tyme := Cputime();
        A`NormGrams, A`AutoNums := NormGramsOrder(A`LeftIdeals);
        vprint Brandt : Cputime(tyme);
    end if;
    if Dimension(M) eq 0 then return []; end if;
    if not assigned M`FactorBases then   
        dcmp := [ EisensteinSubspace(M), CuspidalSubspace(M) ];
        dcmp := [ N : N in dcmp | Dimension(N) ne 0 ];
        M`DecompositionBound := 1; 
    else 
        dcmp := [ ];
        for i in [1..#M`FactorBases] do 
            N := Submodule(M,M`FactorBases[i]);
            if assigned M`FactorIdeals then
                N`DecompositionIdeal := M`FactorIdeals[i];
		N`IsIndecomposable :=
		    M`FactorIsIndecomposable[i];
            end if;
            Append(~dcmp, N);
        end for;
    end if;
    done := &and [ assigned N`IsIndecomposable 
        and N`IsIndecomposable : N in dcmp ];
    // First decompose with respect to known Atkin-Lehner operators.
    // We don't currently treat Atkin-Lehner operators for primes not
    // dividing the discriminant, so we restrict to those remaining.
    /* Begin Atkin-Lehner decomposition. */
    if not done and not Anemic then
        P := PolynomialRing(BaseRing(M)); X := P.1;
        prms := AtkinLehnerPrimes(M);
        vprint Brandt :
            "Decomposing with respect to Atkin-Lehner primes.";
        for p in prms do
            vprint Brandt : "  Prime =", p;
            tyme := Cputime();
            ndcmp := [ Parent(M) | ];   
            for N in dcmp do
                Q := BasisMatrix(N);
                W := AtkinLehnerOperator(N,p);
                for chi in {1,-1} do
                    V := Kernel(W-chi);
                    if Dimension(V) ne 0 then
                        S := [ M`Module | x*Q : x in Basis(V) ];
                        J := Submodule(N,S);
                        J`DecompositionIdeal :=
                            N`DecompositionIdeal join {@ <1,X-chi,p> @};
                        Append(~ndcmp,J);
                    end if; 
                end for;
            end for;
            dcmp := ndcmp;
            for i in [1..#dcmp] do
                if Dimension(dcmp[i]) eq 1 then
                    dcmp[i]`HeckeDegree := 1;
                    dcmp[i]`IsIndecomposable := true;
                end if; 
            end for;
            done := &and [ assigned N`IsIndecomposable 
                and N`IsIndecomposable : N in dcmp ];
            if done then break; end if;
        end for;
        if GetVerbose("Brandt") ge 2 then
            for N in dcmp do
                printf "    Dimension: %4o (%o)\n", Dimension(N),
                    assigned N`IsIndecomposable and N`IsIndecomposable 
                    select "complete" else "incomplete";
            end for;
            print "    Decomposition time:", Cputime(tyme);
        end if;
    end if;   
    /* End Atkin-Lehner decomposition. */
    vprint Brandt : "  Atkin-Lehner dimensions:", [ Dimension(N) : N in dcmp ];
    R := LevelIndices(M)[3];
    dcmp_tyme := Cputime();
    if not done and M`DecompositionBound lt B then
        vprint Brandt, 2 : "  Begin Hecke decomposition.";
        vprint Brandt, 2 :   
            "  Hecke operators known up to bound", M`HeckePrecision;
        vprint Brandt, 2 : "  To decompose up to new bound", B;
        p := NextPrime(M`DecompositionBound);
        while Level(M) mod p eq 0 and 
            (Anemic or R mod p eq 0 or (not assigned M`NormGrams)) do
            p := NextPrime(p);
        end while;
        i := Floor(Log(2,M`DecompositionBound));
        while p le B do
            // Check precomputed Hecke operators...
            if p gt Max(2^i,M`HeckePrecision) then 
                i +:= 1; 
                if i gt 1 and GetVerbose("Brandt") ge 2 then
                    for N in dcmp do
                        printf "Dimension: %4o (%o)\n", Dimension(N),
                            assigned N`IsIndecomposable
                            and N`IsIndecomposable 
                            select "complete" else "incomplete";
                    end for;
                    print "Decomposition time:", Cputime(tyme);
                end if;
                vprint Brandt : "  Current Hecke precision:", M`HeckePrecision;
                vprint Brandt : "  Extending Hecke up to new bound", Min(B,2^i);
                if assigned AmbientModule(M)`NormGrams then
                    tyme := Cputime();
                    ExtendHecke(M,Min(B,2^i));
                    vprint Brandt, 2 : "  Hecke theta time:", Cputime(tyme);
                end if;
            end if;
            vprint Brandt : "  Prime =", p;
            if not assigned AmbientModule(M)`NormGrams then
                tyme := Cputime();
                ExtendAdjacencyHecke(M,[p]);
                vprint Brandt, 2 : "  Hecke adjacency time:", Cputime(tyme);
            end if;
            M`DecompositionBound := p;
            // Compute individual operators...
            // T := HeckeOperator(AmbientModule(M),p);
            tyme := Cputime();
            dcmp := [ N : N in dcmp | 
                assigned N`IsIndecomposable and N`IsIndecomposable ] 
                cat &cat[ HeckeDecomposition(N,p : Proof := Proof) :
                N in dcmp | not
                (assigned N`IsIndecomposable and N`IsIndecomposable) ];
            vprintf Brandt, 2 :
                "  Hecke decomposition time for %o: %o\n", p, Cputime(tyme);
            if &and[ assigned N`IsIndecomposable and 
                N`IsIndecomposable : N in dcmp ] then 
                M`DecompositionBound := Infinity();
                break; 
            end if; 
            p := NextPrime(p);
            while (Anemic or not assigned M`NormGrams) 
                and Level(M) mod p eq 0 do
                p := NextPrime(p);
            end while;
        end while;
        if GetVerbose("Brandt") ge 2 then
            for N in dcmp do
                printf "    Dimension: %4o (%o)\n", Dimension(N),
                    assigned N`IsIndecomposable and N`IsIndecomposable 
                    select "complete" else "incomplete";
            end for;
        end if;
    end if;
    vprint Brandt : "  Decomposition time:", Cputime(dcmp_tyme);
    vprint Brandt : "  Dimensions:", [ Dimension(N) : N in dcmp ];
    DimensionSort(~dcmp);
    if Sort and Characteristic(BaseRing(M)) eq 0 then
        tyme := Cputime();
        vprint Brandt : "  Sorting...";
        dcmp := HeckeSort(dcmp : Anemic := Anemic, Bound := B);
	vprint Brandt : "  Sorting time:", Cputime(tyme);
    end if;
    M`FactorBases := [ [ Eltseq(x) : x in Basis(N) ] : N in dcmp ];
    M`FactorIdeals := [ N`DecompositionIdeal : N in dcmp ];
    M`FactorIsIndecomposable := [ 
	assigned N`IsIndecomposable select
	N`IsIndecomposable else false : N in dcmp ];
    if not M`IsFull then
        ; // Update decomposition of ambient module?
    end if;
    return dcmp;
end intrinsic;

intrinsic HeckeDecomposition(M::ModBrdt,p::RngIntElt : 
    Proof := true, Anemic := false) -> SeqEnum
    {Decomposition of M with respect to the Hecke operator T_p.}
    
    vprintf Brandt, 3:
        "  Computing HeckeOperator T_%o on space of dimension %o\n",
        p, Dimension(M);
    vprintf Brandt, 3: "  Max memory: %o\n", GetMaximumMemoryUsage();
    T := HeckeOperator(M,p);
    vprintf Brandt, 2: "  Determined HeckeOperator T_%o\n", p;
    vprintf Brandt, 3: "  Max memory: %o\n", GetMaximumMemoryUsage();
    if Dimension(M) eq 0 then return []; end if;
    if assigned M`IsIndecomposable and M`IsIndecomposable then 
        return [ M ]; 
    end if;
    if Dimension(M) eq 1 then 
	M`HeckeDegree := 1;
        M`IsIndecomposable := true; 
        return [ M ]; 
    end if;
    tyme := Cputime(); 
    vprintf Brandt, 3: "  Computing charpoly for p = %o.\n", p;
    vprintf Brandt, 3: "  Max memory: %o\n", GetMaximumMemoryUsage();
    if Proof then
        chi := CharacteristicPolynomial(T);
    else
        chi := CharacteristicPolynomial(T :
            Al := "Modular", Proof := false);
    end if;
    vprintf Brandt, 2:
        "  Determined charpoly for p = %o (%o sec)\n", p, Cputime(tyme);
    fac := Factorization(chi);
    vprint Brandt, 2: "  Factorization degrees:", [
	Sprint(Degree(f[1])) * (f[2] eq 1
	select "" else "^" * Sprint(f[2])) : f in fac ];
    if #fac eq 1 and fac[1][2] eq 1 then
        vprintf Brandt, 2:
            "  Factor of size %o is indecomposable.\n", Dimension(M);
        M`HeckeDegree := fac[1][2];
        M`DecompositionIdeal join:= {@ <p,fac[1][1],1> @};
	M`HeckeDegree := 1;
        M`IsIndecomposable := true;
	return [ M ];
    elif #fac eq 1 then
	if not assigned M`HeckeDegree then
	    M`HeckeDegree := fac[1][2];
	else
	    M`HeckeDegree := GCD(M`HeckeDegree,fac[1][2]);
	end if;
    end if;
    vprintf Brandt, 3: "  Max memory: %o\n", GetMaximumMemoryUsage();
    dcmp := [ Parent(M) | ];
    dims := [ Integers() | ];
    for f in fac do
        tyme := Cputime(); 
        dim := Dimension(M);
	deg := Degree(f[1]);
	rem := dim - &+dims;
        if false and deg gt rem and rem lt dim div 2 then
            vprintf Brandt, 2:
                "  Reducing from dimension %o to %o.\n", dim, rem;
            M := OrthogonalComplement(M,dcmp); 
            vprintf Brandt, 2:
		"  Orthogonal complement: %o secs\n", Cputime(tyme);
            T := HeckeOperator(M,p);
            vprintf Brandt, 2:
                "  Recomputed Hecke: %o secs\n", Cputime(tyme);
            dim := Dimension(M);
            dims := [ Integers() | ];
        end if;
        if deg lt dim then
            vprintf Brandt, 3:
                "  Evaluating polynomial of degree %o at T_%o\n", deg, p;
            fT := Evaluate(f[1],T);
            vprintf Brandt, 3:
                "  Max memory: %o\n", GetMaximumMemoryUsage();
            vprintf Brandt, 2: "  Computing kernel for degree %o", deg;
            vprintf Brandt, 2: f[2] eq 1 select " " else "^%o ", f[2];
            vprintf Brandt, 2: "polynomial on space of dimension %o\n", dim;
	    N := Kernel(fT,M);
            vprintf Brandt, 2: "  Determined kernel of dimension %o.\n", Dimension(N);
            vprintf Brandt, 3: "  Max memory: %o\n", GetMaximumMemoryUsage();
	    if f[2] eq 1 then
		M`HeckeDegree := 1;
		N`IsIndecomposable := true;
	    else
		if not assigned M`HeckeDegree then
		    N`HeckeDegree := f[2];
		else
		    N`HeckeDegree := GCD(N`HeckeDegree,f[2]);
		end if;
	    end if;
            N`DecompositionIdeal join:= {@ <p,f[1],1> @};
            Append(~dcmp,N);
            Append(~dims,Dimension(N));
        else
            vprintf Brandt, 2:
                "  Factor of size %o is indecomposable.\n", Dimension(M);
            M`DecompositionIdeal join:= {@ <p,f[1],1> @};
	    M`HeckeDegree := 1;
            M`IsIndecomposable := true;
            Append(~dcmp,M);
            return dcmp;
        end if;
    end for;
    return dcmp;
end intrinsic;

intrinsic AtkinLehnerDecomposition(M::ModBrdt,p::RngIntElt : Proof := true) -> SeqEnum
    {Decomposition of M with respect to the p-th Atkin-Lehner operator.}
    
    require Discriminant(M) mod p eq 0 : "Argument 2 must be a ramified prime.";
    if Dimension(M) eq 0 then return []; end if;
    if assigned M`IsIndecomposable and M`IsIndecomposable then 
        return [ M ]; 
    end if;
    if Dimension(M) eq 1 then 
	M`HeckeDegree := 1;
        M`IsIndecomposable := true; 
        return [ M ]; 
    end if;
    vprintf Brandt, 3:
        "  Computing AtkinLehnerOperator W_%o on space of dimension %o\n",
        p, Dimension(M);
    vprintf Brandt, 3: "  Max memory: %o\n", GetMaximumMemoryUsage();
    T := AtkinLehnerOperator(M,p);
    vprintf Brandt, 2: "  Determined AtkinLehnerOperator W_%o\n", p;
    vprintf Brandt, 3: "  Max memory: %o\n", GetMaximumMemoryUsage();
    tyme := Cputime(); 
    vprintf Brandt, 3: "  Computing charpoly for p = %o.\n", p;
    vprintf Brandt, 3: "  Max memory: %o\n", GetMaximumMemoryUsage();
    if Proof then
        chi := CharacteristicPolynomial(T);
    else
        chi := CharacteristicPolynomial(T : Al := "Modular", Proof := false);
    end if;
    vprintf Brandt, 2:
        "  Determined charpoly for p = %o (%o sec)\n", p, Cputime(tyme);
    fac := Factorization(chi);
    vprint Brandt, 2: "  Factorization degrees:", [
	Sprint(Degree(f[1])) * (f[2] eq 1
	select "" else "^" * Sprint(f[2])) : f in fac ];
    if #fac eq 1 and fac[1][2] eq 1 then
        vprintf Brandt, 2:
            "  Factor of size %o is indecomposable.\n", Dimension(M);
        M`HeckeDegree := fac[1][2];
        M`DecompositionIdeal join:= {@ <p,fac[1][1],1> @};
	M`HeckeDegree := 1;
        M`IsIndecomposable := true;
	return [ M ];
    elif #fac eq 1 then
	if not assigned M`HeckeDegree then
	    M`HeckeDegree := fac[1][2];
	else
	    M`HeckeDegree := GCD(M`HeckeDegree,fac[1][2]);
	end if;
    end if;
    vprintf Brandt, 3: "  Max memory: %o\n", GetMaximumMemoryUsage();
    dcmp := [ Parent(M) | ];
    dims := [ Integers() | ];
    for f in fac do
        tyme := Cputime(); 
        dim := Dimension(M);
	deg := Degree(f[1]);
	rem := dim - &+dims;
        if false and deg gt rem and rem lt dim div 2 then
            vprintf Brandt, 2:
                "  Reducing from dimension %o to %o.\n", dim, rem;
            M := OrthogonalComplement(M,dcmp); 
            vprintf Brandt, 2:
		"  Orthogonal complement: %o secs\n", Cputime(tyme);
            T := AtkinLehnerOperator(M,p);
            vprintf Brandt, 2:
                "  Recomputed Atkin-Lehner: %o secs\n", Cputime(tyme);
            dim := Dimension(M);
            dims := [ Integers() | ];
        end if;
        if deg lt dim then
            vprintf Brandt, 3:
                "  Evaluating polynomial of degree %o at T_%o\n", deg, p;
            fT := Evaluate(f[1],T);
            vprintf Brandt, 3:
                "  Max memory: %o\n", GetMaximumMemoryUsage();
            vprintf Brandt, 2: "  Computing kernel for degree %o", deg;
            vprintf Brandt, 2: f[2] eq 1 select " " else "^%o ", f[2];
            vprintf Brandt, 2: "polynomial on space of dimension %o\n", dim;
	    N := Kernel(fT,M);
            vprintf Brandt, 2: "  Determined kernel of dimension %o.\n", Dimension(N);
            vprintf Brandt, 3: "  Max memory: %o\n", GetMaximumMemoryUsage();
	    if f[2] eq 1 then
		M`HeckeDegree := 1;
		N`IsIndecomposable := true;
	    else
		if not assigned M`HeckeDegree then
		    N`HeckeDegree := f[2];
		else
		    N`HeckeDegree := GCD(N`HeckeDegree,f[2]);
		end if;
	    end if;
            N`DecompositionIdeal join:= {@ <p,f[1],1> @};
            Append(~dcmp,N);
            Append(~dims,Dimension(N));
        else
            vprintf Brandt, 2:
                "  Factor of size %o is indecomposable.\n", Dimension(M);
            M`DecompositionIdeal join:= {@ <p,f[1],1> @};
	    M`HeckeDegree := 1;
            M`IsIndecomposable := true;
            Append(~dcmp,M);
            return dcmp;
        end if;
    end for;
    return dcmp;
end intrinsic;

intrinsic IsIndecomposable(S::ModBrdt,B::RngIntElt) -> BoolElt
    {True if and only if S is indecomposable under the action of 
    the Hecke operators up to the bound B.}
    
    if assigned S`IsIndecomposable then
        return S`IsIndecomposable;
    end if;   
    if Dimension(S) eq 1 then
        S`HeckeDegree := 1;
        S`IsIndecomposable := true;
        return S`IsIndecomposable;
    end if;
    D := Discriminant(S);
    N := Level(S);
    for p in AtkinLehnerPrimes(S) do
        vprint Brandt, 2 :
            "  Considering Atkin-Lehner decomposition at", p;
        W := AtkinLehnerOperator(S,p);
        f := CharacteristicPolynomial(W :
            Al := "Modular", Proof := false);
        fac := Factorization(f);
        if #fac gt 1 then
            S`IsIndecomposable := false;
            return S`IsIndecomposable;
        end if; 
    end for;
    p := 2;
    while N mod p eq 0 do 
        p := NextPrime(p); 
    end while; 
    while p le B do 
        vprint Brandt, 2 : "  Considering decomposition at", p;
        Tp := HeckeOperator(S,p);
        f := CharacteristicPolynomial(Tp :
            Al := "Modular", Proof := false);
        fac := Factorization(f);
        if #fac eq 1 and fac[1][2] eq 1 then
            S`HeckeDegree := 1;
            S`IsIndecomposable := true;
            return S`IsIndecomposable;
	elif #fac eq 1 then
	    if not assigned S`HeckeDegree then
		S`HeckeDegree := fac[1][2];
	    else
		S`HeckeDegree := GCD(S`HeckeDegree,fac[1][2]);
	    end if;
        elif #fac gt 1 then
            S`IsIndecomposable := false;
            return S`IsIndecomposable;
        end if;
        p := NextPrime(p);
    end while;
    return false;   
end intrinsic;

function MergeSort(C,D,Anemic,Bound)
    i := 1; // index for C
    j := 1; // index for D
    while true do
        if i gt #C then
            break;
        elif j gt #D then
            D cat:= C[i..#C];
            break;
        elif 'lt'(C[i],D[j] : Anemic := Anemic, Bound := Bound) then
            Insert(~D,j,C[i]);  
            i +:= 1;
        else 
            j +:= 1;
        end if;
    end while;
    return D;
end function;

procedure DimensionSort(~D)
    n := #D;
    dims := [ Dimension(N) : N in D ];
    pi := SymmetricGroup(n);
    Sort(~dims,~pi);
    D := [ D[i^pi] : i in [1..n] ];
end procedure;

function HeckeSort(D : Anemic := false, Bound := 64)
    // Sort the sequence of Brandt modules according to the 'lt' operator.
    r := #D;
    if r eq 2 then
        vprintf Brandt, 2 :
            "  Sorting sequence of length %o (dimensions: %o, %o).\n",
            r, Dimension(D[1]), Dimension(D[2]);  
        if 'lt'(D[2],D[1] : Anemic := Anemic, Bound := Bound) then
            Reverse(~D);
        end if; 
    elif r gt 2 then
        vprintf Brandt, 2 : "  Sorting sequence of length %o.\n", r;
        s := r div 2;
        D := MergeSort(
            HeckeSort(D[1..s] : Anemic := Anemic),
            HeckeSort(D[s+1..r] : Anemic := Anemic), Anemic, Bound);
    end if;
    return D;
end function;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                         Linear Algebra                             //
//                                                                    //
////////////////////////////////////////////////////////////////////////

intrinsic BasisMatrix(M::ModBrdt) -> ModMatRngElt
    {The matrix whose rows are the basis elements of M.}
    return BasisMatrix(M`Module);
end intrinsic;

intrinsic AtkinLehnerSubspace(M::ModBrdt,q::RngIntElt,eps::RngIntElt) -> ModBrdt
    {The subspace of M on which the Atkin-Lehner operator acts as eps (= +/-1).}
    D := Discriminant(M);
    N := Level(M);
    val, p, m := IsPrimePower(q);
    require val : "Argument 2 must be a prime power.";
    r := Valuation(N,p);
    if m eq 1 and r gt 1 then q := p^r; end if;
    require N mod q eq 0 and GCD(N div q,q) eq 1 :  
        "Argument 2 must be an exact divisor of the level of argument 1.";
    require eps in {1,-1}: "Argument 3 must be in {1,-1}.";
    W := AtkinLehnerOperator(M,q);
    return Kernel(W-eps,M);
end intrinsic;

intrinsic AtkinLehnerEigenvalue(M::ModBrdt,q::RngIntElt) -> RngElt
    {The trace of the qth Atkin-Lehner opertor on the 
    indecomposable Brandt module S.}
    
    D := Discriminant(M);
    N := Level(M);
    val, p := IsPrimePower(q);
    require val : "Argument 2 must be a prime power.";
    require N mod q eq 0 and GCD(N div q,q) eq 1 :  
        "Argument 2 must be an exact divisor of the level of argument 1.";
    W := AtkinLehnerOperator(M,q);
    if W eq 1 then return 1; elif W eq -1 then return -1; end if;
    require false :
        "Argument 1 is not indecomposable under Atkin-Lehner.";
end intrinsic;

function MatrixKernel(T,V)
    return Kernel(T) meet V;
end function;

function MatrixKernelOnBrandt(T,M)
    A := AmbientModule(M);
    if Dimension(M) eq Nrows(T) then
	U := M`Module; 
        V := Kernel(T);
        C := BasisMatrix(V)*BasisMatrix(U);
        return Submodule(M,[ C[i] : i in [1..Dimension(V)] ]);
    elif Degree(M) eq Nrows(T) then
	U := A`Module; 
	V := sub< U | [ U!Eltseq(v) : v in Basis(Kernel(T)) ] >;
        return Submodule(M,Basis(V meet M`Module));
    end if;
end function;

intrinsic Kernel(T::AlgMatElt,M::ModBrdt) -> ModBrdt
    {}
    require BaseRing(M) eq BaseRing(Parent(T)) : 
	"Arguments have incompatible base rings.";
    require Dimension(M) eq Nrows(T) or Degree(M) eq Nrows(T) : 
	"Arguments have incompatible degrees.";
    return MatrixKernelOnBrandt(T,M);
end intrinsic;

intrinsic Kernel(T::ModMatRngElt,M::ModBrdt) -> ModBrdt
    {}
    require BaseRing(M) eq BaseRing(Parent(T)) : 
	"Arguments have incompatible base rings.";
    require Dimension(M) eq Nrows(T) or Degree(M) eq Nrows(T) : 
	"Arguments have incompatible degrees.";
    return MatrixKernelOnBrandt(T,M);
end intrinsic;

intrinsic 'meet'(M::ModBrdt,N::ModBrdt) -> ModBrdt
    {}
    if M eq N then return M; end if; 
    A := AmbientModule(M);
    require AmbientModule(N) eq A : "Modules have no covering module.";
    if M`IsFull then
        return N;
    elif N`IsFull then 
        return M;
    end if; 
    L := Submodule(A,Basis(M`Module meet N`Module));
    L`DecompositionIdeal := 
        M`DecompositionIdeal join N`DecompositionIdeal;
    return L;
end intrinsic;

intrinsic 'subset'(M::ModBrdt,N::ModBrdt) -> BoolElt
    {}
    if M eq N then return true; end if; 
    A := AmbientModule(M);
    require AmbientModule(N) eq A : "Modules have no covering module.";
    return M`Module subset N`Module;
end intrinsic;

intrinsic CharacteristicPolynomial(
    T::AlgMatElt,M::ModBrdt : Proof := true) -> RngUPolElt
    {The characteristic polynomial of T on M.}
    require Degree(Parent(T)) eq Degree(M) : 
        "Arguments have incompatible dimensions.";
    require BaseRing(Parent(T)) cmpeq BaseRing(M) : 
        "Arguments have incompatible base rings.";
    return CharacteristicPolynomial(T,M`Module : Proof := Proof);
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//            Ordering of Indecomposable Brandt Submodules            //
//                                                                    //
////////////////////////////////////////////////////////////////////////

intrinsic 'lt'(R::ModBrdt,S::ModBrdt : Anemic := false, Bound := 64)
    -> BoolElt
    {Comparison operator extending that of Cremona.}
    /* 
    (1) R < S if dim(R) < dim(S);
    (2) R < S if IsEisenstein(R) and IsCuspidal(S)
    (3) When the weight is two and the character is trivial:
        order by Wq eigenvalues, starting with *smallest* p|N and 
        with "+" being less than "-";
    (4) Order by abs(trace(a_p^i)), p not dividing the level, and 
        i = 1,...,g = dim(R) = dim(S), with the positive one being 
        smaller in the the event of equality,
    */
    M := AmbientModule(R);
    require AmbientModule(S) eq M : 
        "Arguments must be components of the same Brandt module.";
    /*
    require IsIndecomposable(R) and IsIndecomposable(S) :
       "Arguments must be indecomposable Brandt modules.";
    */
    if R eq S then return false; end if;
    g := Dimension(S);
    if Dimension(R) lt g then 
        return true; 
    elif Dimension(R) gt g then 
        return false; 
    end if;
    if IsEisenstein(R) and IsCuspidal(S) then
        return true;
    elif IsEisenstein(S) and IsCuspidal(R) then
        return false;
    end if;
    N := Level(S);
    D := Discriminant(S);
    atkin_lehner := AtkinLehnerPrimes(M);
    if not Anemic then
        for p in atkin_lehner do
            q := p^Valuation(N,p);
            eR := AtkinLehnerEigenvalue(R,q); 
            eS := AtkinLehnerEigenvalue(S,q); 
            if eR lt eS then return true; end if;
            if eR gt eS then return false; end if;
        end for;
    end if;
    p := 2;
    while p le Bound do
        Tp := HeckeOperator(M,p);
        fR := CharacteristicPolynomial(Tp,R : Proof := false); 
        fS := CharacteristicPolynomial(Tp,S : Proof := false); 
        if p notin atkin_lehner and fR ne fS then
            for i in [1..g] do
                aS := HeckeTrace(S,p^i : Proof := false);
                aR := HeckeTrace(R,p^i : Proof := false);
                if Abs(aR) lt Abs(aS) then
                    return true; 
                elif Abs(aR) gt Abs(aS) then
                    return false; 
                elif aR gt aS then
                    return true; 
                elif aR lt aS then
                    return false; 
                end if;
            end for; 
        end if;   
        p := NextPrime(p);
    end while;
    return false;
end intrinsic;

intrinsic 'gt'(N::ModBrdt,M::ModBrdt : Anemic := false, Bound := 64)
    -> BoolElt
    {}
    return 'lt'(M,N : Anemic := Anemic, Bound := Bound);
end intrinsic;

