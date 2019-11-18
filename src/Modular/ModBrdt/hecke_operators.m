////////////////////////////////////////////////////////////////////////
//                                                                    //
//                  Hecke Operators for Brandt Modules                //
//                            David Kohel                             //
//                                                                    //
////////////////////////////////////////////////////////////////////////

import "brandt_ideals.m" : ExtendAdjacencyHecke;
import "brandt_modules.m" : NormGramsOrder;

forward ExtendHecke;

function LocalDualGram(L,q)
    Mat := MatrixAlgebra(ResidueClassRing(q), Rank(L));
    K := Kernel(Mat!GramMatrix(L));
    D := sub< L | [ L!v : v in Basis(K) ] cat [ q*v : v in Basis(L) ]>;
    return MinkowskiGramReduction(1/q*GramMatrix(D) : Canonical);
end function;

function brandt_index(i,j,h)
    if j lt i then
        return Binomial(h+1,2) - Binomial(h-j+2,2) + Abs(i-j) + 1;
    end if;
    return Binomial(h+1,2) - Binomial(h-i+2,2) + Abs(i-j) + 1;
end function;

function brandt_coordinates(k,h)
    i := 1;
    r := 1; 
    while k gt (r+h-i) do
        i +:= 1;
        r := Binomial(h+1,2) - Binomial(h-i+2,2) + 1;
    end while;
    j := i + k - r;
    return [i,j];
end function;

function HeckeMatrix(A,S,W)
    n := Degree(A);
    M := Zero(A);
    k := 1;
    for i in [1..n] do 
        M[i,i] := ExactQuotient(S[k],W[i]);
        k +:= 1;
        for j in [i+1..n] do 
            M[i,j] := ExactQuotient(S[k],W[j]);
            M[j,i] := ExactQuotient(S[k],W[i]);
            k +:= 1;
        end for;
    end for;
    return M;
end function;

procedure ExtendHecke(M,prec)
    if prec le M`HeckePrecision then return; end if;
    if M`IsFull then
        h := Dimension(M);
        PS := Universe(M`ThetaSeries);
        k := 1; 
	if not assigned M`NormGrams then
	    M`NormGrams, M`AutoNums := NormGramsOrder(M`LeftIdeals);
	end if;
	for i in [1..h] do
            M`ThetaSeries[k] := PS![
                Coefficient(t,2*k) : k in [0..prec] ] where t is
                ThetaSeries(LatticeWithGram(M`NormGrams[k]),2*prec);
            k +:= 1;
            for j in [i+1..h] do
                M`ThetaSeries[k] := PS![
                    Coefficient(t,2*k) : k in [0..prec] ] where t is
                    ThetaSeries(LatticeWithGram(M`NormGrams[k]),2*prec);
                k +:= 1;
            end for;
        end for;
        M`HeckePrimes := [ t : t in [2..prec] | IsPrime(t) ];
        M`HeckeOperators := [ 
            HeckeMatrix(MatrixAlgebra(BaseRing(M),h),
            [ Coefficient(f,t) : f in M`ThetaSeries ], M`AutoNums)
            : t in M`HeckePrimes ];
        M`HeckePrecision := prec;
    else 
        X := AmbientModule(M); 
        ExtendHecke(X,prec);
        // The submodules get created and destroyed with frequency.
        // Only compute Hecke operators from the ambient module up
        // to the needed precision. 
        g := Dimension(M);
        M`HeckePrimes := [ p : p in X`HeckePrimes | p le prec ];
        U := M`Module; 
        B := BasisMatrix(M);
	for k in [1..#M`HeckePrimes] do
	    T := X`HeckeOperators[k];
	    for i in [1..g] do
		v := B[i]*T;
		if not IsCoercible(U,v) then
		    print "T:"; T;
		    print "p:", X`HeckePrimes[k];
		    print "B:"; B;
		    print "Error:"; v;
		end if;
	    end for;
	end for;
	if g eq 0 then
	    M`HeckeOperators := [
		Matrix(0,[BaseRing(M)|]) : p in M`HeckePrimes ];
	else
	    M`HeckeOperators := [
		Matrix([ Coordinates(U,U!(B[i]*T)) : i in [1..g] ])
		: T in X`HeckeOperators[1..#M`HeckePrimes] ];
	end if;
        M`HeckePrecision := prec;
    end if;
end procedure;

procedure AtkinLehnerSetup(M)
    h := Degree(M);
    if assigned M`NormGrams then
        OrderGrams := [ M`NormGrams[k] where 
            k := brandt_index(i,i,h) : i in [1..h] ];
    else 
	OrderGrams := [
	    ReducedGramMatrix(RightOrder(I)) : I in M`LeftIdeals ];
    end if;
    GramSet := SequenceToSet(OrderGrams);
    prms := AtkinLehnerPrimes(M);
    M`AtkinLehnerPermutations := [ [ i : i in [1..h] ] : p in prms ];
    for A in GramSet do
        L := LatticeWithGram(A);
        I := [ j : j in [1..h] | OrderGrams[j] eq A ];
        for t in [1..#prms] do
	    p := prms[t];
            q := p^Valuation(Level(M),p); 
            B := LocalDualGram(L,q);
            for i in I do
		if assigned M`NormGrams then
		    K := [ brandt_index(i,j,h) : j in I ]; 
                    Ip := [ k : k in K | M`NormGrams[k] eq B ];
		    error if #Ip eq 0,
			"Reduced ideal class not found:\n" *
			"Corrupt Brandt module for level " *
			Sprint(LevelIndices(M)) * "?";
		    error if #Ip gt 1,
			"Multiple [" * Sprint(#Ip) *
			"] reduced ideal classes found:\n" *
			"Corrupt Brandt module for level " *
			Sprint(LevelIndices(M)) * "?";
                else
                    K := I;
                    Ip := [ j : j in I | IsIsometric(
                        LatticeWithGram( 1/(Norm(I)*Norm(J)) *
                        GramMatrix(Conjugate(J)*I)),LatticeWithGram(B))
                        where I := M`LeftIdeals[i]
                        where J := M`LeftIdeals[j] ]; 
                end if;
		assert #Ip eq 1;
                M`AtkinLehnerPermutations[t][i] := I[Index(K,Ip[1])];
            end for; 
        end for;  
    end for;
end procedure;

intrinsic AtkinLehnerOperator(M::ModBrdt,q::RngIntElt) -> AlgMatElt
    {} 
    A := AmbientModule(M);
    N := Level(A);
    D := Discriminant(A);
    require GCD(N div GCD(N,q),q) eq 1 or (N mod q eq 0 and IsPrime(q)) :
	"Argument 2 must be an exact divisor of the level of argument 1.";
    prms := PrimeDivisors(q);
    require &and[ p in AtkinLehnerPrimes(M) : p in prms ]:  
	"Atkin-Lehner operator nonexistent or noncomputable.";
    Wq := MatrixAlgebra(BaseRing(M),Dimension(M))!1;
    if #prms eq 0 then return Wq; end if;
    if not assigned A`AtkinLehnerPermutations then
	AtkinLehnerSetup(A);
    end if;
    h := Dimension(A);
    n := Dimension(M);
    U := M`Module;
    for p in prms do
	Wp := MatrixAlgebra(BaseRing(A),h)!0;
	pi := A`AtkinLehnerPermutations[k]
	    where k := Index(A`AtkinLehnerPrimes,p);
	eps := D mod p eq 0 select -1 else 1;
	for i in [1..h] do
	    Wp[i,pi[i]] := eps;
	    Wp[pi[i],i] := eps;
	end for;
	// Reconstruct Atkin-Lehner matrix for M.
	C := BasisMatrix(U)*Wp;
	Wq *:= Matrix(n,&cat[ Coordinates(U,U!C[i]) : i in [1..n]]);
    end for;
    return Wq;
end intrinsic;

intrinsic CharacterOperator(M::ModBrdt,p::RngIntElt) -> AlgMatElt
    {} 
    A := AmbientModule(M);
    N, m, c := Explode(LevelIndices(A));
    D := N div (m*c^3);
    require IsPrime(p) : "Argument 2 must be a prime.";
    require D mod p eq 0 and Valuation(m,p) eq 1 :  
	"Argument 2 must be a divisor of the discriminant " *
	"and an exact divisor of the conductor."; 
    require c eq 1 : "Argument 1 must have full level index 1.";
    require assigned A`LeftIdeals : "LeftIdeals are not assigned.";
    ZZ := Integers();
    if not assigned A`CharacterPrimes then
        A`CharacterPrimes :=
            [ p : p in A`RamifiedPrimes | Conductor(A) mod p eq 0 ];
        A`CharacterPermutations := [ [ZZ|] : p in A`CharacterPrimes ];
    end if;
    n := Dimension(A);
    i := Index(A`CharacterPrimes,p);
    if #A`CharacterPermutations[i] eq 0 then
        idls := A`LeftIdeals;
        R := LeftOrder(idls[1]);
        K := QuaternionAlgebra(R);
	O := MaximalSuperOrder(R);
	m := Conductor(A) div p; assert m mod p ne 0;
	S := sub< O | [ m*x : x in Basis(O) ] cat [ O!x : x in Basis(R) ] >;
	i := 2;
	repeat
	    u := K!ReducedBasis(S)[i];
	    f := MinimalPolynomial(u);
	    i +:= 1;
	until ZZ!Discriminant(f) mod p ne 0;
        assert KroneckerSymbol(ZZ!Discriminant(f),p) eq -1;
        F := ext< F | PolynomialRing(F)!f > where F := FiniteField(p);
	e := PrimitiveElement(F);
	c := [ CRT([x,1],[p,m]) : x in ChangeUniverse(Eltseq(e),ZZ) ];
        u := c[1] + c[2]*u;
	s := CRT([1,0],[p,m]);
        jdls := [ lideal< R | [ p*s*u*x : x in B ] cat [ p^2*x : x in B ]
            where B := Basis(I) > : I in idls ];
        indices := [ [ j : j in [1..n] |
            IsLeftIsomorphic(idls[j],J) ][1] : J in jdls ];
        char_perms := A`CharacterPermutations;
        char_perms[i] := indices;
        A`CharacterPermutations := char_perms;
    end if;
    g := Sym(n)!(A`CharacterPermutations[i]);
    W := PermutationMatrix(BaseRing(M),g);
    m := Dimension(M);
    U := M`Module;
    C := BasisMatrix(U)*W;
    return Matrix(m,&cat[ Coordinates(U,U!C[i]) : i in [1..m] ]);
end intrinsic;

function HeckeRecursion(ap,p,r,k,e)
    if r eq 0 then
        return Parent(ap)!1;
    elif r eq 1 then
        return ap;
    else 
        return ap * HeckeRecursion(ap,p,r-1,k,e) - 
            e * p^(k-1) * HeckeRecursion(ap,p,r-2,k,e);
    end if;
end function;

intrinsic HeckeTrace(M::ModBrdt,q::RngIntElt : Proof := true) -> RngElt
    {The trace of the q-th Hecke operator on M, for prime power q.}
    val, p, r := IsPrimePower(q); 
    require val : "Argument 2 must be a prime power.";
    g := Dimension(M);
    if q eq 1 then
        return BaseRing(M)!g;
    elif IsPrime(q : Proof := false) then
        return Trace(HeckeOperator(M,q));
    end if;
    Tp := HeckeOperator(M,p);
    fp := CharacteristicPolynomial(Tp :
        Al := "Modular", Proof := Proof);
    R<ap> := quo< Parent(fp) | fp >;
    // k := Weight(M);
    k := 2; 
    // e := Evaluate(DirichletCharacter(M),p);
    e := 1; 
    return Trace(HeckeRecursion(ap,p,r,k,e));
end intrinsic;

intrinsic HeckeOperator(M::ModBrdt,n::RngIntElt) -> AlgMatElt
    {} 
    require n ge 1 : "Argument 2 must be positive.";
    if n eq 1 then
        return Identity(Universe(M`HeckeOperators));
    elif IsPrime(n : Proof := false) then
        if n in M`HeckePrimes then
            return M`HeckeOperators[Index(M`HeckePrimes,n)];
        end if;
    elif IsPrimePower(n) then
        // k := Weight(M);
        // e := Evaluate(DirichletCharacter(M),p);
        k := 2; 
        e := 1; 
        _, p, r := IsPrimePower(n); 
        // Testing purposes: what happens at theses primes?
        if Level(M) mod p eq 0 then
            // By design, only computes up to Hecke operators 
            // previous largest prime
            ExtendHecke(M,n);
            B := BasisMatrix(M);
            A := AmbientModule(M);
            T := HeckeMatrix(MatrixAlgebra(BaseRing(A),Degree(A)),
                [ Coefficient(f,n) : f in A`ThetaSeries ], A`AutoNums);
            U := M`Module; 
            g := Dimension(M);
            return Matrix([ Coordinates(U,U!(B[i]*T)) : i in [1..g] ]);
        end if;
        return HeckeOperator(M,p) * HeckeOperator(M,p^(r-1))
            - e * p^(k-1) * HeckeOperator(M,p^(r-2));
    end if;
    fac := Factorization(n);
    m := fac[#fac][1];
    if m notin M`HeckePrimes then 
        if assigned AmbientModule(M)`NormGrams then
            ExtendHecke(M,m);
	elif GCD(Conductor(M),n) ne 1 then
	    A := AmbientModule(M);
	    A`NormGrams, A`AutoNums := NormGramsOrder(A`LeftIdeals);
	    ExtendHecke(M,m);
	else
            ExtendAdjacencyHecke(M,[ f[1] : f in fac ]);
        end if;
    end if;
    return &*[ HeckeOperator(M,f[1]^f[2]) : f in fac ];
end intrinsic;

