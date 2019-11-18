//////////////////////////////////////////////////////////////////////////////
//                                                                          // 
//                       QUATERNION IDEALS                                  //
//  Copyright (C) 2000 David Kohel <kohel@maths.usyd.edu>                   //
//                                                                          //
//  Distributed under the terms of the GNU General Public License (GPL)     //
//                  http://www.gnu.org/licenses/                            //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

forward CompareOrders, CompareLeftIdeals, CompareGram; 
forward LeftIsogenousIdeal, LeftIsogenousIdeals, SplitIsogenousIdeals;

//////////////////////////////////////////////////////////////////////////////
//                        Auxiliary Random Functions                        //
//////////////////////////////////////////////////////////////////////////////

function RandomElement(A,S)
    return A![ Random(S) : i in [1..4] ];
end function;

//////////////////////////////////////////////////////////////////////////////
//                           Two Sided Ideals                               //
//////////////////////////////////////////////////////////////////////////////

intrinsic TwoSidedIdealClasses(A::AlgQuatOrd[RngInt]) -> SeqEnum
    {A sequence of representatives for the 2-sided ideal classes of
    the order A.}
    D := ideal< A | [ x*y - y*x : x, y in Basis(A) ] >;
    pows := [ p[1]^p[2] : p in Factorization(Discriminant(A)) ];
    gens := [ ideal< A | [ A!q ] cat Basis(D) > : q in pows ];
    V := VectorSpace(GF(2),#pows);
    reprs := [ ]; 
    grams := { MatrixAlgebra(Integers(),4) | };
    for v in V do
        I := ideal< A | 1 >;
        for i in [1..#pows] do 
            if v[i] ne 0 then I *:= gens[i]; end if;
        end for;
        M := (1/Norm(I))*ReducedGramMatrix(I);
        if M notin grams then
            if not IsIdentical(Order(I), A) then
                I := ideal< A | Basis(I) >;
            end if;
            Append(~reprs,I);
            Include(~grams,M);
        end if;
    end for;
    return reprs;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//                            Isogeny Graphs                                //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

intrinsic ReducedLeftIdealClass(I::AlgQuatOrdIdl[RngInt]) -> AlgQuatOrdIdl
    {A reduced left ideal class (of minimal norm).}
    NrmI := Norm(I);
    O := LeftOrder(I); 
    B := ReducedBasis(I);
    if Norm(B[1]) lt NrmI^2 then
        y := Conjugate(O!B[1]);
        I := lideal< O | [ (x*y)/NrmI : x in B ] >;
    end if;
    return I;
end intrinsic;

intrinsic ReducedRightIdealClass(I::AlgQuatOrdIdl[RngInt]) -> AlgQuatOrdIdl
    {A reduced right ideal class (of minimal norm).}
    NrmI := Norm(I);
    O := RightOrder(I); 
    B := ReducedBasis(I);
    if Norm(B[1]) lt NrmI^2 then
        y := Conjugate(O!B[1]);
        I := lideal< O | [ (y*x)/NrmI : x in B ] >;
    end if;
    return I;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//                            Isogeny Graphs                                //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

intrinsic RightIdealClasses(A::AlgQuatOrd[RngInt]) -> SeqEnum
    {Representatives for the right ideals classes of A.}
    require Type(BaseRing(A)) eq RngInt:  
        "Ideals computed only for orders over the integers";
    require IsDefinite(QuaternionAlgebra(A)) : 
        "Ideals computed only for orders in definite algebras";
    return [ Conjugate(I) : I in LeftIdealClasses(A) ];
end intrinsic;

function CharacterVector(prms,p)
    return Vector([ GF(2) | 
        (1 - KroneckerSymbol(p,q)) div 2 : q in prms ]);
end function;

intrinsic LeftIdealClasses(A::AlgQuatOrd[RngInt] :
    IsogenyPrime := 1, Reduce := false) -> SeqEnum
    {Representatives for the left ideals classes of A.}
    /*
    Consider additional parameters: 
      IsogenyPrimeSequence, IdealSequence, GeneraSequences, etc.
    */
    require Type(BaseRing(A)) eq RngInt:  
        "Argument must be an order in a rational quaternion algebra.";
    require IsDefinite(QuaternionAlgebra(A)) : 
        "Argument must be an order in a definite algebras";
    
    if assigned A`LeftIdealBases then
        return [ lideal< A | [ A!Eltseq(M[i]) : i in [1..4] ] >
            where M := UpperTriangularMatrix(B) : B in A`LeftIdealBases ];
    end if;
    
    K := QuaternionAlgebra(A);
    N := Discriminant(A);
    Q := RamifiedPrimes(K);
    CharacterPrimes := [ q : q in Q | q ne 2 and Valuation(N,q) gt 1 ];
    
    if IsogenyPrime ne 1 then
        require IsPrime(IsogenyPrime) : 
            "IsogenyPrime parameter must be prime.";
        require N mod IsogenyPrime ne 0 :
            "IsogenyPrime parameter must be coprime to " * 
            "the discriminant of the argument.";
        p := IsogenyPrime; 
        CharacterPrimes := [ Integers() | ];
    else
        p := 2; 
        while N mod p eq 0 do 
            p := NextPrime(p); 
        end while;
    end if;
    
    if #CharacterPrimes eq 0 then
        Idls := LeftIsogenousIdeals(lideal< A | 1 >,p);
    else
        /*
        Currently the SplitIsogeny function computes the principal 
        left ideal class (that of A) and one coset, that generated 
        by odd p-power isogenies.  Therefore we have to construct 
        enough primes to represent all classes, not just to generate
        all classes.  
        Note that this incurs a significant overhead, not just in 
        the number of primes, but that each time the principal class 
        is recomputed. 
        A much more efficient algorithm would be to compute only the
        principal class and then to construct the rest by multiplying 
        on the left by the 2-sided ideals for A.
        This algorithm suffers two problems (1) (ALGORITHMIC) a 
        verifiable algorithm for the 2-sided ideal classes, and 
        (2) (THEORETICAL) some accounting for the fact that due to 
        extra automorphisms the idelic generators for 2-sided ideals 
        may have different kernels on different kernels under different 
        left and right orders.  Provided that the primes act by 
        characters which change the genus, then the action of the 
        elementary 2-abelian group is free, and (2) is not an 
        obstruction.  
        */  
        V := VectorSpace(GF(2),#CharacterPrimes);
        CharacterClasses :=
            sub< V | CharacterVector(CharacterPrimes,p) >;
        IsogenyPrimes := [ Integers() | ];
        q := NextPrime(IsogenyPrime);
        v := CharacterVector(CharacterPrimes,q);
        while CharacterClasses ne V do
            while N mod q eq 0 or v in CharacterClasses do
                q := NextPrime(q);
                v := CharacterVector(CharacterPrimes,q);
            end while;
            Include(~IsogenyPrimes,q);
            CharacterClasses +:= sub< V | v >;
        end while;
        vprint Quaternion :
            "Building q-isogeny classes for each p in", IsogenyPrimes;
        GeneraRepresentatives := [ lideal< A | 1 > ];
        for q in IsogenyPrimes do 
            NewGeneraRepresentatives := [ ];
            for I in GeneraRepresentatives do
                J := LeftIsogenousIdeal(I,q);
                Append(~NewGeneraRepresentatives,J);
            end for;
            GeneraRepresentatives cat:= NewGeneraRepresentatives;
        end for;
        vprintf Quaternion :
            "Completed %o isogeny classes.\n", #GeneraRepresentatives;
        vprint Quaternion :
            "Extending classes by p-isogenies for p =", p;
        GeneraIdeals := [ ];
        i := 0;
        if p in CharacterPrimes then
            vprintf Quaternion :
                "Isogeny prime %o is a character prime.\n", p;
            for I in GeneraRepresentatives do
                i +:= 1;
                vprint Quaternion, 2 : "Extending class number", i;
                pGeneraIdeals := SplitIsogenousIdeals(A,[I],p); 
                GeneraIdeals cat:= pGeneraIdeals;
            end for;
        else 
            vprintf Quaternion :
                "Isogeny prime %o is a noncharacter prime.\n", p;
            for I in GeneraRepresentatives do
                i +:= 1;
                vprint Quaternion, 2 : "Extending class number", i;
                pGeneraIdeals := LeftIsogenousIdeals(I,p); 
                Append(~GeneraIdeals, pGeneraIdeals);
            end for;
        end if;
        Idls := &cat GeneraIdeals;
    end if;
    Bases := []; 
    for i in [1..#Idls] do
        if Reduce then
            Idls[i] := ReducedLeftIdealClass(Idls[i]);
        end if;
        M := HermiteForm(Matrix(Integers(),[ Eltseq(A!x) : x in Basis(Idls[i]) ]));
        Append(~Bases,Eltseq(M)[[1,2,3,4,6,7,8,11,12,16]]);
    end for;
    A`LeftIdealBases := Bases;
    return Idls; 
end intrinsic;

intrinsic LeftIdealClassDegeneracies(A::AlgQuatOrd[RngInt],B::AlgQuatOrd[RngInt])
    -> AlgMatElt, SeqEnum
    {}
    require Type(BaseRing(A)) eq RngInt:  
        "Arguments must be orders in a rational quaternion algebra.";
    require IsDefinite(QuaternionAlgebra(A)) : 
        "Arguments must be orders in a definite algebras";
    require B subset A :
        "Argument 2 must be a suborder of argument 1.";
    IdealsB := LeftIdealClasses(B);
    return LeftIdealClassDegeneracies(A,IdealsB);
end intrinsic;

intrinsic LeftIdealClassDegeneracies(A::AlgQuatOrd[RngInt],S::[AlgQuatOrd[RngInt]])
    -> AlgMatElt, SeqEnum
    {Given an order A, and a suborder B or sequence of ideals S for some
    suborder B, return the matrix determining the mapping of (ordered)
    ideal classes of B or or S to the the (ordered) sequence ideal classes
    of S, followed by the equivalent data as a sequence of sequences
    of indices the ideal classes mapping to ideal classes of A.}

    require Type(BaseRing(A)) eq RngInt:  
        "Arguments must be orders in a rational quaternion algebra.";
    require IsDefinite(QuaternionAlgebra(A)) : 
        "Arguments must be orders in a definite algebras";
    require #S ne 0 : "Argument 2 must be nonempty";
    B := LeftOrder(S[1]);
    require &and [ LeftOrder(I) eq B : I in S ] :
        "Argument 2 must be a sequence of left ideals of a quaternion order.";
    IdealsA := LeftIdealClasses(A);
    OrdersA := [ RightOrder(I) : I in IdealsA ];
    OrderGramsA := {@ @};
    OrderIndexA := [  ];
    for i in [1..#IdealsA] do
        M := ReducedGramMatrix(RightOrder(IdealsA[i]));
        k := Index(OrderGramsA,M);
        if k eq 0 then
            Include(~OrderGramsA,M);
            Append(~OrderIndexA,[i]);
        else
            Append(~OrderIndexA[k],i); 
        end if;
    end for;
    vprint Quaternion :
        "  Set up right order grams.";
    IdealsB := S;
    IndexBA := [ 0 : i in [1..#IdealsB] ];
    for j in [1..#IdealsB] do
        I := lideal< A | [ A!x : x in Basis(IdealsB[j]) ] >;
        k := Index(OrderGramsA,ReducedGramMatrix(RightOrder(I)));
        for i in OrderIndexA[k] do 
            if CompareLeftIdeals(IdealsA[i],I) eq 0 then
                IndexBA[j] := i;
            end if;
        end for;
        assert IndexBA[j] ne 0;
    end for;
    DegensBA := [ { Integers() | } : j in [1..#IdealsA] ];
    M := RMatrixSpace(Integers(),#IdealsB,#IdealsA)!0;
    for k in [1..#IdealsB] do
        M[k,IndexBA[k]] := 1;
        Include(~DegensBA[IndexBA[k]],k);
    end for;
    return M, [ Sort(SetToSequence(I)) : I in DegensBA ];
end intrinsic;

function LeftIsogenousIdeal(I,p)
    // A p-isogenous left neighbor ideal for I. 
    B := RightOrder(I);
    D := Discriminant(B);
    FF := FiniteField(p);
    PF := PolynomialRing(FF); X := PF.1;
    repeat
        x2 := RandomElement(B,[-p div 2..p div 2]);
        D2 := Trace(x2)^2 - 4*Norm(x2);
    until KroneckerSymbol(D2,p) eq 1;
    a2 := Integers()!Roots(X^2 - Trace(x2)*X + Norm(x2))[1,1];
    x2 := x2 - a2;
    return I*LeftIdeal(B,[B|p,x2]);
end function;

intrinsic LeftNeighborIdeals(I::AlgQuatOrdIdl[RngInt],p::RngIntElt) -> SeqEnum
    {The sequence of left p-neighboring ideals of I.}
    A := LeftOrder(I);
    B := RightOrder(I);
    D := Discriminant(B);
    require Type(BaseRing(B)) eq RngInt :
        "Argument 1 must be an order over the integers.";
    require IsPrime(p) and D mod p ne 0:
        "Argument 2 must be a prime coprime to the discriminant.";
    repeat 
        x1 := RandomElement(B,[-p div 2..p div 2]);
        D1 := Trace(x1)^2 - 4*Norm(x1);
    until KroneckerSymbol(D1,p) eq -1;
    repeat
        x2 := RandomElement(B,[-p div 2..p div 2]);
        D2 := Trace(x2)^2 - 4*Norm(x2);
    until KroneckerSymbol(D2,p) eq 1;
    X := PolynomialRing(FiniteField(p)).1;
    a2 := Integers()!Roots(X^2 - Trace(x2)*X + Norm(x2))[1,1];
    x2 := x2 - a2;
    ZZ := IntegerRing();
    return [ lideal< A | Basis(I * lideal< B | [B|p,x2*(B!ZZ!Q[1] + ZZ!Q[2]*x1)] >) > : Q in P1Classes(p) ];
end intrinsic;

intrinsic RightNeighborIdeals(I::AlgQuatOrdIdl[RngInt],p::RngIntElt) -> SeqEnum
    {The sequence of right p-neighboring ideals of I.}
    A := LeftOrder(I);
    B := RightOrder(I);
    D := Discriminant(A);
    require Type(BaseRing(A)) eq RngInt :
        "Argument 1 must be an order over the integers.";
    require IsPrime(p) and D mod p ne 0:
        "Argument 2 must be a prime coprime to the discriminant.";
    repeat 
        x1 := RandomElement(A,[-p div 2..p div 2]);
        D1 := Trace(x1)^2 - 4*Norm(x1);
    until KroneckerSymbol(D1,p) eq -1;
    repeat
        x2 := RandomElement(A,[-p div 2..p div 2]);
        D2 := Trace(x2)^2 - 4*Norm(x2);
    until KroneckerSymbol(D2,p) eq 1;
    X := PolynomialRing(FiniteField(p)).1;
    a2 := Integers()!Roots(X^2 - Trace(x2)*X + Norm(x2))[1,1];
    x2 := x2 - a2;
    ZZ := IntegerRing();
    return [ rideal< B | Basis(rideal< A | [A|p,x2*(A!ZZ!Q[1] + ZZ!Q[2]*x1)] > * I) > : Q in P1Classes(p) ];
end intrinsic;

function LeftIsogenousIdeals(J,p)
    //The sequence of representatives for left isogenous ideal
    //classes of J constructed by means of p-isogenies.

    A := RightOrder(J);
    D := Discriminant(A);
    MZ := RSpace(Integers(),2);
    EmptyList := [ MZ | ];
    Orders := [ A ];
    Ideals := [ lideal< A | [1] > ];
    
    vprintf Quaternion, 2 :
        "Ideal number 1, right order module\n%o\n", NormModule(Orders[1]);
    
    FF := FiniteField(p);
    PF := PolynomialRing(FF); X := PF.1;
    repeat 
        x1 := RandomElement(A,[-p div 2..p div 2]);
        D1 := Trace(x1)^2 - 4*Norm(x1);
    until KroneckerSymbol(D1,p) eq -1;
    repeat
        x2 := RandomElement(A,[-p div 2..p div 2]);
        D2 := Trace(x2)^2 - 4*Norm(x2);
    until KroneckerSymbol(D2,p) eq 1;
    
    a2 := Integers()!Roots(X^2 - Trace(x2)*X + Norm(x2))[1,1];
    x2 := x2 - a2;
    
    r := 1;
    Frontier := [ [ MZ!P : P in P1Classes(p) ] ]; 
    while #Frontier[r] gt 0 do
        if GetVerbose("Quaternion") ge 1 then
            printf "Frontier at %o-depth %o has %o elements.\n", p, r, #Frontier[r];
            print "Number of ideals =", #Ideals;
        end if;
        for Q in Frontier[r] do
            I := lideal< A | [x2^r*(A!Q[1] + Q[2]*x1), A!p^r] >;
            B := RightOrder(I);
            
            i := 1;
            while i le #Orders and CompareOrders(B,Orders[i]) eq -1 do
                i +:= 1;
            end while; 
            while i le #Orders and IsIsomorphic(B,Orders[i]) do
                if CompareLeftIdeals(Ideals[i],I) eq 0 then
                    Exclude(~Frontier[r],Q);
                    i := #Orders + 1;
                end if; 
                i +:= 1;
            end while; 
            
            if i eq (#Orders + 1) then
                if GetVerbose("Quaternion") ge 2 then
                    printf "Ideal number %o, new right order module\n%o\n", 
                        #Orders + 1, NormModule(B);
                end if;
                Append(~Orders,B);
                Append(~Ideals,I);
            elif i le #Orders then
                if GetVerbose("Quaternion") ge 2 then
                    M := NormModule(B); 
                    printf "Ideal number %o, right order module\n%o\n", 
                        #Orders + 1, NormModule(B);
                end if;
                Insert(~Orders,i,B);
                Insert(~Ideals,i,I);
            end if;
        end for;
        Append(~Frontier,EmptyList);
        for P in Frontier[r] do
            Q := P;
            if (P[2] mod p) ne 0 then // P[2] eq 1 by assumption.
                for t in [0..(p-1)] do
                    Q[1] := P[1] + t*p^r;
                    Append(~Frontier[r+1],Q);
                end for;
            else // P = Q equals <1,0 mod l>.
                for t in [0..(p-1)] do
                    Q[2] := P[2] + t*p^r;
                    Append(~Frontier[r+1],Q);
                end for;
            end if;
        end for;
        r +:= 1; // Increment and continue.
    end while;
    if Type(J) eq AlgQuatOrd then
	return Ideals;
    else
	B := LeftOrder(J);
	return [ lideal< B | Basis(J*I) > : I in Ideals ];
    end if;
end function;

function SplitIsogenousIdeals(A,S0,p)
    // Input a sequence S0 of left A-ideals, and a prime p such that 
    // all p-isogenous left ideals are in a different genus from S0,
    // build the p^(2r+1)-isogenous ideals sequence S1 while extending 
    // S0 with p^2r-isogenous ideals
    
    D := Discriminant(A);
    MZ := RSpace(Integers(),2);
    EmptyList := [ MZ | ];
    IdealSeq := [ S0, [ Parent(A) | ] ];
    OrderSeq := [ [ RightOrder(I) : I in S0 ], [ Parent(A) | ] ];   
    /* 
    Additionally for the input sequence of ideals we need a sequence 
    indicating whether we have visited or "touched" the ideal class. 

    We begin with (the class of) A, so mark this as touched; every 
    other class is initially untouched.  

    The secondary sequence is being built as we go, so every element 
    is by definition touched at the time of creation.  We include 
    the second sequence, but it will be the all true sequence.  
    This could be omitted if we test the parity of t for each operation 
    on the sequence(s). 

    Here we assume that A is in the sequence of ideals, but we do 
    not assume that it is the first element.
    */
    Touched := [ [ Norm(I) eq 1 : I in S0 ], [ Booleans() | ] ]; 
    
    if GetVerbose("Quaternion") ge 2 then
        printf "Beginning with %o + %o ideals " * 
            "in split isogeny routine.\n", #S0, 0; 
    end if;
    
    FF := FiniteField(p);
    PF := PolynomialRing(FF); X := PF.1;
    repeat 
        x1 := RandomElement(A,[-p div 2..p div 2]);
        D1 := Trace(x1)^2 - 4*Norm(x1);
    until KroneckerSymbol(D1,p) eq -1;
    repeat
        x2 := RandomElement(A,[-p div 2..p div 2]);
        D2 := Trace(x2)^2 - 4*Norm(x2);
    until KroneckerSymbol(D2,p) eq 1;
    
    a2 := Integers()!Roots(X^2 - Trace(x2)*X + Norm(x2))[1,1];
    x2 := x2 - a2;
    
    r := 1;
    Frontier := [ [ MZ!P : P in P1Classes(p) ] ]; 
    while #Frontier[r] gt 0 do
        t := (r mod 2) + 1;
        if GetVerbose("Quaternion") ge 1 then
            Parity := t eq 1 select "Odd" else "Even"; 
            printf "Frontier at %o-depth %o has %o elements.\n",
                p, r, #Frontier[r];
            h1 := #IdealSeq[1]; 
            h2 := #IdealSeq[2]; 
            printf "Number of ideals = %o + %o\n", h1, h2;
            printf "Number of untouched ideals = %o\n", 
                &+[ Integers() | 1 : i in [1..h1] | not Touched[1][i] ];
        end if;
        for Q in Frontier[r] do
            I := lideal< A | [x2^r*(A!Q[1] + Q[2]*x1), A!p^r] >;
            B := RightOrder(I);
            
            i := 1;
            while i le #OrderSeq[t] and 
                CompareOrders(B,OrderSeq[t][i]) eq -1 do
                    i +:= 1;
            end while; 
            
            while i le #OrderSeq[t] and IsIsomorphic(B,OrderSeq[t][i]) do
                if CompareLeftIdeals(IdealSeq[t][i],I) eq 0 then
                    if not Touched[t][i] then 
                        // Mark ideal as visited and continue.
                        Touched[t][i] := true;
                    else 
                        Exclude(~Frontier[r],Q);
                    end if;
                    i := #OrderSeq[t] + 1; 
                end if; 
                i +:= 1;
            end while; 
            if i eq (#OrderSeq[t] + 1) then
                if GetVerbose("Quaternion") ge 2 then
                    printf "%o ideal number %o, new right order module\n%o\n",
                        Parity, #OrderSeq[t] + 1, NormModule(B);
                end if;
                Append(~OrderSeq[t],B);
                Append(~IdealSeq[t],I);
                Append(~Touched[t],true);
            elif i le #OrderSeq[t] then
                if GetVerbose("Quaternion") ge 2 then
                    M := NormModule(B); 
                    printf "%o ideal number %o, right order module\n%o\n", 
                        Parity, #OrderSeq[t] + 1, NormModule(B);
                end if;
                Insert(~OrderSeq[t],i,B);
                Insert(~IdealSeq[t],i,I);
                Insert(~Touched[t],i,true);
            end if;
        end for;
        Append(~Frontier,EmptyList);
        for P in Frontier[r] do
            Q := P;
            if (P[2] mod p) ne 0 then // P[2] eq 1 by assumption.
                for t in [0..(p-1)] do
                    Q[1] := P[1] + t*p^r;
                    Append(~Frontier[r+1],Q);
                end for;
            else // P = Q equals <1,0 mod l>.
                for t in [0..(p-1)] do
                    Q[2] := P[2] + t*p^r;
                    Append(~Frontier[r+1],Q);
                end for;
            end if;
        end for;
        r +:= 1; // Increment and continue.
    end while;
    return IdealSeq;
end function;

//////////////////////////////////////////////////////////////////////////////
//                          Comparison Functions                            //
//////////////////////////////////////////////////////////////////////////////

function CompareGram(M1, M2)
    // Return 1 if M1 is less than M2, 0 if M1 and M2 are equal, 
    // and -1 if M2 is less than M1.
    dim := Degree(Parent(M1));
    for i in [1..dim] do
        if M1[i,i] lt M2[i,i] then 
            return 1;
        elif M1[i,i] gt M2[i,i] then
            return -1; 
        end if;
    end for;
    for j in [1..dim-1] do
        for i in [1..dim-j] do 
            if Abs(M1[i,i+j]) gt Abs(M2[i,i+j]) then 
                return 1;
            elif Abs(M1[i,i+j]) lt Abs(M2[i,i+j]) then
                return -1; 
            end if;
        end for;
    end for;
    for j in [1..dim-1] do
        for i in [1..dim-j] do 
            if M1[i,i+j] gt M2[i,i+j] then 
                return 1;
            elif M1[i,i+j] lt M2[i,i+j] then
                return -1; 
            end if;
        end for;
    end for;
    return 0;
end function;

function CompareOrders(A,B)
    MA := ReducedGramMatrix(A);
    MB := ReducedGramMatrix(B);
    return CompareGram(MA,MB);
end function;

function CompareLeftIdeals(I,J)
    A := RightOrder(J);
    MA := Norm(I)*Norm(J)*ReducedGramMatrix(A);
    MB := ReducedGramMatrix(Conjugate(I)*J); 
    return CompareGram(MA,MB);
end function;

