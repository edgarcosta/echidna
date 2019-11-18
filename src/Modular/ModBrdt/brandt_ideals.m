////////////////////////////////////////////////////////////////////////
//                                                                    //  
//                   LOCAL QUATERNION IDEAL ARITHMETIC                //
//                          FOR BRANDT MODULES                        //
//                            by David Kohel                          // 
//                                                                    // 
//////////////////////////////////////////////////////////////////////// 

forward HeckeAdjacencyMatrix; 
forward CompareOrders, CompareLeftIdeals, CompareGram; 

////////////////////////////////////////////////////////////////////////
//                         Accessory Functions                        //
////////////////////////////////////////////////////////////////////////

function RandomElement(A,S)
    return A![ Random(S) : i in [1..4] ];
end function;

procedure ExtendAdjacencyHecke(M,prms)
    if not M`IsFull then
        X := AmbientModule(M); 
        ExtendAdjacencyHecke(X,prms);
    end if;
    for p in prms do
        if M`IsFull and p notin M`HeckePrimes then
            h := Dimension(M);
            M`HeckeOperators cat:= [ HeckeAdjacencyMatrix(M,p) ];
            Append(~M`HeckePrimes,p);
        elif p notin M`HeckePrimes then
            g := Dimension(M);
            T := X`HeckeOperators[Index(X`HeckePrimes,p)];
            U := M`Module;
            B := BasisMatrix(M);
            Append(~M`HeckeOperators,
                Matrix([ Coordinates(U,U!(B[i]*T)) : i in [1..g] ]));
            Append(~M`HeckePrimes,p);
        end if;
    end for;
end procedure;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                          Isogeny Graphs                            //
//                                                                    //
////////////////////////////////////////////////////////////////////////

function HeckeNeighborIndex(Orders,Ideals,B,I,p,x1,x2,Q)
    h := #Ideals;
    J := I*LeftIdeal(B,[x2*(B!Q[1] + Q[2]*x1), B!p]);
    C := RightOrder(J);
    j := 1;
    while j le h do
	if CompareOrders(C,Orders[j]) eq -1 then
	    j +:= 1;
	elif CompareLeftIdeals(Ideals[j],J) ne 0 then
	    j +:= 1;
	else
	    break;
	end if;
    end while;
    return j;
end function;

function HeckeAdjacencyMatrix(M,p)
    vprint Brandt : "Hecke adjacency matrix for p =", p;
    Ideals := M`LeftIdeals;
    h := #Ideals;
    tyme := Cputime();
    Orders := [ RightOrder(I) : I in Ideals ];
    vprint Brandt : "Right order computation time:", Cputime(tyme);
    MZ := RSpace(Integers(),2);
    Frontier := [ MZ!P : P in P1Classes(p) ]; 
    FF := FiniteField(p);
    PF := PolynomialRing(FF); X := PF.1;
    M := MatrixAlgebra(Integers(),h)!0;
    vprintf Brandt : "Computing adjaceny ideals for %o classes.\n", h;
    for i in [1..h] do
        I := Ideals[i];
        B := Orders[i];
        repeat 
            x1 := RandomElement(B,[-p div 2..p div 2]);
            D1 := Trace(x1)^2 - 4*Norm(x1);
	until KroneckerSymbol(D1,p) eq -1;
        repeat
            x2 := RandomElement(B,[-p div 2..p div 2]);
            D2 := Trace(x2)^2 - 4*Norm(x2);
        until KroneckerSymbol(D2,p) eq 1;
        a2 := Integers()!Roots(X^2 - Trace(x2)*X + Norm(x2))[1,1];
        x2 := x2 - a2;
        for Q in Frontier do
	    j := HeckeNeighborIndex(Orders,Ideals,B,I,p,x1,x2,Q);
            error if j eq h+1, "Brandt module ideal sequence incomplete.";
            M[i,j] +:= 1;
        end for;
	vprint Brandt, 3 :
	    "  Adjacent ideals computed for ideal class ", i;
    end for;
    return M;
end function;

////////////////////////////////////////////////////////////////////////
//                       Comparison Functions                         //
////////////////////////////////////////////////////////////////////////

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

