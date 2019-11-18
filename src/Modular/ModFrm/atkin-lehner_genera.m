////////////////////////////////////////////////////////////////////////
//                                                                    //
//      OLD- AND NEW-SPACE ATKIN-LEHNER DECOMPOSITION DIMENSIONS      //
//                    David Kohel, created 1999                       //
//                   Last modified February 2002                      //
//                                                                    //
////////////////////////////////////////////////////////////////////////

function AtkinLehnerClosure(S)
    ClosureS := S join { P*Q div GCD(P,Q)^2 : P in S, Q in S };
    if ClosureS eq S then return S; end if;
    return AtkinLehnerClosure(ClosureS);
end function;

function CharacterCoset(G,w)
   return [ [ w[i]*t[i] : i in [1..#w] ] : t in G ];
end function;

function InclusionMap(S,T)
    return [ Index(T,S[i]) : i in [1..#S] ];
end function;

function PullBackCharacter(w,ii)
    return [ w[ii[k]] : k in [1..#ii] ];
end function;

function CharacterKernel(w)
    r := #w;
    return [ d : d in CartesianPower({0,1},r) | 
        &*[ w[i]^d[i] : i in [1..r] ] eq 1 ];
end function;

////////////////////////////////////////////////////////////////////////
//                                                                    //
////////////////////////////////////////////////////////////////////////

intrinsic ModularDegreeX0(N::RngIntElt) -> RngIntElt
    {The degree of the map X_0(N) -> X(1).}
    fact := Factorization(N);
    return &*[ Integers() | (p[1] + 1)*p[1]^(p[2]-1) : p in fact ];
end intrinsic;

intrinsic NumberOfCuspsX0(N::RngIntElt) -> RngIntElt
    {The number of cusps of X_0(N).}
    return &+[ EulerPhi(GCD(D,N div D)) : D in Divisors(N) ];
end intrinsic;

intrinsic NumberOfEllipticPointsX0(N::RngIntElt,q::RngIntElt) -> RngIntElt
    {The number of elliptic points of order q on X_0(N).}
    fact := Factorization(N);
    if q eq 2 then
	if (N mod 4) eq 0 then return 0; end if;
	return &*[ Integers() | 
	    1 + KroneckerSymbol(-4,p[1]) : p in fact ];
    elif q eq 3 then
	if (N mod 9) eq 0 then return 0; end if;
	return &*[ Integers() |
	    1 + KroneckerSymbol(-3,p[1]) : p in fact ];
    end if;
    return 0;
end intrinsic;

function NewShortCut(N,w)
   if (N le 10) or N in [12,13,16,18,22,25,28,60] then
      return 0;
   elif N in [11,17,19,27,32,49,64] then
      if w eq [-1] then return 1; else return 0; end if;
   elif N in [14,15,33,40,46,48,72] then
      if w eq [1,-1] then return 1; else return 0; end if;
   elif N in [20,21,24,34,36,44,45,52,76,100,108] then
      if w eq [-1,1] then return 1; else return 0; end if;
   elif N in [23,29,31,81] then
      if w eq [-1] then return 2; else return 0; end if;
   elif N in [26,38,50,54,56,80,96,144] then
      if w in [ [1,-1], [-1,1] ] then return 1; 
      else return 0; end if;
   elif N eq 30 then
      if w eq [1,-1,1] then return 1; else return 0; end if;
   elif N eq 37 then 
      return 1; 
   elif N in [35,39,75,98] then
      if w eq [-1,1] then return 2; 
      elif w eq [1,-1] then return 1; 
      else return 0; end if;
   elif N in [42,70] then
      if w eq [-1,1,1] then return 1; else return 0; end if;
   elif N in [51,55,62,63,69,94,104] then
      if w eq [1,1] then return 0;
      elif w eq [1,-1] then return 2;
      elif w eq [-1,1] then return 1; 
      else return 0;
      end if;
   elif N eq 66 then
      if w in [ [1,-1,1], [-1,1,1], [-1,-1,-1] ] then return 1; 
      else return 0; end if;
   elif N eq 78 then
      if w eq [1,1,-1] then return 1; 
      else return 0; end if;
   elif N in [84,132,140,204] then
      if w in [ [-1,1,1], [-1,-1,-1] ] then return 1; 
      else return 0; end if;
   elif N in [90,114,150] then
      if w in [ [1,1,-1], [-1,1,1], [-1,-1,-1] ] then return 1; 
      else return 0; end if;
   elif N in [120,126] then
      if w in [ [1,-1,1], [-1,-1,-1] ] then return 1; 
      else return 0; end if;
   elif N in [160,192] then
      if w eq [1,1] then return 1;
      elif w eq [1,-1] then return 2;
      elif w eq [-1,1] then return 1; 
      else return 0;
      end if;
   elif N eq 105 then
      if w eq [1,1,-1] then return 2;
      elif w eq [-1,-1,-1] then return 1;
      else return 0; 
      end if;
   elif N eq 140 then
      if w in [ [-1,1,1], [-1,-1,-1] ] then return 1;
      else return 0; 
      end if;
   elif N eq 180 then
      if w eq [-1,-1,-1] then 
         return 1;
      else return 0;
      end if;
   elif N eq 240 then
      if w in [ [1,1,1], [1,1,-1], [-1,1,1], [-1,-1,-1] ] then
         return 1;
      else return 0; 
      end if;
   elif N eq 480 then
      if w in [ [1,-1,1], [-1,-1,-1] ] then return 2;
      elif w in [ [1,1,1], [1,1,-1], [-1,1,1], [-1,1,-1] ] then 
         return 1;
      else return 0;
      end if;
   end if;
end function;

intrinsic AtkinLehnerNewEigenspaceDimension(
    N::RngIntElt,w::SeqEnum) -> RngIntElt 
    {}
    DivSeq := Divisors(N);
    require #w eq #Factorization(N) :
        "Length of argument 2 must equal the number of " * 
        "primes dividing argument 1.";
    if ( ( (N le 56) and (N notin [41,43,47,53]) ) or
       (N in [60,62,63,64,66,70,72,75,76,78,80,81,84] cat 
             [90,94,96,98,100,104,105,108,114,120,126,132] cat 
             [140,144,150,160,180,192,204,240,480]) ) then 
        return NewShortCut(N,w);
    end if;
    return ModularGenusX0(N,w) - 
        &+[ &+[ OldSubspaceDimension(N,M,R,w) 
            : R in DivSeq | (N mod (M*R^2)) eq 0 ] : M in DivSeq ];
end intrinsic;

intrinsic AtkinLehnerEigenspaceDimensions(N::RngIntElt) -> RngIntElt
    {The dimensions of the Atkin-Lehner eigenspaces of weight 2
    modular forms for Gamma_0(N).} 
    r := #Factorization(N);
    eigs := [ [ w[i] : i in [1..r] ] : w in CartesianPower({1,-1},r) ];
    return [ ModularGenusX0(N,w) : w in eigs ];
end intrinsic;

intrinsic AtkinLehnerNewEigenspaceDimensions(N::RngIntElt) -> SeqEnum
    {The sequence of dimensions of the new Atkin-Lehner eigenspaces
    for Gamma_0(M) and weight 2.}

    SuppN := PrimeDivisors(N); 
    DivSeq := Divisors(N);
    rs := [ #[ p : p in SuppN | M mod p eq 0 ] : M in DivSeq ];
    CharSeqs := [ [ [w[i] : i in [1..rs[j]]] :
        w in CartesianPower({1,-1},rs[j]) ] : j in [1..#DivSeq] ];
    NewDimSeqs := [ [ 0 : i in [1..2^rs[j]] ] : j in [1..#DivSeq] ];
    GeneraSeqs := [ [ ModularGenusX0(DivSeq[j],w) :
	w in CharSeqs[j] ] : j in [1..#DivSeq] ];
    for k in [1..#DivSeq] do
        if DivSeq[k] notin {1,2,3,4,5,6,7,8,9,10,12,13,16,18,25} then
	    AtkinLehnerNewEigenspaceRecursionDimensions(
	        ~NewDimSeqs, GeneraSeqs, DivSeq, CharSeqs, k);
	end if;
    end for;
    return NewDimSeqs[#DivSeq];
end intrinsic;

intrinsic NewSubspaceDimensionX0(N::RngIntElt) -> SeqEnum
    {The dimensions of the new subspace of weight 2 modular
    forms on X_0(N).}
    Genera := [ ];
    DivSeq := Divisors(N);
    NewDims := [ 0 : i in [1..#DivSeq] ];
    for k in [1..#DivSeq] do
	M := DivSeq[k];
	Append(~Genera,ModularGenusX0(M));
	if M in {1,2,3,4,5,6,7,8,9,10,12,13,16,18,25} then
	    NewDims[k] := 0; 
	else
	    OldDims := &+[ Integers() |
	        NewDims[j] * #Divisors(M div DivSeq[j]) :
                    j in [1..k-1] | M mod DivSeq[j] eq 0 ];	         
  	    NewDims[k] := Genera[k] - OldDims;
	end if;
    end for;
    return NewDims[#NewDims];
end intrinsic;

intrinsic OldSubspaceDimension(
    N::RngIntElt, M::RngIntElt, R::RngIntElt, w::SeqEnum) -> RngIntElt
    {}
    assert (N mod (M*R^2)) eq 0;
    if (N eq M) then return 0; end if;
    if (M eq 1) then return 0; end if;
    S := N div (M*R^2);
    SuppN := PrimeDivisors(N); 
    assert #w eq #SuppN;
    SuppM := [ p : p in SuppN | M mod p eq 0 ];
    SuppS := [ p : p in SuppN | S mod p eq 0 ];
    TogglePrimes := [ p : p in SuppN | 
        (p notin SuppS) and (p notin SuppM) ];
    tt := InclusionMap(TogglePrimes,SuppN);
    if not &and[ IsOne(w[tt[k]]) : k in [1..#TogglePrimes] ] then
	return 0;
    end if;
    ii := InclusionMap(SuppM,SuppN);
    BoundPrimes := [ p : p in SuppM | p notin SuppS ];
    jj := InclusionMap(BoundPrimes,SuppM);
    KernChars := { [ u[i] : i in [1..#SuppM] ] : 
        u in CartesianPower({1,-1},#SuppM) | 
            &and[ IsOne(u[jj[k]]) : k in [1..#BoundPrimes] ] }; 
    return &+[ AtkinLehnerNewEigenspaceDimension(M,v) : v in 
        CharacterCoset(KernChars,PullBackCharacter(w,ii)) ];
end intrinsic;

intrinsic AtkinLehnerNewEigenspaceRecursionDimensions(
    ~NewDimSeqs::SeqEnum, GeneraSeq::SeqEnum, 
    DivSeq::SeqEnum, CharSeqs::SeqEnum, k::RngIntElt)
    {Assumes that for all j < k the old and new dimensions
    have been computed; computes the old subspace dimension
    and uses this the update the new.}
    
    // NewSubspaceDimension(N,w) == 
    //    ModularGenusX0(N,w) - OldSubspaceDimension(N,w);
    // OldSubspaceDimension(N,w) ==
    // &+[
    //    &+[
    //       &+[ NewSubspaceDimension(M,v) : v in 
    //           CharacterCoset(KernChars,PullBackCharacter(w,ii)) ]
    //       : R in RSeq(M) ]
    //    : M in DivSeq \ N
    // ];
    // where
    //    RSeq(M) == [ R in Divisors(N) | (N mod (M*R^2)) eq 0 ];

    N := DivSeq[k];
    SuppN := PrimeDivisors(N); 
    DivSeq_k := Divisors(N); 
    for s in [1..#CharSeqs[k]] do 
	OldDim := 0;
	w := CharSeqs[k][s];
	for M in [ M : M in DivSeq_k | M ne N and M ne 1 ] do
	    j := Index(DivSeq,M);
	    SuppM := [ p : p in SuppN | M mod p eq 0 ];
	    ii := InclusionMap(SuppM,SuppN);
	    RSeq := [ R : R in DivSeq_k | (N mod (M*R^2)) eq 0 ];
	    for R in RSeq do
		S := N div (M*R^2);
		SuppS := [ p : p in SuppN | S mod p eq 0 ];
		TogglePrimes := [ p : p in SuppN | 
 		    (p notin SuppS) and (p notin SuppM) ];
		tt := InclusionMap(TogglePrimes,SuppN);
		if &and[ IsOne(w[tt[k]]) : k in [1..#TogglePrimes] ] then
   		    BoundPrimes := [ p : p in SuppM | p notin SuppS ];
		    jj := InclusionMap(BoundPrimes,SuppM);
		    KernChars := { [ u[i] : i in [1..#SuppM] ] : 
	  	        u in CartesianPower({1,-1},#SuppM) | 
		           &and[ u[jj[k]] eq 1 : k in [1..#BoundPrimes] ] }; 
		    OldDim +:= &+[
			NewDimSeqs[j][Index(CharSeqs[j],v)] :
  		        v in CharacterCoset(
		            KernChars,PullBackCharacter(w,ii)) ];
		end if;
	    end for;
	end for;
	NewDimSeqs[k][s] := GeneraSeq[k][s] - OldDim;
    end for;
end intrinsic;

intrinsic ModularGenusX0(N::RngIntElt) -> RngIntElt
   {The genus of the modular curve X_0(N).}
   fact := Factorization(N);
   mu := &*[ Integers() | 
      (p[1] + 1)*p[1]^(p[2]-1) : p in fact ];
   if (N mod 4) eq 0 then nu2 := 0;
   else nu2 := &*[ Integers() | 
      1 + KroneckerSymbol(-4,p[1]) : p in fact ];
   end if;
   if (N mod 9) eq 0 then nu3 := 0;
   else nu3 := &*[ Integers() |
      1 + KroneckerSymbol(-3,p[1]) : p in fact ];
   end if;
   nuoo := &+[ EulerPhi(GCD(d,N div d)) : d in Divisors(N) ];
   return 1 + ((mu - 3*nu2 - 4*nu3 - 6*nuoo) div 12);
end intrinsic;

intrinsic AtkinLehnerEigenspaceDimension(
    N::RngIntElt,w::SeqEnum) -> RngIntElt
    {The dimension of the space of differentials on X_0(N) 
    with character w under the Atkin Lehner operators.}
    return ModularGenusX0(N,w);
end intrinsic;

intrinsic ModularGenusX0(N::RngIntElt,w::SeqEnum) -> RngIntElt
   {The dimension of the space of differentials on X_0(N) 
   with character w under the Atkin Lehner operators.}
   PrPowDiv := [ f[1]^f[2] : f in Factorization(N) ]; 
   require #w eq #PrPowDiv :
       "The length of argument 2 must equal " *
       "the number of primes dividing argument 1.";
   gplus := AtkinLehnerQuotientGenusX0(N);
   if &and[ e eq 1 : e in w ] then return gplus; end if;
   D := CharacterKernel(w);
   W := { &*[ PrPowDiv[i]^d[i] : i in [1..#PrPowDiv] ] : d in D };
   return AtkinLehnerQuotientGenusX0(N,W) - gplus;
end intrinsic;

intrinsic AtkinLehnerQuotientGenusX0(N::RngIntElt) -> RngIntElt
   {Returns the genus of the quotient of X_0(N) by the Atkin 
   Lehner operators.}
   return AtkinLehnerQuotientGenusX0(N,{ f[1]^f[2] : f in Factorization(N) });
end intrinsic;

intrinsic AtkinLehnerQuotientGenusX0(
    N::RngIntElt, S::[RngIntElt]) -> RngIntElt
    {Returns the genus of the quotient of X_0(N) by the Atkin-Lehner 
    operators w_Q, for Q in S.}
    require N ge 1 : "Argument 1 must be positive.";
    if N eq 1 then return 0; end if;
    return AtkinLehnerQuotientGenusX0(N,{ Q : Q in S });
end intrinsic;

intrinsic AtkinLehnerQuotientGenusX0(
    N::RngIntElt, S::{RngIntElt}) -> RngIntElt
    {Returns the genus of the quotient of X_0(N) by the Atkin-Lehner 
    operators w_Q, for Q in S.}
    require N ge 1 : "Argument 1 must be positive.";
    if N eq 1 then return 0; end if;
    S := AtkinLehnerClosure(S);
    t := Valuation(#S,2);
    R := &+[ AtkinLehnerRamification(N,Q) : Q in S ];
    return ((ModularGenusX0(N) - 1 - (R div 2)) div 2^t) + 1;
end intrinsic;

intrinsic AtkinLehnerQuotientGenusX0(
    N::RngIntElt, Q::RngIntElt) -> RngIntElt
    {Returns the genus of the quotient of X_0(N) by the Atkin-Lehner 
    operator w_Q.}
    require N ge 1 : "Argument 1 must be positive.";
    if N eq 1 then return 0; end if;
    R := AtkinLehnerRamification(N,Q);
    return ((ModularGenusX0(N) + 1 - (R div 2)) div 2);
end intrinsic;

intrinsic AtkinLehnerRamification(N::RngIntElt) -> RngIntElt
    {Returns the sequence of the number of points stabilized by
    the Atkin-Lehner involution w_Q on X_0(N), for each positive
    integer Q exactly dividing N.}
    qs := [ f[1]^f[2] : f in Factorization(N) ]; 
    ex := [ e : e in CartesianPower({0,1},#qs) ]; 
    Qs := [ &*[ qs[i]^e[i] : i in [1..#qs] ] : e in ex ];
    return [ AtkinLehnerRamification(N,Q) : Q in Qs ];
end intrinsic;

intrinsic AtkinLehnerRamification(N::RngIntElt,Q::RngIntElt) 
   -> RngIntElt {Returns the number of points stabilized by the 
   Atkin-Lehner involution w_Q on X_0(N).}

   M := N div Q;
   if (N mod Q) ne 0 or GCD(M,Q) ne 1 then
      return "Argument 2 must exactly divide argument 1.";
   else 
      r, m := SquarefreeFactorization(Q);
   end if;
   R := Zero(Integers());
   if Q eq 1 then
      return 0;
   elif Q eq 2 then
      // D = -4, will catch D = -8 below.
      R +:= PrimitiveIdealNumber(-4,M);
   elif Q eq 3 then
      // D = -3 and D = -12 and return.
      if M eq 1 then 
         return 2; 
      elif (M mod 4) eq 2 then
         // D = -3 to D = -12 inclusion and vice versa.
         return 2*PrimitiveIdealNumber(-3,M div 2);
      else
         return PrimitiveIdealNumber(-3,M) + 
             PrimitiveIdealNumber(-12,M);
      end if;
   elif Q eq 4 then
      // Add in the ramified cusps.
      R +:= NumberOfCuspsX0(N div 4);
   elif (Q mod 4) eq 3 then
      if (M mod 2) eq 0 then
         // Contribution of (-Q |--> -Q) ideals, and of ideals 
         // (-4Q |--> -Q) and duals (-Q |--> -4Q).
         R +:= ( PrimitiveIdealNumber(-Q,M) 
                 + 2*PrimitiveIdealNumber(-Q,M div 2) 
                       *(2 - KroneckerSymbol(-Q,2)) )*ClassNumber(-Q);
      else 
         R +:= PrimitiveIdealNumber(-r,M)*ClassNumber(-Q);
      end if;
   end if;
   return R + PrimitiveIdealNumber(-4*Q,M)*ClassNumber(-4*Q);
end intrinsic;

intrinsic PrimitiveIdealNumber(D::RngIntElt,Q::RngIntElt) -> RngIntElt
   {Returns the number of cyclic ideals of norm Q in the quadratic 
   order of discriminant D.}
   DK := FundamentalDiscriminant(D); 
   xx, m := SquarefreeFactorization(D div DK);
   PrDiv := PrimeDivisors(Q);
   n := 1;
   for p in PrDiv do
      xp := KroneckerSymbol(DK,p);
      s := Valuation(Q,p);
      r := Valuation(m,p);
      if r eq 0 then
         n *:= (1 + xp)*xp^(2*(s-1));
      else
         if s lt 2*r then
            if (s mod 2) eq 0 then
               t := s div 2;
               n *:= (p - 1)*p^(t-1);
            else 
               return 0;
            end if;
         elif s eq 2*r then
            n *:= (p - xp - 1)*p^(r-1);
         else 
            n *:= (1 + xp)*xp^(2*(s-2*r-1))*(p - xp)*p^(r-1);
         end if;
      end if;
   end for;
   return n;
end intrinsic;

