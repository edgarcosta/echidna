////////////////////////////////////////////////////////////////////////
//                                                                    // 
//                           CRYPTANALYSIS                            // 
//                            David Kohel                             //
//                           February 2001                            //
//                                                                    // 
//////////////////////////////////////////////////////////////////////// 

AZ := ["A","B","C","D","E","F","G","H","I","J","K","L","M",
       "N","O","P","Q","R","S","T","U","V","W","X","Y","Z"]; 

////////////////////////////////////////////////////////////////////////
//                                                                    // 
//                         FREQUENCY MATCHING                         //
//                                                                    // 
////////////////////////////////////////////////////////////////////////

intrinsic TranslationCorrelations(S1::[FldReElt],S2::[FldReElt])
    -> SeqEnum
    {The sequence of correlations of the sequence S1 with the 
    cyclic translations of the sequence S2.}

    n := #S1;
    require n eq #S2 : "Arguments must be of the same length."; 

    // Compute the mean value of each sequence: 
    mu1 := &+[ S1[k] : k in [1..n] ]/n;
    mu2 := &+[ S2[k] : k in [1..n] ]/n;

    // Compute the standard deviations of each sequence:
    sig1 := Sqrt(&+[ (S1[k]-mu1)^2 : k in [1..n] ]);
    sig2 := Sqrt(&+[ (S2[k]-mu2)^2 : k in [1..n] ]);

    sig := sig1*sig2;
    CorrSeq := [ ];
    for j in [1..n] do
        Corr := &+[ (S1[i] - mu1) * (S2[ij] - mu2) / sig
            where ij := ((i+j-1) mod n) + 1 : i in [1..n] ];
        Append(~CorrSeq,<j,Corr>);
    end for;
    return CorrSeq;
end intrinsic;

intrinsic TranslationMatches(S::MonStgElt,F::[FldReElt],r::FldReElt) 
    -> SeqEnum 
    {}
    n := 26;
    require #F eq n : "Argument 2 must have 26 elements.";
    X := FrequencyDistribution(S);
    CorrSeq := TranslationCorrelations(X,F);
    return [ x[1] : x in CorrSeq | x[2] gt r ];
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                                                                    // 
//                         FREQUENCY ANALYSIS                         //
//                                                                    // 
////////////////////////////////////////////////////////////////////////

intrinsic Frequency(CT::CryptTxt,W::MonStgElt) -> Fld
    {The number of occurrences of a string W in the ciphertext CT 
    length r, divided by the total number #CT-#W+1 of substrings
    of length #W in CT.}
    return Frequency(String(CT),W);
end intrinsic; 

intrinsic Frequency(CT::MonStgElt,W::MonStgElt) -> Fld
    {The number of occurrences of a string W in the ciphertext CT 
    length r, divided by the total number #CT-#W+1 of substrings
    of length #W in CT.}
    k := #W;
    N := #CT;
    RR := RealField();
    return &+[ RR | 1.0 : i in [1..N-k+1] | CT[[i..i+k]] eq W ]/(N-k+1);
               
end intrinsic; 

intrinsic FrequencyDistribution(W::CryptTxt :
    Precision := 8) -> SeqEnum
    {}
    return FrequencyDistribution(String(W) : Precision := Precision);
end intrinsic;

intrinsic FrequencyDistribution(W::MonStgElt : 
    Precision := 8) -> SeqEnum
    {}
    W := StripEncoding(W : WildCharacter := "*");
    n := #W;
    S := [ 0 : i in [1..26] ];
    for i in [1..n] do
	k := Index(AZ,W[i]);
	if k ne 0 then S[k] +:= 1; end if;
    end for;
    return [ RealField() | RealField(Precision)!e/n : e in S ];
end intrinsic;

intrinsic FrequencyDistribution(W::CryptTxt : Precision := 8) -> SeqEnum
    {}
    return FrequencyDistribution(String(W) : Precision := Precision);
end intrinsic;

intrinsic CoincidenceIndex(W::CryptTxt) -> FldReElt
    {}
    return CoincidenceIndex(String(W));
end intrinsic;

intrinsic CoincidenceIndex(W::MonStgElt) -> FldReElt
    {}
    RR := RealField();
    W := StripEncoding(W : WildCharacter := "*");
    n := #W;
    S := [ 0 : i in [1..26] ];
    for i in [1..n] do
	k := Index(AZ,W[i]);
	if k ne 0 then S[k] +:= 1; end if;
    end for;
    return &+[ RR | 1.0*c*(c-1) : c in S ]/(RR!1.0*n*(n-1));
end intrinsic;

intrinsic Indices(W::CryptTxt,C::MonStgElt) -> SeqEnum
    {}
    return Indices(String(W),C);
end intrinsic;

intrinsic Indices(W::MonStgElt,C::MonStgElt) -> SeqEnum
    {}
    N := #W;
    k := #C;
    S := [ Integers() | ];
    for i in [1..N-k+1] do
	if C eq Substring(W,i,k) then
	    Append(~S,i);
	end if;
    end for;
    return S;
end intrinsic;

intrinsic Multiplicity(S::MonStgElt,W::MonStgElt) -> RngIntElt
    {}
    n := #W;
    return &+[ 1 : i in [1..#S+1-n] | Substring(S,i,n) eq W ];
end intrinsic;

intrinsic Decimation(S::MonStgElt,k::RngIntElt,n::RngIntElt)
    -> MonStgElt
    {}
    k := k mod n;
    if k eq 0 then k := n; end if;
    S := StripEncoding(S : WildCharacter := "*");
    return &cat[ S[n*i+k] : i in [0..(#S div n)-1] ];
end intrinsic;

intrinsic Decimation(
    S::MonStgElt,P::[RngIntElt],n::RngIntElt) -> MonStgElt
    {}
    require #P le n :
        "Argument 2 must have length at most that of argument 3.";
    i, j := Explode(P);
    require i ne j :
        "Argument 2 must represent distinct congruence classes.";
    require n gt 0 : "Argument 3 must be positive.";
    i := ((i-1) mod n) + 1;
    j := ((j-1) mod n) + 1;
    if i eq 0 then i := n; end if;
    if j eq 0 then j := n; end if;
    S := StripEncoding(S : WildCharacter := "*");
    return [ &cat[ S[n*k+i] : i in P ] : k in [0..(#S div n)-1] ];
end intrinsic;

intrinsic CoincidenceIndex(S::SeqEnum) -> FldReElt
    {}
    n := #S; 
    Freq := [ RealField() | ];
    for X in SequenceToSet(S) do
	Append(~Freq,#[ i : i in [1..n] | S[i] eq X ]); 
    end for;
    return &+[ f*(f-1) : f in Freq ]/(1.0*n*(n-1));
end intrinsic;

intrinsic DecimationFrequencies(
    S::MonStgElt,P::[RngIntElt],n::RngIntElt) -> MonStgElt
    {}
    require #P eq 2 : "Argument 2 must have length 2.";
    i, j := Explode(P);
    require i ne j :
        "Argument 2 must represent distinct congruence classes.";
    require n gt 0 : "Argument 3 must be positive.";
    i := i mod n;
    j := j mod n;
    if i eq 0 then i := n; end if;
    if j eq 0 then j := n; end if;
    S := StripEncoding(S : WildCharacter := "*");
    RR := RealField();
    M := MatrixAlgebra(RR,26)!0;
    for k in [0..(#S div n)-1] do
	M[Index(AZ,S[n*k+i]),Index(AZ,S[n*k+j])] +:= 1;
    end for;
    return M/(1.0*(#S div n));
end intrinsic;

intrinsic DecimationFrequency(CT::MonStgElt,W::MonStgElt,
    i::RngIntElt,m::RngIntElt) -> SeqEnum
    {}
    require #W eq 1 : "Argument 2 must have length 1.";
    return DecimationFrequency(CT,W,[i],m);
end intrinsic;

intrinsic DecimationFrequency(CT::MonStgElt,W::MonStgElt,
    I::[RngIntElt],m::RngIntElt) -> SeqEnum
    {}  
    require #W eq #I: "Argument 2 and 3 must have the same length.";
    require &and[ i in {1..m} : i in I ] : 
        "Elements of argument 3 must in the set {1..m}."; 
    n := (#CT div m) - 1;
    f := 0;
    for j in [1..n] do
        X := &cat[ CT[i+m*j] : i in I ];
	if X eq W then
  	    f +:= 1;	
	end if;		
    end for;  
    return 1.0*f/n;
end intrinsic;

intrinsic TranspositionHighFrequencyMatches( 
    CT::MonStgElt, W::MonStgElt, m::RngIntElt, r::FldReElt) -> SeqEnum
    {Transposition frequency matches.}

    require r gt 1 : "Argument 4 must be greater than 1.";
    G := SymmetricGroup(#W);
    Matches := [ Parent(<[0],r>) | ];
    freqs := [ [ DecimationFrequency(CT,W[i],j,m) 
                 : j in [1..m] ] : i in [1..#W] ];
    for I in Subsequences([1..m],#W) do                        
        F := [ DecimationFrequency(CT,W[k],[I[k]],m) : k in [1..#W] ];
        for g in G do
            J := [ I[i^g] : i in [1..#W] ];
            E := &*[ freqs[i][J[i]] : i in [1..#W] ];
   	    if E ne 0 then
                f := DecimationFrequency(CT,W,J,m)/E;         
                // vprintf Crypto : "%o: %o\n", J, f;
                if f gt r then
                    Append(~Matches,<J,f>);
                end if;
            end if;
        end for;
    end for;  
    return Matches;
end intrinsic;

function ReductionIndices(I,m)
   return [ ((i-1) mod m)+1 : i in I ];
end function;

procedure MergeCountReduction(~IdxSeq,~IdxCnt,T,m)
    for I in T do
        J := ReductionIndices(I,m);
        k := Index(IdxSeq,J);
        if k eq 0 then
            Append(~IdxSeq,J);
            Append(~IdxCnt,1);
        else 
            IdxCnt[k] +:= 1;
        end if; 
    end for;        
end procedure;

intrinsic TranspositionMatches(
    CT::MonStgElt,StrSeq::[MonStgElt],m::RngIntElt) -> SeqEnum, SeqEnum
    {}
    r := #StrSeq[1];
    error if &or[ #StrSeq[i] ne r : i in [1..#StrSeq] ],
        "Sequence must consist of strings of the same length.";
    IdxSeq := [ Parent([0]) | ];
    IdxCnt := [ Integers() | ];
    for X in StrSeq do
        T := TranspositionIndexMatches(CT,X,m);
        MergeCountReduction(~IdxSeq,~IdxCnt,T,m);
    end for;
    return IdxSeq, IdxCnt;
end intrinsic;

intrinsic TranspositionIndexMatches(
    CT::MonStgElt, W::MonStgElt, m::RngIntElt) -> SeqEnum
    {Returns the sequence of indices I = [i_1,i_2,...,i_n] such that
    each i_j is between m*k + 1 and m*(k+1) for some k, and W is equal
    to &cat[ CT[i_j] : j in [1..n] ].  The second return argument is
    a sequence of tuples consisting of a representative for the indices
    I with i_j between 1 and m and the count of its multiplicity.}

    r := #W;
    require r gt 1: "Argument 2 must have length at least 2.";
    chars := SetToSequence({ W[i] : i in [1..r] });
    n := (#CT div m) - 1;
    freqw := [ 0 : i in [1..#chars] ];
    for i in [1..r] do
	freqw[Index(chars,W[i])] +:= 1;
    end for;
    Matches := [ Parent([0]) | ];
    for j in [0..n] do
	freqs := [ 0 : i in [1..#chars] ];
	indsj := [ [] : i in [1..#chars] ];
	for i in [1..m] do
            k := Index(chars,CT[m*j+i]);
            if k ne 0 then
               freqs[k] +:= 1;
	       Append(~indsj[k],m*j+i); 
	   end if;            
        end for; 
	if &and[ freqs[i] ge freqw[i] : i in [1..#chars] ] then
	    nchar := [ freqs[Index(chars,W[i])] : i in [1..r] ];
	    indsw := [ indsj[Index(chars,W[i])] : i in [1..r] ];
	    for t in [0..&*nchar-1] do
		s := t;
		I := [ Integers() | ];
		for i in [1..r] do
		    Append(~I,(s mod nchar[i])+1);
		    s div:= nchar[i];
		end for;
                J := [ indsw[i][I[i]] : i in [1..r] ];
                assert &cat [ CT[x] : x in J ] eq W;
		if #SequenceToSet(J) eq r then
		    Append(~Matches,J);
		end if;
	    end for;
	end if;
    end for;     
    MSeq := [ [ ((I[i]-1) mod m)+1 : i in [1..r] ] : I in Matches ];
    MSet := SequenceToSet(MSeq);
    MCounts := [
	<I,#[ i : i in [1..#MSeq] | MSeq[i] eq I ]> : I in MSet ];
    return Matches, MCounts;
end intrinsic;

