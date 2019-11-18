////////////////////////////////////////////////////////////////////////
//                                                                    // 
//          Digraph and Polyalphabetic Frequency Distributions        //
//                            David Kohel                             //
//                           February 2001                            //
//                                                                    // 
//////////////////////////////////////////////////////////////////////// 

AZ := ["A","B","C","D","E","F","G","H","I","J","K","L","M",
       "N","O","P","Q","R","S","T","U","V","W","X","Y","Z"]; 

intrinsic DigraphFrequencyDistribution(
    W::CryptTxt : Precision := 8) -> SeqEnum {}
    return DigraphFrequencyDistribution(
	String(W) : Precision := Precision);
end intrinsic;

intrinsic DigraphFrequencyDistribution(
    W::MonStgElt : Precision := 8) -> AlgMatElt
    {}
    require #W ge 2 :
	"Argument 1 must be of length at least 2.";
    RR := RealField();
    M := MatrixAlgebra(RR,26)!0;
    u := RR!RealField(Precision)!(1/(#W-1));
    i := Index(AZ,W[1]);
    for k in [2..#W] do
	j := Index(AZ,W[k]);
	if j ne 0 then
	    M[i,j] +:= u;
	    i := j;
	end if;
    end for;
    return M;
end intrinsic; 

intrinsic DigraphFrequencyDistribution(
    S::[MonStgElt] : Precision := 8) -> AlgMatElt
    {The matrix of frequencies of C_iC_j in the sequence S or string W.}
    require &and[ #W eq 2 : W in S ] :
	"Argument 1 must be a sequence of strings of length at least 2.";
    RR := RealField();
    M := MatrixAlgebra(RR,26)!0;
    u := RR!RealField(Precision)!(1/#S);
    for W in S do
	i := Index(AZ,W[1]);
	j := Index(AZ,W[2]);
	if i ne 0 and j ne 0 then
	    M[i,j] +:= u;
	end if;
    end for;
    return M;
end intrinsic; 

intrinsic FrequencyDistribution(
    S::MonStgElt,n::RngIntElt,r::FldReElt) -> SetIndx, SeqEnum
    {The indexed set of substrings of length n occurring with frequency
    at least r, followed by the sequence of frequencies.}
    N := #S-n-1;
    s := Ceiling(r*N);
    MS := SequenceToMultiset([ S[[i..i+n-1]] : i in [1..N] ]);
    IS := {@ Strings() | @};
    SQ := [ RealField() | ];
    for W in Set(MS) do
	m := Multiplicity(MS,W);
	if m ge s then
	    Include(~IS,W);
	    Append(~SQ,1.0*m/N);
	end if;
    end for;
    return IS, SQ;
end intrinsic;

intrinsic CoincidenceDiscriminant(S::[MonStgElt] : 
    Precision := 19) -> FldReElt
    {The coincidence discrimiant of the 2-character sequence S.}
    AA := {@ A*B : A, B in AZ @} where  
	AZ := [ CodeToString(64+i) : i in [1..26] ];
    cnts := [ 0 : i in [1..26^2] ];
    for s in S do
	cnts[Index(AA,s)] +:= 1;
    end for;
    F1 := FrequencyDistribution(
	&*[ s[1] : s in S ] : Precision := Precision);
    F2 := FrequencyDistribution(
	&*[ s[2] : s in S ] : Precision := Precision);
    RR := RealField(Precision);    
    return RealField() !
	&+[ (RR!cnts[i+26*(j-1)]/#S-F1[i]*F2[j])^2 : i, j in [1..26]];
end intrinsic;

intrinsic CoincidenceIndex(S::MonStgElt,j::RngIntElt :
    Precision := 19) -> FldReElt
    {}
    require j eq 2 : "Argument 2 must be 2";
    Alph := [ CodeToString(64+i) : i in [1..26] ];
    AA := {@ A*B : A, B in Alph @}; 
    FD := FrequencyDistribution(S : Precision := Precision);
    cnts := [ 0 : i in [1..26^2] ];
    for i in [1..#S-1] do
	cnts[Index(AA,S[i]*S[i+1])] +:= 1;
    end for;
    RR := RealField();    
    RX := RealField(Precision);    
    return &+[ RR | (RX!cnts[i+26*(j-1)]/(#S-1))^2 : i, j in [1..26] ];
end intrinsic;

