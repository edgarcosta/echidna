////////////////////////////////////////////////////////////////////////
//                                                                    // 
//                        MAGMA STRING ENCODING                       // 
//                             David Kohel                            //
//                            February 2001                           //
//                                                                    // 
//////////////////////////////////////////////////////////////////////// 

ALPHABET := ["A","B","C","D","E","F","G","H","I","J","K","L","M",
             "N","O","P","Q","R","S","T","U","V","W","X","Y","Z"]; 
alphabet := ["a","b","c","d","e","f","g","h","i","j","k","l","m",
             "n","o","p","q","r","s","t","u","v","w","x","y","z"]; 

intrinsic RandomSubstitutionKey() -> MonStgElt
    {Returns a string which is a random permutation of the characters
    A through Z, all upper case.}
    S := ALPHABET;
    X := "";
    for i in [1..#S] do
	c := Random(S);
	X cat:= c;
	Exclude(~S,c);
    end for;
    return X;
end intrinsic;

intrinsic SubstitutionEnciphering(K::MonStgElt,W::MonStgElt :
    Encode := true) -> MonStgElt
    {Given a 26 character key K and a plaintext file W, each over
    the alphabet A...Z, return the substitution ciphertext for W
    defined by the simple substitution key K.}
	
    if Encode then
	K := StripEncoding(K);
	W := StripEncoding(W);
    end if;
    require #K eq 26 : "Invalid substitution key."; 
    n := #W;
    I := [ i eq -22 select 27 else i
	where i := StringToCode(W[i])-64 : i in [1..n] ];
    K cat:= "*";
    return &cat[ I[i] eq -54 select "\n" else K[I[i]] : i in [1..n] ];
end intrinsic;

intrinsic SubstitutionEnciphering(A::SetIndx,K::SetIndx,W::MonStgElt) -> MonStgElt
    {Given an alphabet A, a key K of the same length, and a plaintext file W
    over A, return the substitution ciphertext for W  defined by K.}
	
    //K := StripEncoding(K);
    //W := StripEncoding(W);
    require #K eq #A :
	"Arguments 1 and 2 must have the same length.";
    require Type(Universe(A)) eq MonStg and Type(Universe(K)) eq MonStg : 
	"Arguments 1 and 2 must be indexed sets of strings.";
    C := "";
    I := [ Index(K,W[i]) : i in [1..#W] ]; 
    return &cat[ I[i] ne 0 select A[I[i]] else W[i] : i in [1..#I] ];
end intrinsic;

intrinsic StripEncoding(W::MonStgElt :
    LineLength := 0, WildCharacter := "") -> MonStgElt
    {Returns the string generated from W by discarding all non-alphabetic
    characters and changing all remaining characters to upper case.}
    require LineLength ge 0 :
        "Parameter LineLength must be non-negative.";
    newline := "\n";
    X := "";
    j := 0;
    for i in [1..#W] do
	c := W[i];
	if c in ALPHABET then
	    X cat:= c;
	    j +:= 1;
	    if LineLength ne 0 and j mod LineLength eq 0 then
		X cat:= newline;
	    end if;
	elif c in alphabet then
	    X cat:= ALPHABET[Index(alphabet,c)];
	    j +:= 1;
	    if LineLength ne 0 and j mod LineLength eq 0 then
		X cat:= newline;
	    end if;
	elif c eq WildCharacter then
	    X cat:= c;
	    j +:= 1;
	end if;
    end for;
    return X;
end intrinsic;

function ByteBits(n)
    S := [ Integers() | ];
    for i in [1..8] do
	Append(~S,n mod 2);
	n div:= 2;
    end for;
    return Reverse(S);
end function;

intrinsic BitEncoding(W::MonStgElt) -> SeqEnum
    {The sequence of bits (over FiniteField(2)) encoding the string W.}
    S := &cat[ ByteBits(StringToCode(W[i])) : i in [1..#W] ];
    return ChangeUniverse(S,GF(2));
end intrinsic;

intrinsic BitDecoding(S::SeqEnum) -> SeqEnum
    {The ASCII string represented by the bit sequence S.}
    N := #S;
    // require N mod 8 eq 0 : "Argument must have length divisible by 8.";
    require Universe(S) eq GF(2) :
        "Argument must be a sequence of the field of 2 elements.";
    ChangeUniverse(~S,Integers());
    Word := "";
    for j in [0..(N div 8)-1] do
	n := 0;
	for i in [1..8] do
	    n +:= S[8*j+i]*2^(8-i);
	end for;
	if n eq 0 then break; end if;
	Word cat:= CodeToString(n);
    end for;
    return Word;
end intrinsic;


