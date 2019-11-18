//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//                            CRYPTOSYSTEMS                                 //
//        Copyright (C) 2013 David Kohel <David.Kohel@univ-amu.fr>          //
//                                                                          //
//  Distributed under the terms of the GNU General Public License (GPL)     //
//                                                                          //
//                  http://www.gnu.org/licenses/                            //
//                                                                          //
//        All rights granted to distribute under the GPL, version 2,        //
//          or (at your option) any later version of the license.           //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

/* Created David Kohel, February 2000 */

Alphabet := ["A","B","C","D","E","F","G","H","I","J","K","L","M",
             "N","O","P","Q","R","S","T","U","V","W","X","Y","Z"];

declare verbose Crypt, 2;

import "public_key.m" : RSAEnciphering;

////////////////////////////////////////////////////////////////////////
//                       ATTRIBUTION DECLARATIONS                     //
////////////////////////////////////////////////////////////////////////

declare type Crypt[CryptKey];

declare attributes Crypt :
   CipherType,
   IsSymmetric,
   BlockLength,
   Domain,
   Codomain;

////////////////////////////////////////////////////////////////////////
//                                                                    // 
//                     ENCODING SPECIFICATION                         // 
//                                                                    // 
////////////////////////////////////////////////////////////////////////

function EncodingType(C)
    if CipherType(C) in {"LFSR","ShrinkingGenerator"} then
	return "Binary";
    elif CipherType(C) eq "RSA" then
	return "RSA";
    else
	return "Alphabetic";
    end if;
end function;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                          CONSTRUCTORS                              //
//                                                                    // 
////////////////////////////////////////////////////////////////////////

intrinsic SubstitutionCryptosystem() -> Crypt
    {}
    C := New(Crypt);
    C`IsSymmetric := true;
    C`CipherType := "Substitution";
    return C;
end intrinsic;

intrinsic SubstitutionCryptosystem(Alph::SetIndx) -> Crypt
    {}
    C := New(Crypt);
    C`IsSymmetric := true;
    C`CipherType := "Substitution";
    C`Domain := Alph;
    C`Codomain := Alph;
    return C;
end intrinsic;

intrinsic TranspositionCryptosystem(m::RngIntElt) -> Crypt
    {}
    C := New(Crypt);
    C`IsSymmetric := true;
    C`CipherType := "Transposition";
    C`BlockLength := m;
    return C;
end intrinsic;

intrinsic VigenereCryptosystem(m::RngIntElt) -> Crypt
    {The Vigenere cryptosystem of block length m.}
    C := New(Crypt);
    C`IsSymmetric := true;
    C`CipherType := "Vigenère";
    C`BlockLength := m;
    return C;
end intrinsic;

intrinsic LFSRCryptosystem() -> Crypt
    {The linear feedback shift register cryptosystem.}
    C := New(Crypt);
    C`IsSymmetric := true;
    C`CipherType := "LFSR";
    return C;
end intrinsic;

intrinsic ShrinkingGeneratorCryptosystem() -> Crypt
    {The shrinking generator cryptosystem, based on a pair of
    linear feedback shift registers.}
    C := New(Crypt);
    C`IsSymmetric := true;
    C`CipherType := "ShrinkingGenerator";
    return C;
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                  COERCION AND KEY CREATION                         //
//                                                                    //
////////////////////////////////////////////////////////////////////////

intrinsic IsCoercible(C::Crypt,W::.) -> BoolElt, MonStgElt
   {}
   if Type(W) eq CryptKey then
       if C eq Parent(W) then
	   return true, W;
       end if;
   elif Type(W) eq MonStgElt then
       if C`CipherType notin {"Vigenère","Substitution"} then
	   return false, "Invalid coercion.";
       end if;
       // Test that the key length is valid.
       if not assigned C`Domain then
	   W := StripEncoding(W : WildCharacter := "*");
	   m := assigned C`BlockLength select C`BlockLength else #W;
       else
	   m := #C`Domain;
       end if;
       if m eq #W or m eq 0 then
	   K := New(CryptKey);
	   K`Parent := C;
	   K`IsEnciphering := true;
	   K`KeyString := W;
	   return true, K;
       end if;
   elif Type(W) eq SeqEnum then
       if C`CipherType eq "ShrinkingGenerator" then
	   S := Universe(W);
	   if Type(S) ne Crypt or #W ne 2 or 
	       S`CipherType ne "LFSR" then
	       return false, "Invalid coercion.";
	   end if;
	   K := New(CryptKey);
	   K`Parent := C;
	   K`IsEnciphering := true;
	   K`KeyString := W;
	   return true, K;
       elif C`CipherType eq "RSA" then
	   if Type(Universe(W)) ne RngInt or #W ne 2 then
	       return false, "Invalid coercion.";
	   end if;
	   K := New(CryptKey);
	   K`Parent := C;
	   K`IsEnciphering := true;
	   K`KeyString := W;
	   return true, K;
       elif C`CipherType notin {"Transposition"} then
	   return false, "Invalid coercion.";
       end if;
       m := assigned C`BlockLength select C`BlockLength else #W;
       if Type(Universe(W)) ne RngInt then
	   return false, "Invalid coercion.";
       elif SequenceToSet(W) ne {1..m} then
	   if 0 notin W then
	       return false, "Invalid coercion.";
	   else
	       W1 := [ i : i in W | i ne 0 ];
	       if #W1 ne #SequenceToSet(W1) or
		   &or [ i notin {1..m} : i in W1 ] then
		   return false, "Invalid coercion.";
	       end if;
	   end if;
       end if;
       K := New(CryptKey);
       K`Parent := C;
       K`IsEnciphering := true;
       K`KeyString := W;
       return true, K;
   elif Type(W) eq SetIndx then
       if not assigned C`Domain or C`CipherType ne "Substitution" then
	   return false, "Invalid coercion";
       end if;
       m := #C`Domain;
       if m eq #W or m eq 0 then
	   K := New(CryptKey);
	   K`Parent := C;
	   K`IsEnciphering := true;
	   K`KeyString := W;
	   return true, K;
       end if;
   elif Type(W) eq Tup then
       if C`CipherType notin {"LFSR"} then
	   return false, "Invalid coercion.";
       end if;
       if Type(W[1]) ne RngUPolElt or Type(W[2]) ne SeqEnum
	   or Degree(W[1]) ne #W[2] then
	   return false, "Invalid coercion.";
       end if;
       K := New(CryptKey);
       K`Parent := C;
       K`IsEnciphering := true;
       K`KeyString := "";
       K`ConnectionPolynomial := W[1];
       K`InitialState := W[2];
       return true, K;
   end if;
   return false, "Invalid coercion.";
end intrinsic;

intrinsic RandomKey(C::Crypt) -> CryptKey
    {}
   if C`CipherType eq "Substitution" then
       if not assigned C`Domain then
	   K := RandomSubstitutionKey();
       else
	   S := C`Domain;
	   K := {@ @};
	   for i in [1..#S] do
	       c := Random(S);
	       Include(~K,c);
	       Exclude(~S,c);
	   end for;
       end if;
       return C!K;
   elif C`CipherType eq "Transposition" then
       require assigned C`BlockLength : "Attribute BlockLength must be " *
           "assigned to construct a random key.";
       m := C`BlockLength;
       I := [1..m];
       K := [];
       for i in [1..m] do
	   j := Random(I);
	   Exclude(~I,j);
	   Append(~K,j);
       end for;
       return C!K;
   elif C`CipherType eq "Vigenère" then
       require assigned C`BlockLength : "Attribute BlockLength must be " *
           "assigned to construct a random key.";
       return C!&cat[ Random(Alphabet) : i in [1..C`BlockLength] ];
   end if;
   require false : "No random key constructor for this cryptosystem.";
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                            PRINTING                                //
//                                                                    //
////////////////////////////////////////////////////////////////////////

intrinsic Print(C::Crypt, level::MonStgElt)
    {}
    printf C`CipherType cat " cryptosystem";
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                            EQUALITY                                //
//                                                                    //
////////////////////////////////////////////////////////////////////////

intrinsic 'eq'(C::Crypt,S::Crypt) -> BoolElt
    {}
    return C cmpeq S;
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//               ENCODING, ENCIPHERING AND DECIPHERING                //
//                                                                    //
////////////////////////////////////////////////////////////////////////

intrinsic Decoding(S::CryptTxt) -> MonStgElt
    {Given cryptographic text, return the associated decoded string.
    Note that certain alphabetic encodings used here are non-invertible,
    and the decoding does not give back the original message text.
    Also note that the decoding of ciphertext is still an enciphered
    string.  The encoding of the decoded cryptographic text will return 
    the original cryptographic text.}

    type := EncodingType(Cryptosystem(S));
    if type eq "Alphabetic" then
	return S`String;
    elif type eq "Binary" then
	return BitDecoding(S`String);
    elif type eq "RSA" then
	C := Cryptosystem(S);
	m := BlockLength(C);
	t := m-8;
	MS := S`String;
	// #MS div t???
	is_plaintext :=
	   &and [ &and [ 0 eq MS[i*m-8+j] : j in [1..8] ]
  	      : i in [1..#MS div t] ];
        require is_plaintext : "Argument is not valid plaintext.";
	DecStr := &cat[ MS[(i-1)*m+1..i*m-8] : i in [1..#MS div t] ];
	return BitDecoding(DecStr);
    end if;
    require false : "Unknown encoding type for cryptosystem.";
end intrinsic;

intrinsic Encoding(C::Crypt,M::MonStgElt) -> CryptTxt
    {Given a message text W, encode the message in the domain of 
    plaintext for the cryptosystem.}

    S := New(CryptTxt);
    S`Cryptosystem := C;
    S`IsPlainText := true;
    type := EncodingType(Cryptosystem(S));
    if type eq "Alphabetic" then
	if not assigned C`Domain then
	    S`String := StripEncoding(M : WildCharacter := "*");
	else
	    S`String := M;
	end if;
    elif type eq "RSA" then
	MS := BitEncoding(M);
	m := BlockLength(C);
	t := (m-8);
	MS cat:= [ GF(2) | 0 : i in [1..t - (#MS mod t)] ];
	Z := [ GF(2) | 0 : i in [1..8] ];
	MS := &cat[ MS[(i-1)*t+1..i*t] cat Z : i in [1..(#MS div t)] ];
	S`String := MS;
    else
	S`String := BitEncoding(M);
    end if;
    return S;
end intrinsic;

intrinsic Encoding(C::Crypt,W::[FldFinElt]) -> CryptTxt
    {Given a binary message text W, encode the message for
    the cryptosystem C.}

    require EncodingType(C) eq "Binary" :
        "Argument 1 must use binary encoding.";
    require Universe(W) eq GF(2) :
	"Argument 2 must be a binary sequence.";
    S := New(CryptTxt);
    S`Cryptosystem := C;
    S`String := W;
    return S;
end intrinsic;

/*
function SubstitutionEnciphering(K,PT)
    n := #PT;
    I := [ StringToCode(PT[i])-64 : i in [1..n] ];
    I := [ I[i] eq -22 select 27 else I[i] : i in [1..#I] ];
    K cat:= "*";
    return &cat[ I[i] eq -54 select "\n" else K[I[i]] : i in [1..n] ];
end function;
*/

function TranspositionEnciphering(K,PT)
    m := #K;
    N := #PT;
    k := N mod m;
    if k ne 0 then
	PT cat:= &cat[ Random(Alphabet) : i in [m-k] ];
    end if;
    CT := "";
    k := 0;
    while k+m le N do
	CT cat:= &cat[ K[i] eq 0 select "*"
           else PT[k+K[i]] : i in [1..m] ];
	k +:= m;
    end while;
    return CT;
end function;

/*
function HomophonicEnciphering(S,PT)
    m := #S;
    n := #PT;
    indx := [ StringToCode(PT[i])-64 : i in [1..n] ];
    return &cat[ indx[i] eq -54 select "\n"
                 else S[Random([1..m])][indx[i]] : i in [1..n] ];
end function;
*/

function VigenereEnciphering(K,PT)
    m := #K;
    n := #PT;
    indx := [ StringToCode(PT[i])-65 : i in [1..n] ];
    j := 1;
    X := "";
    for i in [1..n] do
	if indx[i] eq -55 then
	    /* Newline character is code 10. */ 
	    X cat:= "\n";
	else
	    k := StringToCode(K[((j-1) mod m)+1])-65;
	    if k eq -23 or indx[i] eq -23 then
   	        /* Character "*" is code 42. */
		X cat:= "*";
	    else
		X cat:= CodeToString(((indx[i] + k) mod 26)+65);
	    end if;
	    j +:= 1;
	end if;
    end for;
    return X;
end function;

function LFSREnciphering(K,PT)
    g := K`ConnectionPolynomial;
    IS := K`InitialState;
    n := #PT;
    KS := LFSRSequence(g,IS,n);
    return [ PT[i] + KS[i] : i in [1..n] ];
end function;

intrinsic Deciphering(K::CryptKey,CT::CryptTxt) -> MonStgElt
    {}
    C := Parent(K);
    require C eq Cryptosystem(CT) :
        "Arguments have incompatible cryptosystems.";
    if C`IsSymmetric then
	return Enciphering(InverseKey(K),CT);
    elif CipherType(C) eq "RSA" then
	CS := String(CT);
	MS := RSAEnciphering(K,CS);
	X := New(CryptTxt);
	X`Cryptosystem := C;
	X`IsPlainText := true;
	X`String := MS;
	return X;
    end if;
    require false : 
	"Parent of argument 1 must be a symmetric key cryptosystem.";
end intrinsic;

intrinsic Enciphering(K::CryptKey,M::CryptTxt) -> MonStgElt
    {}
    C := K`Parent;
    require C eq M`Cryptosystem :
        "Arguments have incompatible cryptosystems.";
    KS := K`KeyString;
    PT := M`String;
    if C`CipherType eq "Substitution" then
	if not assigned C`Domain then
	    CT := SubstitutionEnciphering(KS,PT : Encode := false);
	else
	    CT := SubstitutionEnciphering(C`Domain,KS,PT);
	end if;
	X := New(CryptTxt);
	X`Cryptosystem := C;
	X`IsPlainText := false;
	X`String := CT;
	return X;
    elif C`CipherType eq "Transposition" then
	CT := TranspositionEnciphering(KS,PT);
	X := New(CryptTxt);
	X`Cryptosystem := C;
	X`IsPlainText := false;
	X`String := CT;
	return X;
    elif C`CipherType eq "Vigenère" then
	CT := VigenereEnciphering(KS,PT);
	X := New(CryptTxt);
	X`Cryptosystem := C;
	X`IsPlainText := false;
	X`String := CT;
	return X;
    elif C`CipherType eq "LFSR" then
	CT := LFSREnciphering(K,PT);
	X := New(CryptTxt);
	X`Cryptosystem := C;
	X`IsPlainText := false;
	X`String := CT;
	return X;
    elif C`CipherType eq "RSA" then
	CT := RSAEnciphering(K,PT);
	X := New(CryptTxt);
	X`Cryptosystem := C;
	X`IsPlainText := false;
	X`String := CT;
	return X;
    end if;
    error "Enciphering algorithm unknown for this cryptosystem.";
end intrinsic;

/////////////////////////////////////////////////////////////////////////
//                                                                     //
//                         ATTRIBUTE ACCESS                            //
//                                                                     //
/////////////////////////////////////////////////////////////////////////

intrinsic CipherType(C::Crypt) -> MonStgElt
    {The string identifying the cryptographic algorithm of C.}
    return C`CipherType;
end intrinsic;

intrinsic BlockLength(C::Crypt) -> MonStgElt
    {The string identifying the cryptographic algorithm of C.}
    require assigned C`BlockLength :
       "Attribute BlockLength is not assigned for argument.";
    return C`BlockLength;
end intrinsic;

intrinsic DomainAlphabet(C::Crypt) -> SeqEnum
    {}
    type := EncodingType(C);
    if type eq "Binary" then
	return GF(2);
    elif type eq "Alphabetic" then
	return Alphabet;
    end if;
    require false : "Argument cryptosystem has unknown alphabet type.";
end intrinsic;

intrinsic CodomainAlphabet(C::Crypt) -> SeqEnum
    {}
    type := EncodingType(C);
    if type eq "Binary" then
	return GF(2);
    elif type eq "Alphabetic" then
	return Alphabet;
    end if;
    require false : "Argument cryptosystem has unknown alphabet type.";
end intrinsic;


