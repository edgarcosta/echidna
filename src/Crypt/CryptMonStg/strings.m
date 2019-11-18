//////////////////////////////////////////////////////////////////////////////
//        Conversions for Binary, Hexadecimal, and Radix-64 Strings         //
/////////////////////////////////////////////////////////////////////////////

Hex := "0123456789abcdef";
Radix64 := 
    "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";

intrinsic ASCIIToHexString(S::MonStgElt) -> MonStgElt
    {}
    return &*[ IntegerToHexString(StringToCode(S[i])) : i in [1..#S] ];
end intrinsic;

intrinsic BitStringToInteger(B::MonStgElt) -> RngIntElt
    {}
    n := #B;
    if n eq 0 then return 0; end if;
    // Big endian integer:
    return &+[ StringToInteger(B[i])*2^(n-i) : i in [1..n] ];
end intrinsic;

intrinsic IntegerToBitString(n::RngIntElt) -> MonStgElt
    {}
    if n eq 0 then return ""; end if;
    // Big endian bit string:
    bits := IntegerToSequence(n,2);
    return &*[ IntegerToString(b) : b in Reverse(bits) ];
end intrinsic;

intrinsic IntegerToHexString(n::RngIntElt) -> MonStgElt
    {}
    if n eq 0 then return ""; end if;
    // Big endian bit string:
    bits := IntegerToSequence(n,2);
    prty := (4 - (#bits mod 4)) mod 4;
    bits cat:= [ 0 : i in [1..prty] ];
    return BitStringToHexString(&*[ IntegerToString(b) : b in Reverse(bits) ]);
end intrinsic;

intrinsic IntegerToRadix64String(n::RngIntElt) -> MonStgElt
    {}
    if n eq 0 then return ""; end if;
    // Big endian bit string:
    bits := IntegerToSequence(n,2);
    prty := (6 - (#bits mod 6)) mod 6;
    bits cat:= [ 0 : i in [1..prty] ];
    return BitStringToRadix64String(&*[ IntegerToString(b) : b in Reverse(bits) ]);
end intrinsic;

intrinsic BitStringToHexString(B::MonStgElt) -> MonStgElt
    {}
    n := #B;
    require n mod 4 eq 0 : "Length of argument must be a multiple of four.";
    return &*[ Hex[BitStringToInteger(B[[4*i-3 ..4*i]])+1] : i in [1..n div 4] ];
end intrinsic;

intrinsic HexStringToBitString(B::MonStgElt) -> MonStgElt
    {}
    n := #B;
    if n eq 0 then return ""; end if;
    bits := [ ];  
    for i in [0..n-2] do
	kbits := IntegerToSequence(Index(Hex,B[n-i])-1,2);
	while #kbits lt 4 do
	    kbits := [ 0 ] cat kbits;
	end while;
	bits cat:= kbits;
    end for;
    bits cat:= IntegerToSequence(Index(Hex,B[1])-1,2);
    return &*[ IntegerToString(s) : s in Reverse(bits) ];
end intrinsic;

intrinsic BitStringToRadix64String(B::MonStgElt) -> MonStgElt
    {}
    n := #B;
    require n mod 6 eq 0 : "Length of argument must be a multiple of six.";
    return &*[ Radix64[BitStringToInteger(B[[6*i-5 ..6*i]])+1] : i in [1..n div 6] ];
end intrinsic;

intrinsic Radix64StringToBitString(C::MonStgElt) -> MonStgElt
    {}
    I := [ Index(Radix64,C[i])-1 : i in [1..#C] ];
    N := [ &+[ I[4*i+j]*64^(4-j) : j in [1..4] ] : i in [0..(#I div 4)-1] ];
    B := &cat[ Reverse(IntegerToSequence(N[i],2,24)) : i in [1..#N] ];
    return &cat[ &cat[ IntegerToString(B[8*i+j]) : j in [1..8] ] : 
       i in [0..(#B div 8)-1] ];
end intrinsic;

intrinsic Radix64ToOctetSequence(C::MonStgElt) -> SeqEnum
    {}
    require #C mod 4 eq 0 :
       "Length of argument must be a multiple of four.";
    I := [ Index(Radix64,C[i])-1 : i in [1..#C] ];
    N := [ &+[ I[4*i+j]*64^(4-j) : j in [1..4] ] : i in [0..(#I div 4)-1] ];
    B := &cat[ Reverse(IntegerToSequence(N[i],2,24)) : i in [1..#N] ];
    return [ &cat[ IntegerToString(B[8*i+j]) : j in [1..8] ] : 
       i in [0..(#B div 8)-1] ];
end intrinsic;

