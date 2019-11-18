//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//                       PUBLIC KEY CRYPTOSYSTEMS                           //
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

/* Created David Kohel, May 2000 */

ALPHABET := ["A","B","C","D","E","F","G","H","I","J","K","L","M",
             "N","O","P","Q","R","S","T","U","V","W","X","Y","Z"];

intrinsic RSACryptosystem(m::RngIntElt) -> Crypt
    {The RSA cryptosystem of block length m bits, and moduli
    bounded by m bits.}
    require m gt 0 : "Argument must be a positive integer.";
    require m mod 64 eq 0 : "Argument must be divisible by 64.";
    C := New(Crypt);
    C`IsSymmetric := false;
    C`CipherType := "RSA";
    C`BlockLength := m;
    return C;
end intrinsic;

function XCRT(A,M)
    a1 := A[1]; a2 := A[2]; m1 := M[1]; m2 := M[2];
    m0 := GCD(m1,m2); m1 div:= m0; m2 div:= m0;
    c0 := a1 mod m0;
    c1 := CRT([(a1-c0) div m0,(a2-c0) div m0],[m1,m2]);
    return c0 + c1*m0 mod (m0*m1*m2);
end function;

intrinsic RandomKeys(C::Crypt : Exponent := 0) -> CryptKey, CryptKey
    {Given an RSA cryptosystem, generates an RSA public-private key
    pair, with modulus bounded in bits by the block length of C.}
    require CipherType(C) eq "RSA" :
       "Argument 1 must be an RSA cryptosystem.";
    m := BlockLength(C);
    p := RandomPrime(m div 2 : Proof := false);
    while Exponent ne 0 and GCD(p-1,Exponent) ne 1 do
	p := RandomPrime(m div 2 : Proof := false);
    end while;
    q := RandomPrime(m div 2 : Proof := false);
    // Might have p = q for trivially small m:
    while (Exponent ne 0 and GCD(q-1,Exponent) ne 1) or q eq p do
       q := RandomPrime(m div 2 : Proof := false);
    end while;
    n := p*q;
    if Exponent eq 0 then
	e := Random(n);
	while GCD(e,p-1) ne 1 or GCD(e,q-1) ne 1 do
	    e := Random(n);
	end while;
    else
	e := Exponent;
    end if;
    // Compute the public enciphering key:
    K := New(CryptKey);
    K`Parent := C;
    K`IsEnciphering := true;
    K`KeyString := [e,n];
    // Compute the private deciphering key:
    f := XCRT([InverseMod(e,p-1),InverseMod(e,q-1)],[p-1,q-1]);
    L := New(CryptKey);
    L`Parent := C;
    L`IsEnciphering := false;
    L`KeyString := [f,n];
    return K, L;
end intrinsic;

intrinsic IsPublicPrivatePair(K::CryptKey,L::CryptKey) -> BoolElt
    {Given two RSA keys K and L, returns true if and only
    if the K and L are inverse keys.}
    C := Parent(K);
    require C eq Parent(L) :
       "Arguments must have the same parent cryptosystem.";
    require CipherType(C) eq "RSA" : "Arguments must be RSA keys.";
    e, n := Explode(K`KeyString);
    f, m := Explode(L`KeyString);
    if n ne m then return false; end if;
    return Modexp(2,e*f-1,n) eq 1 and Modexp(3,e*f-1,n) eq 1;
end intrinsic;

intrinsic RSAExponent(K::CryptKey) -> RngIntElt
    {}
    return String(K)[1];
end intrinsic;

intrinsic RSAModulus(K::CryptKey) -> RngIntElt
    {}
    return String(K)[2];
end intrinsic;

function BitsToInteger(S)
    S := ChangeUniverse(S,Integers());
    return &+[ S[i]*2^(i-1) : i in [1..#S] ];
end function;

function IntegerToBits(n,t)
    S := [ GF(2) | ];
    for i in [1..t] do
	Append(~S,n mod 2);
	n div:= 2;
    end for;
    return S;
end function;

function RSAEnciphering(K,MS)
    // INPUT: MS is the bit sequence of the message string.
    // OUTPUT: Ciphertext bit sequence CS. 
    C := Parent(K);
    m := BlockLength(C);
    e, n := Explode(String(K));
    CS := [ Integers() | ];
    error if not #MS mod m eq 0,
	"Block length must divide the length of an encoded bit sequence.";
    // This should be moved to the encoding algorithm.
    // MS cat:= [ GF(2)!0 : i in [1..((t-#MS) mod t)] ];
    max := #MS div m;
    for i in [1..max] do
	mi := BitsToInteger(MS[m*(i-1)+1..m*i]);
	error if mi gt n, "Integer represented by bit sequence " *
	    "must be bounded by the RSA modulus.";
        /*
	// This should be moved to the encoding algorithm.
	if i eq max then
	    h := 8*Ceiling(Log(256,mi));
	    k := Floor(Log(2,n));
	    if h+8 lt m then
		mi +:= &*[ Random({0,1})*2^i : i in [h+8..k] ];
	    end if;
	end if;
	*/
	ci := Modexp(mi,e,n);
	Append(~CS,ci);
    end for;
    return &cat[ IntegerToBits(ci,m) : ci in CS ];
end function;

