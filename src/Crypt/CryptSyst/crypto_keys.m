//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//                     ASSOCIATED KEYS OF CRYPTOSYSTEMS                     //
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

/*
We view a cryptosystem as a collection of ciphers (= an enciphering
and deciphering map pair), each of which is parametrized by a key or
key pair.  By equating the ciphers with the keys which parameterize
them, the cryptosystem keys are therefore *defined* as elements of
the cryptosystem.
*/

import "cryptosystems.m" : EncodingType;

////////////////////////////////////////////////////////////////////////
//                       ATTRIBUTION DECLARATIONS                     //
////////////////////////////////////////////////////////////////////////

declare attributes CryptKey :
    Parent,
    IsEnciphering,  // true or false (= Deciphering)
    KeyString,
    // For LFSR stream ciphers:
    ConnectionPolynomial,
    InitialState;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                            PRINTING                                //
//                                                                    //
////////////////////////////////////////////////////////////////////////

intrinsic Print(K::CryptKey, level::MonStgElt)
    {}
    if Parent(K)`CipherType eq "LFSR" then
	printf "<%o, %o>", K`ConnectionPolynomial,
	    &cat[ IntegerToString(ZZ!c) : c in K`InitialState ]
	        where ZZ := Integers();
    else
	printf "%o", K`KeyString;
    end if;
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                            EQUALITY                                //
//                                                                    //
////////////////////////////////////////////////////////////////////////

intrinsic 'eq'(C::CryptKey,S::CryptKey) -> BoolElt
    {}
    return C`Parent eq S`Parent and C`KeyString eq S`KeyString;
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                            PARENTS                                 //
//                                                                    //
////////////////////////////////////////////////////////////////////////

intrinsic Parent(K::CryptKey) -> Crypt
    {}
    return K`Parent;
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                         ATTRIBUTE ACCESS                           //
//                                                                    //
////////////////////////////////////////////////////////////////////////

intrinsic String(K::CryptKey) -> MonStgElt
    {The string -- (usually, but not always) of type MonStgElt --
    of the cryptogrphic key, otherwise the defining data.}
    return K`KeyString;
end intrinsic;

intrinsic InverseKey(K::CryptKey) -> CryptKey
    {The inverse key of a symmetric cryptosystem.}
    C := Parent(K);
    require C`IsSymmetric :
	"Parent of argument must be a symmetric key cryptosystem.";
    if C`CipherType eq "Substitution" then
	S := String(K);
	AZ := DomainAlphabet(C);
	return C!&cat[ i eq 0 select "*" else AZ[i] where
 	   i := Index(S,AZ[i]) : i in [1..#S] ];
    elif C`CipherType eq "Transposition" then
	P := K`KeyString; // = permutation sequence of integers
	m := #P;
	R := [ 0 : i in [1..m] ];
	for i in [1..m] do
	    R[P[i]] := i;
	end for;
	return C!R;
    elif C`CipherType eq "Vigenère" then
	S := String(K);
	AZ := DomainAlphabet(C);
	return C!&cat[
    	    n eq 0 select "*" else AZ[ n eq 1 select 1 else 28-n ]
	    where n := Index(AZ,S[i]) : i in [1..#S] ];
    elif C`CipherType eq "LFSR" then
	return K;
    end if;
    require false : "Unknown cryptosystem type.";
end intrinsic;
