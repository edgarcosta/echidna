//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//                 PLAIN AND CIPHER TEXT OF CRYPTOSYSTEMS                   //
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
In lieu of differentiated string monoids, this gives a validity check
that a string belongs to the domain (of plaintext) or the codomain
(of ciphertext) of a cryptosystem.
*/

import "cryptosystems.m" : EncodingType;

////////////////////////////////////////////////////////////////////////
//                       ATTRIBUTION DECLARATIONS                     //
////////////////////////////////////////////////////////////////////////

declare type CryptTxt;

declare attributes CryptTxt :
    Cryptosystem,
    IsPlainText,  // true or false (= Deciphering)
    String;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                            PRINTING                                //
//                                                                    //
////////////////////////////////////////////////////////////////////////

intrinsic Print(T::CryptTxt, level::MonStgElt)
    {}
    C := T`Cryptosystem;
    if EncodingType(C) in {"Binary","RSA"} then
        ZZ := Integers();
	printf "%o", &cat[ IntegerToString(ZZ!c) : c in T`String ];
    else
	printf "%o", T`String;
    end if;
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                            EQUALITY                                //
//                                                                    //
////////////////////////////////////////////////////////////////////////

intrinsic 'eq'(C::CryptTxt,S::CryptTxt) -> BoolElt
    {}
    return C`Cryptosystem eq S`Cryptosystem and C`String eq S`String;
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                         ATTRIBUTE ACCESS                           //
//                                                                    //
////////////////////////////////////////////////////////////////////////

intrinsic Cryptosystem(W::CryptTxt) -> Crypt
    {The cryptosytem of W.}
    return W`Cryptosystem;
end intrinsic;

intrinsic String(K::CryptTxt) -> MonStgElt
    {The key string -- of type MonStgElt -- the cryptogrphic key.}
    return K`String;
end intrinsic;

intrinsic IsPlainText(W::CryptTxt) -> Crypt
    {Returns true if and only if W is plaintext.}
    return W`IsPlainText;
end intrinsic;

intrinsic IsCipherText(W::CryptTxt) -> Crypt
    {Returns true if and only if W is ciphertext.}
    return not W`IsPlainText;
end intrinsic;






