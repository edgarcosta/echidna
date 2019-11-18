//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//        Copyright (C) 2015 David Kohel <David.Kohel@univ-amu.fr>          //
//                                                                          //
//  Distributed under the terms of the GNU General Public License (GPL)     //
//                                                                          //
//                  http://www.gnu.org/licenses/                            //
//                                                                          //
//        All rights granted to distribute under the GPL, version 2,        //
//          or (at your option) any later version of the license.           //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

//////////////////////////////////////////////////////////////////////////////
//                         ATTRIBUTE DECLARATIONS                           //
//////////////////////////////////////////////////////////////////////////////

declare verbose GalChar, 2;

declare type GalChar;

declare type GalCharAdd : GalChar;
declare type GalCharMult : GalChar;
declare attributes GalChar :
    CharacterType,
    BaseField,
    Codomain,
    Function;

declare attributes GalCharAdd : zeta;

declare attributes GalCharMult : Order, zeta;

//////////////////////////////////////////////////////////////////////////////
//                               PRINTING                                   //
//////////////////////////////////////////////////////////////////////////////

intrinsic Print(chi::GalChar, level::MonStgElt)
    {}
    printf "%o Galois character over %o", chi`CharacterType, chi`BaseField;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//                             CONSTRUCTORS                                 //
//////////////////////////////////////////////////////////////////////////////

intrinsic AdditiveCharacter(FF::FldFin : zeta := 0) -> GalCharAdd
    {}
    C := New(GalCharAdd);
    C`CharacterType := "Additive";
    C`BaseField := FF;
    p := Characteristic(FF);
    if zeta eq 0 then
        K<z> := CyclotomicField(p);
    else
        K := Parent(zeta);
        if Type(K) in {FldRe,FldCom} then
            eps := 10^-(Precision(K)-8);
            require Abs(zeta^p - 1) le eps : "Parameter zeta must have order " * Sprint(p) * ".";
        else
            require zeta^p eq 1 : "Parameter zeta must have order " * Sprint(p) * ".";
        end if;
        z := zeta;
    end if;
    C`Codomain := Parent(z);
    ZZ := IntegerRing();
    C`zeta := z;
    C`Function := func< x | z^(ZZ!Trace(x)) >;
    return C;
end intrinsic;

intrinsic MultiplicativeCharacter(FF::FldFin,m::RngIntElt : zeta := 0) -> GalCharMult
    {}
    require #FF mod m eq 1 :
        "Argument 2 must divide the order of the multiplicative group of argument 1.";
    C := New(GalCharMult);
    C`CharacterType := "Multiplicative";
    C`BaseField := FF;
    ZZ := IntegerRing();
    if zeta eq 0 then
        if m eq 1 then
            K := ZZ; z := 1;
        elif m eq 2 then
            K := ZZ; z := -1;
        elif m ne 1 then
            K<z> := CyclotomicField(m);
        end if;
    else
        K := Parent(zeta);
        if Type(K) in {FldRe,FldCom} then
            eps := 10^-(Precision(K)-8);
            require Abs(zeta^m - 1) le eps : "Parameter zeta must have order " * Sprint(m) * ".";
        else
            require zeta^m eq 1 : "Parameter zeta must have order " * Sprint(m) * ".";
        end if;
        K := Parent(zeta);
        z := zeta;
    end if;
    C`Codomain := K;
    C`Order := m;
    C`zeta := z;
    if m eq 1 then
        C`Function := func< x | x eq 0 select K!0 else K!1 >;
    elif m eq 2 then
        assert IsPrimeField(FF);
        p := Characteristic(FF);
        C`Function := func< x | KroneckerSymbol(ZZ!Norm(x),p) >;
    else
        r := (#FF - 1) div m;
        u := PrimitiveElement(FF)^r;
        C`Function := func< x | x eq 0 select K!0 else z^Log(u,Norm(x)^r) >;
    end if;
    return C;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//                             EVALUATIONS                                  //
//////////////////////////////////////////////////////////////////////////////

intrinsic '@'(x::FldFinElt,chi::GalChar) -> FldElt
    {}
    return chi`Function(x);
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//                           Character Sums                                 //
//////////////////////////////////////////////////////////////////////////////

intrinsic GaussSum(chi::GalCharMult,psi::GalCharAdd,FF::FldFin : zeta := 0) -> RngElt
    {Given a multiplicative character chi, an additive character psi,
    and finite field FF of characteristic p, returns the Gauss sum
    \sum chi(Nr(x))*psi(Tr(x)) in QQ(zeta) where zeta is a p-th root
    of unity. If the parameter zeta is not given, it is constructed
    as a generator of the cyclotomic field.}
    if Type(Codomain(chi)) notin {RngInt,FldRat} and
        Type(Codomain(psi)) notin {RngInt,FldRat} then
        require Codomain(chi) eq Codomain(psi) :
            "Arguments must have compatible codomains.";
    end if;
    return &+[ chi(x)*psi(x) : x in FF ];
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//                             Access Functions                            //
//////////////////////////////////////////////////////////////////////////////

intrinsic Codomain(chi::GalChar) -> Rng
    {The codomain of the Galois character.}
    return chi`Codomain;
end intrinsic;

intrinsic Order(chi::GalCharMult) -> RngIntElt
    {The order of the multiplicative Galois character.}
    return chi`Order;
end intrinsic;

intrinsic Order(psi::GalCharAdd) -> RngIntElt
    {The order of the additive Galois character.}
    return Characteristic(psi`BaseField);
end intrinsic;
