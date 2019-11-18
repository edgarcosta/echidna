//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//                 CLASS POLYNOMIAL DATABASE CONSTRUCTOR                    //
//                                                                          // 
//         Copyright (C) 2009 David Kohel <kohel@iml.univ-mrs.fr>           //
//                                                                          //
//  Distributed under the terms of the GNU General Public License (GPL)     //
//                                                                          //
//                  http://www.gnu.org/licenses/                            //
//                                                                          //
//        All rights granted to distribute under the GPL, version 2,        //
//          or (at your option) any later version of the license.           //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

function DividesConductor(D,p)
    return not ((D mod p^2) ne 0
        or (p eq 2 and (D div p^2) mod 4 notin {0,1}));    
end function;

function IsValidClassPolynomial(f,p,B)
    for q in Primes([1..B]) do
        P := PolynomialRing(FiniteField(q));
        fac := Factorization(P!f);
        if &or[ Degree(g[1]) gt 2 : g in fac ] then
            return false;
        end if;
    end for;
    return true;
end function;

intrinsic BuildAtkinClassPolynomialDatabase(
    Dat::DBUser, p::RngIntElt, S::[RngIntElt] : ClassNumberBound := 0)
    {Build the database of Atkin class polynomials of
    level p for D in S.}
    
    require Dat`DBIdentifier eq "Class polynomial" :
        "Argument 1 must be the database of class polynomials.";
    require IsPrime(p : Proof := false) : 
        "Argument 2 must be a prime level.";
    print "Building database for prime p =", p;
    DBMP := ModularPolynomialDatabase();
    Phi := ModularPolynomial(DBMP,"Atkin", p);
    DBMF := AtkinModularFunctionDatabase();
    uu := AtkinModularFunction(DBMF,p);
    for D in S do
        require D lt 0 and D mod 4 in {0,1} :
            "Argument 3 must be a sequence of discriminants.";
        require KroneckerSymbol(FundamentalDiscriminant(D),p) ne -1
            and not DividesConductor(D,p) : 
            "Argument 3 must consist of discriminants of " *
            "quadratic orders in which argument 2 is split.";
        h := ClassNumberBound ne 0 select ClassNumber(D) else 0;
        if h le ClassNumberBound then
            tyme := Cputime();
            if <"Atkin",p,D> in Dat then
                printf "Discriminant %o already in database\n", D;
            else
                f := AtkinClassPolynomial(p,D :
                    AtkinModularFunction := uu,
                    AtkinModularPolynomial := Phi);
                assert IsValidClassPolynomial(f,p);
                Write(Dat,<"Atkin",p,D>,f : Overwrite := true);
                m := Isqrt(D div FundamentalDiscriminant(D));
                printf "Completed D = %o (m = %o, h(D) = %o) [%o secs]\n",
                    D, m, Degree(f), Cputime(tyme);
                print "Polynomial:";
                print f;
            end if;
        else
            printf "Class number %o for D = %o exceeds bound.\n", h, D;
        end if;
    end for;
end intrinsic;

intrinsic BuildDedekindEtaClassPolynomialDatabase(
    Dat::DBUser, p::RngIntElt, S::[RngIntElt] : ClassNumberBound := 0)
    {Build the database of class polynomials for the canonical 
    modular curve of level p, for all D in S.}
    
    require Dat`DBIdentifier eq "Class polynomial" :
        "Argument 1 must be the database of class polynomials.";
    require IsPrime(p : Proof := false) : 
        "Argument 2 must be a prime level.";
    print "Building database for prime p =", p;
    for D in S do
        require D lt 0 and D mod 4 in {0,1} :
            "Argument 3 must be a sequence of discriminants.";
        m := Isqrt(D div FundamentalDiscriminant(D));
        require KroneckerSymbol(D,p) ne -1 and m mod p ne 0 : 
            "Argument 3 must consist of discriminants of " *
            "quadratic orders in which argument 2 maximal " *
            "and not inert.";
        if <"Dedekind eta",p,D> notin Dat then
            h := ClassNumberBound ne 0 select ClassNumber(D) else 0;
            if h le ClassNumberBound then
                tyme := Cputime();
                f := DedekindEtaClassPolynomial(p,D);
                Write(Dat,<"Dedekind eta",p,D>,f : Overwrite := true);
                printf "Completed D = %o (m = %o, h(D) = %o) [%o secs]\n",
                    D, m, Degree(f), Cputime(tyme);
            else
                printf "Class number %o for D = %o exceeds bound.\n", h, D;
            end if;
        else
            printf "Discriminant %o already in database\n", D;
        end if;
    end for;
end intrinsic;

intrinsic BuildHilbertClassPolynomialDatabase(
    Dat::DBUser, S::[RngIntElt] : ClassNumberBound := 0)
    {Build the database of Hilbert class polynomials for D in S.}
    require Dat`DBIdentifier eq "Class polynomial" :
        "Argument 1 must be the database of class polynomials.";
    for D in S do
        require D lt 0 and D mod 4 in {0,1} : 
            "Argument 3 must be a sequence of discriminants.";
        if <"Hilbert",D> notin Dat then
            if ClassNumberBound ne 0 then
                h := ClassNumber(D);
            else
                h := 0;
            end if;
            if h le ClassNumberBound then
                tyme := Cputime();
                f := HilbertClassPolynomial(D);
                Write(Dat,<"Hilbert",D>,f : Overwrite := true);
                m := Isqrt(D div FundamentalDiscriminant(D));
                printf "Completed D = %o (m = %o, h(D) = %o) [%o secs]\n",
                    D, m, Degree(f), Cputime(tyme);
            else
                printf "Class number %o for D = %o exceeds bound.\n", h, D;
            end if;
        else
            printf "Discriminant %o already in database\n", D;
        end if;
    end for;
end intrinsic;

intrinsic BuildWeberClassPolynomialDatabase(
    Dat::DBUser, S::[RngIntElt] : ClassNumberBound := 0)
    {Build the database of Hilbert class polynomials for D in S.}
    require Dat`DBIdentifier eq "Class polynomial" :
        "Argument 1 must be the database of class polynomials.";
    for D in S do
        require D lt 0 and (D mod 4) in {0,1} : 
            "Argument 3 must be a sequence of negative discrimiants."; 
        require (D mod 8) eq 1: 
            "Argument 3 must consist of discriminants congruent to 1 mod 8.";
        if <"Weber",D> notin Dat then
            if ClassNumberBound ne 0 then
                h := ClassNumber(D);
            else
                h := 0;
            end if;
            if h le ClassNumberBound then
                tyme := Cputime();
                f := WeberClassPolynomial(D);
                Write(Dat,<"Weber",D>,f);
                m := Isqrt(D div FundamentalDiscriminant(D));
                printf "Completed D = %o (m = %o, h(D) = %o) [%o secs]\n",
                    D, m, Degree(f), Cputime(tyme);
            else
                printf "Class number %o for D = %o exceeds bound.\n", h, D;
            end if;
        else
            printf "Discriminant %o already in database\n", D;
        end if;
    end for;
end intrinsic;
