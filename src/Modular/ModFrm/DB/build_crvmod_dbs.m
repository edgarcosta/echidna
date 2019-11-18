//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//                    MODULAR POLYNOMIALS DATABASE                          //
//                                                                          //
//  Copyright (C) 2000-2007 David Kohel <kohel@maths.usyd.edu>              //
//                                                                          //
//  Distributed under the terms of the GNU General Public License (GPL)     //
//                                                                          //
//                  http://www.gnu.org/licenses/                            //
//                                                                          //
//        All rights granted to distribute under the GPL, version 2,        //
//          or (at your option) any later version of the license.           //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

intrinsic BuildClassicalModularPolynomialDatabase(Dat::DBUser,S::[RngIntElt])
    {Build the database of classical modular polynomials for N in S.}
    require Dat`DBIdentifier eq "Modular polynomial" :
        "Argument 1 must be the database of modular polynomials.";
    for N in S do
        if <"Classical",N> in Dat then continue; end if;
        Phi := ClassicalModularPolynomial(N :
            Database := false, Al := "Modular");
        Write(Dat,Phi,<"Classical",N> : Overwrite := true);
        print "Completed N =", N;
    end for;
end intrinsic;

intrinsic BuildDedekindEtaModularPolynomialDatabase(Dat::DBUser,S::[RngIntElt])
    {Build the database of Dedekind eta modular polynomials for N in S.}
    require Dat`DBIdentifier eq "Modular polynomial" :
        "Argument 1 must be the database of modular polynomials.";
    P2 := PolynomialRing(Integers(),2 : Global);
    for N in S do
        Phi := P2!DedekindEtaModularPolynomial(N);
        Write(Dat,Phi,<"Dedekind eta",N> : Overwrite := true);
        print "Completed N =", N;
    end for;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//               CANONICAL INVOLUTION DATABASE CONSTRUCTOR                  //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

intrinsic BuildModularPolynomialInvolutionDatabase(
    ModelType::MonStgElt,S::[RngIntElt])
    {}
    require ModelType in {"Atkin","Dedekind eta"} :
        "Argument 1 must be \"Atkin\" or \"Dedekind eta\".";
    DBME := ModularPolynomialDatabase();
    DBCI := ModularInvolutionDatabase();
    for N in S do
        if <ModelType,N> notin DBCI then
            require <ModelType,N> in DBME : 
                "Elements of argument 2 must specify objects" *
                "in the modular polynomials database.";
            printf "Computing involution of level %o.\n", N;
            num, den := ModularInvolution(ModelType,N : Al := "Modular");
            Write(DBCI,[num,den],<ModelType,N>);
        else
            printf "Already computed involution of level %o.\n", N;
        end if;
    end for;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//               MODULAR CORRESPONDENCE DATABASE CONSTRUCTOR                //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

intrinsic BuildModularPolynomialCorrespondenceDatabase(
    Dat::DBUser, ModelType::MonStgElt, N::RngIntElt, S::[RngIntElt] : 
    Overwrite := false)
    {Build the database of modular correspondences on X_0(N) for p in S.}
    require Dat`DBIdentifier eq "Modular correspondence" :
        "Argument 1 must be the database of modular correspondences.";
    require ModelType in {"Atkin","Dedekind eta"} : 
        "Argument 2 must be \"Atkin\" or \"Dedekind eta\".";
    if ModelType eq "Atkin" then
        require N in {2,3,5,7,11,13,17,19,23,29,31,41,47,59,71} : 
            "Argument 3 must in {2,3,5,7,11,13,17,19,23,29,31,41,47,59,71}.";
    else
        require N in {2,3,4,5,7,9,13,25} :
            "Argument 3 must in {2,3,4,5,7,9,13,25}.";
    end if;
    require &and[ IsPrime( p : Proof := false) : p in S ] :
        "Argument 4 must be a sequence of primes.";
    printf "Computing modular correspondences on X_0(%o).\n", N;
    PS := LaurentSeriesRing(Integers()); q := PS.1;
    if ModelType eq "Atkin" then
        prec := deg*(deg+3) where deg := Max(S)+1;
        if N in S then
            prec := Max(prec,deg*(deg+3)) where deg := 2*N;
        end if;
        DBAS := AtkinModularFunctionDatabase();
        f := AtkinModularFunction(DBAS,N,prec);
    elif ModelType eq "Dedekind eta" then
        prec := p^2+p+1 where p := Max(S);
        if N in S then prec := Max(prec,2*(N^2+N+1)); end if;
        f := CanonicalDedekind(PS,N,Max(N+1,prec)) + O(q^prec);
    end if;
    for p in S do
        if <ModelType,N,p> notin Dat or Overwrite then 
            print "Computing correspondence for p =", p;
            Phi := ModularCorrespondence(ModelType,N,p :
                Al := "Modular", ModularFunction := f,
                InitialModulus := 1024, IncrementModulus := true);
            Write(Dat,Phi,<ModelType,N,p> : Overwrite := true);
            print "  completed correspondence for p =", p;
        else
            print "Already computed correspondence for p =", p;
        end if;
    end for;
end intrinsic;

