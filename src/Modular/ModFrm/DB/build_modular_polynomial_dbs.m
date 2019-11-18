//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//                      MODULAR POLYNOMIALS DATABASE                        //
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

forward ModularPolynomialCRT;

function BalancedMod(a,m)
    t := m div 2;
    a mod:= m;
    if a le t then return a;
    else return a-m;
    end if;
end function;

intrinsic BuildModularPolynomialDatabase(
    Dat::DBUser, ModelType::MonStgElt, S::[RngIntElt] : Al := "Global", InitialPrime := 0)
    {Build the database of modular equations for N in S.}
    require Dat`DBIdentifier eq "Modular polynomial" :
        "Argument 1 must be the database of modular polynomials.";
    require ModelType in {"Atkin", "Classical", "Reduced classical", "Dedekind eta", "Reduced Dedekind eta"} :
        "Argument 2 must be one of \"Atkin\", \"Classical\", \"Reduced Classical\", \"Dedekind eta\", or \"Reduced Dedekind eta\".";
    require Al in {"Global", "Local", "Modular"} :
        "Parameter Al must be one of \"Global\", \"Local\", or \"Modular\"";
    for N in S do
	if <ModelType,N> in Dat then continue; end if;
	vprint ModularPolynomial : "Computing modular polynomial database of level =", N;
	if Al in {"Modular","Local"} then
	    Phi := ModularPolynomial(Dat, ModelType, N : Al := Al, InitialPrime := InitialPrime, Extend := true);
	else
	    // This will actually use a "Modular" algorithm (in most cases)
	    // but does not build or use the local database in a modular
	    // reconstruction.
	    case ModelType:
	    when "Atkin":
		Phi := AtkinModularPolynomial(N);
	    when "Classical":
		Phi := ClassicalModularPolynomial(N);
	    when "Reduced classical":
		Phi := ReducedClassicalModularPolynomial(N);
	    when "Dedekind eta":
		Phi := DedekindEtaModularPolynomial(N);
	    when "Reduced Dedekind eta":
		Phi := ReducedDedekindEtaModularPolynomial(3,N);
	    else
		require false :
		    "Argument 2 must be one of \"Atkin\", \"Classical\", \"Reduced Classical\", \"Dedekind eta\", or \"Reduced Dedekind eta\".";
	    end case;
	end if;
	Write(Dat,<ModelType,N>,Phi);
    end for;
end intrinsic;

intrinsic BuildLocalModularPolynomialDatabase(
    Dat::DBUser, ModelType::MonStgElt, N::RngIntElt, S::[RngIntElt])
    {Build the database of mod p modular equations of level N for p in S.}
    require Dat`DBIdentifier eq "Modular polynomial" :
        "Argument 1 must be the database of modular polynomials.";
    require ModelType in {"Atkin", "Classical", "Reduced classical", "Dedekind eta", "Reduced Dedekind eta"} :
        "Argument 2 must be one of \"Atkin\", \"Classical\", \"Reduced Classical\", \"Dedekind eta\", or \"Reduced Dedekind eta\".";
    /*
    // For testing purposes, I don't want to use the global database,
    // but if this does exist then the specializations are determined.
    if <ModelType,N> in Dat then
	printf "%o modular equation of level %o already in database.\n", ModelType, N;
	return;
    end if;
    */
    vprint ModularPolynomial : "Computing local modular polynomial database of level =", N;
    for q in S do
	bool, p, m := IsPrimePower(q : Proof := false);
	require bool : "Argument 4 must consist of primes.";
	if N eq p then continue; end if;
	if <ModelType,N,q> in Dat then continue; end if;
	vprintf ModularPolynomial : "Modular prime power = %o^%o\n", p, m;
	if m eq 1 then
	    FF := FiniteField(p);
	else
	    FF := pAdicQuotientRing(p,m);
	end if;
	case ModelType:
	when "Atkin":
	    Phi := AtkinModularPolynomial(N,FF);
	when "Classical":
	    Phi := ClassicalModularPolynomial(N,FF);
	when "Reduced classical":
	    Phi := ReducedClassicalModularPolynomial(N,FF);
	when "Dedekind eta":
	    Phi := DedekindEtaModularPolynomial(N,FF);
	when "Reduced Dedekind eta":
	    Phi := ReducedDedekindEtaModularPolynomial(3,N,FF);
	end case;
	Write(Dat,<ModelType,N>,Phi : Overwrite);
    end for;
end intrinsic;

