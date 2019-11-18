//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//                    J-INVARIANT POWER SERIES DATABASE                     //
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

/* Created by David Kohel, September 2001 */

DATDIR := GetEchidnaDatabaseRoot() * "/FncMod/";
prefix := "jinv";

forward jInvariantWrite;

//////////////////////////////////////////////////////////////////////////////
//                          CREATION FUNCTION                               //
//////////////////////////////////////////////////////////////////////////////

intrinsic jInvariantDatabase() -> DBUser
    {The database of the j-invariant power series.}
    Dat := New(DBUser);
    Dat`DBIdentifier := "j-Invariant";
    return Dat;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//                       J-INVARIANT SERIES ACCESS                          //
//////////////////////////////////////////////////////////////////////////////

intrinsic jInvariant(Dat::DBUser,R::Rng,N::RngIntElt
    : Extend := false) -> RngSerLaurElt
    {}
    require Dat`DBIdentifier eq "j-Invariant" : 
        "Argument 1 must be a database of j-invariant coefficients.";
    t := System("test -d " * DATDIR);
    if t ne 0 then System("mkdir " * DATDIR); end if;
    filename := DATDIR * prefix * ".dbz";
    t := System("test -f " * filename);
    if t ne 0 then
	q := LaurentSeriesRing(Integers()).1;
	jInvariantWrite(q^-1+744 + 196884*q+O(q^2));
    end if;
    file := POpen("bunzip2 -c " * filename, "r");   
    prec := Explode(StringToIntegerSequence(Gets(file)));
    if prec lt N then
	vprint ModularPolynomial: "...";
	vprint ModularPolynomial: "Database precision =", prec;
	vprint ModularPolynomial: "Extending...";
	delete file;
	if Extend then
	    I := [1..N];
	    modulus := 1;
	    log_modulus := 0;
	    char := PreviousPrime(Floor(2^29.5));
	    cffs := [ Integers() | 0 : i in I ];
	    stable := false;
	    tyme := Cputime();
	    while not stable do
		vprintf ModularPolynomial : "Computing j(q) mod %o\n", char;
		tyme := Cputime(); 
		K := FiniteField(char);
		PK := LaurentSeriesRing(K);
		t := PK.1; 
                j := jInvariant(t + O(t^N));
		pcffs := ChangeUniverse(Eltseq(j),Integers());
		while #pcffs lt N do Append(~pcffs,0); end while;
		ncffs := [ CRT([cffs[i],pcffs[i]],[modulus,char]) : i in I ];
                modulus *:= char;
		log_modulus +:= Log(char);
		log_current := Log(Max([Abs(c) : c in ncffs]));
		max_good := Min(
		   [ i : i in I | ncffs[i] ne cffs[i] ] cat [N+1])-1;
   	        if (log_current + 8) lt log_modulus or max_good eq N then
		    stable := true;
		    vprintf ModularPolynomial :
  		        "Terminating with %o coefficients stable " *
		        "and precision margin of %o\n", max_good,
		        RealField(8)!(log_modulus - log_current);
		else 
		    if (log_current + 1) lt log_modulus then
			vprintf ModularPolynomial :
			    "Continuing with %o coefficients stable " *
			    "and precision margin of %o\n", max_good,
			    RealField(8)!(log_modulus - log_current);
		    else
			vprintf ModularPolynomial :
			    "Continuing with %o coefficients stable.\n",
			    max_good;
		    end if;
		end if;
		cffs := ncffs;
		char := PreviousPrime(char); 
		vprintf ModularPolynomial :
		   "Total modular computation time = %o\n", Cputime(tyme);
	    end while;
	    PS := LaurentSeriesRing(Integers());
	    q := PS.1;
	    j := q^-1 * PS!cffs + O(q^(N-1));
	    Write(Dat,j);
	    return LaurentSeriesRing(R)!j;
	end if;
        require false :
            "j-invariant not represented in database " * 
            "to precision given by argument 3";
    end if;
    PS := LaurentSeriesRing(R);
    j := PS!0;
    q := PS.1;
    for i in [-1..N-2] do
	j +:= StringToInteger(strseq)*q^i where strseq := Gets(file);
    end for;
    delete file;
    return j + O(q^(N-1));
end intrinsic; 

intrinsic DatabasePrecision(Dat::DBUser) -> RngIntElt
    {}
    require Dat`DBIdentifier eq "j-Invariant" : 
        "Argument 1 must be a database of j-Invariant.";
    filename := DATDIR * prefix * ".dbz";
    file := POpen("bunzip2 -c " * filename, "r");   
    prec := Explode(StringToIntegerSequence(Gets(file)));
    delete file;
    return prec;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//                             WRITE ACCESS                                 //
//////////////////////////////////////////////////////////////////////////////

procedure jInvariantWrite(f)
    ZZ := Integers();
    filename := DATDIR * prefix * ".db";
    file := Open(filename,"w");   
    rel := RelativePrecision(f);
    Puts(file, IntegerToString(rel));
    for i in [0..rel-1] do
        Puts(file,IntegerToString(ZZ!Coefficient(f,i-1)));
    end for;
    delete file;
    System("bzip2 -c " * filename * " > " * filename * "z");
    System("chmod a+r " * filename * "z");
    System("rm " * filename);
end procedure;
