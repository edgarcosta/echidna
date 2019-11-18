//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//                      ATKIN MODULAR FUNCTION DATABASE                     //
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
prefix := "ser";
level_length := 4;

//////////////////////////////////////////////////////////////////////////////

forward IsInAtkinModularFunctionDomain, ExistsAtkinModularFunctionDataFile;
forward AtkinModularFunctionDataFile, AtkinModularFunctionWrite;

//////////////////////////////////////////////////////////////////////////////
//                          CREATION FUNCTION                               //
//////////////////////////////////////////////////////////////////////////////

intrinsic AtkinModularFunctionDatabase() -> DBUser
    {The database of Atkin modular functions.}
    Dat := New(DBUser);
    Dat`DBIdentifier := "Atkin modular function";
    Dat`WriteFunction := AtkinModularFunctionWrite;
    Dat`ExistsFunction := ExistsAtkinModularFunctionDataFile;
    Dat`IsInDomainFunction := IsInAtkinModularFunctionDomain;
    return Dat;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//                           POWER SERIES ACCESS                            //
//////////////////////////////////////////////////////////////////////////////

intrinsic AtkinModularFunction(
    Dat::DBUser,N::RngIntElt) -> RngSerLaurElt
    {The power series which is a root of the Nth Atkin modular
    polynomial to the default precision.}

    require Dat`DBIdentifier eq "Atkin modular function" : 
	"Argument 1 must be a database of Atkin modular functions.";
    bool, filename := ExistsAtkinModularFunctionDataFile(N);
    require bool : "Argument 1 contains no datafile for this level.";
    file := POpen("bunzip2 -c " * filename, "r");   
    strseq := Gets(file);
    val, prec := Explode(StringToIntegerSequence(strseq));
    strseq := Gets(file);
    PS := LaurentSeriesRing(RationalField()); t := PS.1;
    f := PS!0;
    for i in [0..prec-1] do
	f +:= StringToInteger(strseq)*t^(val+i);
	strseq := Gets(file);
    end for;
    delete file;
    return f + O(t^(val+prec));
end intrinsic; 

intrinsic AtkinModularFunction(Dat::DBUser,N::RngIntElt,n::RngIntElt
    : Extend := false) -> RngSerLaurElt
    {The power series which is a root of the Nth Atkin modular
    polynomial, to precision n.}

    prec := n;
    require Dat`DBIdentifier eq "Atkin modular function" : 
	"Argument 1 must be a database of Atkin modular functions.";
    bool, filename := ExistsAtkinModularFunctionDataFile(N);
    if not bool and Extend then
	AtkinModularFunctionWrite(N,AtkinModularFunction(N,1));
	bool, filename := ExistsAtkinModularFunctionDataFile(N);
    end if;
    require bool : "Argument 1 contains no datafile for this level.";
    file := POpen("bunzip2 -c " * filename, "r");   
    strseq := Gets(file);
    val, rel := Explode(StringToIntegerSequence(strseq));
    if rel lt prec then
	require Extend :
	    "Atkin modular function is not known to precision " * IntegerToString(prec);
	delete file;
	prec_extend := Ceiling(prec/200)*200;
	BuildAtkinModularFunctionDatabase(Dat,[N],prec_extend);
	file := POpen("bunzip2 -c " * filename, "r");   
	strseq := Gets(file);
    end if;
    PS := LaurentSeriesRing(RationalField()); t := PS.1;
    f := PS!0;
    for i in [0..prec-1] do
	strseq := Gets(file);
	f +:= StringToInteger(strseq)*t^(val+i);
    end for;
    delete file;
    return f + O(t^(val+prec));
end intrinsic; 

intrinsic DatabasePrecision(Dat::DBUser,N::RngIntElt) -> RngIntElt
    {}
    require Dat`DBIdentifier eq "Atkin modular function" : 
	"Argument 1 must be a database of Atkin modular function.";
    bool, filename := ExistsAtkinModularFunctionDataFile(N);
    if not bool then return 0; end if; 
    file := POpen("bunzip2 -c " * filename, "r");   
    strseq := Gets(file);
    _, prec := Explode(StringToIntegerSequence(strseq));
    delete file;
    return prec;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//                             WRITE ACCESS                                 //
//////////////////////////////////////////////////////////////////////////////

procedure AtkinModularFunctionWrite(N,f)
    // {Write f to the Atkin modular function database.}
    ZZ := Integers();
    filename := AtkinModularFunctionDataFile(N);
    file := Open(filename,"w");   
    // Empty the contents of the file, in case it did exist.
    Flush(file);
    val := Valuation(f);
    rel := RelativePrecision(f);
    Puts(file, IntegerToString(val) * " " * IntegerToString(rel));
    for i in [0..rel-1] do
	Puts(file,IntegerToString(ZZ!Coefficient(f,val+i)));
    end for;
    delete file;
    System("bzip2 -c " * filename * " > " * filename * "z");
    System("chmod a+r " * filename * "z");
    System("rm " * filename);
end procedure;

//////////////////////////////////////////////////////////////////////////////
//                            FILE STRUCTURE                                //
//////////////////////////////////////////////////////////////////////////////

function AtkinModularFunctionFilename(N)
    level := IntegerToString(N);   
    while #level lt level_length do level := "0" cat level; end while;
    DIR := &*[ DATDIR, "Atk/" ];
    t := System("test -d " * DATDIR);
    if t ne 0 then System("mkdir " * DATDIR); end if;
    t := System("test -d " * DIR);
    if t ne 0 then System("mkdir " * DIR); end if;
    filename := &*[ DIR, prefix, ".", level, ".db" ];
    return filename;
end function;

function AtkinModularFunctionDataFile(N)
    filename := AtkinModularFunctionFilename(N);
    System("touch " * filename);
    return filename;
end function;

function IsInAtkinModularFunctionDomain(N)
    if Type(N) eq RngIntElt then
	return true, "";
    end if;
    return false, "Argument 1 must be an integer.";
end function;

function ExistsAtkinModularFunctionDataFile(N)
    // Returns true if and only if the compressed data file 
    // exists, and if so, returns the file handle for reading.
    filename := AtkinModularFunctionFilename(N);
    t := System("test -f " * filename * "z");
    if t ne 0 then return false, _; end if;
    return true, filename * "z";
end function;
