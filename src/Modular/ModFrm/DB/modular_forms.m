//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//                          MODULAR FORMS DATABASE                          //
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

/* Created by David Kohel, October 2001 */

DATDIR := GetEchidnaDatabaseRoot() * "/ModFrm/";
prefix := "frms";
level_length := 6;
weight_length := 2;

//////////////////////////////////////////////////////////////////////////////

forward ModularFormsDataFile, ModularFormsWrite;
forward IsInModularFormsDomain, ExistsModularFormsDataFile;

//////////////////////////////////////////////////////////////////////////////
//                          CREATION FUNCTION                               //
//////////////////////////////////////////////////////////////////////////////

intrinsic ModularFormsDatabase() -> DBUser
    {The database of modular curves.}
    Dat := New(DBUser);
    Dat`DBIdentifier := "Modular forms";
    Dat`WriteFunction := ModularFormsWrite;
    Dat`ExistsFunction := ExistsModularFormsDataFile;
    Dat`IsInDomainFunction := IsInModularFormsDomain;
    return Dat;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//                          MODULAR FORMS ACCESS                            //
//////////////////////////////////////////////////////////////////////////////

intrinsic ModularForms(Dat::DBUser,N::RngIntElt,k::RngIntElt,s::[RngIntElt]) -> SeqEnum
    {The modular forms on Gamma_0(N) of weight k, with signs
    s = [+/-1,...+/-1] under the Atkin-Lehner involutions.}

    require Dat`DBIdentifier eq "Modular forms" : 
	"Argument 1 must be a database of modular forms.";
    require N gt 1 :
	"Argument 2 must be an integer greater than 1."; 
    require k ge 0 and k mod 2 eq 0 :
	"Argument 3 must be a non-negative even integer."; 
    fac := Factorization(N);
    require &and[ e in {1,-1} : e in s ] and #s eq #fac : 
	"Argument 4 must be a sequence over {1,-1} of length equal to the number of prime divisors of argument 2.";
    bool, filename := ExistsModularFormsDataFile(<N,k,s>);
    require bool : "Argument 1 contains no datafile for this level.";
    PS<q> := PowerSeriesRing(RationalField() : Global := false);
    forms := [ PS | ];
    file := POpen("bunzip2 -c " * filename, "r");   
    num := StringToInteger(Gets(file));
    for i in [1..num] do
	val, prec := Explode(StringToIntegerSequence(Gets(file)));
	f := PS!0;
	for i in [0..prec-1] do
	    f +:= StringToInteger(Gets(file))*q^(val+i);
	end for;
	Append(~forms,f + O(q^(val+prec)));
    end for;
    delete file;
    return forms;
end intrinsic; 

intrinsic ModularForms(Dat::DBUser,N::RngIntElt,k::RngIntElt,s::[RngIntElt],n::RngIntElt) -> SeqEnum
    {The modular forms on Gamma_0(N) of weight k, with signs
    s = [+/-1,...+/-1] under the Atkin-Lehner involutions to
    precision n.}

    prec := n;
    require Dat`DBIdentifier eq "Modular forms" : 
	"Argument 1 must be a database of modular forms.";
    require N gt 1 :
	"Argument 2 must be an integer greater than 1."; 
    require k ge 0 and k mod 2 eq 0 :
	"Argument 3 must be a non-negative even integer."; 
    fac := Factorization(N);
    require &and[ e in {1,-1} : e in s ] and #s eq #fac : 
	"Argument 4 must be a sequence of length equal to the " * 
	"number of prime divisors of argument 2.";
    bool, filename := ExistsModularFormsDataFile(<N,k,s>);
    require bool : "Argument 1 contains no datafile for this level.";
    PS<q> := PowerSeriesRing(RationalField() : Global := false);
    forms := [ PS | ];
    file := POpen("bunzip2 -c " * filename, "r");   
    num := StringToInteger(Gets(file));
    for i in [1..num] do
	val, rel := Explode(StringToIntegerSequence(Gets(file)));
	require rel ge prec :
	    "Database entry not determined to requested precision.";
	f := PS!0;
	for i in [0..rel-1] do
	    f +:= StringToInteger(Gets(file))*q^(val+i);
	end for;
	Append(~forms,f + O(q^(val+prec)));
    end for;
    delete file;
    return forms;
end intrinsic; 

intrinsic ModularFormsPrecision(
    Dat::DBUser,N::RngIntElt,k::RngIntElt,s::[RngIntElt]) -> SeqEnum
    {The database precision of modular forms on Gamma_0(N) of weight k, 
    and signs s = [+/-1,...+/-1] under the Atkin-Lehner involutions.}

    require Dat`DBIdentifier eq "Modular forms" : 
	"Argument 1 must be a database of modular forms.";
    require N gt 1 :
	"Argument 2 must be an integer greater than 1."; 
    require k ge 0 and k mod 2 eq 0 :
	"Argument 3 must be a non-negative even integer."; 
    n := #PrimeDivisors(N);
    require &and[ e in {1,-1} : e in s ] and #s eq n : 
	"Argument 4 must be a sequence of length equal to the number of prime divisors of argument 2.";
    bool, filename := ExistsModularFormsDataFile(<N,k,s>);
    require bool : "Argument 1 contains no datafile for this level.";
    file := POpen("bunzip2 -c " * filename, "r");   
    num := StringToInteger(Gets(file));
    if num eq 0 then
	rel := Infinity();
    else
	_, rel := Explode(StringToIntegerSequence(Gets(file)));
    end if;
    delete file;
    return rel+1;
end intrinsic; 

//////////////////////////////////////////////////////////////////////////////
//                             WRITE ACCESS                                 //
//////////////////////////////////////////////////////////////////////////////

procedure ModularFormsWrite(X,B)
    // Write the sequence F of forms of level N, signs sequence S, and
    // weight k to the modular forms database.
    ZZ := IntegerRing();
    if Type(X) ne Tup or #X ne 3 then
	error if true, "Argument 2 must be a tuple of 3 elements.";
    end if;
    N := X[1]; k := X[2]; s := X[3];
    filename := ModularFormsDataFile(N,k,s);
    file := Open(filename,"w");   
    // Empty the contents of the file, in case it did exist.
    Flush(file);
    // Write the number of forms we are going to write:
    Puts(file, IntegerToString(#B));
    for f in B do
	val := Valuation(f);
	rel := RelativePrecision(f);
	Puts(file, IntegerToString(val) * " " * IntegerToString(rel));
	den := LCM([ Denominator(c) : c in Eltseq(f) ]);
	for i in [0..rel-1] do
	    Puts(file,IntegerToString(ZZ!(den*Coefficient(f,val+i))));
	end for;
    end for;
    // Close
    delete file;
    // and compress it:
    System("bzip2 -c " * filename * " > " * filename * "z");
    System("chmod a+r " * filename * "z");
    System("rm " * filename);
end procedure;

//////////////////////////////////////////////////////////////////////////////
//                            FILE STRUCTURE                                //
//////////////////////////////////////////////////////////////////////////////

function ModularFormsFilename(N,k,s)
    level := IntegerToString(N);   
    while #level lt level_length do
	level := "0" cat level;
    end while;
    weight := IntegerToString(k);   
    while #weight lt weight_length do
	weight := "0" cat weight;
    end while;
    signs := &cat[ e eq 1 select "0" else "1" : e in s ];
    // Could use "+" and "-" ...
    // signs := &cat[ e eq 1 select "+" else "-" : e in s ];
    dirname := DATDIR * level * "/";
    filename := &*[ dirname, prefix, ".", weight, ".", signs, ".db" ];
    return filename, dirname;
end function;

function ModularFormsDataFile(N,k,s)
    filename, dirname := ModularFormsFilename(N,k,s);
    t := System("test -d " * dirname);
    if t ne 0 then System("mkdir " * dirname); end if;
    System("touch " * filename);
    return filename;
end function;

function IsInModularFormsDomain(X)
    if Type(X) ne Tup or #X ne 3 then
	return false, "Argument must be a tuple of length 3";
    end if;
    N := X[1];
    if Type(N) ne RngIntElt or N le 0 then
	return false, "Argument component 1 must be a positive integer.";
    end if;
    k := X[2];
    if Type(k) ne RngIntElt or k le 0 or k mod 2 ne 0 then
	return false, "Argument component 2 must be an even positive integer.";
    end if;
    s := X[3];
    fac := Factorization(N);
    if Type(s) ne SeqEnum or Type(Universe(s)) ne RngInt
	or #s ne #fac or &or[ e notin {1,-1} : e in s ] then
	return false, "Argument component 3 must be a sequence of length " *
	    "equal to the number of prime divisors of component 2.";
    end if;
    return true, "";
end function;

function ExistsModularFormsDataFile(X)
    // Returns true if and only if the compressed data file 
    // exists, and if so, returns the file handle for reading.
    N := X[1]; k := X[2]; s := X[3];
    filename, dirname := ModularFormsFilename(N,k,s);
    t := System("test -d " * dirname);
    if t ne 0 then return false, _; end if;
    t := System("test -f " * filename * "z");
    if t ne 0 then return false, _; end if;
    return true, filename * "z";
end function;
