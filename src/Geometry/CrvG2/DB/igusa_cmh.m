//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//                  Genus 2 CM Interface to CMH                             //
//        Copyright (C) 2014 David Kohel <David.Kohel@univ-amu.fr>          //
//                                                                          //
//  Distributed under the terms of the GNU General Public License (GPL)     //
//                                                                          //
//                  http://www.gnu.org/licenses/                            //
//                                                                          //
//        All rights granted to distribute under the GPL, version 2,        //
//          or (at your option) any later version of the license.           //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

DATDIR := GetEchidnaDatabaseRoot() * "/IgusaCMH/";
// These lengths should correspond to the quartic CM field database:
rdisc_len := 10;
trace_len := 6;
snorm_len := 8;
class_len := 6;
cond_len := 6;

/*
Examples:

[ 101, 13, 17 ]:
Class number 3.

[ 29, 7, 5 ]:
Class number 2 but breaks into two orbits, only one is computed. 
*/

//////////////////////////////////////////////////////////////////////////////

forward IgusaCMHDataFile, IgusaCMHWrite;
forward IsValidDAB, IsInIgusaCMHDomain, ExistsIgusaCMHDataFile;

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

intrinsic BuildIgusaCMHDatabase(Dat::DBUser,DAB::[RngIntElt] :
    Conductor := [], InvariantType := 2, Overwrite := false,
    Checkpoints := false, Precision := 0)
    {}
    require Dat`DBIdentifier eq "Igusa CMH" : 
	"Argument 1 must be the database of Igusa CMH invariants.";
    require IsValidDAB(DAB,2) : "Argument 2 must be valid quartic CM invariants.";
    require Conductor eq [] : "Parameter \"Conductor\" must be [].";
    require InvariantType in {0,1,2} : "Parameter \"InvariantType\" must be in {0,1,2}.";
    if <DAB,Conductor,InvariantType> in Dat and not Overwrite then
        return;
    end if;
    D, A, B := Explode(DAB);
    Dstr := Sprint(D);
    Astr := Sprint(A);
    Bstr := Sprint(B);
    tmpDIR := "/tmp";
    inputGen := Sprintf("cmh-classpol.sh -o %o/ -p %o, %o", tmpDIR, Astr, Bstr);
    t := System(inputGen);
    require t eq 0 :
        "Quartic CM field class group data generation failed for DAB = " * Sprint(DAB) * ".";
    tmpFILE := tmpDIR * Sprintf("/%o_%o_%o",Dstr,Astr,Bstr);
    ARGS := "-j " * Sprint(InvariantType);
    if Checkpoints then
        chckDIR := Sprintf("%o_%o_%o",Dstr,Astr,Bstr);
    else
        ARGS *:= " --no-checkpoints";
    end if;
    if Precision ne 0 then
        ARGS *:= Sprintf(" -b %o", Precision);
    end if;
    ARGS *:= " 2>/dev/null";
    cmpolGen := Sprintf("cm2 -i %o.in -o %o.pol %o", tmpFILE, tmpFILE, ARGS);
    t := System(cmpolGen);
    require t eq 0 :
        "Igusa CMH polynomial generation failed for DAB = " * Sprint(DAB) * ".";
    filename := IgusaCMHDataFile(D,A,B :
        Conductor := Conductor, InvariantType := InvariantType);
    t := System("bzip2 -c " * tmpFILE * ".pol > " * filename * "z" * "; sleep 1");
    System("rm -f " * tmpFILE * ".gp.log");
    System("rm -f " * tmpFILE * ".in");
    if Checkpoints then
        System("rm -rf " * chckDIR);
    end if;
    System("rm -f " * tmpFILE * ".pol");
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//                          CREATION FUNCTION                               //
//////////////////////////////////////////////////////////////////////////////

intrinsic IgusaCMHDatabase( : Overwrite := false) -> DBUser
    {The database of the Igusa CMH invariants.}
    Dat := HackobjCreateRaw(DBUser);
    Dat`DBIdentifier := "Igusa CMH";
    if Overwrite then
	procedure OverwriteFunction(K,X)
	    IgusaCMHWrite(K,X : Overwrite := true);
	end procedure;
	Dat`WriteFunction := OverwriteFunction;
    else
	Dat`WriteFunction := IgusaCMHWrite;
    end if;
    Dat`ExistsFunction := ExistsIgusaCMHDataFile;
    Dat`IsInDomainFunction := IsInIgusaCMHDomain;
    return Dat;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////

function pad_int(n,r)
    if n lt 0 then
	return "-" * pad_int(-n,r-1);
    end if;
    s := Sprint(Abs(n));
    while #s lt r do
	s := "0" * s;
    end while;
    return s;
end function;

function IsValidDAB(DAB,i)
    if #DAB ne 3 then
	return false, Sprintf("Argument %o must be a sequence of three integers.",i);
    end if;
    D, A, B := Explode(DAB);
    bool := D mod 4 in {0,1} and D gt 1 and
	not IsSquare(D) and IsFundamental(D);
    if not bool then
	return bool,
	    Sprintf("Argument %o, element 1, must be a positive fundamental discriminant.",i);
    end if;
    D1 := A^2 - 4*B;
    if not A eq 0 and B lt 0 then
	bool := D1 mod D eq 0 and IsSquare(D1 div D);
	if not bool then
	    return bool,
		Sprintf("Argument %o, elements 2 and 3, are not valid.",i);
	end if;
    end if;
    return true, "";
end function;

//////////////////////////////////////////////////////////////////////////////
// EXISTENCE TESTS:
// These are access function which depend only on the existence of data files
// and which should remain in sync with the data for Igusa invariants which
// stored as IgusaScheme and IgusaField.
//////////////////////////////////////////////////////////////////////////////

intrinsic IgusaCMHRealSubfieldDiscriminants(Dat::DBUser) -> SeqEnum
    {The list of discriminants D such that some [D,A,B] is reresented in the database.}
    require Dat`DBIdentifier eq "Igusa CMH" : 
	"Argument must be the database of Igusa CMH invariants.";
    RMInvs := [ ];
    DIRS := POpen("ls -d " * DATDIR * "[0-9]*", "r");
    while true do
	dir := Gets(DIRS);
	if IsEof(dir) then break; end if;
	split_string := Split(dir,"/");
	Dstr := split_string[#split_string];
	D := StringToInteger(Dstr);
	Append(~RMInvs,D);
    end while;
    return RMInvs;
end intrinsic;

intrinsic IgusaCMHQuarticCMFieldInvariants(Dat::DBUser) -> SeqEnum
    {The list of quartic CM field invariants [D,A,B] represented in the database.}
    require Dat`DBIdentifier eq "Igusa CMH" :
	"Argument must be the database of Igusa CMH invariants.";
    DABInvs := [ ];
    FILES := POpen("ls " * DATDIR * "[0-9]*/igusa.*", "r");
    while true do
	file := Gets(FILES);
	if IsEof(file) then break; end if;
	split_string := Split(file,"/");
	Dstr := split_string[#split_string-1];
	igusa_string := split_string[#split_string];
	_, Astr, Bstr := Explode(Split(igusa_string,"."));
	D := StringToInteger(Dstr);
	A := StringToInteger(Astr);
	B := StringToInteger(Bstr);
	Append(~DABInvs,[D,A,B]);
    end while;
    return DABInvs;
end intrinsic;

intrinsic IgusaCMHQuarticCMFieldInvariants(Dat::DBUser,D::RngIntElt) -> SeqEnum
    {The list of quartic CM field invariants [D,A,B] represented in the database.}
    require Dat`DBIdentifier eq "Igusa CMH" :
	"Argument 1 must be the database of Igusa CMH invariants.";
    DABInvs := [ ];
    rdisc_str := pad_int(D, rdisc_len);
    dirpath := DATDIR * rdisc_str * "/";
    if System("test -d " * dirpath) ne 0 then
	return DABInvs;
    end if;
    FILES := POpen("ls " * dirpath * "igusa.*", "r");
    while true do
	file := Gets(FILES);
	if IsEof(file) then break; end if;
	split_string := Split(file,"/");
	igusa_string := split_string[#split_string];
	_, Astr, Bstr := Explode(Split(igusa_string,"."));
	A := StringToInteger(Astr);
	B := StringToInteger(Bstr);
	Append(~DABInvs,[D,A,B]);
    end while;
    return DABInvs;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

/*
**************** 2 - FORMAT OF THE CMH OUTPUT FILE *********************

Take for example the CM field defined by x^4+7*x^2+5.

The .pol file contains irreducible factors over the totally real subfield
K0r of the reflex field. In the dihedral case, we guarantee that only one
orbit under the Q-automorphism of K0r[x] is present. In the Galois case,
both polynomials are given for each orbit.

 1. 42006    : a version number
 2. 521 27 52: D,A,B invariants of the CM field K
 3. 13 54 521: [Dr,Ar,Br]
 4. 1        : (ntriples) number of polynomial triples in this file.
 5. 2        : Currently defined defaults are:
             [0] Goren-Lauter / van Wamelen (I2^5/I10,I2^3I4/I10,I2^2I6/I10)
             [1] Kohel I4I6/I10,I2^3I4/I10,I2^2I6/I10
             [2] Streng I4I6'/I10, I2I4^2/I10, I4^5/I10^2 (I6'=(I2I4-3I6)/2)
 6. 4 7      : nperiods, nclasses. This is not really useful. nclasses is equal to the degree of H1
 7. 0        : index of this polynomial triple. Starts at 0.
 8. 0        : index of the current polynomial. Starts at 0, then 1, then 2.
 9. 7        : Degree of the current polynomial (=nclasses for H1, =nclasses-1 for iH2 and iH3).
10.
  a) 2 2 1 101 2: factorization of the denominator.
  b) a0 b0    : integers for a0+b0*w (see above for what w is)
  ...      
11. 0 1 6    : iH2 of degree nclasses-1
12.
  a) 2 2 2 101 4 : factorization of the denominator. Same syntax as above.
  b) a0 b0 
  ...
*/

//////////////////////////////////////////////////////////////////////////////
// Igusa CMH read functions
//////////////////////////////////////////////////////////////////////////////

intrinsic IgusaCMHInvariants(Dat::DBUser,DAB::SeqEnum[RngIntElt],cond::SeqEnum[RngIntElt]) -> SeqEnum
    {The Igusa CMH invariants of conductor cond (= []) from the database.}
    require Dat`DBIdentifier eq "Igusa CMH" : 
	"Argument 1 must be the database of Igusa CMH invariants.";
    bool, error_string := IsValidDAB(DAB,2); require bool : error_string;
    require cond eq [] : "Argument 3 must be the conductor [].";
    return IgusaCMHInvariants(Dat,DAB : Conductor := cond);
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

intrinsic IgusaCMHInvariants(Dat::DBUser,DAB::SeqEnum[RngIntElt] :
    Filename := "", BZipped := true, InvariantType := 2,
    Conductor := [], RealSubringGenerator := 0) -> SeqEnum
    {The Igusa CMH invariants from the database.}
    require Dat`DBIdentifier eq "Igusa CMH" : 
	"Argument 1 must be the database of Igusa CMH invariants.";
    bool, error_string := IsValidDAB(DAB,2); require bool : error_string;
    require Conductor eq [] : "Parameter \"Conductor\" must be the conductor [].";
    require InvariantType in {0,1,2} : "Parameter \"InvariantType\" must be in {0,1,2}.";
    if Filename eq "" then
        bool, filename := ExistsIgusaCMHDataFile(<DAB,Conductor,InvariantType>);
    else
        filename := Filename; t := System("test -f " * filename); bool := t eq 0;
    end if;
    require bool : "Argument 1 contains no data file for this number field and conductor.";
    D := DAB[1]; d := D mod 4 eq 0 select D div 4 else D;
    DBCM := QuarticCMFieldDatabase();
    if QuarticCMFieldType(DBCM,DAB) eq [4] and false then
        assert false;
        Fr := IntegerRing(); w := 0;
        PF<x> := PolynomialRing(Fr);
        to_Fr := func< S | Fr!S[1] >;
    else
        DAB_r := QuarticCMReflexFieldInvariants(DBCM,DAB);
        Dr := DAB_r[1]; dr := Dr mod 4 eq 0 select Dr div 4 else Dr;
        if RealSubringGenerator cmpeq 0 then
            PZ<x> := PolynomialRing(IntegerRing());
            Fr<w> := QuadraticField(dr);
            PF<x> := PolynomialRing(Fr);
            to_Fr := func< S | Fr!S >;
        else
            w := RealSubringGenerator;
            require w^2 eq dr :
                "Parameter \"RealSubringGenerator\" must square to " * Sprint(dr) * ".";
            Fr := Parent(w);
            PF<x> := PolynomialRing(Fr);
            to_Fr := func< S | S[1] + S[2]*w >;
        end if;
    end if;
    if BZipped then
        file := POpen("bunzip2 -c " * filename * " 2>/dev/null", "r");
    else
        file := POpen("cat " * filename * " 2>/dev/null", "r");
    end if;
    _ := Gets(file); // 1. a version number
    _ := Gets(file); // 2. D, A, B
    DAB_r := StringToIntegerSequence(Gets(file)); // 3. Dr, Ar, Br
    norb := StringToInteger(Gets(file));  // 4. Number of orbits
    itype := StringToInteger(Gets(file)); // 5. Invariant type:
    if InvariantType eq 0 then
        require itype eq 0 : "Invariant type (= " * Sprint(itype) * ") must be 0.";
    elif InvariantType eq 1 then
        require itype eq 1 : "Invariant type (= " * Sprint(itype) * ") must be 1 (LIX).";
    elif InvariantType eq 2 then
        require itype eq 2 : "Invariant type (= " * Sprint(itype) * ") must be 2 (Streng).";
    end if;
    rels := {@ @};
    degs := [ IntegerRing() | ];
    for i in [1..norb] do
        _ := Gets(file); // 6. Num periods, poly degrees
        // "Triple index, polynomial index, degree:"
        next := Gets(file); // 7-8-9. Indices of triple and degree (= 0, 0, deg)
        if IsEof(next) then
            require false : 
                "Database file for DAB = " * Sprint(DAB) *
                " terminating with fewer than expected number of orbits";
            break;
        end if;
        idxi, idxj, deg := Explode(StringToIntegerSequence(next));
        require idxi eq i-1 and idxj eq 0 :
            "Database file for DAB = " * Sprint(DAB) *
            " has incorrect indices for polynomials.";
        N_fact := StringToIntegerSequence(Gets(file)); // 10. a) Factored denominator
        n := N_fact[1];
        if n eq 0 then
            N := 1;
        else
            N := &*[ N_fact[i]^N_fact[i+1] : i in [2..2*n by 2] ];
        end if;
	H1 := [ Fr | ];
	rel := [ ];
	for s in [0..deg] do
	    Append(~H1,to_Fr(StringToIntegerSequence(Gets(file))));
	end for;
	Append(~rel,<Polynomial(H1),N>);
	for j in [2,3] do
            next := Gets(file); // 11. i-1, j-1, Degree of polynomial = deg - 1
            idxi, idxj, degj := Explode(StringToIntegerSequence(next));
            require idxi eq i-1 and idxj eq j-1 and degj eq deg-1 :
                "Database file for DAB = " * Sprint(DAB) *
                " has incorrect indices for secondary polynomials.";
	    Nj_fact := StringToIntegerSequence(Gets(file));
            nj := Nj_fact[1];
            if nj eq 0 then
                Nj := 1;
            else
                Nj := &*[ Nj_fact[i]^Nj_fact[i+1] : i in [2..2*nj by 2] ];
            end if;
            Gj := [ Fr | ];
	    for s in [0..deg-1] do
		Append(~Gj,to_Fr(StringToIntegerSequence(Gets(file))));
	    end for;
	    Append(~rel,<Polynomial(Gj),Nj>);
	end for;
        Include(~rels,rel);
        Append(~degs,deg);
    end for;
    delete file;
    return rels, degs;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

function IgusaCMHFilename(D,A,B : Conductor := [], InvariantType := 2)
    rdisc_str := pad_int(D, rdisc_len);
    trace_str := pad_int(A, trace_len);
    snorm_str := pad_int(B, snorm_len);
    dirpath := DATDIR * rdisc_str * "/";
    if Conductor eq [] then
	cond_str := "";
    else
	cond_str := ".[";
	for i in [1..#Conductor-1] do
	    cond_str *:= pad_int(Conductor[i],cond_len) * ",";
	end for;
	cond_str *:= pad_int(Conductor[#Conductor],cond_len) * "]";
    end if;
    if InvariantType eq 2 then
        ext := ".db";
    else
        ext := "." * Sprint(InvariantType) * ".db";
    end if;
    filename := &*[ dirpath, "igusa.", trace_str, ".", snorm_str, cond_str, ext ];
    return filename, dirpath;
end function;

function IsInIgusaCMHDomain(X)
    error_string := "Argument must be a sequence of CM field invariants, a tuple of CM field invariants and conductor indices, a quartic CM field or its defining polynomial or an order therein.";
    if ExtendedType(X) eq RngUPolElt[RngInt] or
	ExtendedType(X) eq RngUPolElt[FldRat] then
	if not IsIrreducible(X) then
   	    return false, error_string;
	end if;
	K := NumberField(X);
	if Degree(K) ne 4 or not IsCMField(K) then
   	    return false, error_string;
	end if;
    elif Type(X) eq FldNum then
	if Degree(X) ne 4 or not IsCMField(X) then
   	    return false, error_string;
	end if;
    elif Type(X) eq RngOrd then
	K := NumberField(X);
	if Degree(K) ne 4 or not IsCMField(K) then
   	    return false, error_string;
	end if;
    elif Type(X) eq Tup and #X in {2,3} then
	if &and[ ExtendedType(X[i]) ne SeqEnum[RngIntElt] : i in [1,2] ]or #X[1] ne 3 or #X[2] gt 3 then
   	    return false, error_string;
	end if;
    elif ExtendedType(X) ne SeqEnum[RngIntElt] or #X ne 3 then
	return false, error_string;
    end if;
    return true, "";
end function;

function ExistsIgusaCMHDataFile(X)
    // Returns true if and only if the compressed data file exists,
    // and if so, returns the file handle for reading.
    // assert &and[ m eq 1 : m in cond ];
    // 
    // Note that IsInIgusaDomain has verified that X is a valid quartic CM field,
    // defining polynomial, order, or DAB sequence.
    if Type(X) eq RngUPolElt then
	DAB := QuarticCMFieldInvariants(NumberField(X));
	cond := [IntegerRing()|]; 
        invar_type := 2; 
    elif Type(X) eq FldNum then
	DAB := QuarticCMFieldInvariants(X);
	cond := [IntegerRing()|];
        invar_type := 2; 
    elif Type(X) eq RngOrd then
	DAB := QuarticCMFieldInvariants(NumberField(X));
	cond := ConductorAbelianInvariants(X);
        invar_type := 2; 
    elif Type(X) eq Tup then
	DAB := X[1];
	cond := X[2];
        if #X eq 3 then
            invar_type := X[3];
        else
            invar_type := 2;
        end if;
    elif ExtendedType(X) eq SeqEnum[RngIntElt] then
        if #X ne 3 then
            return false, "Unrecognized datafile descriptor.";
        end if;
	DAB := X;
	cond := [IntegerRing()|];
        invar_type := 2;
    else
        return false, "Unrecognized datafile descriptor.";
    end if;
    D, A, B := Explode(DAB);
    filename, dirpath := IgusaCMHFilename(D,A,B :
        Conductor := cond, InvariantType := invar_type);
    t := System("test -d " * dirpath);
    if t ne 0 then return false, filename * "z"; end if;
    t := System("test -f " * filename * "z");
    if t ne 0 then return false, filename * "z"; end if;
    t := System("test -s " * filename * "z");
    if t ne 0 then return false, filename * "z"; end if;
    return true, filename * "z";
end function;

function IgusaCMHDataFile(D,A,B : Conductor := [], InvariantType := 2)
    filename, dirpath := IgusaCMHFilename(D,A,B :
        Conductor := Conductor, InvariantType := InvariantType);
    if System("test -d " * dirpath) ne 0 then
	System(&*[ "mkdir ", dirpath]);
	System(&*[ "chmod a+rx ", dirpath]);
    end if;
    //System("touch " * filename);
    return filename;
end function;

