//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//        IGUSA INVARIANTS OF QUARTIC CM FIELDS, LIX REPRESENTATION         //
//                                                                          //
//          Copyright (C) 2006 David Kohel <kohel@maths.usyd.edu>           //
//                                                                          //
//  Distributed under the terms of the GNU General Public License (GPL)     //
//                                                                          //
//                  http://www.gnu.org/licenses/                            //
//                                                                          //
//        All rights granted to distribute under the GPL, version 2,        //
//          or (at your option) any later version of the license.           //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

DATDIR := GetEchidnaDatabaseRoot() * "/IgusaLIX/";
// These lengths should correspond to the quartic CM field database:
rdisc_len := 10;
trace_len := 6;
snorm_len := 8;
class_len := 6;
cond_len := 6;

//////////////////////////////////////////////////////////////////////////////

forward IgusaLIXDataFile, IgusaLIXWrite;
forward IsInIgusaLIXDomain, ExistsIgusaLIXDataFile;

//////////////////////////////////////////////////////////////////////////////
//                          CREATION FUNCTION                               //
//////////////////////////////////////////////////////////////////////////////

intrinsic IgusaLIXDatabase( : Overwrite := false) -> DBUser
    {The database of the Igusa LIX invariants.}
    Dat := HackobjCreateRaw(DBUser);
    Dat`DBIdentifier := "Igusa LIX";
    if Overwrite then
	procedure OverwriteFunction(K,X)
	    IgusaLIXWrite(K,X : Overwrite := true);
	end procedure;
	Dat`WriteFunction := OverwriteFunction;
    else
	Dat`WriteFunction := IgusaLIXWrite;
    end if;
    Dat`ExistsFunction := ExistsIgusaLIXDataFile;
    Dat`IsInDomainFunction := IsInIgusaLIXDomain;
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

function IsValidConductor(cond)
    if cond eq [] then
	return true;
    end if;
    if cond[1] le 1 then
	return false;
    end if;
    for i in [1..#cond-1] do
	if cond[i+1] lt 0 then
	    return false;
	end if;
	if cond[i+1] mod cond[i] ne 0 then
	    return false;
	end if;
    end for;
    return true;
end function;

//////////////////////////////////////////////////////////////////////////////
// EXISTENCE TESTS:
// These are access function which depend only on the existence of data files
// and which should remain in sync with the data for Igusa invariants which
// stored as IgusaScheme and IgusaField.
//////////////////////////////////////////////////////////////////////////////

intrinsic IgusaLIXRealSubfieldDiscriminants(Dat::DBUser) -> SeqEnum
    {The list of discriminants D such that some [D,A,B] is reresented in the database.}
    require Dat`DBIdentifier eq "Igusa LIX" : 
	"Argument must be the database of Igusa LIX invariants.";
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

intrinsic IgusaLIXQuarticCMFieldInvariants(Dat::DBUser) -> SeqEnum
    {The list of quartic CM field invariants [D,A,B] represented in the database.}
    require Dat`DBIdentifier eq "Igusa LIX" :
	"Argument must be the database of Igusa LIX invariants.";
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

intrinsic IgusaLIXQuarticCMFieldInvariants(Dat::DBUser,D::RngIntElt) -> SeqEnum
    {The list of quartic CM field invariants [D,A,B] represented in the database.}
    require Dat`DBIdentifier eq "Igusa LIX" :
	"Argument 1 must be the database of Igusa LIX invariants.";
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
// Igusa LIX read functions
//////////////////////////////////////////////////////////////////////////////

intrinsic IgusaLIXInvariants(
    Dat::DBUser,DAB::SeqEnum[RngIntElt],cond::SeqEnum[RngIntElt] : NormalizeSign := true) -> SeqEnum
    {}
    require Dat`DBIdentifier eq "Igusa LIX" : 
	"Argument 1 must be the database of Igusa LIX invariants.";
    bool, error_string := IsValidDAB(DAB,2); require bool : error_string;
    require IsValidConductor(cond) : "Argument 3 must be a valid conductor sequence.";
    return IgusaLIXInvariants(Dat,DAB : Conductor := cond, NormalizeSign := NormalizeSign);
end intrinsic;

intrinsic IgusaLIXInvariants(
    Dat::DBUser,DAB::SeqEnum[RngIntElt] : Conductor := [], NormalizeSign := true) -> SeqEnum
    {}
    require Dat`DBIdentifier eq "Igusa LIX" : 
	"Argument 1 must be the database of Igusa LIX invariants.";
    bool, error_string := IsValidDAB(DAB,2); require bool : error_string;
    require IsValidConductor(Conductor) : "Argument 3 must be a valid conductor sequence.";
    bool, filename := ExistsIgusaLIXDataFile(<DAB,Conductor>);
    require bool : "Argument 1 contains no data file for this number field and conductor.";
    // DATABASE FILE CONTENTS
    // 1. Number of orbits of invariants
    // 2. For each Galois invariant orbit:
    //    a. Degree of the CM orbit
    //    b. The first coefficient sequence, for H1
    //    c. For G2, G3,
    //       - the coefficient sequence for Gi
    //       - the denominator for Gi
    Rewrite := false;
    file := POpen("bunzip2 -c " * filename * " 2>/dev/null", "r");
    norb := StringToInteger(Gets(file));
    rels := {@ @};
    degs := [ IntegerRing() | ];
    for i in [1..norb] do
	deg := StringToInteger(Gets(file));
	H1_seq := [ IntegerRing() | ];
	rel := [ ];
	for s in [0..deg] do
	    Append(~H1_seq,StringToInteger(Gets(file)));
	end for;
        H1 := Polynomial(H1_seq);
        if NormalizeSign and LeadingCoefficient(H1) lt 0 then H1 *:= -1; Rewrite := true; end if;
        Append(~rel,<H1,1>);
	for j in [2,3] do
	    Gj := [ IntegerRing() | ];
	    for s in [0..deg-1] do
		Append(~Gj,StringToInteger(Gets(file)));
	    end for;
	    Nj := StringToInteger(Gets(file));
            Gj := Polynomial(Gj);
            if NormalizeSign and Nj lt 0 then Gj *:= -1; Nj *:= -1; Rewrite := true; end if;
            Append(~rel,<Gj,Nj>);
	end for;
	Include(~rels,rel);
	Append(~degs,deg);
    end for;
    delete file;
    if Rewrite then IgusaLIXWrite(<DAB,Conductor>,rels : Overwrite); end if;
    return rels, degs;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
// IgusaLIX writing function.
//////////////////////////////////////////////////////////////////////////////

procedure IgusaLIXWrite(X,rels : Overwrite := false);
    // Note that IsInIgusaDomain has verified that X is a valid quartic CM field,
    // defining polynomial, order, or DAB sequence.
    if Type(X) eq RngUPolElt then
	DAB := QuarticCMFieldInvariants(NumberField(X));
	cond := [IntegerRing()|];
    elif Type(X) eq FldNum then
	DAB := QuarticCMFieldInvariants(X);
	cond := [IntegerRing()|];
    elif Type(X) eq RngOrd then
	DAB := QuarticCMFieldInvariants(NumberField(X));
	cond := ConductorAbelianInvariants(X);
	D, A, B := Explode(DAB);
    elif Type(X) eq Tup then
	DAB := X[1];
	cond := X[2];
    else
	// DAB is an invariant sequence of 3 integers.
	DAB := X;
	cond := [IntegerRing()|];
    end if;
    error if not IsValidDAB(DAB,0), "Argument DAB (= " * Sprint(DAB) * " must be valid quartic CM field invariants.";
    error if not IsValidConductor(cond), "Argument cond (= " * Sprint(cond) * " must be valid conductor sequence.";
    D, A, B := Explode(DAB);
    // First check if rels is one equation sequence or a sequence of equations
    // sequences; in the former case we embed it as a sequence of sequences.
    if Type(Universe(rels)) eq SetCart then
        assert Type(rels[1][1]) eq RngUPolElt;
	assert Type(rels[1][2]) eq RngIntElt;
	rels := [ rels ];
    end if;
    degs := [ Degree(rel[1][1]) : rel in rels ];
    // Make sure that the Igusa relations are correctly normalized:
    for i in [1..#rels] do
        if LeadingCoefficient(rels[i][1][1]) lt 0 then
            rels[i][1][1] *:= -1;
        end if;
        for j in [2,3] do
            if rels[i][j][2] lt 0 then
                rels[i][j][1] *:= -1;
                rels[i][j][2] *:= -1;
            end if;
        end for;
    end for;
    // This writes the Igusa relations and their degree.
    filename := IgusaLIXDataFile(D,A,B : Conductor := cond);
    num_invs := 0;
    // TEST WHETHER YOU ARE ADDING ANY NEW INVARIANTS, OTHERWISE RETURN.
    DBIX := IgusaLIXDatabase();
    if not Overwrite and <DAB,cond> in DBIX then
	rels_pre, degs_pre := IgusaLIXInvariants(DBIX,[D,A,B],cond);
    else
	rels_pre := [];
	degs_pre := [];
    end if;
    num_invs := #rels_pre;
    // MERGE IN ANY NEW INVARIANTS IN rels.
    for k in [1..#rels] do
	rel := rels[k];
	deg := degs[k];
	l := 1;
	n := #rels_pre;
	while l le n+1 do
	    if l gt #rels_pre or deg gt degs_pre[l] then
		Include(~rels_pre,rel);
		Append(~degs_pre,deg);
	    elif deg eq degs_pre[l] then
		rel_pre := rels_pre[l];
		if &and[ rel[t] eq rel_pre[t] : t in [1..3] ] then
		    break;
		end if;
	    end if;
	    l +:= 1;
	end while;
    end for;
    rels := rels_pre;
    degs := degs_pre;
    // RETURN IF THERE IS NOTHING TO WRITE:
    if num_invs eq #rels then return; end if;
    DBCM := QuarticCMFieldDatabase();
    if not DAB in DBCM then
	K := QuarticCMField(DAB);
	Write(DBCM,K);
    end if;
    // DATABASE FILE CONTENTS
    // 1. Number of orbits of invariants
    // 2. For each Galois invariant orbit:
    //    a. Degree of the CM orbit
    //    b. The first coefficient sequence, for H1
    //    c. For G2, G3,
    //       - the coefficient sequence for Gi
    //       - the denominator for Gi
    // COMPARE TO ABOVE...
    file := Open(filename,"w"); Flush(file);
    Puts(file,Sprint(#rels));
    for i in [1..#rels] do
	Puts(file,Sprint(degs[i]));
	for c in Coefficients(rels[i][1][1]) do
	    Puts(file,Sprint(c));
	end for;
	for j in [2,3] do
	    Gj := rels[i][j][1];
            Nj := rels[i][j][2];
            if Nj lt 0 then Nj := -Nj; Gj := -Gj; end if;
	    Gj_cffs := Coefficients(Gj);
	    while #Gj_cffs lt degs[i] do Gj_cffs cat:= [ 0 ]; end while;
	    for c in Gj_cffs do
		Puts(file,Sprint(c));
	    end for;
	    Puts(file,Sprint(Nj));
	end for;
    end for;
    delete file;
    System("bzip2 -c " * filename * " > " * filename * "z" * "; wait");
    System("chmod a+r " * filename * "z");
    System("rm " * filename);
end procedure;

//////////////////////////////////////////////////////////////////////////////
// N.B. IgusaLIXFilename and IgusaSchemeFilename have the same definitions.
//////////////////////////////////////////////////////////////////////////////

function IgusaLIXFilename(D,A,B : Conductor := [])
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
    filename := &*[ dirpath, "igusa.", trace_str, ".", snorm_str, cond_str, ".db" ];
    return filename, dirpath;
end function;

function IsInIgusaLIXDomain(X)
    error_string := "Argument must an sequence of CM field invariants, a tuple of CM field invariants and conductor indices, a quartic CM field or its defining polynomial or an order therein.";
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
    elif Type(X) eq Tup and #X eq 2 then
	if &and[ ExtendedType(X[i]) ne SeqEnum[RngIntElt] : i in [1,2] ]or #X[1] ne 3 or #X[2] gt 3 then
   	    return false, error_string;
	end if;
    elif ExtendedType(X) ne SeqEnum[RngIntElt] or #X ne 3 then
	return false, error_string;
    end if;
    return true, "";
end function;

function ExistsIgusaLIXDataFile(X)
    // Returns true if and only if the compressed data file exists,
    // and if so, returns the file handle for reading.
    // assert &and[ m eq 1 : m in cond ];
    // 
    // Note that IsInIgusaDomain has verified that X is a valid quartic CM field,
    // defining polynomial, order, or DAB sequence.
    if Type(X) eq RngUPolElt then
	DAB := QuarticCMFieldInvariants(NumberField(X));
	cond := [IntegerRing()|]; 
    elif Type(X) eq FldNum then
	DAB := QuarticCMFieldInvariants(X);
	cond := [IntegerRing()|];
    elif Type(X) eq RngOrd then
	DAB := QuarticCMFieldInvariants(NumberField(X));
	cond := ConductorAbelianInvariants(X);
    elif Type(X) eq Tup then
	DAB := X[1];
	cond := X[2];
    else
	// X is an invariant sequence of 3 integers.
	DAB := X;
	cond := [IntegerRing()|];
    end if;
    D, A, B := Explode(DAB);
    filename, dirpath := IgusaLIXFilename(D,A,B : Conductor := cond);
    t := System("test -d " * dirpath);
    if t ne 0 then return false, filename * "z"; end if;
    t := System("test -f " * filename * "z");
    if t ne 0 then return false, filename * "z"; end if;
    return true, filename * "z";
end function;

function IgusaLIXDataFile(D,A,B : Conductor := [])
    filename, dirpath := IgusaLIXFilename(D,A,B : Conductor := Conductor);
    if System("test -d " * dirpath) ne 0 then
	System(&*[ "mkdir ", dirpath]);
	System(&*[ "chmod a+rx ", dirpath]);
    end if;
    System("touch " * filename);
    return filename;
end function;

//////////////////////////////////////////////////////////////////////////////
