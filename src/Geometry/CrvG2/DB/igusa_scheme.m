//////////////////////////////////////////////////////////////////////////////
//                                                                          // 
//            SCHEMES OF IGUSA INVARIANTS OF QUARTIC CM FIELDS              //
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

DATDIR := GetEchidnaDatabaseRoot() * "/IgusaSchCM/";
// These lengths should correspond to the quartic CM field database:
rdisc_len := 10;
trace_len := 6;
snorm_len := 8;
class_len := 6;

//////////////////////////////////////////////////////////////////////////////

forward IgusaSchemeDataFile, IgusaSchemeWrite;
forward IsInIgusaSchemeDomain, ExistsIgusaSchemeDataFile; 

//////////////////////////////////////////////////////////////////////////////
//                          CREATION FUNCTION                               //
//////////////////////////////////////////////////////////////////////////////

intrinsic IgusaSchemeDatabase() -> DBUser
    {The database of the Igusa schemes.}
    Dat := HackobjCreateRaw(DBUser);
    Dat`DBIdentifier := "Igusa scheme";
    Dat`WriteFunction := IgusaSchemeWrite;
    Dat`ExistsFunction := ExistsIgusaSchemeDataFile;
    Dat`IsInDomainFunction := IsInIgusaSchemeDomain;
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

//////////////////////////////////////////////////////////////////////////////

function IsValidDAB(DAB,i)
    if #DAB ne 3 then
        return false, Sprintf("Argument %o must be a sequence of three integers.",i);
    end if;
    D, A, B := Explode(DAB);
    bool := D mod 4 in {0,1} and D gt 1 and
        not IsSquare(D) and IsFundamental(D);
    if not bool then
	return bool, Sprintf("Argument %o, element 1, must be a positive fundamental discriminant.",i);
    end if;
    D1 := A^2 - 4*B;
    if not A eq 0 and B lt 0 then
        bool := D1 mod D eq 0 and IsSquare(D1 div D);
        if not bool then
            return bool, Sprintf("Argument %o, elements 2 and 3, are not valid.",i);
        end if;
    end if;
    return true, "";
end function;

//////////////////////////////////////////////////////////////////////////////

intrinsic IgusaSchemeInvariants(Dat::DBUser,DAB::SeqEnum[RngIntElt]) -> SeqEnum
    {}
    require Dat`DBIdentifier eq "Igusa scheme" : 
        "Argument 1 must be the database of Igusa schemes.";
    bool, error_string := IsValidDAB(DAB,2); require bool : error_string;
    bool, filename := ExistsIgusaSchemeDataFile(DAB);
    require bool : "Argument 1 contains no data file for this number field.";
    file := POpen("bunzip2 -c " * filename * " 2>/dev/null", "r");
    // DATABASE FILE CONTENTS
    // 1. Number of orbits of invariants
    // 2. Invariant entry:
    //    a. Degree of the CM orbit
    //    b. The relations seqeuence:
    //       The number of relations, followed by the relations 
    Pig := PolynomialRing(IntegerRing(),3 : Global);
    j1 := Pig.1; j2 := Pig.2; j4 := Pig.3; 
    norb := StringToInteger(Gets(file));
    degs := [ IntegerRing() | ];
    rels := [ [ Pig | ] : k in [1..norb] ];
    for r in [1..norb] do
        Append(~degs,StringToInteger(Gets(file)));
	nrel := StringToInteger(Gets(file));
	for s in [1..nrel] do
            rel := Pig!0;
	    nmon := StringToInteger(Gets(file));
            for t in [1..nmon] do
                i, j, k, c := Explode(StringToIntegerSequence(Gets(file)));
                rel +:= c*(j1^i*j2^j*j4^k);
            end for;
            Append(~rels[r],rel);
        end for;
    end for;
    delete file;
    return rels, degs;
end intrinsic; 

intrinsic IgusaSchemeRealSubfieldDiscriminants(Dat::DBUser) -> SeqEnum
    {The list of discriminants D such that some [D,A,B] is reresented in the database.}
    require Dat`DBIdentifier eq "Igusa scheme" :
	"Argument 1 must be the database of Igusa schemes.";
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

intrinsic IgusaSchemeQuarticCMFieldInvariants(Dat::DBUser) -> SeqEnum
    {The list of quartic CM field invariants [D,A,B] represented in the database.}
    require Dat`DBIdentifier eq "Igusa scheme" :
	"Argument 1 must be the database of Igusa schemes.";
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

intrinsic IgusaSchemeQuarticCMFieldInvariants(Dat::DBUser,D::RngIntElt) -> SeqEnum
    {The list of quartic CM field invariants [D,A,B] represented in the database.}
    require Dat`DBIdentifier eq "Igusa scheme" :
	"Argument 1 must be the database of Igusa schemes.";
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
// IgusaScheme writing function.
//////////////////////////////////////////////////////////////////////////////

procedure IgusaSchemeWrite(D,A,B,rels,degs)
    // First check if rels is one equation seequence or a sequence of equations
    // sequences; in the former case we embed it as a sequence of sequences. 
    if Type(Universe(rels)) eq RngMPol then
        assert Type(degs) eq RngIntElt;
        rels := [rels];
        degs := [degs];
    end if;
    // This writes the Igusa relations and their degree.
    filename := IgusaSchemeDataFile(D,A,B);
    num_invs := 0;
    // TEST WHETHER YOU ARE ADDING ANY NEW INVARIANTS, OTHERWISE RETURN.
    DBIS := IgusaSchemeDatabase(); 
    rels_pre, degs_pre := IgusaSchemeInvariants(DBIS,[D,A,B]);
    num_invs := #rels_pre;
    // MERGE IN ANY NEW INVARIANTS IN rels.
    for k in [1..#rels] do
	rel := rels[k];
	deg := degs[k];
	l := 1;
	while l le #rels_pre+1 do
	    if l gt #rels_pre or deg gt degs_pre[l] then
		Append(~rels_pre,rel);
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
    // DATABASE FILE CONTENTS
    // 1. Number of invariants
    // 2. Invariant entry:
    //    a. Degree of the CM orbit
    //    b. The relations seqeuence:
    //       The number of relations, followed by the relations 
    file := Open(filename,"w"); Flush(file);
    Puts(file,Sprint(#rels));
    for r in [1..#rels] do
        Puts(file,Sprint(degs[r]));
        Puts(file,Sprint(#rels[r]));
        for fnc in rels[r] do
            mons := Monomials(fnc);
            Puts(file,Sprint(#mons));
            for mon in Monomials(fnc) do
                i, j, k := Explode(Exponents(mon));
                monseq := [i,j,k] cat [ MonomialCoefficient(fnc,mon) ];
                Puts(file,&*[ IntegerToString(x) * " " : x in monseq ]);
            end for;
        end for;
    end for;
    delete file;
    System("bzip2 -c " * filename * " > " * filename * "z");
    System("chmod a+r " * filename * "z");
    System("rm " * filename);
end procedure;

function IgusaSchemeFilename(D,A,B)
    rdisc_str := pad_int(D, rdisc_len);
    trace_str := pad_int(A, trace_len);
    snorm_str := pad_int(B, snorm_len);
    dirpath := DATDIR * rdisc_str * "/";
    filename := &*[ dirpath, "igusa.", trace_str, ".", snorm_str, ".db" ];   
    return filename, dirpath;
end function;

function IsInIgusaSchemeDomain(X)
    if ExtendedType(X) ne SeqEnum[RngIntElt] or #X ne 3 then
	return false, "Argument must an sequence of CM field invariants.";
    end if;
    return true, "";
end function;

function ExistsIgusaSchemeDataFile(DAB)
    // Returns true if and only if the compressed data file exists,
    // and if so, returns the file handle for reading.
    // assert &and[ m eq 1 : m in cond ];
    D, A, B := Explode(DAB);
    filename, dirpath := IgusaSchemeFilename(D,A,B);
    t := System("test -d " * dirpath);
    if t ne 0 then return false, filename * "z"; end if;
    t := System("test -f " * filename * "z");
    if t ne 0 then return false, filename * "z"; end if;
    return true, filename * "z";
end function;

function IgusaSchemeDataFile(D,A,B)
    filename, dirpath := IgusaSchemeFilename(D,A,B);
    if System("test -d " * dirpath) ne 0 then
        System(&*[ "mkdir ", dirpath]);
    end if;
    System("touch " * filename);
    return filename;
end function;

//////////////////////////////////////////////////////////////////////////////
