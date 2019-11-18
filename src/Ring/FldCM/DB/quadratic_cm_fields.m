//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//                         QUADRATIC CM FIELDS                              //
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

DATDIR := GetEchidnaDatabaseRoot() * "/FldCM/2/";
class_len := 6;
disc_length := 8;
prefix := "disc";
range := 10000;

//////////////////////////////////////////////////////////////////////////////

forward QuadraticCMOrderDataFile, QuadraticCMOrderWrite;
forward IsInQuadraticCMOrderDomain, ExistsQuadraticCMOrderDataFile;
forward QuadraticCMClassNumberDataFile, ExistsQuadraticCMClassNumberDataFile;

//////////////////////////////////////////////////////////////////////////////
//                          CREATION FUNCTION                               //
//////////////////////////////////////////////////////////////////////////////

intrinsic QuadraticCMFieldDatabase() -> DBUser
    {The database of quadratic CM [= imaginary quadratic] fields.}
    Dat := New(DBUser);
    Dat`DBIdentifier := "Quadratic CM fields";
    Dat`Invariant := 2;
    Dat`WriteFunction := QuadraticCMOrderWrite;
    Dat`ExistsFunction := ExistsQuadraticCMOrderDataFile;
    Dat`IsInDomainFunction := IsInQuadraticCMOrderDomain;
    return Dat;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
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

function IntegerSequenceToString(S)
    case #S:
    when 0:
	return "";
    when 1:
	return Sprint(S[1]);
    else
	return &*[ Sprint(n) * " " : n in S[1..#S-1] ] * Sprint(S[#S]);
    end case;
end function;

//////////////////////////////////////////////////////////////////////////////
// Access functions
//////////////////////////////////////////////////////////////////////////////

intrinsic QuadraticCMField(Dat::DBUser,D::RngIntElt) -> FldQuad
    {Given an integer D return the quadratic CM field K of discriminant D.
    The following fields are automatically assigned:
    
    K`IsCMField,
    K`QuadraticCMFieldInvariants,
    K`SexticCMFieldType,
    K`TotallyRealSubfield,
    K`CMFieldClassInvariants.}
    require Dat`DBIdentifier eq "Quadratic CM fields" : 
	"Argument 1 must be the database of quadratic CM fields.";
    require D lt 0 and D mod 4 in {0,1} : "Argument 2 is not a valid CM discriminant.";
    D := FundamentalDiscriminant(D);
    K := QuadraticField(D);
    K`IsCMField := true;
    K`QuadraticCMFieldInvariants := [D];
    K`TotallyRealSubfield := BaseField(K);
    K`CMFieldClassInvariants := QuadraticCMOrderClassInvariants(Dat,D);
    return K;
end intrinsic;

intrinsic QuadraticCMFieldClassNumber(Dat::DBUser,D::RngIntElt) -> SeqEnum
    {}
    require Dat`DBIdentifier eq "Quadratic CM fields" : 
	"Argument 1 must be the database of quadratic CM fields.";
    require D lt 0 and D mod 4 in {0,1} : "Argument 2 must be a valid CM discriminant.";
    require IsFundamental(D) : "Argument 2 must be a fundamental discriminant.";
    bool, filename, index := ExistsQuadraticCMOrderDataFile(D);
    require bool : "Argument 1 contains no data file for this discriminant.";
    file := POpen("bunzip2 -c " * filename, "r");
    for i in [1..index] do
	h_string := Gets(file);
    end for;
    delete file;
    h_invs := StringToIntegerSequence(h_string);
    require h_invs ne [ 0 ] : "Argument 1 contains no data for this discriminant.";
    return &*h_invs;
end intrinsic; 

intrinsic QuadraticCMOrderClassNumber(Dat::DBUser,D::RngIntElt) -> SeqEnum
    {}
    require Dat`DBIdentifier eq "Quadratic CM fields" : 
	"Argument 1 must be the database of quadratic CM fields.";
    require D lt 0 and D mod 4 in {0,1} : "Argument 2 must be a valid CM discriminant.";
    bool, filename, index := ExistsQuadraticCMOrderDataFile(D);
    require bool : "Argument 1 contains no data file for this discriminant.";
    file := POpen("bunzip2 -c " * filename, "r");
    for i in [1..index] do
	h_string := Gets(file);
    end for;
    delete file;
    h_invs := StringToIntegerSequence(h_string);
    require h_invs ne [ 0 ] : "Argument 1 contains no data for this discriminant.";
    return &*h_invs;
end intrinsic; 

intrinsic QuadraticCMFieldClassInvariants(Dat::DBUser,D::RngIntElt) -> SeqEnum
    {}
    require Dat`DBIdentifier eq "Quadratic CM fields" : 
	"Argument 1 must be the database of quadratic CM fields.";
    require D lt 0 and D mod 4 in {0,1} : "Argument 2 must be a valid CM discriminant.";
    require IsFundamental(D) : "Argument 2 must be a fundamental discriminant.";
    bool, filename, index := ExistsQuadraticCMOrderDataFile(D);
    require bool : "Argument 1 contains no data file for this discriminant.";
    file := POpen("bunzip2 -c " * filename, "r");
    for i in [1..index] do
	h_string := Gets(file);
    end for;
    delete file;
    h_invs := StringToIntegerSequence(h_string);
    require #h_invs ne 0 : "Argument 1 contains no data for this discriminant.";
    return h_invs;
end intrinsic; 

intrinsic QuadraticCMOrderClassInvariants(Dat::DBUser,D::RngIntElt) -> SeqEnum
    {}
    require Dat`DBIdentifier eq "Quadratic CM fields" : 
	"Argument 1 must be the database of quadratic CM fields.";
    require D lt 0 and D mod 4 in {0,1} : "Argument 2 must be a valid CM discriminant.";
    bool, filename, index := ExistsQuadraticCMOrderDataFile(D);
    require bool : "Argument 1 contains no data file for this discriminant.";
    file := POpen("bunzip2 -c " * filename, "r");
    for i in [1..index] do
	h_string := Gets(file);
    end for;
    delete file;
    h_invs := StringToIntegerSequence(h_string);
    require #h_invs ne 0 : "Argument 1 contains no data for this discriminant.";
    return h_invs;
end intrinsic; 

intrinsic QuadraticCMOrderDiscriminantsWithClassNumber(Dat::DBUser,h::RngIntElt) -> SeqEnum
    {The quadratic CM field invariants with class number h}
    require Dat`DBIdentifier eq "Quadratic CM fields" : 
	"Argument 1 must be the database of quadratic CM fields.";
    bool, filename := ExistsQuadraticCMClassNumberDataFile(h);
    if not bool then return [ ]; end if;
    Disc_list := [ ];
    file := POpen("bunzip2 -c " * filename, "r");
    DISC := Gets(file);
    while not IsEof(DISC) do
	D, c := Explode(StringToIntegerSequence(DISC));
	Append(~Disc_list,D);
	DISC := Gets(file);
    end while;
    return Disc_list;
end intrinsic;

intrinsic QuadraticCMFieldDiscriminantsWithClassNumber(Dat::DBUser,h::RngIntElt) -> SeqEnum
    {The quadratic CM field invariants with class number h}
    require Dat`DBIdentifier eq "Quadratic CM fields" : 
	"Argument 1 must be the database of quadratic CM fields.";
    bool, filename := ExistsQuadraticCMClassNumberDataFile(h);
    if not bool then return [ ]; end if;
    Disc_list := [ ];
    file := POpen("bunzip2 -c " * filename, "r");
    DISC := Gets(file);
    while not IsEof(DISC) do
	D, c := Explode(StringToIntegerSequence(DISC));
	if c eq 1 then
	    Append(~Disc_list,D);
	end if;
	DISC := Gets(file);
    end while;
    return Disc_list;
end intrinsic;

intrinsic QuadraticCMOrderDiscriminantsWithClassInvariants(
    Dat::DBUser,h_invs::[RngIntElt]) -> SeqEnum
    {The quadratic CM field discriminants with class invariants h_invs.}
    require Dat`DBIdentifier eq "Quadratic CM fields" : 
	"Argument 1 must be the database of quadratic CM fields.";
    n := #h_invs;
    if n eq 0 or h_invs[1] le 0 then
	require false : "Argument 2 must be a valid sequence of abelian invariants.";
    end if;
    for i in [1..n-1] do
	if h_invs[i+1] mod h_invs[i] ne 0 then
	    require false : "Argument 2 must be a valid sequence of abelian invariants.";
	end if;
    end for;
    h := &*h_invs;
    bool, filename := ExistsQuadraticCMClassNumberDataFile(h);
    if not bool then return [ ]; end if;
    file := POpen("bunzip2 -c " * filename, "r");
    Disc_list := [ ];
    DISC := Gets(file);
    while not IsEof(DISC) do
	DISC_seq := StringToIntegerSequence(DISC);
	D := DISC_seq[1];
	c := DISC_seq[2];
	h_invs1 := DISC_seq[[3..#DISC_seq]];
	if h_invs1 eq h_invs then 
	    Append(~Disc_list,D);
	end if;
	DISC := Gets(file);
    end while;
    return Disc_list;
end intrinsic;

intrinsic QuadraticCMFieldDiscriminantsWithClassInvariants(Dat::DBUser,h_invs::[RngIntElt]) -> SeqEnum
    {The quadratic CM field discriminants with class invariants h_invs.}
    require Dat`DBIdentifier eq "Quadratic CM fields" : 
	"Argument 1 must be the database of quadratic CM fields.";
    n := #h_invs;
    if n eq 0 or h_invs[1] le 0 then
	require false : "Argument 2 must be a valid sequence of abelian invariants.";
    end if;
    for i in [1..n-1] do
	if h_invs[i+1] mod h_invs[i] ne 0 then
	    require false : "Argument 2 must be a valid sequence of abelian invariants.";
	end if;
    end for;
    h := &*h_invs;
    bool, filename := ExistsQuadraticCMClassNumberDataFile(h);
    if not bool then return [ ]; end if;
    file := POpen("bunzip2 -c " * filename, "r");
    Disc_list := [ ];
    DISC := Gets(file);
    while not IsEof(DISC) do
	DISC_seq := StringToIntegerSequence(DISC);
	D := DISC_seq[1];
	c := DISC_seq[2];
	h_invs1 := DISC_seq[[3..#DISC_seq]];
	if c eq 1 and h_invs1 eq h_invs then 
	    Append(~Disc_list,D);
	end if;
	DISC := Gets(file);
    end while;
    return Disc_list;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//                FILE STRUCTURE FOR CLASS INVARIANTS                       //
//////////////////////////////////////////////////////////////////////////////

function QuadraticCMClassNumberFilename(h)
    class_str := pad_int(h, class_len);
    dirpath := DATDIR * "Class/";
    filename := &*[ dirpath, "class.", class_str, ".db" ];   
    return filename, dirpath;
end function;

function ExistsQuadraticCMClassNumberDataFile(h)
    filename, dirpath := QuadraticCMClassNumberFilename(h);
    t := System("test -d " * dirpath);
    if t ne 0 then return false, filename * "z"; end if;
    t := System("test -f " * filename * "z");
    if t ne 0 then return false, filename * "z"; end if;
    return true, filename * "z";
end function;

function QuadraticCMClassNumberDataFile(h)
    filename, dirpath := QuadraticCMClassNumberFilename(h);
    if System("test -d " * dirpath) ne 0 then
	System("mkdir " * dirpath);
    end if;
    System("touch " * filename);
    return filename;
end function;

procedure QuadraticCMClassInvariantsWrite(D,h_invs)
    h := &*h_invs;
    bool, filename := ExistsQuadraticCMClassNumberDataFile(h);
    DK := FundamentalDiscriminant(D); c := Isqrt(D div DK);
    if bool then 
        Class_invs := [];  
        file := POpen("bunzip2 -c " * filename, "r");
        Disc_line := Gets(file);
        while not IsEof(Disc_line) do
            Disc_seq := StringToIntegerSequence(Disc_line);
            if D gt Disc_seq[1] then
                Append(~Class_invs, [D, c] cat h_invs);
            elif Disc_seq[1] eq D then
                error if Disc_seq[3..#Disc_seq] ne h_invs,
                    Sprintf("Discriminant %o reports class invariants %o != %o",D, h_invs, Disc_seq[3..#Disc_seq]);
                return;
            end if;
            Append(~Class_invs, Disc_seq);
   	    Disc_line := Gets(file);
        end while;
        if D lt Disc_seq[1] then
            Append(~Class_invs, [D, c] cat h_invs);
        end if;
        delete file;
    else
        Class_invs := [ [D, c] cat h_invs ];  
    end if;
    filename := QuadraticCMClassNumberDataFile(D,h);
    file := Open(filename,"w"); 
    for Di in Class_invs do
	Puts(file,IntegerSequenceToString(Di));
    end for;
    delete file;
    System("bzip2 -c " * filename * " > " * filename * "z");
    System("chmod a+r " * filename * "z");
    System("rm " * filename);
end procedure;

//////////////////////////////////////////////////////////////////////////////
//                              FILE STRUCTURE                              //
//////////////////////////////////////////////////////////////////////////////

function DirectoryPath(N)
    dir_range := 100*range;
    N1 := dir_range*((N-1) div dir_range);
    D1 := IntegerToString(N1+1);
    D2 := IntegerToString(N1+dir_range);
    while #D1 lt disc_length do D1 := "0" cat D1; end while;
    while #D2 lt disc_length do D2 := "0" cat D2; end while;
    return &cat[ D1, "-", D2 ];    
end function;

function QuadraticCMOrderFilename(D)
    N1 := range*((Abs(D)-1) div range);
    D1 := IntegerToString(N1+1);
    D2 := IntegerToString(N1+range);
    while #D1 lt disc_length do D1 := "0" cat D1; end while;
    while #D2 lt disc_length do D2 := "0" cat D2; end while;
    dirpath := DATDIR cat DirectoryPath(Abs(D));
    filename := &cat[ dirpath, "/", prefix, ".", D1, "-", D2, ".db" ];
    index := ((Abs(D) - N1) div 2);
    return filename, dirpath, index;
end function;

function IsInQuadraticCMOrderDomain(K)
    case Type(K):
    when RngIntElt:
	if K gt 0 or K mod 4 notin {0,1} then
	    return false, "Argument must be a imaginary quadratic field, order, or discriminant.";
	end if;
    when FldQuad:
	if Discriminant(K) gt 0 then
	    return false, "Argument must be a imaginary quadratic field or order.";
	end if;
    when FldNum:
	if Degree(K) ne 2 or Discriminant(K) gt 0 then
	    return false, "Argument must be a imaginary quadratic field or order.";
	end if;
    when RngQuad:
	if Discriminant(K) gt 0 then
	    return false, "Argument must be a imaginary quadratic field or order.";
	end if;
    when RngOrd:
	if Degree(NumberField(K)) ne 2 or Discriminant(K) gt 0 then
	    return false, "Argument must be a imaginary quadratic field or order.";
	end if;
    else
	return false, "Argument must be a imaginary quadratic field or order.";
    end case;
    return true, "";
end function;

function ExistsQuadraticCMOrderDataFile(D)
    // Returns true if and only if the compressed data file 
    // exists, and if so, returns the filename for reading.
    filename, dirpath, index := QuadraticCMOrderFilename(D);
    t := System("test -d " * dirpath);
    if t ne 0 then return false, _, _; end if;
    t := System("test -f " * filename * "z");
    if t ne 0 then return false, _, _; end if;
    return true, filename * "z", index;
end function;

function QuadraticCMOrderDataFile(D)
    filename, dirpath, index := QuadraticCMOrderFilename(D);
    t := System("test -d " * dirpath);
    if t ne 0 then System("mkdir " * dirpath); end if;
    System("touch " * filename);
    return filename, index;
end function;

procedure QuadraticCMOrderWrite(D,h_invs) 
    /*
    // If we want just one argument K (field or ring):
    case Type(K):
    when {FldNum,FldQuad}:
        D := Discriminant(MaximalOrder(K));
    when {RngNum,RngQuad}:
        D := Discriminant(K);
    end case;
    h_invs := AbelianInvariants(ClassGroup(K));
    */
    bool, filename, index := ExistsQuadraticCMOrderDataFile(D);
    h := &*h_invs;
    if bool then 
        Class_list := [];  
        file := POpen("bunzip2 -c " * filename, "r");
        Class_line := Gets(file);
	while not IsEof(Class_line) do
	    Append(~Class_list,StringToIntegerSequence(Class_line));
	    Class_line := Gets(file);
	end while;
	delete file;
	// Ensure consistency:
	assert #Class_list eq range div 2;
    else
        Class_list := [ [ 0 ] : i in [1..range div 2] ];
    end if;
    if Class_list[index] ne [ 0 ] then
	printf "Warning: overwrite previous value of %o with %o for D = %o\n", Class_list[index], h_invs, D;
    end if;
    Class_list[index] := h_invs;
    filename, index := QuadraticCMOrderDataFile(D);
    file := Open(filename,"w"); Flush(file);
    for h_invs in Class_list do
	Puts(file,IntegerSequenceToString(h_invs));
    end for;
    delete file;
    System("bzip2 -c " * filename * " > " * filename * "z");
    System("chmod a+r " * filename * "z");
    System("rm " * filename);
end procedure;
