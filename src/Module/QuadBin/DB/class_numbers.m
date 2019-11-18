//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//                          CLASS NUMBERS DATABASE                          //
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

/* Created by David Kohel, March 2001 */

DATDIR := GetEchidnaDatabaseRoot() * "/RngQuad/NumCls/";
prefix := "num";
disc_length := 8;
range := 10000;

//////////////////////////////////////////////////////////////////////////////

forward ClassNumberDataFile, ClassNumberSequenceWrite;
forward IsInClassNumberDomain, ExistsClassNumberDataFile;

//////////////////////////////////////////////////////////////////////////////
//                          CREATION FUNCTION                               //
//////////////////////////////////////////////////////////////////////////////

intrinsic ClassNumberDatabase() -> DBUser
    {The database of imaginary quadratic class numbers.}
    Dat := New(DBUser);
    Dat`DBIdentifier := "Class number";
    Dat`WriteFunction := ClassNumberSequenceWrite;
    Dat`ExistsFunction := ExistsClassNumberDataFile;
    Dat`IsInDomainFunction := IsInClassNumberDomain;
    return Dat;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//                           CLASS NUMBER ACCESS                            //
//////////////////////////////////////////////////////////////////////////////

intrinsic ClassNumbers(Dat::DBUser, N::RngIntElt) -> RngIntElt
    {The sequence of class numbers of the negative discriminants D
    with N-10000 < |D| <= N, where N mod 10000 = 0.}
    
    require Dat`DBIdentifier eq "Class number" : 
        "Argument 1 must be a database of quadratic class numbers.";
    require N gt 0 and N mod range eq 0 :
        "Argument 2 must be a positive integer of the form 10^4*n.";
    bool, filename := ExistsClassNumberDataFile(-N);
    require bool :
	"Argument 1 contains no data for this discriminant.";
    Classnos := [ Integers() | ];
    file := POpen("bunzip2 -c " * filename,"r");   
    for i in [1..range div 2] do
	Append(~Classnos,StringToInteger(Gets(file)));
    end for;
    Discs := [ -n : n in [N-range+1..N] | n mod 4 in {0,3} ];
    return Classnos, Discs;
end intrinsic;

intrinsic ClassNumbers(Dat::DBUser, S::[RngIntElt]) -> SeqEnum
    {The sequence of class numbers of the discriminants D 
    with S[1] <= |D| <= S[2]], where S[1] mod 10000 = 1,
    S[2] mod 10000 = 0.}
    N1, N2 := Explode(S);
    require Dat`DBIdentifier eq "Class number" : 
        "Argument 1 must be a database of quadratic class numbers.";
    require #S eq 2 : 
        "Argument 2 must be a sequence of two integers.";
    require N1 gt 0 and N1 mod range eq 1 :
        "First element of argument 2 must be a positive " *
        "integer of the form 10000n1+1.";
    require N2 gt N1 and N2 mod range eq 0 :
        "Second element of argument 2 must be an integer " *
        "of the form 10000n2 greater than the first.";
    Classnos := [ Integers() | ];
    Discs := [ Integers() | ];
    N := N1;
    k := (N2-N1+1) div range;
    for i in [0..k-1] do 
	bool, filename := ExistsClassNumberDataFile(-N);
	require bool : "Argument 1 contains no data for this range.";
	file := POpen("bunzip2 -c " * filename,"r");   
	for i in [1..range div 2] do
	    Append(~Classnos,StringToInteger(Gets(file)));
	end for;
	Discs cat:= [ -n : n in [N..N+range] | n mod 4 in {0,3} ];
	N +:= range;
    end for;
    return Classnos, Discs;
end intrinsic;

intrinsic ClassNumber(Dat::DBUser, D::RngIntElt) -> RngIntElt
    {The class number of the discriminant D < 0.}
    require Dat`DBIdentifier eq "Class number" : 
        "Argument 1 must be a database of quadratic class numbers.";
    bool, filename, index := ExistsClassNumberDataFile(D);
    require bool :
	"Argument 1 contains no data for this discriminant.";
    file := POpen("bunzip2 -c " * filename,"r");   
    for i in [1..index] do
	h_string := Gets(file);
    end for;
    h := StringToInteger(h_string);
    require h ne 0 :
	"Argument 1 contains no data for this discriminant.";
    delete file;
    return h;
end intrinsic; 

//////////////////////////////////////////////////////////////////////////////
//                             WRITE ACCESS                                 //
//////////////////////////////////////////////////////////////////////////////

procedure ClassNumberSequenceWrite(X)
    // Write the sequence of class numbers for discriminants D in 
    // the range N-10000 < |D| <= N to the class number database.
    Classnos := X[1]; N := X[2];
    error if #Classnos ne (range div 2), "Invalid class number sequence.";
    D := -N;
    filename := ClassNumberDataFile(D);
    SplitSeq := [ IntegerToString(h) : h in Classnos ];
    file := Open(filename,"w");
    Put(file,&cat[ h cat "\n" : h in SplitSeq ]);
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

function ClassNumberFilename(D)
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

function IsInClassNumberDomain(D)
    if Type(D) ne RngIntElt or D ge 0 or D mod 4 notin {0,1} then
	return false, "Argument must be a negative discriminant.";
    end if;
    return true, "";
end function;

function ExistsClassNumberDataFile(D)
    // Returns true if and only if the compressed data file 
    // exists, and if so, returns the filename for reading.
    filename, dirpath, index := ClassNumberFilename(D);
    t := System("test -d " * dirpath);
    if t ne 0 then return false, _, _; end if;
    t := System("test -f " * filename * "z");
    if t ne 0 then return false, _, _; end if;
    return true, filename * "z", index;
end function;

function ClassNumberDataFile(D)
    filename, dirpath := ClassNumberFilename(D);
    t := System("test -d " * dirpath);
    if t ne 0 then System("mkdir " * dirpath); end if;
    System("touch " * filename);
    return filename;
end function;

