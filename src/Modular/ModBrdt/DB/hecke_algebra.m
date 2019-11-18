//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//                          HECKE ALGEBRA DATABASE                          //
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

/* Created by David Kohel, May 2005 */

DATDIR := GetEchidnaDatabaseRoot() * "/ModBrdt/";
prefix := "hcke";
discr_length := 6;
level_length := 6;
fullc_length := 3;

//////////////////////////////////////////////////////////////////////////////

import "quaternion_algebras.m" : IsValidLevel;

//////////////////////////////////////////////////////////////////////////////

forward HeckeOperatorDataFile, HeckeOperatorWrite;
forward IsInHeckeOperatorDomain, ExistsHeckeOperatorDataFile;

//////////////////////////////////////////////////////////////////////////////
//                          CREATION FUNCTION                               //
//////////////////////////////////////////////////////////////////////////////

intrinsic HeckeAlgebraDatabase() -> DBUser
    {The Hecke algebra database.}
    Dat := New(DBUser);
    Dat`DBIdentifier := "Hecke algebra";
    Dat`WriteFunction := HeckeOperatorWrite;
    Dat`ExistsFunction := ExistsHeckeOperatorDataFile;
    Dat`IsInDomainFunction := IsInHeckeOperatorDomain;
    return Dat;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//                         HECKE OPERATOR ACCESS                            //
//////////////////////////////////////////////////////////////////////////////

intrinsic HeckeOperator(
    Dat::DBUser,L::[RngIntElt],p::RngIntElt) -> AlgMatElt
    {The Hecke operator T_p on M.}
    require Dat`DBIdentifier eq "Hecke algebra" : 
	"Argument 1 must be the database of Hecke algebras.";
    require #L in {2,3} : 
	"Argument 2 must be a sequence of 2 or 3 integers.";
    D, m := Explode(L);
    c := #L eq 3 select L[3] else 1;
    val, error_message := IsValidLevel(D,m,c);
    require val : error_message;
    t, filename := ExistsHeckeOperatorDataFile(<[D,m,c],"T",p>);
    require t : "No data file for this discriminant and level";
    file := POpen("bunzip2 -c " * filename, "r");   
    // First line should be the line of automorphism numbers.
    require c eq 1 : "Argument 2 must have third entry 1.";
    if GCD(D,m) eq 1 then
	n := BrandtModuleDimension(D,m);
    else
	DBQA := QuaternionAlgebraDatabase();
	n := ClassNumber(QuaternionIdealClasses(DBQA,D,m));
    end if;
    T := ZeroMatrix(Integers(),n,n);
    i := 1;
    strseq := Gets(file);
    while not IsEof(strseq) do
	I := StringToIntegerSequence(strseq);
	for j in I do
	    T[i,Abs(j)] +:= Sign(j);
	end for;
	i +:= 1;
	strseq := Gets(file);
    end while;
    return T;
end intrinsic; 

intrinsic AtkinLehnerOperator(
    Dat::DBUser,L::[RngIntElt],p::RngIntElt) -> AlgMatElt
    {The Hecke operator T_p on M.}
    require Dat`DBIdentifier eq "Hecke algebra" : 
	"Argument 1 must be the database of Hecke algebras.";
    require #L in {2,3} : 
	"Argument 2 must be a sequence of 2 or 3 integers.";
    D, m := Explode(L);
    c := #L eq 3 select L[3] else 1;
    require D mod p eq 0 or m mod p eq 0 and IsPrime(p) : 
	"Argument 3 must be a prime dividing the level.";
    val, error_message := IsValidLevel(D,m,c);
    require val : error_message;
    t, filename := ExistsHeckeOperatorDataFile(<[D,m,c],"W",p>);
    require t : "No data file for this discriminant and level";
    file := POpen("bunzip2 -c " * filename, "r");   
    // First line should be the line of automorphism numbers.
    require c eq 1 : "Argument 2 must have third entry 1.";
    if GCD(D,m) eq 1 then
	n := BrandtModuleDimension(D,m);
    else
	DBQA := QuaternionAlgebraDatabase();
	n := ClassNumber(QuaternionIdealClasses(DBQA,D,m));
    end if;
    T := ZeroMatrix(Integers(),n,n);
    i := 1;
    strseq := Gets(file);
    while not IsEof(strseq) do
	I := StringToIntegerSequence(strseq);
	for j in I do
	    T[i,Abs(j)] +:= Sign(j);
	end for;
	i +:= 1;
	strseq := Gets(file);
    end while;
    return T;
end intrinsic; 

intrinsic CharacterOperator(
    Dat::DBUser,L::[RngIntElt],p::RngIntElt) -> AlgMatElt
    {The Hecke operator T_p on M.}
    require Dat`DBIdentifier eq "Hecke algebra" : 
	"Argument 1 must be the database of Hecke algebras.";
    require #L in {2,3} : 
	"Argument 2 must be a sequence of 2 or 3 integers.";
    D, m := Explode(L);
    c := #L eq 3 select L[3] else 1;
    val, error_message := IsValidLevel(D,m,c);
    require val : error_message;
    require D mod p eq 0 and IsPrime(p) : 
	"Argument 3 must be a prime dividing the discriminant and level.";
    t, filename := ExistsHeckeOperatorDataFile(<[D,m,c],"U",p>);
    require t : "No data file for this discriminant and level";
    file := POpen("bunzip2 -c " * filename, "r");   
    // First line should be the line of automorphism numbers.
    require c eq 1 : "Argument 2 must have third entry 1.";
    if GCD(D,m) eq 1 then
	n := BrandtModuleDimension(D,m);
    else
	DBQA := QuaternionAlgebraDatabase();
	n := ClassNumber(QuaternionIdealClasses(DBQA,D,m));
    end if;
    T := ZeroMatrix(Integers(),n,n);
    i := 1;
    strseq := Gets(file);
    while not IsEof(strseq) do
	I := StringToIntegerSequence(strseq);
	for j in I do
	    T[i,Abs(j)] +:= Sign(j);
	end for;
	i +:= 1;
	strseq := Gets(file);
    end while;
    return T;
end intrinsic; 

//////////////////////////////////////////////////////////////////////////////
//                             WRITE ACCESS                                 //
//////////////////////////////////////////////////////////////////////////////

procedure HeckeOperatorWrite(D,m,c,S,T,p)
    filename := HeckeOperatorDataFile(D,m,c,S,p);
    file := Open(filename,"w");   
    Flush(file);
    n := Degree(Parent(T));
    for i in [1..n] do
	line := "";
	for j in [1..n] do
	    if T[i,j] ne 0 then
		a := T[i,j]; s := Sign(a); m := Abs(a);
		for k in [1..m] do
		    line *:= " " * Sprint(s*j);
		end for;
	    end if;
	end for; 
	Puts(file,line);
    end for;
    delete file;
    System("bzip2 -c " * filename * " > " * filename * "z");
    System("chmod a+r " * filename * "z");
    System("rm " * filename);
end procedure;

//////////////////////////////////////////////////////////////////////////////
//                            FILE STRUCTURE                                //
//////////////////////////////////////////////////////////////////////////////

function DirectoryPath(N)
    n1 := 400*((N-1) div 400);
    s1 := IntegerToString(n1+1);
    s2 := IntegerToString(n1+400);
    while #s1 lt level_length do s1 := "0" cat s1; end while;
    while #s2 lt level_length do s2 := "0" cat s2; end while;
    return s1 * "-" * s2;    
end function;

function HeckeOperatorFilename(D,m,c,S,p)
    N := D*m*c^3;
    subdr := DirectoryPath(N);
    level := IntegerToString(N);   
    discr := IntegerToString(D);   
    fullc := IntegerToString(c);   
    prime := IntegerToString(p);   
    while #level lt level_length do level := "0" cat level; end while;
    while #discr lt discr_length do discr := "0" cat discr; end while;
    while #fullc lt fullc_length do fullc := "0" cat fullc; end while;
    while #prime lt level_length do prime := "0" cat prime; end while;
    dirpath := &*[ DATDIR, subdr, "/", level, "/" ];  
    filename := &*[
	level, ".", discr, ".", fullc, ".",
	prefix, ".", S, ".", prime, ".db" ];   
    return dirpath * filename, dirpath;
end function;

function IsInHeckeOperatorDomain(X)
    if Type(X) ne Tup or #X ne 3 then 
	return false, "Argument must be a tuple of length 3.";
    end if;
    L := X[1]; S := X[2]; p := X[3];
    if not Type(L) eq SeqEnum or Type(Universe(L)) ne RngInt or #L notin {2,3} then 
	return false,
	    "Argument first component must be an integer sequence of length 2 or 3.";
    end if;
    D, m := Explode(L);
    c := #L eq 2 select 1 else L[3];
    if Type(S) ne MonStgElt or S notin {"T","W","U"} then
	return false, "Argument must have second component in {\"T\",\"W\",\"U\"}.";
    elif Type(p) ne RngIntElt then
	return false, "Argument must have third component an integer.";
    end if;
    return true, "";
end function;

function ExistsHeckeOperatorDataFile(X)
    // Returns true if and only if the compressed data file 
    // exists, and if so, returns the file handle for reading.
    L := X[1]; S := X[2]; p := X[3];
    D, m := Explode(L);
    c := #L eq 2 select 1 else L[3];
    filename, dirpath := HeckeOperatorFilename(D,m,c,S,p);
    t := System("test -d " * dirpath);
    if t ne 0 then return false, _; end if;
    t := System("test -f " * filename * "z");
    if t ne 0 then return false, _; end if;
    return true, filename * "z";
end function;

function HeckeOperatorDataFile(D,m,c,S,p)
    filename, dirpath := HeckeOperatorFilename(D,m,c,S,p);
    if System("test -d " * dirpath) ne 0 then
	System(&*[ "mkdir ", dirpath]);
    end if;
    System("touch " * filename);
    return filename;
end function;

