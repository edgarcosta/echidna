//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//                QUATERNION ALGEBRA (BRANDT GROUPOID) DATABASE             //
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

/* Created by David Kohel, September 2000 */

DATDIR := GetEchidnaDatabaseRoot() * "/ModBrdt/";
prefix := "quat";
discr_length := 6;
level_length := 6;
fullc_length := 3;

//////////////////////////////////////////////////////////////////////////////

forward QuaternionAlgebraDataFile, QuaternionAlgebraWrite;
forward IsInQuaternionAlgebraDomain, ExistsQuaternionAlgebraDataFile;

//////////////////////////////////////////////////////////////////////////////
//                          CREATION FUNCTION                               //
//////////////////////////////////////////////////////////////////////////////

intrinsic QuaternionAlgebraDatabase() -> DBUser
    {The quaternion algebra database.}
    Dat := New(DBUser);
    Dat`DBIdentifier := "Quaternion algebra";
    Dat`WriteFunction := QuaternionAlgebraWrite;
    Dat`ExistsFunction := ExistsQuaternionAlgebraDataFile;
    Dat`IsInDomainFunction := IsInQuaternionAlgebraDomain;
    return Dat;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//           Accessary Function for Quaternions and Brandt Modules          //
//////////////////////////////////////////////////////////////////////////////

function IsValidLevel(D,m,c)
    if D le 0 or m le 0 or c le 0 then
	return false, "Arguments 2 and 3 must be positive."; 
    end if; 
    fac := Factorization(D);
    if #fac mod 2 eq 0 then
	return false, 
	    "Argument 2 must have an odd number of primes divisors.";
    end if;
    if &or[ p[2] ne 1 : p in fac ] then
	return false, "Argument 2 must be square free";
    end if;
    if &or[ Valuation(m,p[1]) gt 1 : p in fac ] then
	return false,
	    "Argument 3 must not be divisible by " * 
	    "the square of a divisor of argument 2.";
    end if;
    if c ne 1 then
	c1 := &*PrimeDivisors(c);
	if D mod c1 eq 0 then
	    return false, "Argument 4 must be supported at argument 2.";
	end if;
    end if;
    return true, _;
end function; 

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

function OrientedOrder(M,v)
    D1 := M[1,1]*M[2,2]-M[1,2]*M[2,1];
    D2 := M[1,1]*M[3,3]-M[1,3]*M[3,1];
    T1 := M[1,1]*M[2,3]-M[1,3]*M[2,1];
    K := QuaternionAlgebra(-D1,-D2,-T1);
    i := K.1 + (t1-(D1 mod 2))/2 where t1 is M[1,2]; 
    // assert Trace(i) eq M[1,2]; 
    j := K.2 + (t2-(D2 mod 2))/2 where t2 is M[1,3];
    // assert Trace(j) eq M[1,3];
    k := (i*j - (v[1] + v[2]*i + v[3]*j))/v[4];
    return QuaternionOrder(Integers(),[1,i,j,k]);
end function;

//////////////////////////////////////////////////////////////////////////////
//                             READ ACCESS                                  //
//////////////////////////////////////////////////////////////////////////////

intrinsic QuaternionIdealClasses(
    Dat::DBUser,D::RngIntElt,m::RngIntElt) -> SymAlgQuat
    {The left ideals classes of a quaternion order of conductor m
    in the quaternion algebra of discriminant D.}
    require Dat`DBIdentifier eq "Quaternion algebra" : 
	"Argument 1 must be a database of quaternion algebras.";
    val, error_message := IsValidLevel(D,m,1);
    require val : error_message;
    t, filename := ExistsQuaternionAlgebraDataFile([D,m,1]);
    require t : "No data file for this discriminant and level";
    file := POpen("bunzip2 -c " * filename, "r");   
    Q := StringToIntegerSequence(Gets(file));
    // First line should be defining gram matrix and vector to 
    // specify an orientation on multiplication. 
    if #Q eq 16 then
	M := Matrix(4,Q);
    else
	assert #Q eq 10; // Symmetric form is exploited.
	M := SymmetricMatrix(Q);
    end if;
    v := StringToIntegerSequence(Gets(file));
    A := OrientedOrder(M,v);
    h := StringToInteger(Gets(file));
    // Remaining lines give the bases of ideals.
    Bases := [ ];
    for k in [1..h] do
	Q := StringToIntegerSequence(Gets(file));
	Append(~Bases,Q);
    end for;
    A`LeftIdealBases := Bases;
    A`FullLevelIndex := 1;
    return QuaternionIdealClasses(A);
end intrinsic; 

intrinsic ReducedQuaternionIdealClasses(
    DBQA::DBUser,D::RngIntElt,m::RngIntElt) -> DBUser
    {Development purposes only.}
    require DBQA`DBIdentifier eq "Quaternion algebra" : 
	"Argument 1 must be the quaternion algebra database.";
    Q := QuaternionIdealClasses(DBQA,D,m);
    I := LeftIdealClass(Q,1);
    if Norm(I) eq 1 then
	return Q;
    end if;
    A := LeftOrder(I);
    B := RightOrder(I);
    I := Conjugate(I);
    Bases := [ ];
    for ABasis in A`LeftIdealBases do
	J := lideal< A | [ A!M[i] : i in [1..4] ] >
	    where M := UpperTriangularMatrix(ABasis);
	K := ReducedLeftIdealClass(I*J);
	M := HermiteForm(Matrix([ Eltseq(B!x) : x in ReducedBasis(K) ]));
	Append(~Bases,Eltseq(M)[[1,2,3,4,6,7,8,11,12,16]]);
    end for;
    B`LeftIdealBases := Bases;
    B`FullLevelIndex := 1;
    return QuaternionIdealClasses(B);
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//                             WRITE ACCESS                                 //
//////////////////////////////////////////////////////////////////////////////

procedure QuaternionIdealClassesWrite(G)
    // {Write G to the quaternion database.}
    N, m, c := Explode(LevelIndices(G));
    filename := QuaternionAlgebraDataFile(N div (m*c^3),m,c);
    file := Open(filename,"w");   
    // Empty the contents of the file, in case it did exist.
    Flush(file);
    // First line is the gram matrix of order 1.
    A := Order(G);
    // Basis should be reduced.
    Q := Eltseq(GramMatrix(A))[[1,5,6,9,10,11,13,14,15,16]];
    Puts(file,&*[ IntegerToString(x) * " " : x in Q ]);
    // Second line gives the coordinates of element i*j 
    Puts(file,&*[ IntegerToString(x) * " " : x in Eltseq(A.1*A.2) ]);
    // Third line is the class number.
    Puts(file,IntegerToString(ClassNumber(G)));
    // Following lines are the coordinates of the ideals.
    for Q in A`LeftIdealBases do
	Puts(file,&*[ IntegerToString(x) * " " : x in Q ]);
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

function QuaternionAlgebraFilename(D,m,c)
    N := D*m*c^3;
    subdr := DirectoryPath(N);
    level := IntegerToString(N);   
    discr := IntegerToString(D);   
    fullc := IntegerToString(c);   
    while #level lt level_length do level := "0" cat level; end while;
    while #discr lt discr_length do discr := "0" cat discr; end while;
    while #fullc lt fullc_length do fullc := "0" cat fullc; end while;
    suppath := &*[ DATDIR, subdr ];
    dirpath := &*[ DATDIR, subdr, "/", level, "/" ];
    filename := &*[ level, ".", discr, ".", fullc, ".", prefix, ".db" ];   
    return dirpath * filename, dirpath, suppath;
end function;

function IsInQuaternionAlgebraDomain(X)
    if Type(X) ne SeqEnum or Type(Universe(X)) ne RngInt or #X notin {2,3} then 
	return false, "Argument must be an integer sequence of length 2 or 3.";
    end if;
    D, m := Explode(X);
    c := #X eq 2 select 1 else X[3];
    if not IsValidLevel(D,m,c) then  
	return false, "Argument must specify a valid discriminant and conductor.";
    end if;
    return true, "";
end function;

function ExistsQuaternionAlgebraDataFile(X)
    // Returns true if and only if the compressed data file 
    // exists, and if so, returns the file handle for reading.
    D, m := Explode(X);
    c := #X eq 2 select 1 else X[3];
    filename, dirpath := QuaternionAlgebraFilename(D,m,c);
    t := System("test -d " * dirpath);
    if t ne 0 then return false, _; end if;
    t := System("test -f " * filename * "z");
    if t ne 0 then return false, _; end if;
    return true, filename * "z";
end function;

function QuaternionAlgebraDataFile(D,m,c)
    filename, dirpath, suppath := QuaternionAlgebraFilename(D,m,c);
    if System("test -d " * suppath) ne 0 then
	System(&*[ "mkdir ", suppath]);
    end if;
    if System("test -d " * dirpath) ne 0 then
	System(&*[ "mkdir ", dirpath]);
    end if;
    System("touch " * filename);
    return filename;
end function;

