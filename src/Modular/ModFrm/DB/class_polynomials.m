//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//                         CLASS POLYNOMIALS DATABASE                       //
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

DATDIR := GetEchidnaDatabaseRoot() * "/PolCM/";
prefix := "pol";
disc_length := 8;
disc_range := 10000;

//////////////////////////////////////////////////////////////////////////////

forward ClassPolynomialDataFile, ClassPolynomialWrite;
forward IsInClassPolynomialDomain, ExistsClassPolynomialDataFile;

//////////////////////////////////////////////////////////////////////////////
//                          CREATION FUNCTION                               //
//////////////////////////////////////////////////////////////////////////////

intrinsic ClassPolynomialDatabase() -> DBUser
    {The database of class polynomials.}
    Dat := New(DBUser);
    Dat`DBIdentifier := "Class polynomial";
    Dat`WriteFunction := ClassPolynomialWrite;
    Dat`ExistsFunction := ExistsClassPolynomialDataFile;
    Dat`IsInDomainFunction := IsInClassPolynomialDomain;
    return Dat;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//                        CLASS POLYNOMIAL ACCESS                           //
//////////////////////////////////////////////////////////////////////////////

intrinsic HilbertClassPolynomial(Dat::DBUser, D::RngIntElt) -> RngUPolElt
    {Returns the Hilbert class polynomial for D.} 
    require Dat`DBIdentifier eq "Class polynomial" : "Argument 1 must be a database of class polynomials.";
    require D mod 4 in {0,1} : "Argument 2 must be a valid discriminant.";
    return ClassPolynomial(Dat,"Hilbert",D);
end intrinsic;

intrinsic WeberClassPolynomial(Dat::DBUser, D::RngIntElt) -> RngUPolElt
    {Returns the Weber class polynomial for D.} 
    require Dat`DBIdentifier eq "Class polynomial" : "Argument 1 must be a database of class polynomials.";
    require D mod 4 in {0,1} : "Argument 2 must be a valid discriminant.";
    require D mod 8 eq 1 : "Argument 2 must be congruent to 1 mod 8 for polynomial type Weber.";
    return ClassPolynomial(Dat,"Weber",D);
end intrinsic;

intrinsic ClassPolynomial(
    Dat::DBUser, PolyType::MonStgElt, p::RngIntElt, D::RngIntElt) -> RngUPolElt
    {The class polynomial of type PolyType, level p and discriminant D.}
    require Dat`DBIdentifier eq "Class polynomial" : 
        "Argument 1 must be a database of class polynomials.";
    require PolyType in {"Atkin", "Eta"} :
        "Argument 2 specifies an unrecognized class polynomial type.";
    require D mod 4 in {0,1} :
        "Argument 3 must be a valid discriminant.";
    if PolyType eq "Weber" then
        require D mod 8 eq 1 : "Argument 2 must be congruent to " *
            "1 mod 8 for polynomial type Weber.";
    end if;
    bool, filename := ExistsClassPolynomialDataFile(<PolyType,p,D>);
    require bool : 
	"Argument 1 contains no data for this type and discriminant.";
    file := POpen("bunzip2 -c " * filename, "r");   
    P := PolynomialRing(Integers()); x := P.1;
    i := 0;
    h := P!0;
    str := Gets(file);
    while not IsEof(str) do
        h +:= StringToInteger(str)*x^i;
        i +:= 1;
        str := Gets(file);
    end while;
    return h;
end intrinsic; 

intrinsic ClassPolynomial(Dat::DBUser,
    PolyType::MonStgElt, D::RngIntElt) -> RngUPolElt
    {The class polynomial of type PolyType and discriminant D.}
    
    require Dat`DBIdentifier eq "Class polynomial" : 
        "Argument 1 must be a database of class polynomials.";
    require PolyType in {"Hilbert", "Weber"} :
        "Argument 2 specifies an unrecognized class polynomial type.";
    require D mod 4 in {0,1} :
        "Argument 3 must be a valid discriminant.";
    if PolyType eq "Weber" then
        require D mod 8 eq 1 : "Argument 2 must be congruent to " *
            "1 mod 8 for polynomial type \"Weber\".";
    end if;
    bool, filename := ExistsClassPolynomialDataFile(<PolyType,D>);
    require bool :
        "Argument 1 contains no data for this type and discriminant.";
    file := POpen("bunzip2 -c " * filename, "r");   
    P := PolynomialRing(Integers());  x := P.1;
    i := 0;
    h := P!0;
    str := Gets(file);
    while not IsEof(str) do
        h +:= StringToInteger(str)*x^i;
        i +:= 1;
        str := Gets(file);
    end while;
    return h;
end intrinsic; 

//////////////////////////////////////////////////////////////////////////////
//                         ACCESSORY FUNCTIONS                              //
//////////////////////////////////////////////////////////////////////////////

function IsAdmissible(D,p)
    chi := KroneckerSymbol(D,p);
    if chi eq 1 then
	return true;
    elif chi eq -1 then
	return false;
    end if;
    if p eq 2 then
	return (D mod 16) in {8,12};
    end if;
    return D mod p^2 ne 0;
end function;

//////////////////////////////////////////////////////////////////////////////
//                             WRITE ACCESS                                 //
//////////////////////////////////////////////////////////////////////////////

procedure ClassPolynomialWrite(X,h)
    // {Write A to the class polynomial database.}
    if #X eq 2 then
	PolyType := X[1]; p := 1; D := X[2];
    else // #X eq 3
	PolyType := X[1]; p := X[2]; D := X[3];
    end if;
    error if PolyType notin {"Atkin", "Eta", "Hilbert", "Weber"},
        "Class polynomial type not recognized."; 
    error if PolyType eq "Eta" and p notin {2,3,5,7,13},
	"Class polynomial level not valid.";
    error if PolyType eq "Atkin" and not IsPrime(p),
	"Class polynomial level not valid.";
    error if D gt 0 or not IsAdmissible(D,p),
	"Class polynomial discriminant and level not valid.";
    filename := ClassPolynomialDataFile(PolyType,p,D);
    file := Open(filename,"w");   
    // Empty the contents of the file, in case it did exist.
    Flush(file);
    for c in Eltseq(h) do
        Puts(file,IntegerToString(c));
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
    n1 := disc_range*((N-1) div disc_range);
    s1 := IntegerToString(n1+1);
    s2 := IntegerToString(n1+disc_range);
    while #s1 lt disc_length do s1 := "0" cat s1; end while;
    while #s2 lt disc_length do s2 := "0" cat s2; end while;
    return &cat[ s1, "-", s2 ];    
end function;

function ClassPolynomialFilename(PolyType,p,D)
    subdr := DirectoryPath(-D);
    disc := IntegerToString(-D);   
    while #disc lt disc_length do disc := "0" cat disc; end while;
    case PolyType:
    when "Atkin": pol := "Atk";
    when "Eta": pol := "Eta";
    when "Hilbert": pol := "Cls";
    when "Weber": pol := "Wbr";
    end case;
    if p eq 1 then
	levelpath := DATDIR * pol;
    else
	level := IntegerToString(p);
	while #level lt 3 do level := "0" cat level; end while;
	levelpath := &*[ DATDIR, pol, "/", level ];
    end if;
    dirpath := &*[ levelpath, "/", subdr, "/" ];
    filename := &*[ dirpath, prefix, ".", disc, ".db" ];
    return filename, levelpath, dirpath;
end function;

function IsInClassPolynomialDomain(X)
    if Type(X) ne Tup or #X notin {2,3} then 
	return false, "Argument must be a tuple of length 2 or 3.";
    end if;
    PolyType := X[1];
    if Type(PolyType) ne MonStgElt then 
	return false, "Argument component 1 must be a string.";
    end if;
    D := X[2];
    if Type(X[2]) ne RngIntElt then 
	return false, "Argument component 2 must be an integer.";
    end if;
    if #X eq 3 and (Type(X[3]) ne RngIntElt or Type(X[3]) ne RngIntElt) then
	return false, "Argument component 3 must be an integer.";
    end if;
    return true, "";
end function;

function ExistsClassPolynomialDataFile(X)
    // Returns true if and only if the compressed data file 
    // exists, and if so, returns the filename for reading.
    if #X eq 2 then
	PolyType := X[1]; p := 1; D := X[2];
    else // #X eq 3
	PolyType := X[1]; p := X[2]; D := X[3];
    end if;
    filename, levelpath, dirpath := ClassPolynomialFilename(PolyType,p,D);
    t := System("test -d " * levelpath);
    if t ne 0 then return false, _; end if;
    t := System("test -d " * dirpath);
    if t ne 0 then return false, _; end if;
    t := System("test -f " * filename * "z");
    if t ne 0 then return false, _; end if;
    return true, filename * "z";
end function;

function ClassPolynomialDataFile(PolyType,p,D)
    // Creates the file and returns its name.
    filename, levelpath, dirpath := ClassPolynomialFilename(PolyType,p,D);
    t := System("test -d " * levelpath);
    if t ne 0 then System("mkdir " * levelpath); end if;
    t := System("test -d " * dirpath);
    if t ne 0 then System("mkdir " * dirpath); end if;
    System("touch " * filename);
    return filename;
end function;

