//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//                   HUMBERT MODULAR POLYNOMIALS                            //
//                                                                          //
//  Copyright (C) 2007 David Gruenewald <davidg@maths.usyd.edu>             //
//  Copyright (C) 2007 David Kohel <kohel@maths.usyd.edu>                   //
//                                                                          //
//  Distributed under the terms of the GNU General Public License (GPL)     //
//                  http://www.gnu.org/licenses/                            //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

/*
Humbert polynomials computed by David Gruenewald, April 2007.
*/

DATDIR := GetEchidnaDatabaseRoot() * "/PolRM/";
prefix := "pol";
disc_length := 3;

//////////////////////////////////////////////////////////////////////////////
ModelTypes := AssociativeArray(Strings());
ModelList := [
    ["Satake","Level1Satake"],
    ["Level1Satake","Level1Satake"],
    ["Rosenhain","Level2Rosenhain"],
    ["Level2Rosenhain","Level2Rosenhain"],
    ["Runge","Level2Theta"],
    ["Level2ThetaNull","Level2Theta"],
    ["Level2Theta","Level2Theta"]
    ];
for Name in ModelList do
    ModelTypes[Name[1]] := Name[2];
end for;
    
//////////////////////////////////////////////////////////////////////////////

forward HumbertPolynomialDataFile, HumbertPolynomialWrite;
forward IsInHumbertPolynomialDomain, ExistsHumbertPolynomialDataFile;

//////////////////////////////////////////////////////////////////////////////
//                          CREATION FUNCTION                               //
//////////////////////////////////////////////////////////////////////////////

intrinsic HumbertPolynomialDatabase() -> DBUser
    {The database of Humbert polynomials.}
    Dat := New(DBUser);
    Dat`DBIdentifier := "Humbert polynomial";
    Dat`WriteFunction := HumbertPolynomialWrite;
    Dat`ExistsFunction := ExistsHumbertPolynomialDataFile;
    Dat`IsInDomainFunction := IsInHumbertPolynomialDomain;
    return Dat;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//                  HUMBERT MODULAR POLYNOMIAL ACCESS                       //
//////////////////////////////////////////////////////////////////////////////

intrinsic Level1SatakeHumbertPolynomial(Dat::DBUser, D::RngIntElt) -> RngMPolElt
    {The level 1 Satake Humbert polynomial of real discriminant D.}
    bool, filename := ExistsHumbertPolynomialDataFile(<"Level1Satake",D,1>);
    require bool :
	"Argument 1 contains no datafile for Satake Humbert polynomials of this discriminant.";
    P4 := PolynomialRing(Integers(),[2,3,5,6]);
    file := POpen("bunzip2 -c " * filename, "r");   
    strseq := Gets(file);
    humpol := P4!0;
    while not IsEof(strseq) do
	c := StringToIntegerSequence(strseq);
	humpol +:= c[5]*Monomial(P4,c[[1..4]]);
	strseq := Gets(file);
    end while;
    return humpol;
end intrinsic;

intrinsic RosenhainHumbertPolynomial(Dat::DBUser, D::RngIntElt) -> RngMPolElt
    {The Rosenhain Humbert polynomial of real discriminant D.}
    bool, filename := ExistsHumbertPolynomialDataFile(<"Level2Rosenhain",D,1>);
    require bool :
	"Argument 1 contains no datafile for Rosenhain Humbert polynomials of this discriminant.";
    P3 := PolynomialRing(Integers(),3 : Global);
    file := POpen("bunzip2 -c " * filename, "r");   
    strseq := Gets(file);
    humpol := P3!0;
    while not IsEof(strseq) do
	c := StringToIntegerSequence(strseq);
	humpol +:= c[4]*Monomial(P3,c[[1..3]]);
	strseq := Gets(file);
    end while;
    return humpol;
end intrinsic;

intrinsic RungeHumbertPolynomial(Dat::DBUser, D::RngIntElt) -> RngMPolElt
    {The Runge Humbert polynomial of real discriminant D.}
    bool, filename := ExistsHumbertPolynomialDataFile(<"Level2Theta",D,1>);
    require bool :
	"Argument 1 contains no datafile for Runge Humbert polynomials of this discriminant.";
    return Level2ThetaNullHumbertPolynomial(Dat,D);
end intrinsic;

intrinsic Level2ThetaNullHumbertPolynomial(Dat::DBUser, D::RngIntElt) -> RngMPolElt
    {The level 2 theta Humbert polynomial of real discriminant D.}
    bool, filename := ExistsHumbertPolynomialDataFile(<"Level2Theta",D,1>);
    require bool :
	"Argument 1 contains no datafile for Runge Humbert polynomials of this discriminant.";
    P4 := PolynomialRing(Integers(),4 : Global);
    file := POpen("bunzip2 -c " * filename, "r");   
    strseq := Gets(file);
    humpol := P4!0;
    while not IsEof(strseq) do
	c := StringToIntegerSequence(strseq);
	humpol +:= c[5]*Monomial(P4,c[[1..4]]);
	strseq := Gets(file);
    end while;
    return humpol;
end intrinsic;

intrinsic HumbertPolynomial(
    Dat::DBUser, ModelType::MonStgElt,D::RngIntElt) -> RngMPolElt
    {The Humbert polynomial of model ModelType and real discriminant D.}
    require Dat`DBIdentifier eq "Humbert polynomial" : 
	"Argument 1 must be a database of Humbert polynomials.";
    require ModelType in Keys(ModelTypes) : 
	"Argument 2 specifies an unrecognized model type.";
    case ModelTypes[ModelType]:
    when "Level1Satake":
	return Level1SatakeHumbertPolynomial(Dat,D);
    when "Level2Rosenhain":
	return RosenhainHumbertPolynomial(Dat,D);
    when "Level2Theta":
	return Level2ThetaNullHumbertPolynomial(Dat,D);
    end case;
end intrinsic; 

//////////////////////////////////////////////////////////////////////////////
//                             WRITE ACCESS                                 //
//////////////////////////////////////////////////////////////////////////////

procedure HumbertPolynomialWrite(Key,HD)
    // Write HD to the modular polynomial database.
    ModelType := Key[1];
    D := Key[2];
    i := #Key eq 3 select Key[3] else 1;
    error if Type(BaseRing(Parent(HD))) ne RngInt,
        "Humbert polynomial must be defined over the integers for writing.";
    error if ModelType notin Keys(ModelTypes),
	"Humbert polynomial model type not recognized."; 
    filename := HumbertPolynomialDataFile(ModelTypes[ModelType],D,i);
    file := Open(filename,"w");   
    // Empty the contents of the file, in case it did exist.
    Flush(file);
    // First line is the gram matrix of order 1.
    for m in Monomials(HD) do
	monseq := Exponents(m);
	Append(~monseq,MonomialCoefficient(HD,m));
	Puts(file,&*[ IntegerToString(x) * " " : x in monseq ]);
    end for;
    delete file;
    System("bzip2 -c " * filename * " > " * filename * "z");
    System("rm " * filename);
end procedure;

//////////////////////////////////////////////////////////////////////////////
//                            FILE STRUCTURE                                //
//////////////////////////////////////////////////////////////////////////////

function HumbertPolynomialFilename(ModelType,D,i)
    modeldir := ModelTypes[ModelType];
    disc := IntegerToString(D);   
    while #disc lt disc_length do disc := "0" cat disc; end while;
    indx := IntegerToString(i);
    while #indx lt 2 do indx := "0" cat indx; end while;
    dirpath := &*[ DATDIR, modeldir, "/", disc, "/" ];
    filename := &*[ dirpath, prefix, ".", indx, ".db" ];
    return filename, dirpath;
end function;

function IsInHumbertPolynomialDomain(X)
    if not (Type(X) eq Tup and #X in {2,3}) then
	return false, "Argument 1 must be a tuple of length 2.";
    end if;
    if not Type(X[1]) eq MonStgElt then
	return false, "Tuple element 1 must be an string.";
    end if;
    if not X[1] in Keys(ModelTypes) then
	return false, "Tuple element 1 must be a known Humbert model type.";
    end if;
    ModelType := ModelTypes[X[1]];
    D := X[2];
    if not Type(D) eq RngIntElt then
	return false, "Tuple element 2 must be an integer.";
    end if;
    if #X eq 3 then
	i := X[3];
	if not Type(D) eq RngIntElt then
	    return false, "Tuple element 3 must be an integer.";
	end if;
    end if;
    return true, "";
end function;

function ExistsHumbertPolynomialDataFile(X)
    // Returns true if and only if the compressed data file 
    // exists, and if so, returns the file handle for reading.
    ModelType := ModelTypes[X[1]];
    D := X[2];
    i := #X eq 3 select X[3] else 1;
    filename, dirpath := HumbertPolynomialFilename(ModelType,D,i);
    t := System("test -d " * dirpath);
    if t ne 0 then return false, _; end if;
    t := System("test -f " * filename * "z");
    if t ne 0 then return false, _; end if;
    return true, filename * "z";
end function;

function HumbertPolynomialDataFile(ModelType,D,i)
    ModelType := ModelTypes[ModelType];
    filename, dirpath := HumbertPolynomialFilename(ModelType,D,i);
    if System("test -d " * dirpath) ne 0 then
	System(&*[ "mkdir ", dirpath]);
    end if;
    System("touch " * filename);
    return filename;
end function;

