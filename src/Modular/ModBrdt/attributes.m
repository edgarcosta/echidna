////////////////////////////////////////////////////////////////////////
//                                                                    //
//                            Verbose mode                            //
//                                                                    //
////////////////////////////////////////////////////////////////////////

declare verbose Brandt, 3;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                       Attribute declarations                       //
//                                                                    //
////////////////////////////////////////////////////////////////////////

declare attributes ModBrdt:
    Module,           // inner product module of brandt module
    Degree,           // the degree r of the symmetric product Sym^r(I)
    BaseRing,         // the base ring
    LeftIdealClasses, //  
    HeckeDegree,      // e such that all known Hecke operators T 
    IsIndecomposable, // satisfy f(T)^e = 0 where deg(f) = d, e*d = dim
    IsFull,           // either IsFull, or 
    AmbientModule,    //    AmbientModule must be defined 
    RamifiedPrimes,   // primes ramified of the quaternion algebra 
    Conductor,        // index of the order in a maximal order
    FullLevelIndex,   // full level index of the order in a maximal order
    ConductorPrimes,  // divisors of the conductor
    DegeneracyIndices,// 
    AutoNums,         // the numbers of units  
    NormGrams,        // quadratic norm lattices of ideals 
    ThetaSeries,      // theta series for the quadratic modules 
    HeckePrecision,   // precision of to which Hecke operators are known
    HeckePrimes,      // primes indices for known operators
    HeckeOperators,   // known hecke operators
    AtkinLehnerPrimes,  // the prime divisors of the level
    AtkinLehnerPermutations,  // The sequences of A-L coordinate perms
    CharacterPrimes,
    CharacterPermutations,
    FactorBases,      // bases of simple submodules 
    FactorIdeals,     //   and defining ideals
    FactorIsIndecomposable, // 
    NewFactorBases,   // bases of simple submodules 
    NewFactorIdeals,  //   and defining ideals
    NewFactorIsIndecomposable, // 
    DecompositionIdeal,
    DecompositionBound,
    ModularSymbols,   // 
    CuspidalModularSymbols;

declare attributes ModBrdtElt:
    Parent,
    Element;

