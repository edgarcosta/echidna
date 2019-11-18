
intrinsic Prime(n::RngIntElt) -> RngIntElt
    {Returns the nth prime.}
    require n ge 1 : "Argument must be positive.";
    p := 2;
    for i in [1..n-1] do
	p := NextPrime(p);
    end for;
    return p;
end intrinsic;

intrinsic Primes(n::RngIntElt) -> SeqEnum
    {The first n primes.}
    require n ge 1 : "Argument must be positive.";
    prmseq := [ 2 ];
    for i in [1..n-1] do
	Append(~prmseq,NextPrime(prmseq[i]));
    end for;
    return prmseq;
end intrinsic;

intrinsic Primes(S::[RngIntElt]) -> SeqEnum
    {The subsequence of primes in S.}
    return [ p : p in S | IsPrime(p) ];
end intrinsic;
