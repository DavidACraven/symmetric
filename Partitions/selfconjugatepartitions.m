intrinsic IsSelfConjugate(pa::SeqEnum[RngIntElt]) -> BoolElt
{Return true if the partition pa is self-conjugate. Input must be a partition with no trailing zeros.}
require IsPartition(pa) and pa[#pa] gt 0: "Input should be a partition with no trailing zeros";
return ConjugatePartition(pa) eq pa;
end intrinsic;


intrinsic SelfConjugatePartitions(n::RngIntElt,k::RngIntElt) -> SeqEnum
{The self-conjugate partitions of n of length at most k (or equivalently with first row of size at most k), (n >= 0, k >= 0).}
requirege n,0; requirege k,0;
if n eq 0 then return [[]]; end if;
if k lt Sqrt(n) then return []; end if;
if(n eq 2*k-1) then
  X:=[[k] cat [1:j in [2..k]]];
else
  X:=[];
end if;
for i in Reverse([1..k]) do
  if(n lt 2*i-1) then continue i; end if;
  if(n eq 2*i-1 and i ne k) then
    X cat:=[[i] cat [1:j in [2..i]]];
  else
    Y:=SelfConjugatePartitions(n-2*i+1,i-1);
    if(#Y eq 0) then continue i; end if;
    X cat:=[[i] cat [ii+1:ii in j] cat [1:ii in [#j+2..i]]:j in Y];
  end if;
end for;
return X;
end intrinsic;


intrinsic SelfConjugatePartitions(n::RngIntElt) -> SeqEnum
{The unrestricted self-conjugate partitions of n (n >= 0).}
requirege n,0;
return SelfConjugatePartitions(n,(n+1) div 2);
end intrinsic;


intrinsic NumberOfSelfConjugatePartitions(n::RngIntElt) -> RngIntElt
{The number of unrestricted self-conjugate partitions of the non-negative integer n.}
requirege n,0;
R<x>:=PolynomialRing(Integers());
pol:=&*[x^(2*i+1)+1:i in [0..n div 2]];
return Coefficient(pol,n);
end intrinsic;


intrinsic SelfConjugateEndoskeleton(pa::[RngIntElt]) -> SeqEnum
{ Computes the largest self-conjugate partition contained within the partition pa. }
pa2:=ConjugatePartition(pa);
nn:=Minimum(#pa,#pa2);
return [Minimum(pa[i],pa2[i]):i in [1..nn]];
end intrinsic;


intrinsic SelfConjugateExoskeleton(pa::[RngIntElt]) -> SeqEnum
{ Computes the smallest self-conjugate partition containing the partition pa. }
pa2:=ConjugatePartition(pa);
nn:=Maximum(#pa,#pa2);
return [Maximum(pa[i],pa2[i]):i in [1..nn]];
end intrinsic;
