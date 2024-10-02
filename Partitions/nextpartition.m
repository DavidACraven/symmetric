// Iterator for partitions. Useful when storing them all is too resource-intensive. Note that it loops back to [n] once it hits [1^n].

/*
These are the original code. It has been improved, see below.

intrinsic NextPartition(pa::SeqEnum[RngIntElt],n::RngIntElt) -> SeqEnum
{Given a partition pa of size n (where n is specified to speed up calculations slightly), returns the next partition in the lexicographic ordering on partitions. If (1^n) is given as input, it returns (n). Note that no checking is done as to whether the input is a partition with no trailing zeros, to maintain speed.}

if #pa eq n then return [n]; end if;
//if #pa eq 1 then return [n-1,1]; end if;
nn:=Position(pa,1);
if(nn eq 0) then return Prune(pa) cat [pa[#pa]-1,1]; end if;
// So now the last part is 1.

firstpart:=pa[nn-1]-1;
origpart:=[pa[i]:i in [1..nn-2]];
rest:=n-&+(origpart cat [0]);
a:=rest div firstpart;
b:=rest mod firstpart;
Y:=origpart cat [firstpart:i in [1..a]];
if b ne 0 then Append(~Y,b); end if;
return Y;

end intrinsic;


intrinsic NextPartition(~pa::SeqEnum[RngIntElt],n::RngIntElt)
{Given a partition pa of size n (where n is specified to speed up calculations slightly), destructively returns the next partition in the lexicographic ordering on partitions. If (1^n) is given as input, it returns (n). Note that no checking is done as to whether the input is a partition with no trailing zeros, to maintain speed.}
if #pa eq n then
  pa:=[n];
else
  nn:=Position(pa,1);
  if(nn eq 0) then
    pa:=Prune(pa) cat [pa[#pa]-1,1];
  else
    // So now the last part is 1.
    firstpart:=pa[nn-1]-1;
    origpart:=[pa[i]:i in [1..nn-2]];
    rest:=n-&+(origpart cat [0]);
    a:=rest div firstpart;
    b:=rest mod firstpart;
    pa:=origpart cat [firstpart:i in [1..a]];
    if b ne 0 then Append(~pa,b); end if;
  end if;
end if;
end intrinsic;

*/


intrinsic NextPartition(pa::SeqEnum[RngIntElt],n::RngIntElt) -> SeqEnum
{Given a partition pa of size n (where n is specified to speed up calculations slightly), returns the next partition in the lexicographic ordering on partitions. If (1^n) is given as input, it returns (n). Note that no checking is done as to whether the input is a partition of n with no trailing zeros, to maintain speed.}
nn:=Position(pa,1);
if(nn gt 1) then
  // So the last part is 1 but it is not 1^n
  firstpart:=pa[nn-1]-1;
  rest:=#pa-nn+2;
  a:=rest div firstpart;
  b:=rest mod firstpart;
  pa:=[pa[i]:i in [1..nn-2]] cat [firstpart:i in [0..a]];
  if b ne 0 then Append(~pa,b); end if;
elif(nn eq 0) then
  pa[#pa]-:=1;
  Append(~pa,1);
else
  pa:=[n];
end if;
return pa;

end intrinsic;


intrinsic NextPartition(pa::SeqEnum[RngIntElt]) -> SeqEnum
{Given a partition pa of length n, returns the next partition in the lexicographic ordering on partitions. If (1^n) is given as input, it returns (n).}
require IsPartition(pa) and pa[#pa] gt 0: "Input must be partition with no trailing zeros";
n:=&+pa;
nn:=Position(pa,1);
if(nn gt 1) then
  // So the last part is 1 but it is not 1^n
  firstpart:=pa[nn-1]-1;
  rest:=#pa-nn+2;
  a:=rest div firstpart;
  b:=rest mod firstpart;
  pa:=[pa[i]:i in [1..nn-2]] cat [firstpart:i in [0..a]];
  if b ne 0 then Append(~pa,b); end if;
elif(nn eq 0) then
  pa[#pa]-:=1;
  Append(~pa,1);
else
  pa:=[n];
end if;
return pa;
end intrinsic;

intrinsic NextPartition(~pa::SeqEnum[RngIntElt],n::RngIntElt)
{Given a partition pa of size n (where n is specified to speed up calculations slightly), destructively returns the next partition in the lexicographic ordering on partitions. If (1^n) is given as input, it returns (n). Note that no checking is done as to whether the input is a partition of n with no trailing zeros, to maintain speed.}
nn:=Position(pa,1);
if(nn gt 1) then
  // So the last part is 1 but it is not 1^n
  firstpart:=pa[nn-1]-1;
  rest:=#pa-nn+2;
  a:=rest div firstpart;
  b:=rest mod firstpart;
  pa:=[pa[i]:i in [1..nn-2]] cat [firstpart:i in [0..a]];
  if b ne 0 then Append(~pa,b); end if;
elif(nn eq 0) then
  pa[#pa]-:=1;
  Append(~pa,1);
else
  pa:=[n];
end if;
end intrinsic;


intrinsic NextPartition(~pa::SeqEnum[RngIntElt])
{Given a partition pa of length n, destructively returns the next partition in the lexicographic ordering on partitions. If (1^n) is given as input, it returns (n).}

require IsPartition(pa) and pa[#pa] gt 0: "Input must be partition with no trailing zeros";
n:=&+pa;
nn:=Position(pa,1);
if(nn gt 1) then
  // So the last part is 1 but it is not 1^n
  firstpart:=pa[nn-1]-1;
  rest:=#pa-nn+2;
  a:=rest div firstpart;
  b:=rest mod firstpart;
  pa:=[pa[i]:i in [1..nn-2]] cat [firstpart:i in [0..a]];
  if b ne 0 then Append(~pa,b); end if;
elif(nn eq 0) then
  pa[#pa]-:=1;
  Append(~pa,1);
else
  pa:=[n];
end if;
end intrinsic;

intrinsic NumberOfPartitionsWithAtMostParts(n::RngIntElt,k::RngIntElt) -> RngIntElt
{Given a non-negative integer n and a positive integer k, returns the number of partitions of n into at most k parts.}

requirege n,0;
requirege k,1;

// Counts into at most k parts, not exactly k parts.
// This is the term in x^n of the function 1/(1-x)(1-x^2)...(1-x^k).
// 1/(1-x) is 1+x+x^2+...

R<x>:=PolynomialRing(Integers());
f:=&*[&+[x^(i*j):i in [0..n div j]]:j in [1..k]];
return Coefficient(f,n);

end intrinsic;


intrinsic NumberOfPartitionsWithExactlyParts(n,k) -> RngIntElt
{Given a non-negative integer n and a positive integer k, returns the number of partitions of n into exactly k parts.}

requirege n,0;
requirege k,1;
if(n lt k) then return 0; end if;

return NumberOfPartitionsWithAtMostParts(n-k,k);

end intrinsic;


intrinsic IndexToPartition(n::RngIntElt,m::RngIntElt) -> SeqEnum
{Given a non-negative integer n and a positive integer m, returns the mth partition of size n in the lexicographic ordering on partitions, so the mth entry in the sequence Partitions(n).}

requirege n,0;
num:=NumberOfPartitions(n);
requirerange m,1,num;

if m eq 1 then
  return [n];
elif m eq num then
  return [1:i in [1..n]];
end if;

n2:=n; m2:=m; LargestPart:=n2; Part:=[];

while n2 gt 0 do
  y:=0;
  for i in Reverse([1..LargestPart]) do
    x:=NumberOfPartitionsWithExactlyParts(n2,i);
    if(x+y lt m2) then y:=y+x; continue; end if;
    Append(~Part,i); m2:=m2-y; n2:=n2-i; LargestPart:=i; break i;
  end for;
end while;

return Part;

end intrinsic;


