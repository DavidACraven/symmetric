intrinsic HookPartitions(n::RngIntElt) -> SeqEnum
{The collection of all hook partitions of size n, ordered lexicographically.}
requirege n,1;
return [[i] cat [1:j in [1..n-i]]:i in [n..1 by -1]];
end intrinsic;

intrinsic AlmostHookPartitions(n::RngIntElt) -> SeqEnum
{The collection of all almost-hook partitions of size n, ordered lexicographically.}
requirege n,1;
return [[i,2] cat [1:j in [1..n-i-2]]:i in [n-2..2 by -1]];
end intrinsic;

intrinsic TwoPartPartitions(n::RngIntElt) -> SeqEnum
{The collection of all partitions of size n with exactly two parts, ordered lexicographically.}
requirege n,2;
return [[n-i,i]:i in [1..n div 2]];
end intrinsic;

intrinsic ThreePartPartitions(n::RngIntElt) -> SeqEnum
{The collection of all partitions of size n with exactly three parts, ordered lexicographically.}
requirege n,3;
return Reverse(Sort(&cat[[[n-i-2*j,i+j,j]:j in [1..(n-2*i) div 3]]:i in [0..(n-2) div 2-1]]));
end intrinsic;
