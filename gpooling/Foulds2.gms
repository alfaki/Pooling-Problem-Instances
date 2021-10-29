$ontext
    Foulds2 pooling problem data.
    Author: Mohammed Alfaki, Wed Nov  9 15:36:08 2011
$offtext

$eolcom #

# Declare sets
    set i    / 1*12 /;
    set s(i) / 1*6  /;
    set t(i) / 9*12 /;
    set k    / 1*1  /;

alias (i,j);

# The arc unit cost c_{ij}
table c(i,j)
          7       8       9      10      11      12
  1    6.00    0.00    0.00    0.00    0.00    0.00
  2   16.00    0.00    0.00    0.00    0.00    0.00
  3    0.00    0.00    1.00   -5.00    4.00   -2.00
  4    0.00    3.00    0.00    0.00    0.00    0.00
  5    0.00   13.00    0.00    0.00    0.00    0.00
  6    0.00    0.00   -2.00   -8.00    1.00   -5.00
  7    0.00    0.00   -9.00  -15.00   -6.00  -12.00
  8    0.00    0.00   -9.00  -15.00   -6.00  -12.00 ;

# The adjacency matrix (the arcs set A)
table a(i,j)
      7   8   9  10  11  12
  1   1   0   0   0   0   0
  2   1   0   0   0   0   0
  3   0   0   1   1   1   1
  4   0   1   0   0   0   0
  5   0   1   0   0   0   0
  6   0   0   1   1   1   1
  7   0   0   1   1   1   1
  8   0   0   1   1   1   1 ;

# Source qualities/terminal quality upper bounds
table q(i,k)
          1
  1    3.00
  2    1.00
  3    2.00
  4    3.50
  5    1.50
  6    2.50
  9    2.50
 10    1.50
 11    3.00
 12    2.00 ;

# Node capacity lower bound
parameter bl(i) /  1     0.00
                   2     0.00
                   3     0.00
                   4     0.00
                   5     0.00
                   6     0.00
                   9     0.00
                  10     0.00
                  11     0.00
                  12     0.00 / ;

# Node capacity upper bound
parameter bu(i) /  1   600.00
                   2   600.00
                   3   600.00
                   4   600.00
                   5   600.00
                   6   600.00
                   7   600.00
                   8   600.00
                   9   100.00
                  10   200.00
                  11   100.00
                  12   200.00 / ;

$include xmodel.gms