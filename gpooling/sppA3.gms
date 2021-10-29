$ontext
    sppA3 pooling problem data.
    Author: Mohammed Alfaki, Wed Nov  9 15:36:08 2011
$offtext

$eolcom #

# Declare sets
    set i    / 1*45 /;
    set s(i) / 1*20 /;
    set t(i) /31*45 /;
    set k    / 1*24 /;

alias (i,j);

# The arc unit cost c_{ij}
table c(i,j)
         21      22      23      24      25      26      27      28      29      30      31      32      33      34      35      36      37      38      39      40      41      42      43      44      45
  1    0.00   28.00    0.00    0.00   28.00   28.00    0.00   28.00    0.00    0.00    0.00    0.00    0.00    0.00  -17.00    0.00    0.00    0.00  -15.00    0.00  -21.00    0.00  -21.00  -15.00    0.00
  2   13.00    0.00    0.00   13.00    0.00   13.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00  -31.00  -35.00    0.00    0.00  -29.00    0.00    0.00    0.00    0.00    0.00
  3   43.00    0.00    0.00    0.00    0.00    0.00   43.00    0.00    0.00   43.00   -5.00    0.00    0.00   -6.00    0.00    0.00    0.00   -4.00    0.00    0.00   -6.00    0.00    0.00    0.00    0.00
  4    0.00    0.00   49.00   49.00    0.00   49.00   49.00    0.00    0.00    0.00    0.00    1.00    0.00    0.00    0.00    5.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00
  5   45.00   45.00    0.00   45.00    0.00    0.00   45.00   45.00   45.00   45.00    0.00    0.00    0.00   -4.00    0.00    0.00    0.00    0.00    0.00    3.00   -4.00    0.00    0.00    0.00    0.00
  6    0.00    0.00    0.00    0.00    0.00    0.00   34.00   34.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00  -10.00    0.00    0.00   -9.00    0.00  -15.00    0.00    0.00    0.00  -15.00
  7   30.00    0.00   30.00    0.00    0.00    0.00   30.00   30.00   30.00    0.00    0.00  -18.00    0.00  -19.00  -15.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00  -13.00    0.00
  8    0.00    0.00    0.00    0.00   40.00   40.00   40.00    0.00   40.00   40.00    0.00    0.00    0.00   -9.00    0.00   -4.00    0.00   -7.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00
  9    0.00   26.00   26.00   26.00    0.00   26.00   26.00    0.00   26.00   26.00    0.00  -22.00    0.00    0.00    0.00    0.00    0.00  -21.00    0.00  -16.00    0.00    0.00    0.00    0.00    0.00
 10    0.00    0.00    0.00    0.00    0.00    0.00    0.00   47.00    0.00    0.00    0.00    0.00    0.00    0.00    2.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00
 11    0.00    0.00    0.00   12.00    0.00   12.00   12.00   12.00    0.00    0.00    0.00    0.00    0.00    0.00  -33.00  -32.00    0.00  -35.00    0.00    0.00  -37.00    0.00  -37.00    0.00    0.00
 12    0.00    0.00    0.00    0.00   40.00    0.00   40.00    0.00    0.00   40.00    0.00   -8.00   -5.00    0.00   -5.00   -4.00    0.00    0.00    0.00    0.00   -9.00    0.00    0.00   -3.00   -9.00
 13    0.00   27.00   27.00   27.00   27.00    0.00   27.00    0.00    0.00   27.00  -21.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00
 14    0.00   38.00    0.00   38.00    0.00   38.00   38.00   38.00    0.00    0.00    0.00  -10.00    0.00  -11.00    0.00   -6.00    0.00    0.00   -5.00   -4.00    0.00    0.00    0.00   -5.00  -11.00
 15   50.00    0.00    0.00   50.00   50.00   50.00    0.00    0.00    0.00    0.00    0.00    2.00    5.00    0.00    0.00    0.00    0.00    0.00    0.00    8.00    0.00    1.00    0.00    0.00    1.00
 16    0.00    0.00   34.00   34.00    0.00   34.00    0.00    0.00   34.00    0.00    0.00    0.00    0.00    0.00    0.00  -10.00    0.00    0.00    0.00   -8.00    0.00    0.00    0.00   -9.00    0.00
 17   14.00   14.00   14.00   14.00   14.00    0.00    0.00    0.00    0.00    0.00  -34.00    0.00    0.00    0.00    0.00    0.00  -34.00    0.00    0.00    0.00    0.00    0.00  -35.00    0.00    0.00
 18    0.00   19.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00   19.00    0.00    0.00    0.00    0.00    0.00    0.00  -29.00    0.00    0.00    0.00    0.00  -30.00    0.00    0.00    0.00
 19    0.00    0.00    0.00   16.00    0.00    0.00   16.00   16.00   16.00    0.00    0.00    0.00    0.00    0.00  -29.00    0.00    0.00    0.00    0.00    0.00    0.00  -33.00    0.00    0.00    0.00
 20   31.00   31.00    0.00    0.00    0.00    0.00    0.00   31.00   31.00   31.00    0.00  -17.00    0.00    0.00    0.00  -13.00    0.00    0.00    0.00    0.00  -18.00    0.00    0.00    0.00  -18.00
 21    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00  -48.00    0.00    0.00    0.00    0.00  -44.00  -48.00    0.00    0.00  -42.00  -49.00    0.00    0.00    0.00    0.00
 22    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00  -48.00    0.00    0.00  -49.00    0.00    0.00  -48.00    0.00  -43.00    0.00    0.00    0.00    0.00    0.00    0.00
 23    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00  -48.00  -48.00  -45.00    0.00    0.00    0.00    0.00  -47.00  -43.00  -42.00    0.00    0.00  -49.00    0.00  -49.00
 24    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00  -48.00    0.00  -49.00  -45.00    0.00  -48.00    0.00    0.00  -42.00    0.00    0.00    0.00    0.00    0.00
 25    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00  -45.00    0.00    0.00    0.00    0.00  -47.00    0.00    0.00  -49.00  -49.00  -49.00    0.00    0.00
 26    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00  -45.00  -49.00    0.00  -44.00    0.00    0.00    0.00    0.00  -49.00  -49.00    0.00  -43.00  -49.00
 27    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00  -48.00  -45.00    0.00  -45.00  -44.00    0.00    0.00  -43.00  -42.00  -49.00  -49.00  -49.00    0.00  -49.00
 28    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00  -45.00    0.00    0.00    0.00    0.00    0.00  -43.00    0.00  -49.00  -49.00    0.00  -43.00    0.00
 29    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00  -48.00  -48.00    0.00  -49.00  -45.00  -44.00  -48.00  -47.00    0.00    0.00    0.00    0.00  -49.00  -43.00  -49.00
 30    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00  -49.00    0.00    0.00    0.00  -47.00    0.00  -42.00    0.00    0.00    0.00  -43.00  -49.00 ;

# The adjacency matrix (the arcs set A)
table a(i,j)
     21  22  23  24  25  26  27  28  29  30  31  32  33  34  35  36  37  38  39  40  41  42  43  44  45
  1   0   1   0   0   1   1   0   1   0   0   0   0   0   0   1   0   0   0   1   0   1   0   1   1   0
  2   1   0   0   1   0   1   0   0   0   0   0   0   0   0   0   1   1   0   0   1   0   0   0   0   0
  3   1   0   0   0   0   0   1   0   0   1   1   0   0   1   0   0   0   1   0   0   1   0   0   0   0
  4   0   0   1   1   0   1   1   0   0   0   0   1   0   0   0   1   0   0   0   0   0   0   0   0   0
  5   1   1   0   1   0   0   1   1   1   1   0   0   0   1   0   0   0   0   0   1   1   0   0   0   0
  6   0   0   0   0   0   0   1   1   0   0   0   0   0   0   0   1   0   0   1   0   1   0   0   0   1
  7   1   0   1   0   0   0   1   1   1   0   0   1   0   1   1   0   0   0   0   0   0   0   0   1   0
  8   0   0   0   0   1   1   1   0   1   1   0   0   0   1   0   1   0   1   0   0   0   0   0   0   0
  9   0   1   1   1   0   1   1   0   1   1   0   1   0   0   0   0   0   1   0   1   0   0   0   0   0
 10   0   0   0   0   0   0   0   1   0   0   0   0   0   0   1   0   0   0   0   0   0   0   0   0   0
 11   0   0   0   1   0   1   1   1   0   0   0   0   0   0   1   1   0   1   0   0   1   0   1   0   0
 12   0   0   0   0   1   0   1   0   0   1   0   1   1   0   1   1   0   0   0   0   1   0   0   1   1
 13   0   1   1   1   1   0   1   0   0   1   1   0   0   0   0   0   0   0   0   0   0   0   0   0   0
 14   0   1   0   1   0   1   1   1   0   0   0   1   0   1   0   1   0   0   1   1   0   0   0   1   1
 15   1   0   0   1   1   1   0   0   0   0   0   1   1   0   0   0   0   0   0   1   0   1   0   0   1
 16   0   0   1   1   0   1   0   0   1   0   0   0   0   0   0   1   0   0   0   1   0   0   0   1   0
 17   1   1   1   1   1   0   0   0   0   0   1   0   0   0   0   0   1   0   0   0   0   0   1   0   0
 18   0   1   0   0   0   0   0   0   0   1   0   0   0   0   0   0   1   0   0   0   0   1   0   0   0
 19   0   0   0   1   0   0   1   1   1   0   0   0   0   0   1   0   0   0   0   0   0   1   0   0   0
 20   1   1   0   0   0   0   0   1   1   1   0   1   0   0   0   1   0   0   0   0   1   0   0   0   1
 21   0   0   0   0   0   0   0   0   0   0   1   0   0   0   0   1   1   0   0   1   1   0   0   0   0
 22   0   0   0   0   0   0   0   0   0   0   1   0   0   1   0   0   1   0   1   0   0   0   0   0   0
 23   0   0   0   0   0   0   0   0   0   0   1   1   1   0   0   0   0   1   1   1   0   0   1   0   1
 24   0   0   0   0   0   0   0   0   0   0   0   1   0   1   1   0   1   0   0   1   0   0   0   0   0
 25   0   0   0   0   0   0   0   0   0   0   0   0   1   0   0   0   0   1   0   0   1   1   1   0   0
 26   0   0   0   0   0   0   0   0   0   0   0   0   1   1   0   1   0   0   0   0   1   1   0   1   1
 27   0   0   0   0   0   0   0   0   0   0   0   1   1   0   1   1   0   0   1   1   1   1   1   0   1
 28   0   0   0   0   0   0   0   0   0   0   0   0   1   0   0   0   0   0   1   0   1   1   0   1   0
 29   0   0   0   0   0   0   0   0   0   0   1   1   0   1   1   1   1   1   0   0   0   0   1   1   1
 30   0   0   0   0   0   0   0   0   0   0   0   0   0   1   0   0   0   1   0   1   0   0   0   1   1 ;

# Source qualities/terminal quality upper bounds
table q(i,k)
          1       2       3       4       5       6       7       8       9      10      11      12      13      14      15      16      17      18      19      20      21      22      23      24
  1   15.60   40.98   73.28   16.51   50.23   15.50   54.26   24.69   28.10    4.97   34.49   41.98  -15.60  -40.98  -73.28  -16.51  -50.23  -15.50  -54.26  -24.69  -28.10   -4.97  -34.49  -41.98
  2   36.26   77.91    3.42   25.73    6.63   22.23   66.37   63.22   31.15    2.71   79.20   52.85  -36.26  -77.91   -3.42  -25.73   -6.63  -22.23  -66.37  -63.22  -31.15   -2.71  -79.20  -52.85
  3    2.86   22.26   35.35   42.33   12.04   12.03   18.71   50.22   60.58   43.16   56.03   62.41   -2.86  -22.26  -35.35  -42.33  -12.04  -12.03  -18.71  -50.22  -60.58  -43.16  -56.03  -62.41
  4   31.81   75.70   77.63   20.05   10.42   48.63   33.94   45.15   42.56   51.14   28.25    8.62  -31.81  -75.70  -77.63  -20.05  -10.42  -48.63  -33.94  -45.15  -42.56  -51.14  -28.25   -8.62
  5   15.72   12.67   74.34   19.49   29.20   52.03   55.23   51.74   26.64   29.38   78.62   54.17  -15.72  -12.67  -74.34  -19.49  -29.20  -52.03  -55.23  -51.74  -26.64  -29.38  -78.62  -54.17
  6   52.89   37.19   13.38   40.06   58.41    4.21   13.50   58.24   79.22    0.67    2.20   77.53  -52.89  -37.19  -13.38  -40.06  -58.41   -4.21  -13.50  -58.24  -79.22   -0.67   -2.20  -77.53
  7   20.28   43.06   15.47   47.22   32.96   16.09   14.80   21.11    5.70   59.27    1.27   49.38  -20.28  -43.06  -15.47  -47.22  -32.96  -16.09  -14.80  -21.11   -5.70  -59.27   -1.27  -49.38
  8   21.22   22.66   14.16   27.61   69.89   44.05   37.76   64.89   58.90   77.14   17.66   13.56  -21.22  -22.66  -14.16  -27.61  -69.89  -44.05  -37.76  -64.89  -58.90  -77.14  -17.66  -13.56
  9    9.57   14.08   17.84   72.46   75.31   35.76   71.14   76.45   40.86   60.97   36.30    1.45   -9.57  -14.08  -17.84  -72.46  -75.31  -35.76  -71.14  -76.45  -40.86  -60.97  -36.30   -1.45
 10   77.89   71.64   46.68   51.01   64.50   19.92   58.28   14.07   58.91   78.27   43.65    1.59  -77.89  -71.64  -46.68  -51.01  -64.50  -19.92  -58.28  -14.07  -58.91  -78.27  -43.65   -1.59
 11   13.90   11.43   64.85   51.00   33.11   55.87   50.49   21.82   39.83   47.25    4.36   65.08  -13.90  -11.43  -64.85  -51.00  -33.11  -55.87  -50.49  -21.82  -39.83  -47.25   -4.36  -65.08
 12    9.21   67.57   35.02   25.35   36.64   73.19   14.58   61.58   45.28    3.84   54.14   26.48   -9.21  -67.57  -35.02  -25.35  -36.64  -73.19  -14.58  -61.58  -45.28   -3.84  -54.14  -26.48
 13   58.51   44.09   70.23   59.84   57.94   48.36   68.91    7.20   29.97   12.25   51.73   70.03  -58.51  -44.09  -70.23  -59.84  -57.94  -48.36  -68.91   -7.20  -29.97  -12.25  -51.73  -70.03
 14   67.38   75.08   39.02    6.99   23.87   38.81   65.52   19.92   65.21   66.29   71.24   34.67  -67.38  -75.08  -39.02   -6.99  -23.87  -38.81  -65.52  -19.92  -65.21  -66.29  -71.24  -34.67
 15   60.54   48.01   32.45   70.48   49.19   22.75   68.93   26.24   75.79   57.83   60.44   45.52  -60.54  -48.01  -32.45  -70.48  -49.19  -22.75  -68.93  -26.24  -75.79  -57.83  -60.44  -45.52
 16   18.82   21.98   75.43   40.62   11.09   15.96   48.89   49.25   68.01   27.45    1.81   35.08  -18.82  -21.98  -75.43  -40.62  -11.09  -15.96  -48.89  -49.25  -68.01  -27.45   -1.81  -35.08
 17   18.05   68.33   16.47   37.11   65.66   40.89   40.11   14.62   20.15    8.14   40.72   58.97  -18.05  -68.33  -16.47  -37.11  -65.66  -40.89  -40.11  -14.62  -20.15   -8.14  -40.72  -58.97
 18   62.45   62.02   65.73   65.00   18.29   16.52   47.04   70.19   21.83   74.35   48.36   76.28  -62.45  -62.02  -65.73  -65.00  -18.29  -16.52  -47.04  -70.19  -21.83  -74.35  -48.36  -76.28
 19   42.66   11.68   25.93   44.73   25.43   32.61   78.55   44.11   22.13   51.55   32.12   26.04  -42.66  -11.68  -25.93  -44.73  -25.43  -32.61  -78.55  -44.11  -22.13  -51.55  -32.12  -26.04
 20   67.90   27.03   77.46   18.41   23.04    5.71   45.17   35.07   13.42    1.36   70.16   54.33  -67.90  -27.03  -77.46  -18.41  -23.04   -5.71  -45.17  -35.07  -13.42   -1.36  -70.16  -54.33
 31   94.87   99.72   29.85   27.70   86.16   75.31   30.75   68.00   27.14   91.94   98.50   56.69  -15.79   -1.38  -12.70  -15.30   -9.01  -11.54  -17.09   -6.92   -8.09  -19.26  -13.40  -12.67
 32   52.29   62.51   83.78   63.46   32.37   63.62   87.79   28.83   64.66   52.67   80.03   91.41  -17.00  -14.00  -11.58   -6.89  -17.53   -4.96  -18.97  -19.63  -18.83  -16.98   -0.95  -17.70
 33   79.55   38.96   68.72   23.12   36.18   28.81   48.48   58.92   76.43   43.87   72.58   72.52  -15.26  -13.72   -3.57  -15.87   -1.69  -12.93   -3.34  -14.68   -8.28  -17.11   -8.66  -15.63
 34   77.11   55.70   56.94   41.56   69.76   78.36   24.80   40.31   70.73   59.74   91.95   70.95  -15.57  -13.97  -11.03   -3.42  -14.74   -6.19  -16.84   -9.78   -4.94   -7.62  -10.62  -13.30
 35   61.35   23.79   69.56   53.95   73.36   87.43   85.61   62.61   62.70   43.11   24.79   26.14  -12.54  -16.90  -19.95  -10.55   -5.62  -16.95  -17.51   -0.49   -8.45  -15.59   -7.17   -8.86
 36   42.15   29.90   95.18   82.30   95.62   71.76   87.63   95.23   55.28   51.83   87.73   72.64  -17.08  -15.85   -3.27   -1.77   -8.96  -10.87  -13.66  -15.86   -2.62   -6.16   -0.32   -2.48
 37   23.85   38.62   43.26   62.32   62.65   96.11   21.53   68.38   49.94   21.15   75.35   49.89  -10.08   -6.76  -13.14   -7.48   -5.61  -10.22  -13.48  -19.28   -3.37   -1.80   -9.11   -3.64
 38   91.22   51.45   27.31   97.41   34.41   25.55   34.43   96.87   47.50   28.27   36.71   35.83  -18.54   -9.63   -9.97  -11.64  -17.76   -8.95  -18.01  -12.20   -3.49   -9.20   -0.34   -4.84
 39   48.69   92.35   90.69   37.80   91.03   49.00   21.99   59.52   80.63   79.85   80.80   68.46   -3.13   -1.87   -5.61  -11.85  -17.63   -3.51   -2.00  -11.41  -10.11   -4.46  -12.79  -17.74
 40   75.86   81.88   99.95   90.55   51.29   52.12   33.51   78.37   93.23   93.41   35.02   96.01   -5.32  -12.77  -13.34  -18.26  -13.12  -13.03  -10.53   -9.21  -19.68  -14.65   -2.11   -2.09
 41   33.80   55.34   86.83   50.29   97.23   62.53   70.27   97.93   69.98   45.74   49.99   29.62  -18.58  -12.48  -15.86  -19.66  -10.69   -9.09   -4.73   -7.18  -18.84   -1.89  -19.93  -15.37
 42   75.99   90.39   81.92   96.86   57.56   34.16   96.22   31.49   44.79   52.79   32.09   37.99   -4.45  -14.24   -4.33   -6.47  -13.85  -18.23   -7.48   -2.23  -18.78   -3.58   -5.37   -9.32
 43   30.73   97.08   97.75   21.24   83.27   38.09   65.96   57.56   98.93   90.36   92.33   93.65   -6.94   -1.89   -2.98  -17.15  -13.80  -16.34   -9.51  -17.48   -9.35   -2.57   -2.92   -4.44
 44   77.37   51.59   84.06   98.49   63.61   92.06   61.11   69.20   38.00   67.93   56.44   58.33   -3.42   -6.65   -3.92   -4.71  -18.56   -0.24   -5.89   -6.44  -13.10   -0.18  -16.39   -4.72
 45   99.80   72.00   80.39   80.49   51.55   36.63   55.32   48.48   29.45   80.71   65.23   59.80   -9.63  -11.91  -12.59  -12.50   -2.61   -1.47  -14.07  -17.12  -16.04  -12.26  -16.55  -10.60 ;

# Node capacity lower bound
parameter bl(i) /  1     0.00
                   2     0.00
                   3     0.00
                   4     0.00
                   5     0.00
                   6     0.00
                   7     0.00
                   8     0.00
                   9     0.00
                  10     0.00
                  11     0.00
                  12     0.00
                  13     0.00
                  14     0.00
                  15     0.00
                  16     0.00
                  17     0.00
                  18     0.00
                  19     0.00
                  20     0.00
                  31     0.00
                  32     0.00
                  33     0.00
                  34     0.00
                  35     0.00
                  36     0.00
                  37     0.00
                  38     0.00
                  39     0.00
                  40     0.00
                  41     0.00
                  42     0.00
                  43     0.00
                  44     0.00
                  45     0.00 / ;

# Node capacity upper bound
parameter bu(i) /  1    69.00
                   2   183.00
                   3   246.00
                   4   283.00
                   5   146.00
                   6   177.00
                   7   271.00
                   8   291.00
                   9   129.00
                  10   277.00
                  11    93.00
                  12    81.00
                  13   197.00
                  14   237.00
                  15   207.00
                  16    79.00
                  17    48.00
                  18   122.00
                  19   200.00
                  20   247.00
                  21    72.00
                  22   106.00
                  23   174.00
                  24   145.00
                  25   161.00
                  26    93.00
                  27    72.00
                  28   200.00
                  29    63.00
                  30   122.00
                  31   284.00
                  32   169.00
                  33   163.00
                  34   257.00
                  35   147.00
                  36   198.00
                  37   231.00
                  38   277.00
                  39   278.00
                  40   247.00
                  41   262.00
                  42   139.00
                  43   289.00
                  44    30.00
                  45    76.00 / ;

$include xmodel.gms