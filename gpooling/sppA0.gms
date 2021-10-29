$ontext
    sppA0 pooling problem data.
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
  1   21.00    0.00   21.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00  -27.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00  -21.00    0.00    0.00
  2    0.00   43.00   43.00   43.00    0.00   43.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    3.00    0.00    0.00    0.00    0.00    0.00   -5.00    0.00    0.00    0.00    2.00    0.00
  3    0.00    0.00    0.00    0.00    0.00   28.00    0.00    0.00   28.00   28.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00  -21.00  -13.00    0.00    0.00    0.00    0.00    0.00  -12.00
  4    0.00   37.00    0.00   37.00    0.00    0.00    0.00    0.00   37.00    0.00    0.00    0.00    0.00    0.00  -13.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00
  5    0.00   50.00   50.00    0.00    0.00    0.00    0.00    0.00   50.00    0.00    0.00    6.00    0.00   10.00    0.00    2.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00   10.00
  6   13.00    0.00   13.00    0.00    0.00    0.00    0.00   13.00    0.00   13.00    0.00    0.00    0.00    0.00    0.00    0.00  -37.00    0.00  -28.00    0.00    0.00    0.00    0.00  -28.00  -27.00
  7    0.00   14.00    0.00   14.00   14.00    0.00    0.00   14.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00  -36.00    0.00    0.00  -34.00    0.00    0.00    0.00    0.00  -26.00
  8    0.00    0.00    0.00    0.00    0.00    0.00   25.00   25.00    0.00    0.00    0.00  -19.00    0.00  -15.00  -25.00    0.00    0.00  -24.00    0.00    0.00    0.00    0.00    0.00    0.00  -15.00
  9    0.00    0.00   31.00    0.00    0.00    0.00   31.00    0.00   31.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00  -18.00    0.00    0.00  -10.00    0.00    0.00    0.00    0.00
 10    0.00    0.00    0.00    0.00    0.00   14.00   14.00    0.00   14.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00  -27.00    0.00  -28.00    0.00    0.00
 11   36.00   36.00    0.00    0.00    0.00    0.00    0.00    0.00   36.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00
 12   31.00    0.00    0.00    0.00   31.00    0.00    0.00    0.00   31.00    0.00    0.00    0.00  -19.00    0.00    0.00  -17.00    0.00    0.00    0.00    0.00    0.00   -9.00    0.00    0.00    0.00
 13    0.00    0.00    0.00    0.00   37.00   37.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00  -13.00    0.00    0.00    0.00   -4.00    0.00    0.00    0.00    0.00
 14   25.00   25.00   25.00   25.00    0.00   25.00    0.00   25.00   25.00    0.00    0.00  -19.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00
 15   50.00    0.00    0.00    0.00    0.00   50.00    0.00    0.00    0.00   50.00    2.00    0.00    0.00    0.00    0.00    0.00    0.00    1.00    0.00    0.00    9.00    0.00    0.00    0.00   10.00
 16    0.00    0.00    0.00    0.00    0.00   43.00    0.00    0.00   43.00   43.00   -5.00   -1.00    0.00    0.00    0.00    0.00    0.00   -6.00    0.00    0.00    0.00    3.00    0.00    0.00    0.00
 17    0.00   26.00    0.00   26.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00  -24.00    0.00  -24.00    0.00    0.00    0.00    0.00    0.00    0.00  -14.00    0.00    0.00  -14.00
 18   29.00   29.00   29.00    0.00    0.00   29.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00  -11.00    0.00    0.00    0.00    0.00    0.00  -19.00    0.00  -11.00    0.00  -12.00  -11.00
 19    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00   -7.00    0.00
 20    0.00    0.00    0.00   14.00   14.00   14.00    0.00    0.00    0.00   14.00  -34.00    0.00    0.00    0.00    0.00    0.00  -36.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00
 21    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00  -40.00    0.00    0.00    0.00  -49.00  -41.00  -48.00  -41.00    0.00    0.00    0.00    0.00
 22    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00  -50.00    0.00    0.00    0.00    0.00  -40.00  -42.00  -41.00    0.00
 23    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00  -48.00  -44.00  -50.00    0.00    0.00    0.00  -50.00    0.00    0.00    0.00    0.00    0.00  -42.00    0.00    0.00
 24    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00  -50.00    0.00  -50.00  -48.00    0.00    0.00    0.00  -48.00    0.00    0.00  -42.00    0.00    0.00
 25    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00  -48.00    0.00    0.00    0.00    0.00    0.00    0.00  -49.00  -41.00    0.00    0.00  -40.00  -42.00    0.00  -40.00
 26    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00  -48.00    0.00    0.00    0.00    0.00    0.00    0.00  -49.00    0.00    0.00  -41.00    0.00  -42.00    0.00  -40.00
 27    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00  -40.00  -50.00  -48.00    0.00  -49.00    0.00    0.00  -41.00    0.00    0.00  -41.00  -40.00
 28    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00  -48.00    0.00    0.00    0.00    0.00  -48.00    0.00    0.00  -41.00    0.00  -41.00  -40.00    0.00    0.00  -40.00
 29    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00  -48.00  -44.00  -50.00  -40.00    0.00    0.00    0.00    0.00  -41.00  -48.00    0.00    0.00  -42.00    0.00    0.00
 30    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00  -40.00    0.00    0.00    0.00    0.00    0.00    0.00  -41.00    0.00    0.00  -41.00  -40.00 ;

# The adjacency matrix (the arcs set A)
table a(i,j)
     21  22  23  24  25  26  27  28  29  30  31  32  33  34  35  36  37  38  39  40  41  42  43  44  45
  1   1   0   1   0   0   0   0   0   0   0   1   0   0   0   0   0   0   0   0   0   0   0   1   0   0
  2   0   1   1   1   0   1   0   0   0   0   0   0   0   1   0   0   0   0   0   1   0   0   0   1   0
  3   0   0   0   0   0   1   0   0   1   1   0   0   0   0   0   0   0   1   1   0   0   0   0   0   1
  4   0   1   0   1   0   0   0   0   1   0   0   0   0   0   1   0   0   0   0   0   0   0   0   0   0
  5   0   1   1   0   0   0   0   0   1   0   0   1   0   1   0   1   0   0   0   0   0   0   0   0   1
  6   1   0   1   0   0   0   0   1   0   1   0   0   0   0   0   0   1   0   1   0   0   0   0   1   1
  7   0   1   0   1   1   0   0   1   0   0   0   0   0   0   0   0   1   0   0   1   0   0   0   0   1
  8   0   0   0   0   0   0   1   1   0   0   0   1   0   1   1   0   0   1   0   0   0   0   0   0   1
  9   0   0   1   0   0   0   1   0   1   0   0   0   0   0   0   0   0   1   0   0   1   0   0   0   0
 10   0   0   0   0   0   1   1   0   1   0   0   0   0   0   0   0   0   0   0   0   1   0   1   0   0
 11   1   1   0   0   0   0   0   0   1   0   0   0   0   0   0   0   0   0   0   0   0   0   0   0   0
 12   1   0   0   0   1   0   0   0   1   0   0   0   1   0   0   1   0   0   0   0   0   1   0   0   0
 13   0   0   0   0   1   1   0   0   0   0   0   0   0   0   0   0   1   0   0   0   1   0   0   0   0
 14   1   1   1   1   0   1   0   1   1   0   0   1   0   0   0   0   0   0   0   0   0   0   0   0   0
 15   1   0   0   0   0   1   0   0   0   1   1   0   0   0   0   0   0   1   0   0   1   0   0   0   1
 16   0   0   0   0   0   1   0   0   1   1   1   1   0   0   0   0   0   1   0   0   0   1   0   0   0
 17   0   1   0   1   0   0   0   0   0   0   0   0   1   0   1   0   0   0   0   0   0   1   0   0   1
 18   1   1   1   0   0   1   0   0   0   0   0   0   0   1   0   0   0   0   0   1   0   1   0   1   1
 19   0   0   0   0   0   0   0   0   0   0   0   0   0   0   0   0   0   0   0   0   0   0   0   1   0
 20   0   0   0   1   1   1   0   0   0   1   1   0   0   0   0   0   1   0   0   0   0   0   0   0   0
 21   0   0   0   0   0   0   0   0   0   0   0   0   0   1   0   0   0   1   1   1   1   0   0   0   0
 22   0   0   0   0   0   0   0   0   0   0   0   0   0   0   0   0   1   0   0   0   0   1   1   1   0
 23   0   0   0   0   0   0   0   0   0   0   1   1   1   0   0   0   1   0   0   0   0   0   1   0   0
 24   0   0   0   0   0   0   0   0   0   0   0   0   1   0   1   1   0   0   0   1   0   0   1   0   0
 25   0   0   0   0   0   0   0   0   0   0   1   0   0   0   0   0   0   1   1   0   0   1   1   0   1
 26   0   0   0   0   0   0   0   0   0   0   1   0   0   0   0   0   0   1   0   0   1   0   1   0   1
 27   0   0   0   0   0   0   0   0   0   0   0   0   0   1   1   1   0   1   0   0   1   0   0   1   1
 28   0   0   0   0   0   0   0   0   0   0   1   0   0   0   0   1   0   0   1   0   1   1   0   0   1
 29   0   0   0   0   0   0   0   0   0   0   1   1   1   1   0   0   0   0   1   1   0   0   1   0   0
 30   0   0   0   0   0   0   0   0   0   0   0   0   0   1   0   0   0   0   0   0   1   0   0   1   1 ;

# Source qualities/terminal quality upper bounds
table q(i,k)
          1       2       3       4       5       6       7       8       9      10      11      12      13      14      15      16      17      18      19      20      21      22      23      24
  1   31.81   20.24   46.07   51.68   67.54   42.38   13.12   47.28   46.15   68.95   10.02   72.96  -31.81  -20.24  -46.07  -51.68  -67.54  -42.38  -13.12  -47.28  -46.15  -68.95  -10.02  -72.96
  2   34.73   38.49   28.09   40.21   34.18    3.33   65.84   16.58   42.82   56.70   72.61   29.68  -34.73  -38.49  -28.09  -40.21  -34.18   -3.33  -65.84  -16.58  -42.82  -56.70  -72.61  -29.68
  3   28.82   50.27   33.39   65.67    7.49   55.40   69.83   27.06   29.77   25.10   73.33   77.38  -28.82  -50.27  -33.39  -65.67   -7.49  -55.40  -69.83  -27.06  -29.77  -25.10  -73.33  -77.38
  4   69.76   16.55    7.09   14.78   34.81   45.33   51.09   73.74   23.51   17.19   67.10   13.47  -69.76  -16.55   -7.09  -14.78  -34.81  -45.33  -51.09  -73.74  -23.51  -17.19  -67.10  -13.47
  5   39.28   13.01   37.76   65.85   75.68    4.01    8.22    7.76   10.63   22.84    9.97    7.12  -39.28  -13.01  -37.76  -65.85  -75.68   -4.01   -8.22   -7.76  -10.63  -22.84   -9.97   -7.12
  6   77.99   49.99   70.67   54.29    6.49   72.33   63.73    7.80   56.56   52.13   74.37    3.97  -77.99  -49.99  -70.67  -54.29   -6.49  -72.33  -63.73   -7.80  -56.56  -52.13  -74.37   -3.97
  7   79.04   11.51    1.32    3.04   66.51   71.80   14.54   21.04   74.75   53.37   28.01   48.15  -79.04  -11.51   -1.32   -3.04  -66.51  -71.80  -14.54  -21.04  -74.75  -53.37  -28.01  -48.15
  8   31.08   24.38   35.34   34.78   18.20   52.77   25.05   39.56   50.73   32.42    7.29   15.36  -31.08  -24.38  -35.34  -34.78  -18.20  -52.77  -25.05  -39.56  -50.73  -32.42   -7.29  -15.36
  9   59.74   70.27    7.55   46.74   45.11   66.78   13.17    3.60   11.55   28.67   50.79   69.88  -59.74  -70.27   -7.55  -46.74  -45.11  -66.78  -13.17   -3.60  -11.55  -28.67  -50.79  -69.88
 10   41.44   72.35   57.77   25.08   52.58   63.88   15.49   30.02   65.70   10.67   20.64   22.21  -41.44  -72.35  -57.77  -25.08  -52.58  -63.88  -15.49  -30.02  -65.70  -10.67  -20.64  -22.21
 11   12.66   28.06   62.79   32.81   68.22   28.73   66.77   23.53   27.29   41.82   61.47   64.09  -12.66  -28.06  -62.79  -32.81  -68.22  -28.73  -66.77  -23.53  -27.29  -41.82  -61.47  -64.09
 12   23.59   43.76   58.93   57.98   48.87   13.62   34.98   74.71   44.59   56.08   56.08   52.13  -23.59  -43.76  -58.93  -57.98  -48.87  -13.62  -34.98  -74.71  -44.59  -56.08  -56.08  -52.13
 13   26.81    8.25   53.11   54.35   43.33   27.44   16.07   42.06   48.08   52.67   42.80   58.14  -26.81   -8.25  -53.11  -54.35  -43.33  -27.44  -16.07  -42.06  -48.08  -52.67  -42.80  -58.14
 14   77.82   69.55   66.69    6.80   41.42   56.37   34.87   77.07   40.06   57.96   47.70    8.96  -77.82  -69.55  -66.69   -6.80  -41.42  -56.37  -34.87  -77.07  -40.06  -57.96  -47.70   -8.96
 15   32.47   74.54   18.37   12.67   52.48   58.57   57.54   68.32   73.86   76.42    1.17   28.15  -32.47  -74.54  -18.37  -12.67  -52.48  -58.57  -57.54  -68.32  -73.86  -76.42   -1.17  -28.15
 16   42.00    9.55   61.75   17.84   23.40   57.34   35.64    2.98   56.68   58.79   76.47   17.05  -42.00   -9.55  -61.75  -17.84  -23.40  -57.34  -35.64   -2.98  -56.68  -58.79  -76.47  -17.05
 17   25.02   71.90   60.13   34.48   57.76   57.08   68.52   25.76   61.49   46.92   31.93   69.74  -25.02  -71.90  -60.13  -34.48  -57.76  -57.08  -68.52  -25.76  -61.49  -46.92  -31.93  -69.74
 18   40.15   29.97   34.91   12.35   14.38   16.92   64.63   53.09    7.50   36.12   57.87   63.27  -40.15  -29.97  -34.91  -12.35  -14.38  -16.92  -64.63  -53.09   -7.50  -36.12  -57.87  -63.27
 19   45.93   70.78   52.53   38.45   73.26   67.69   37.83   76.91    9.23   47.49    7.06   63.55  -45.93  -70.78  -52.53  -38.45  -73.26  -67.69  -37.83  -76.91   -9.23  -47.49   -7.06  -63.55
 20   17.00   78.31    4.88   42.58   77.08   29.91   44.87   51.62   35.89   36.77    0.62   26.36  -17.00  -78.31   -4.88  -42.58  -77.08  -29.91  -44.87  -51.62  -35.89  -36.77   -0.62  -26.36
 31   89.68   54.59   78.86   74.96   42.98   77.22   90.33   31.79   39.65   89.70   84.05   26.38  -14.17   -9.87   -3.65   -9.70   -8.42   -4.93  -16.43  -17.19   -1.61  -17.78   -2.24  -14.91
 32   85.69   85.39   97.76   87.50   27.58   84.67   21.70   26.11   65.66   93.72   91.80   51.56  -16.36  -13.52   -6.08   -1.13   -8.17  -11.54   -0.32   -4.95  -15.92  -15.04   -1.30  -16.00
 33   77.02   75.43   96.30   44.72   42.89   29.77   99.86   36.27   77.15   21.51   68.04   56.75   -9.54  -10.73  -12.57  -11.36  -18.17  -17.18  -15.20  -11.14   -0.44  -12.00   -3.44  -19.80
 34   84.49   66.67   68.76   53.45   39.62   57.70   39.28   98.95   39.34   95.30   52.75   47.93   -7.28  -12.74   -9.42   -3.93   -1.46   -4.42  -15.61  -14.68   -3.77   -1.77  -14.94  -14.03
 35   89.70   26.76   72.04   67.57   50.66   53.50   90.16   74.91   35.73   31.02   91.10   39.92  -15.54  -11.97   -1.71  -14.89   -6.08   -2.41   -0.64   -4.57   -2.25  -10.65  -16.25   -8.58
 36   45.33   32.41   66.21   40.31   58.62   51.06   86.25   23.72   82.99   91.64   54.14   92.58  -19.00  -12.77  -12.10  -14.89   -2.44  -10.96  -11.49   -7.81   -2.62  -19.59  -14.10   -4.73
 37   73.62   92.09   77.65   78.34   84.48   28.58   34.15   66.51   39.60   33.72   52.25   35.43  -18.30   -5.76   -1.09   -7.73  -19.83  -19.23   -4.03   -6.57  -13.79  -18.27   -8.16   -8.84
 38   48.30   83.46   29.36   53.85   46.11   56.44   35.14   91.93   85.62   80.93   50.29   52.76   -1.89   -1.23   -0.76  -19.60   -9.48   -5.00   -0.82   -6.17  -12.10   -5.58  -13.82  -16.71
 39   36.85   38.28   27.92   76.81   98.21   89.69   44.12   87.31   48.20   57.38   87.65   43.51   -2.06  -14.81  -17.45   -4.25   -5.59   -0.87   -0.74  -14.04   -3.94  -16.39  -16.47   -3.33
 40   90.56   86.18   22.29   70.36   54.44   21.81   93.09   93.28   26.44   54.10   89.68   47.52  -19.58   -2.59   -7.47  -11.55  -10.89   -4.08  -10.82  -18.56   -3.10  -18.26  -15.96  -12.72
 41   76.89   75.00   31.14   30.31   91.89   80.75   20.97   67.00   51.75   75.63   54.91   67.80   -7.03  -14.56   -6.23   -1.60   -7.65   -9.25  -15.88  -11.67   -5.42  -15.38  -14.07  -12.01
 42   50.68   82.27   84.51   49.28   22.10   43.15   75.65   24.74   74.95   83.86   41.21   82.91  -10.94  -17.87  -13.50  -16.56   -0.01   -0.48  -14.43  -14.08  -14.88   -2.79   -9.54  -19.88
 43   42.23   75.38   54.70   36.37   43.03   97.19   45.93   66.87   77.94   42.01   57.13   27.12   -9.80   -7.60   -3.37  -14.63   -5.74  -15.77  -19.92   -8.14   -9.90  -17.57   -9.27   -6.48
 44   57.79   56.35   30.91   76.98   34.38   98.13   77.69   62.91   93.21   34.57   95.63   53.44   -9.73  -18.48  -18.91   -6.02   -5.72   -6.73   -7.64   -3.23   -0.27  -19.22  -12.07  -13.62
 45   43.24   24.24   50.50   90.41   23.54   28.23   24.82   28.24   94.15   24.52   67.32   44.09  -16.21   -0.08   -1.08   -2.01  -14.66   -6.48  -18.29  -19.09  -10.22  -15.18   -1.77  -12.50 ;

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
parameter bu(i) /  1   166.00
                   2   240.00
                   3   217.00
                   4   150.00
                   5   161.00
                   6   118.00
                   7    59.00
                   8   219.00
                   9   169.00
                  10   273.00
                  11    66.00
                  12    69.00
                  13   177.00
                  14    62.00
                  15   178.00
                  16     9.00
                  17   302.00
                  18    96.00
                  19   175.00
                  20    63.00
                  21    97.00
                  22   158.00
                  23    91.00
                  24    94.00
                  25   147.00
                  26   138.00
                  27   177.00
                  28   184.00
                  29   113.00
                  30   137.00
                  31   176.00
                  32   265.00
                  33   195.00
                  34   107.00
                  35   183.00
                  36   254.00
                  37   119.00
                  38   231.00
                  39   265.00
                  40   250.00
                  41   231.00
                  42   247.00
                  43   268.00
                  44   215.00
                  45    14.00 / ;

$include xmodel.gms