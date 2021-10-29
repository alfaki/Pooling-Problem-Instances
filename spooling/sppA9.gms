$ontext
    sppA9 pooling problem data.
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
  1   31.00   31.00   31.00   31.00   31.00   31.00   31.00    0.00   31.00   31.00  -19.00    0.00  -19.00  -19.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00  -17.00
  2   38.00   38.00   38.00   38.00   38.00   38.00   38.00   38.00   38.00   38.00    0.00  -10.00    0.00  -12.00   -3.00    0.00    0.00   -8.00   -9.00    0.00   -9.00    0.00  -10.00   -3.00  -10.00
  3   28.00   28.00   28.00   28.00   28.00   28.00    0.00   28.00   28.00    0.00    0.00    0.00    0.00  -22.00  -13.00  -17.00  -20.00  -18.00  -19.00  -21.00    0.00  -14.00    0.00  -13.00    0.00
  4   48.00   48.00   48.00   48.00    0.00   48.00    0.00    0.00   48.00   48.00   -2.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00   -1.00    0.00    0.00    0.00    7.00    0.00
  5   22.00   22.00   22.00    0.00    0.00    0.00   22.00   22.00   22.00   22.00  -28.00  -26.00  -28.00    0.00  -19.00    0.00    0.00    0.00    0.00    0.00    0.00  -20.00    0.00    0.00  -26.00
  6   12.00   12.00   12.00   12.00   12.00   12.00   12.00    0.00    0.00   12.00    0.00    0.00    0.00    0.00    0.00    0.00  -36.00    0.00    0.00    0.00    0.00    0.00    0.00  -29.00    0.00
  7    0.00   28.00   28.00   28.00   28.00   28.00    0.00   28.00   28.00   28.00    0.00  -20.00    0.00  -22.00  -13.00  -17.00  -20.00  -18.00  -19.00    0.00    0.00  -14.00  -20.00    0.00  -20.00
  8   28.00   28.00   28.00    0.00   28.00   28.00   28.00   28.00   28.00   28.00    0.00  -20.00    0.00    0.00    0.00    0.00    0.00  -18.00    0.00  -21.00  -19.00  -14.00    0.00  -13.00  -20.00
  9   47.00   47.00   47.00   47.00   47.00   47.00    0.00    0.00   47.00   47.00    0.00    0.00   -3.00    0.00    6.00    0.00    0.00    0.00    0.00    0.00    0.00    5.00    0.00    0.00   -1.00
 10    0.00   26.00   26.00   26.00   26.00   26.00   26.00   26.00   26.00   26.00  -24.00    0.00    0.00    0.00    0.00  -19.00    0.00    0.00  -21.00    0.00    0.00  -16.00  -22.00    0.00  -22.00
 11   15.00    0.00   15.00   15.00   15.00   15.00   15.00   15.00   15.00   15.00  -35.00    0.00    0.00    0.00    0.00  -30.00  -33.00    0.00    0.00    0.00  -32.00  -27.00    0.00    0.00  -33.00
 12   26.00   26.00   26.00   26.00   26.00   26.00    0.00   26.00   26.00   26.00  -24.00  -22.00    0.00  -24.00  -15.00    0.00    0.00  -20.00    0.00  -23.00    0.00    0.00    0.00  -15.00  -22.00
 13   46.00   46.00   46.00   46.00   46.00   46.00   46.00   46.00    0.00   46.00   -4.00   -2.00    0.00    0.00    0.00    0.00   -2.00    0.00   -1.00   -3.00   -1.00    0.00    0.00    0.00   -2.00
 14   37.00   37.00    0.00   37.00    0.00   37.00   37.00   37.00   37.00   37.00  -13.00    0.00    0.00    0.00    0.00    0.00    0.00   -9.00    0.00    0.00  -10.00    0.00    0.00    0.00    0.00
 15   45.00   45.00   45.00    0.00    0.00   45.00   45.00    0.00   45.00   45.00   -5.00    0.00   -5.00   -5.00    0.00    0.00    0.00    0.00    0.00    0.00   -2.00    0.00   -3.00    4.00   -3.00
 16   44.00    0.00   44.00   44.00   44.00   44.00   44.00   44.00   44.00   44.00    0.00   -4.00    0.00    0.00    3.00    0.00   -4.00    0.00    0.00   -5.00   -3.00    0.00    0.00    3.00   -4.00
 17   50.00   50.00   50.00   50.00   50.00   50.00   50.00   50.00   50.00   50.00    0.00    0.00    0.00    0.00    0.00    5.00    0.00    0.00    0.00    0.00    0.00    8.00    2.00    0.00    0.00
 18   31.00   31.00   31.00   31.00   31.00    0.00    0.00    0.00   31.00   31.00  -19.00    0.00  -19.00    0.00  -10.00  -14.00  -17.00  -15.00    0.00  -18.00    0.00    0.00    0.00    0.00  -17.00
 19    0.00   29.00   29.00    0.00   29.00   29.00   29.00    0.00   29.00   29.00    0.00    0.00    0.00  -21.00    0.00  -16.00    0.00    0.00  -18.00    0.00    0.00    0.00  -19.00    0.00  -19.00
 20   29.00    0.00    0.00   29.00    0.00   29.00    0.00   29.00   29.00   29.00  -21.00    0.00    0.00  -21.00  -12.00  -16.00  -19.00    0.00  -18.00  -20.00    0.00    0.00    0.00    0.00    0.00
 21    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00  -50.00  -48.00    0.00    0.00  -41.00  -45.00    0.00  -46.00  -47.00  -49.00    0.00    0.00  -48.00  -41.00    0.00
 22    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00  -50.00  -48.00  -50.00  -50.00  -41.00  -45.00    0.00  -46.00    0.00  -49.00  -47.00    0.00  -48.00  -41.00  -48.00
 23    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00  -50.00  -48.00  -50.00  -50.00  -41.00  -45.00  -48.00    0.00  -47.00  -49.00  -47.00  -42.00  -48.00    0.00    0.00
 24    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00  -50.00  -48.00  -50.00  -50.00  -41.00  -45.00  -48.00  -46.00    0.00  -49.00  -47.00    0.00  -48.00  -41.00  -48.00
 25    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00  -50.00  -48.00  -50.00  -50.00    0.00  -45.00  -48.00  -46.00    0.00  -49.00  -47.00  -42.00  -48.00  -41.00  -48.00
 26    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00  -50.00  -48.00    0.00  -50.00  -41.00    0.00  -48.00  -46.00  -47.00  -49.00  -47.00  -42.00  -48.00  -41.00  -48.00
 27    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00  -48.00  -50.00  -50.00  -41.00  -45.00  -48.00  -46.00  -47.00  -49.00  -47.00  -42.00  -48.00  -41.00    0.00
 28    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00  -50.00  -48.00  -50.00  -50.00  -41.00  -45.00  -48.00  -46.00  -47.00  -49.00  -47.00    0.00    0.00  -41.00  -48.00
 29    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00  -50.00  -48.00    0.00  -50.00  -41.00  -45.00  -48.00    0.00    0.00  -49.00  -47.00  -42.00  -48.00  -41.00  -48.00
 30    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00    0.00  -48.00  -50.00    0.00  -41.00  -45.00  -48.00  -46.00  -47.00  -49.00  -47.00  -42.00  -48.00  -41.00    0.00 ;

# The adjacency matrix (the arcs set A)
table a(i,j)
     21  22  23  24  25  26  27  28  29  30  31  32  33  34  35  36  37  38  39  40  41  42  43  44  45
  1   1   1   1   1   1   1   1   0   1   1   1   0   1   1   0   0   0   0   0   0   0   0   0   0   1
  2   1   1   1   1   1   1   1   1   1   1   0   1   0   1   1   0   0   1   1   0   1   0   1   1   1
  3   1   1   1   1   1   1   0   1   1   0   0   0   0   1   1   1   1   1   1   1   0   1   0   1   0
  4   1   1   1   1   0   1   0   0   1   1   1   0   0   0   0   0   0   0   0   1   0   0   0   1   0
  5   1   1   1   0   0   0   1   1   1   1   1   1   1   0   1   0   0   0   0   0   0   1   0   0   1
  6   1   1   1   1   1   1   1   0   0   1   0   0   0   0   0   0   1   0   0   0   0   0   0   1   0
  7   0   1   1   1   1   1   0   1   1   1   0   1   0   1   1   1   1   1   1   0   0   1   1   0   1
  8   1   1   1   0   1   1   1   1   1   1   0   1   0   0   0   0   0   1   0   1   1   1   0   1   1
  9   1   1   1   1   1   1   0   0   1   1   0   0   1   0   1   0   0   0   0   0   0   1   0   0   1
 10   0   1   1   1   1   1   1   1   1   1   1   0   0   0   0   1   0   0   1   0   0   1   1   0   1
 11   1   0   1   1   1   1   1   1   1   1   1   0   0   0   0   1   1   0   0   0   1   1   0   0   1
 12   1   1   1   1   1   1   0   1   1   1   1   1   0   1   1   0   0   1   0   1   0   0   0   1   1
 13   1   1   1   1   1   1   1   1   0   1   1   1   0   0   0   0   1   0   1   1   1   0   0   0   1
 14   1   1   0   1   0   1   1   1   1   1   1   0   0   0   0   0   0   1   0   0   1   0   0   0   0
 15   1   1   1   0   0   1   1   0   1   1   1   0   1   1   0   0   0   0   0   0   1   0   1   1   1
 16   1   0   1   1   1   1   1   1   1   1   0   1   0   0   1   0   1   0   0   1   1   0   0   1   1
 17   1   1   1   1   1   1   1   1   1   1   0   0   0   0   0   1   0   0   0   0   0   1   1   0   0
 18   1   1   1   1   1   0   0   0   1   1   1   0   1   0   1   1   1   1   0   1   0   0   0   0   1
 19   0   1   1   0   1   1   1   0   1   1   0   0   0   1   0   1   0   0   1   0   0   0   1   0   1
 20   1   0   0   1   0   1   0   1   1   1   1   0   0   1   1   1   1   0   1   1   0   0   0   0   0
 21   0   0   0   0   0   0   0   0   0   0   1   1   0   0   1   1   0   1   1   1   0   0   1   1   0
 22   0   0   0   0   0   0   0   0   0   0   1   1   1   1   1   1   0   1   0   1   1   0   1   1   1
 23   0   0   0   0   0   0   0   0   0   0   1   1   1   1   1   1   1   0   1   1   1   1   1   0   0
 24   0   0   0   0   0   0   0   0   0   0   1   1   1   1   1   1   1   1   0   1   1   0   1   1   1
 25   0   0   0   0   0   0   0   0   0   0   1   1   1   1   0   1   1   1   0   1   1   1   1   1   1
 26   0   0   0   0   0   0   0   0   0   0   1   1   0   1   1   0   1   1   1   1   1   1   1   1   1
 27   0   0   0   0   0   0   0   0   0   0   0   1   1   1   1   1   1   1   1   1   1   1   1   1   0
 28   0   0   0   0   0   0   0   0   0   0   1   1   1   1   1   1   1   1   1   1   1   0   0   1   1
 29   0   0   0   0   0   0   0   0   0   0   1   1   0   1   1   1   1   0   0   1   1   1   1   1   1
 30   0   0   0   0   0   0   0   0   0   0   0   1   1   0   1   1   1   1   1   1   1   1   1   1   0 ;

# Source qualities/terminal quality upper bounds
table q(i,k)
          1       2       3       4       5       6       7       8       9      10      11      12      13      14      15      16      17      18      19      20      21      22      23      24
  1   44.13   79.97   18.18   16.04   58.84   58.00   12.71   35.87   73.12   15.37   69.65   74.97  -44.13  -79.97  -18.18  -16.04  -58.84  -58.00  -12.71  -35.87  -73.12  -15.37  -69.65  -74.97
  2   47.71   60.74   36.67   44.42   49.87    2.29   47.47   52.64   45.00   73.18   72.81    4.89  -47.71  -60.74  -36.67  -44.42  -49.87   -2.29  -47.47  -52.64  -45.00  -73.18  -72.81   -4.89
  3   36.59   63.46   64.04   39.90    2.67   39.20   22.10   53.76   26.57   24.54   24.15   69.84  -36.59  -63.46  -64.04  -39.90   -2.67  -39.20  -22.10  -53.76  -26.57  -24.54  -24.15  -69.84
  4   32.87   65.41   75.96   73.45   27.01   47.89   14.41   69.64    4.27   65.73   14.06   10.45  -32.87  -65.41  -75.96  -73.45  -27.01  -47.89  -14.41  -69.64   -4.27  -65.73  -14.06  -10.45
  5   42.84    7.87   11.64   63.76    6.47   45.27   77.20   31.79   66.99   66.89    0.50   64.98  -42.84   -7.87  -11.64  -63.76   -6.47  -45.27  -77.20  -31.79  -66.99  -66.89   -0.50  -64.98
  6    9.69   48.21    3.19   31.10   49.66   63.28   13.70   24.34   50.84   57.58   62.31   31.37   -9.69  -48.21   -3.19  -31.10  -49.66  -63.28  -13.70  -24.34  -50.84  -57.58  -62.31  -31.37
  7   58.90   56.50   23.22    9.22   12.72   40.93   11.17   50.67   17.13   32.27   19.34   78.28  -58.90  -56.50  -23.22   -9.22  -12.72  -40.93  -11.17  -50.67  -17.13  -32.27  -19.34  -78.28
  8   51.96    3.43   77.39   78.41   23.13   69.47   54.09   45.10   11.98   61.43   74.43   33.17  -51.96   -3.43  -77.39  -78.41  -23.13  -69.47  -54.09  -45.10  -11.98  -61.43  -74.43  -33.17
  9   25.88   12.85   19.13   26.93   11.16   61.94   45.17   20.07   66.92   39.75   33.13    3.07  -25.88  -12.85  -19.13  -26.93  -11.16  -61.94  -45.17  -20.07  -66.92  -39.75  -33.13   -3.07
 10   21.96   29.81   44.03   73.86    9.82   56.28   51.82   76.88   55.69    2.18   32.12   25.79  -21.96  -29.81  -44.03  -73.86   -9.82  -56.28  -51.82  -76.88  -55.69   -2.18  -32.12  -25.79
 11   70.16   47.71    4.09   28.68   58.39   50.78   16.02    5.61   66.81   59.70   40.55   21.13  -70.16  -47.71   -4.09  -28.68  -58.39  -50.78  -16.02   -5.61  -66.81  -59.70  -40.55  -21.13
 12   46.80   15.51   70.42   66.90   54.97   41.62   36.30   56.99   49.57   78.89   66.06   62.33  -46.80  -15.51  -70.42  -66.90  -54.97  -41.62  -36.30  -56.99  -49.57  -78.89  -66.06  -62.33
 13   33.70   20.12   77.54   68.62   67.18   38.69   18.87   37.09   65.44   70.43    2.02   61.64  -33.70  -20.12  -77.54  -68.62  -67.18  -38.69  -18.87  -37.09  -65.44  -70.43   -2.02  -61.64
 14   45.21   27.11   62.63   12.26    2.40   35.01   76.37   59.89   49.05   78.00   46.80   16.65  -45.21  -27.11  -62.63  -12.26   -2.40  -35.01  -76.37  -59.89  -49.05  -78.00  -46.80  -16.65
 15    4.17   23.46   18.44   66.62   74.19   39.08   32.65   33.86   33.55   14.75   50.99   66.85   -4.17  -23.46  -18.44  -66.62  -74.19  -39.08  -32.65  -33.86  -33.55  -14.75  -50.99  -66.85
 16   24.61   64.79   25.01   43.31   52.12   52.02   63.36   48.39   63.09   25.51   53.74   67.23  -24.61  -64.79  -25.01  -43.31  -52.12  -52.02  -63.36  -48.39  -63.09  -25.51  -53.74  -67.23
 17   64.24   52.41   60.38   34.19   20.42   32.69   47.85   52.39   78.42   68.60   13.69   36.14  -64.24  -52.41  -60.38  -34.19  -20.42  -32.69  -47.85  -52.39  -78.42  -68.60  -13.69  -36.14
 18    6.81   64.75   27.18   73.81   66.49   15.99   78.03   60.54   77.17   66.80   10.49   29.26   -6.81  -64.75  -27.18  -73.81  -66.49  -15.99  -78.03  -60.54  -77.17  -66.80  -10.49  -29.26
 19   66.64   18.54   15.71   18.21   42.91    8.24   25.47   57.15   52.92   68.55   65.33   56.99  -66.64  -18.54  -15.71  -18.21  -42.91   -8.24  -25.47  -57.15  -52.92  -68.55  -65.33  -56.99
 20   16.54   55.20   25.39   36.64    4.03   79.92   76.21    2.23   21.31   10.66    8.74   77.64  -16.54  -55.20  -25.39  -36.64   -4.03  -79.92  -76.21   -2.23  -21.31  -10.66   -8.74  -77.64
 31   95.97   62.50   52.36   65.51   74.93   88.78   28.15   45.16   20.08   78.33   58.63   48.56   -6.57   -0.38  -16.94   -5.21   -9.14   -3.28  -10.54   -9.97   -5.12  -11.66   -5.91   -9.23
 32   48.68   38.67   36.84   92.99   99.84   83.51   57.80   70.12   93.04   37.60   31.55   77.59   -5.19  -11.40  -11.00   -8.47  -17.35   -1.62   -3.29   -5.61   -9.30   -2.48   -3.66   -8.20
 33   84.39   21.45   43.57   24.05   75.54   89.48   66.10   20.48   77.80   28.72   33.04   99.07  -15.85  -12.54  -12.05   -5.86   -0.97   -1.67   -5.32  -10.92  -17.98   -2.66   -7.76  -15.74
 34   36.63   58.81   26.67   43.33   34.18   53.34   48.50   45.38   43.84   63.73   67.17   91.37  -19.38   -7.40  -14.91   -6.72   -3.94  -18.81  -12.51  -10.97   -5.50   -3.64  -10.17   -9.34
 35   57.03   59.61   46.64   32.69   86.24   21.60   80.07   53.28   28.03   45.75   33.24   94.90  -12.66   -0.43  -12.95  -15.13  -16.57   -8.62  -17.71  -11.74  -15.70  -16.24  -11.14   -8.71
 36   64.52   24.89   91.23   38.06   24.06   94.03   20.51   42.63   22.12   89.33   52.66   96.74   -0.41   -2.58   -6.12  -19.07   -9.99   -6.70   -6.37   -0.84   -1.82  -10.75   -8.17  -13.92
 37   87.02   68.65   55.85   73.92   24.52   83.50   85.08   27.10   69.94   54.73   35.11   44.68   -3.80   -7.53  -13.51  -13.53   -1.06  -13.79   -2.10  -12.26  -17.23   -2.84   -9.58   -1.69
 38   89.12   78.37   72.42   32.05   53.47   32.79   49.78   74.14   95.15   27.16   73.50   77.30  -15.26  -12.94  -14.35  -17.50  -18.53  -19.73   -3.54   -1.96   -7.57  -14.28   -6.47  -14.78
 39   90.55   45.91   47.03   57.15   62.71   80.58   51.19   51.73   73.22   82.80   42.86   93.73  -10.33  -10.76   -6.75   -8.10   -6.12  -12.94  -17.54   -8.13   -6.43  -15.32   -1.36  -11.55
 40   22.53   79.28   47.69   33.78   83.62   67.99   62.96   67.78   62.78   44.72   74.47   29.83  -14.94  -16.21   -9.95   -8.83  -18.92   -6.47   -2.24   -1.89   -2.54   -2.48  -11.42  -15.00
 41   52.79   81.18   72.34   50.69   76.32   91.99   78.75   35.65   23.95   20.93   74.19   31.78   -7.69  -16.07   -4.37  -13.90   -0.17  -12.20  -18.77  -19.79  -10.40   -7.56   -2.05  -15.50
 42   41.72   32.08   73.40   99.43   83.14   63.57   29.81   86.43   73.71   98.43   75.39   75.21  -11.64   -6.28  -10.17   -8.09   -9.14  -13.25  -18.98  -13.73   -9.11   -7.62   -1.76  -10.35
 43   78.61   46.46   35.67   84.10   93.26   81.82   87.93   27.93   81.49   45.46   90.40   52.25   -2.23  -10.91  -18.89  -15.13   -5.25   -2.55   -1.60  -16.22  -14.40   -3.14  -15.25  -10.88
 44   34.94   49.78   64.81   66.40   23.36   79.45   33.61   28.42   68.86   81.01   50.23   98.19  -11.18  -19.82  -19.72  -10.11  -16.55   -2.01   -5.68   -7.21  -11.69   -7.38   -6.16  -16.57
 45   42.93   60.83   79.92   51.69   46.99   22.32   55.93   20.43   22.13   58.77   85.91   65.95  -17.78  -11.72   -1.61   -7.39  -14.56   -9.57  -10.72  -13.92  -16.33   -2.10   -7.11  -12.63 ;

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
parameter bu(i) /  1    80.00
                   2   130.00
                   3    36.00
                   4    72.00
                   5   247.00
                   6   117.00
                   7   224.00
                   8   236.00
                   9   298.00
                  10   297.00
                  11     7.00
                  12   273.00
                  13   185.00
                  14   283.00
                  15   162.00
                  16   282.00
                  17    70.00
                  18   172.00
                  19   264.00
                  20    16.00
                  21    66.00
                  22   150.00
                  23    80.00
                  24    86.00
                  25   145.00
                  26   173.00
                  27   195.00
                  28    55.00
                  29    65.00
                  30   105.00
                  31   155.00
                  32     0.00
                  33    25.00
                  34    17.00
                  35   189.00
                  36    51.00
                  37   158.00
                  38    20.00
                  39   264.00
                  40    13.00
                  41   285.00
                  42   255.00
                  43   157.00
                  44   149.00
                  45   120.00 / ;

$include xmodel.gms