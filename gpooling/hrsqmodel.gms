$ontext
    File name: hrsqmodel.gms
    Author: Mohammed Alfaki, December, 2010.
    GAMS model for the heuristic algorithm with the PQ-formulation.
$offtext
#===============================================================================
# Declare options
#===============================================================================
options optcr=1.e-5, optca=1.e-5, limrow=0, limcol=0;
#===============================================================================
# Declare sets and parameters
#===============================================================================
sets lt(i), l(i), tau(t), Tp(t);
lt(i) = i(i)-s(i); l(i) = i(i)-s(i)-t(i);
tau(t) = no; Tp(t) = no;
parameters Fp(i,j); Fp(i,j) = 0;
scalars igap, gap; igap = 1.e-3; gap = 1.e-6;

# Is there a path between (s,l)
parameter p(i,j);
#===============================================================================
# Compute p(s,i) using the Breadth-first-search (BFS)
#===============================================================================
alias (i,ii,iii), (j,jj), (l,h), (Tp,Tpp);
scalar u,path,n,mn;
set openlst(i);
set closedlst(i);
parameter val(i);
loop((ii,jj)$(ord(ii)<=ord(jj)),
  n = 1;
  path = 0;
  val(i) = +inf;
  openlst(i) = no;
  closedlst(i) = no;
  openlst(i)$(ord(i) eq ord(ii)) = yes;
  val(i)$(ord(i) eq ord(ii)) = n;
  while((card(openlst)>0 and path eq 0),
    mn = smin(openlst(i), val(i));
    loop(i$openlst(i),
      if((mn eq val(i)),
        u = ord(i);
        val(i) = +inf;
      );
    );
    openlst(i)$(ord(i) eq u) = no;
    if((ord(jj) eq u),
      path = 1;
    else
      closedlst(i)$(ord(i) eq u) = yes;
      loop((iii,j)$(ord(iii) eq u and a(iii,j)>0 and 
                                         not closedlst(j) and not openlst(j)),
        n = n+1;
        val(j) = n;
        openlst(i)$(ord(i) eq ord(j)) = yes;
      );
    );
  );
  p(ii,jj) = path;
);
#===============================================================================
# Declare variables/bounds
#===============================================================================
variable cost;
positive variables y(s,i), f(i,j);

y.up(s,l) = a(s,l);
f.lo(i,j) = min(bl(i),bl(j))*a(i,j);
f.up(i,j) = min(bu(i),bu(j))*a(i,j);
#===============================================================================
# Declare constraints
#===============================================================================
equations obj(t), sflowcaplb(s,t), sflowcapub(s,t), tflowcaplb(t), 
          ptflowcapub(i,t), flowmassblnc(i,t), qualubLP(t,k), 
          flowpathblnc(s,i,t), qualub(t,k), qualubTp(t,k), propblnc(i), 
          rlt1(i,t), fub(i,j,t);
#===============================================================================
# Define constraints
#===============================================================================
#-----------------------------Objective function--------------------------------
obj(tau).. cost =e= sum((i,j)$(a(i,j)*p(j,tau)>0), c(i,j)*f(i,j));
#-------------------------Raw material availabilities---------------------------
sflowcaplb(s,tau)$(bl(s)*p(s,tau)>0).. 
      sum(j$(a(s,j)>0), Fp(s,j)) + sum(j$(a(s,j)*p(j,tau)>0), f(s,j)) =g= bl(s);
sflowcapub(s,tau)$(bu(s)<+inf and p(s,tau)>0).. 
      sum(j$(a(s,j)>0), Fp(s,j)) + sum(j$(a(s,j)*p(j,tau)>0), f(s,j)) =l= bu(s);
#----------------Pool capacities and product demand restrictions----------------
tflowcaplb(tau)$(bl(tau)>0).. 
                            sum(j$(a(j,tau)>0), Fp(j,tau)+f(j,tau)) =g= bl(tau);
ptflowcapub(lt,tau)$(bu(lt)<+inf and p(lt,tau)>0).. 
                                sum(j$(a(j,lt)>0), Fp(j,lt)+f(j,lt)) =l= bu(lt);
#------------------------Flow mass balance around pools-------------------------
flowmassblnc(l,tau)$(p(l,tau)>0)..   sum(s$(a(s,l)>0), f(s,l)) - f(l,tau) =e= 0;
#---------------Product quality specifications at tau when p0=0-----------------
qualubLP(tau,k)$(abs(q(tau,k))<+inf)..
                              sum(s$(a(s,tau)>0), (q(s,k)-q(tau,k))*f(s,tau)) +
                 sum((s,l)$(a(s,l)*a(l,tau)>0), (q(s,k)-q(tau,k))*f(s,l)) =l= 0;
#-----------------------Commodity flow balance around pools---------------------
flowpathblnc(s,l,tau)$(a(s,l)>0)..                Fp(s,l)+f(s,l)$(p(l,tau)>0) - 
           y(s,l)*(f(l,tau)$(a(l,tau)>0) + sum(Tp$(a(l,Tp)>0), Fp(l,Tp))) =e= 0;
#------------------------Product quality specifications-------------------------
qualub(tau,k)$(abs(q(tau,k))>0 and abs(q(tau,k))<+inf).. 
                              sum(s$(a(s,tau)>0), (q(s,k)-q(tau,k))*f(s,tau)) + 
        sum((s,l)$(a(s,l)*a(l,tau)>0), (q(s,k)-q(tau,k))*y(s,l)*f(l,tau)) =l= 0;
qualubTp(Tp,k)$(abs(q(Tp,k))>0 and abs(q(Tp,k))<+inf).. 
                                sum(s$(a(s,Tp)>0), (q(s,k)-q(Tp,k))*Fp(s,Tp)) + 
          sum((s,l)$(a(s,l)*a(l,Tp)>0), (q(s,k)-q(Tp,k))*y(s,l)*Fp(l,Tp)) =l= 0;
#-------------------------Commodity proportion balances-------------------------
propblnc(l)..                               sum(s$(p(s,l)>0), y(s,l)) - 1 =e= 0;
#---------------------RLT for commodity proportion balances---------------------
rlt1(l,tau)$(a(l,tau)>0)..      sum(s$(a(s,l)>0), y(s,l)*f(l,tau)) =e= f(l,tau);
#----------------------------Flow bound constraints-----------------------------
fub(i,j,tau)$(a(i,j)*p(j,tau)>0)..          Fp(i,j)+f(i,j) =l= min(bu(i),bu(j));
#===============================================================================
# Solve the model
#===============================================================================
model hrslp /obj, sflowcaplb, sflowcapub, tflowcaplb, ptflowcapub, flowmassblnc, 
             qualubLP/;
hrslp.solprint = 2;

option nlp = baron;
model hrsnlp /obj, sflowcaplb, sflowcapub, tflowcaplb, ptflowcapub, 
              flowpathblnc, qualub, qualubTp, propblnc, rlt1, fub/;
$onecho > baron.opt
maxiter -1
rlt1.equclass('*','*') 1
$offecho
hrsnlp.optfile = 1;
hrsnlp.solprint = 2;
hrsnlp.tolinfeas = igap;
hrsnlp.workspace = 1500;
#===============================================================================
# Output and text and variables for the main algorithm
#===============================================================================
$set console 
$ifthen set fo $set console hrs.log
$elseif %system.filesys% == UNIX $set console /dev/tty
$elseif %system.filesys% == DOS $set console con
$else "%console%." == "." abort "filesys not recognized"
$endif
file screen /'%console%'/;
put screen;
put /;
put 'Model: HRS+MCF, NLP solver: ' system.nlp/;
put '=========================================='/;
put 'Iter                    Feasible Solution '/;
putclose;
#===============================================================================    
sets T_diff_Tp(t), tau_p(t);
T_diff_Tp(t) = yes;
alias (T_diff_Tp, T_active);
scalars z_p, obj_best, p0, ttime, t_p, timep, starttime, elapsed, mdlstat; 
starttime = jnow; p0 = 0; obj_best = 0; ttime = 1200; 
t_p = ttime/card(t); timep = t_p;
parameters f_p(i,j), Yp(s,i), objp0(t), minobj;
f_p(i,j) = 0; Yp(s,i) = 0; objp0(t) = +INF;
scalars hrstime, tmp, vars, nlts, nlcsts, lcsts; 
vars = 0; nlts = 0; nlcsts = 0; lcsts = 0;
#===============================================================================
# The main algorithm
#===============================================================================
repeat(
  z_p = 0;
  f_p(i,j) = 0;
  put screen;
  put 'Iteration ' (p0+1):>3:0 ':'/;
  putclose;
  if((p0 eq 0), 
    loop(T_diff_Tp,
      tau(T_diff_Tp) = yes;
      f.l(i,j)$(a(i,j)>0) = 0; cost.l = 0;
      solve hrslp minimizing cost using lp;
      mdlstat = hrslp.modelstat;
      tau(T_diff_Tp) = no;
      put screen;
      put '  Term ' T_diff_Tp.tl:>3:0 ', STAT ' mdlstat:>2:0', ';
      put 'obj = ' cost.l:>14:4/;
      putclose;
      if((mdlstat le 2),
        objp0(T_diff_Tp) = cost.l;
        if((cost.l < z_p),
          z_p = cost.l;
          f_p(i,j)$(a(i,j)>0) = 0;
          f_p(i,j)$(a(i,j)*p(j,T_diff_Tp)>0) = f.l(i,j);
          tau_p(t) = no;
          tau_p(T_diff_Tp) = yes;
          vars = hrslp.numvar-1; nlts = 0;
          lcsts = hrslp.numequ-1; nlcsts = 0;
        );
      );
    );
  else
    minobj = smin(T_active, objp0(T_active));
    loop(T_diff_Tp$(objp0(T_diff_Tp) eq minobj and timep > 0),
      tau(T_diff_Tp) = yes;
      f.l(i,j)$(a(i,j)>0) = 0; cost.l = 0;
      timep = (p0+1)*t_p-(jnow - starttime)*24*3600;
      if(timep > 0, 
        hrsnlp.reslim = timep;
        solve hrsnlp minimizing cost using nlp;
        mdlstat = hrsnlp.modelstat;
        vars = max(vars, hrsnlp.numvar-1); tmp = 0; 
        loop((s,l)$(a(s,l)*a(l,T_diff_Tp)>0), tmp = tmp+1;);  
        nlts = max(nlts, tmp); loop(l$(a(l,T_diff_Tp)>0), tmp = tmp+1;);
        tmp = tmp+card(k); nlcsts = max(nlcsts,tmp); 
        lcsts = max(lcsts, hrsnlp.numequ-nlcsts-1);      
        tau(T_diff_Tp) = no;
        put screen;
        put '  Term ' T_diff_Tp.tl:>3:0 ', STAT ' mdlstat:>2:0', obj = ' cost.l/;
        putclose;
        if((mdlstat le 2),
          z_p = cost.l; 
          f_p(i,j)$(a(i,j)>0) = 0;
          f_p(i,j)$(a(i,j)*p(j,T_diff_Tp)>0) = f.l(i,j);
          Yp(s,l) = y.l(s,l);
        else
          z_p = inf;
        );
        tau_p(t) = no;
        tau_p(T_diff_Tp) = yes;
        minobj = inf;
      );
    );
  );
  p0 = p0+1;
  if((z_p < -igap), 
    loop(tau_p, Fp(i,j)$(a(i,j)*p(j,tau_p)>0) = Fp(i,j)+f_p(i,j););
    obj_best = sum((i,j)$(a(i,j)>0), c(i,j)*Fp(i,j));
    Tp(tau_p) = yes;
    put screen;
    screen.nd = 0;
    screen.nw = 4;
    put p0;
    screen.nw = 14;
    screen.nd = 4;
    put @28 obj_best/;
    putclose;
  );
  T_diff_Tp(tau_p) = no;
  hrstime = (jnow - starttime)*24*3600;
until(p0 eq card(t) or hrstime ge ttime));

elapsed = hrstime;
option Fp:6:0:2; display Fp;
option Yp:6:0:2; display Yp;
parameters fblnc(s,i), qallb(t,k), yblnc(i);
scalar infeas, best; best = 0;

fblnc(s,l)$(p(s,l)>0) = abs(sum(j$(a(l,j)>0), Yp(s,l)*Fp(l,j)) - 
                Fp(s,l)$(a(s,l)>0) - sum(h$(p(s,h)*a(h,l)>0), Yp(s,h)*Fp(h,l)));
qallb(t,k)$(abs(q(t,k))>0 and abs(q(t,k))<+inf) = 
sum((l,s)$(p(s,l)*a(l,t)>0), (q(s,k) - q(t,k))*Yp(s,l)*Fp(l,t)) + 
                                   sum(s$(a(s,t)>0), (q(s,k) - q(t,k))*Fp(s,t));
yblnc(l) = abs(sum(s$(p(s,l)>0), Yp(s,l)) - 1);
infeas =  max(smax((s,i),fblnc(s,i)), smax(i,yblnc(i)), smax((t,k),qallb(t,k)));

put screen;
screen.nw = 14;
screen.nd = 4;
put /'=========================================='/;
put 'PQ-HRS best solution     = ' obj_best /;
putclose;
#===============================================================================
# The ALT heuristic to find proportion variables and improve the solution
#===============================================================================
equations obj1, obj2, sflowcaplb1(s), sflowcaplb2(s), sflowcapub1(s), 
          sflowcapub2(s), tflowcaplb1(t), tflowcaplb2(t), ptflowcapub1(i), 
          ptflowcapub2(i), flowpathblnc1(s,i), flowpathblnc2(s,i), 
          qualub1(t,k), qualub2(t,k), propblnc2(i);
scalars alt_obj, falt_obj, yalt_obj, converge; falt_obj = +INF; yalt_obj = +INF;
parameters Fb(i,j), Yb(s,i); Fb(i,j) = Fp(i,j); Yb(s,l) = Yp(s,l);
#=========================Fixing proportion variables===========================
obj1.. cost =e= sum((i,j)$(a(i,j)>0), c(i,j)*f(i,j));
sflowcaplb1(s)$(bl(s)>0).. sum(j$(a(s,j)>0), f(s,j)) =g= bl(s);
sflowcapub1(s)$(bu(s)<+inf).. sum(j$(a(s,j)>0), f(s,j)) =l= bu(s);
tflowcaplb1(t)$(bl(t)>0).. sum(j$(a(j,t)>0), f(j,t)) =g= bl(t);
ptflowcapub1(lt)$(bu(lt)<+inf).. sum(j$(a(j,lt)>0), f(j,lt)) =l= bu(lt);
flowpathblnc1(s,l)$(p(s,l)>0).. sum(j$(a(l,j)>0), Yb(s,l)*f(l,j)) - 
             f(s,l)$(a(s,l)>0) - sum(h$(p(s,h)*a(h,l)>0), Yb(s,h)*f(h,l)) =e= 0;
qualub1(t,k)$(abs(q(t,k))>0 and abs(q(t,k))<+inf)..
                sum((l,s)$(p(s,l)*a(l,t)>0), (q(s,k) - q(t,k))*Yb(s,l)*f(l,t)) +
                              sum(s$(a(s,t)>0), (q(s,k) - q(t,k))*f(s,t)) =l= 0;
option lp = cplex;
model alty /obj1, sflowcaplb1, sflowcapub1, tflowcaplb1, ptflowcapub1, 
            flowpathblnc1, qualub1/;
alty.solprint = 2;
#==========================Fixing flow of f(l,j)================================ 
obj2.. cost =e= sum((s,j)$(a(s,j)>0), c(s,j)*f(s,j)) +
                                          sum((l,j)$(a(l,j)>0), c(l,j)*Fb(l,j));
sflowcaplb2(s)$(bl(s)>0).. sum(j$(a(s,j)>0), f(s,j)) =g= bl(s);
sflowcapub2(s)$(bu(s)<+inf).. sum(j$(a(s,j)>0), f(s,j)) =l= bu(s);
tflowcaplb2(t)$(bl(t)>0).. sum(s$(a(s,t)>0), f(s,t)) + 
                                           sum(l$(a(l,t)>0), Fb(l,t)) =g= bl(t);
ptflowcapub2(lt)$(bu(lt)<+inf).. sum(s$(a(s,lt)>0), f(s,lt)) + 
                                        sum(l$(a(l,lt)>0), Fb(l,lt)) =l= bu(lt);
flowpathblnc2(s,l)$(p(s,l)>0).. sum(j$(a(l,j)>0), y(s,l)*Fb(l,j)) - 
             f(s,l)$(a(s,l)>0) - sum(h$(p(s,h)*a(h,l)>0), y(s,h)*Fb(h,l)) =e= 0;
qualub2(t,k)$(abs(q(t,k))>0 and abs(q(t,k))<+inf)..
                sum((l,s)$(p(s,l)*a(l,t)>0), (q(s,k) - q(t,k))*y(s,l)*Fb(l,t)) +
                              sum(s$(a(s,t)>0), (q(s,k) - q(t,k))*f(s,t)) =l= 0;
propblnc2(l).. sum(s$(p(s,l)>0), y(s,l)) - 1 =e= 0;
model altf /obj2, sflowcaplb2, sflowcapub2, tflowcaplb2, ptflowcapub2, 
            flowpathblnc2, qualub2, propblnc2/;
altf.solprint = 2;
altf.tolinfeas = igap;
#===============================================================================
# FALT algorithm
#===============================================================================
starttime = jnow;
repeat(
  y.l(s,l) = 0; f.l(s,j) = 0; cost.l = 0;
  solve altf minimizing cost using lp;
  Fb(s,j) = f.l(s,j); Yb(s,l) = y.l(s,l);
  f.l(i,j) = 0; cost.l = 0;
  solve alty minimizing cost using lp;
  Fb(l,j) = f.l(l,j);
  converge = (alty.modelstat le 2 and altf.modelstat le 2 and 
              smax((s,l)$(p(s,l)>0), abs(y.l(s,l)-Yb(s,l))) < gap and 
              smax((i,j)$(a(i,j)>0), abs(f.l(i,j)-Fb(i,j))) < gap);
  timep = (jnow - starttime)*24*3600;
until(converge or timep ge ttime));
Fb(i,j) = Fp(i,j); Yb(s,l) = Yp(s,l);
if(converge, 
  falt_obj = sum((i,j)$(a(i,j)>0), c(i,j)*f.l(i,j));
  if((falt_obj le obj_best),
    alt_obj = falt_obj; best = 1; 
    Fp(i,j) = f.l(i,j); Yp(s,l) = y.l(s,l);
    elapsed = hrstime+timep;
  );
);
put screen;
put 'FALT improved solution   = ' falt_obj/;
putclose;
#===============================================================================
# YALT algorithm
#===============================================================================
starttime = jnow;
repeat(
  f.l(i,j) = 0; cost.l = 0;
  solve alty minimizing cost using lp;
  Fb(l,j) = f.l(l,j);
  y.l(s,l) = 0; f.l(s,j) = 0; cost.l = 0;
  solve altf minimizing cost using lp;
  Fb(s,j) = f.l(s,j);
  converge = (alty.modelstat le 2 and altf.modelstat le 2 and 
              smax((s,l)$(p(s,l)>0), abs(y.l(s,l)-Yb(s,l))) < gap and 
              smax((i,j)$(a(i,j)>0), abs(f.l(i,j)-Fb(i,j))) < gap);
  Yb(s,l) = y.l(s,l);
  timep = (jnow - starttime)*24*3600;
until(converge or timep ge ttime));
if(converge, 
  yalt_obj = sum((i,j)$(a(i,j)>0), c(i,j)*f.l(i,j));
  if((yalt_obj le falt_obj), 
    alt_obj = yalt_obj; best = 2;
    Fp(i,j) = f.l(i,j);
    Yp(s,l) = y.l(s,l);
    elapsed = hrstime+timep;
  );
);

if((elapsed>ttime), elapsed = ttime;);

put screen;
put 'YALT improved solution   = ' yalt_obj/;
putclose;
put screen;
screen.nd = 2;
put 'Total time in seconds    = ' elapsed /;
put '=========================================='/;
putclose;
#============================Print solution information=========================
file line;
put_utility line 'msg' / '#####' ' Solution Summary #####';
line.nd = 6;
line.nw = 16;
put_utility line 'msg' / obj_best ' ' alt_obj ' ' elapsed ' ' best ' ' infeas;
line.nd = 0;
put_utility line 'msg' / 1 ' ' p0 ' ' vars ' ' nlts ' ' lcsts ' ' nlcsts;
option Fp:6:0:2; display Fp;
option Yp:6:0:2; display Yp;
execute_unload 'sol.gdx', Fp, Yp;
#========================================END====================================
