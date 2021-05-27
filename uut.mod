// Test
//****************************输入参数****************************\\
//排班周期
int N = ...;
//周末(非行政上班时间)
{int} weekend = ...;//表示集合
//3种职级划分
int pc = ...;
{int} P = ...; //分别表示
//不同 职级医师的个数
int cp1 = ...; int cp2 = ...; int cp3 = ...;
int Cp[1..pc] = ...; 
//不同职级医师的不工作的天数集合
{int} nw_p1[1..cp1] = ...;
{int} nw_p2[1..cp2] = ...;
{int} nw_p3[1..cp3] = ...;
//四种类型的班的编号
int sn = ...;
int S[1..sn] = ...;// 白班，夜班，门诊，值班
//不合理的排班次序集合
int forbidden_S[1..7][1..2] = ...;
// 每天每种类型的班需要的最少和最多的医师数量
int D_min[1..N][1..sn] = ...;
int D_max[1..N][1..sn] = ...;
//最多连续上夜班的天数
int N_max = ...;
//最多连续工作的天数
int W_max = ...;

//职级为p的上类型为s的班的最少和最多天数
int Q_min[1..pc][1..sn] = ...;

int Q_max[1..pc][1..sn] = ...;
//**************************去掉的变量**************************\\
//每名医师在周末累计工作的最大天数
//int on_weekend_day_max = 1; //2
//不同职级每名医师在周末最少工作时间和最多工作时间，主要考虑住院医师可能值很多的班，或者
//int on_weekend_hours_min[1..pc] = [0, 0, 0]; //门诊8，值班24
//int on_weekend_hours_max[1..pc] = [24, 24, 16];
//最少连续休息的天数
//int R_min = 1;
//不同职级医师不能排的班的集合
//int fs_p1 = 3; //门诊
//int fs_p3[1..2] = [2, 4]; //夜班和值班

//每名医师最少和最多工作天数； 分不同职级？
int on_all_day_min = ...;
int on_all_day_max = ...; //6

//每种类型的班的时长
int long_shift[1..sn] = ...;

//不同职级医师工作总时长的上下限
int on_all_hours_min[1..pc] = ...;//
int on_all_hours_max[1..pc] = ...; //[64, 64, 42]

//软约束权重
int cn = ...;
int w[1..cn] = ...;
//最多值班次数 
int duty_max = ...;

//在周末累计休息不能低于最低限制
int rest_weekend_min = ...;

//Model
//****************************决策遍历和辅助变量****************************\\
dvar boolean X1[1..cp1][1..N][1..sn];
dvar boolean X2[1..cp2][1..N][1..sn];
dvar boolean X3[1..cp3][1..N][1..sn];
//dvar boolean X[p in P][1..Cp[p]][1..N][1..sn];
//dvar boolean w[X1, X2, X3];???
//int X1_S[i in 1..cp1][j in 1..N] = sum(k in 1..sn) X1[i][j][k];
//是否工作
dvar boolean O1[1..cp1][1..N];
dvar boolean O2[1..cp2][1..N];
dvar boolean O3[1..cp3][1..N];
//dvar boolean O[p in P][1..Cp[p]][1..N];
//是否休息
dvar boolean R1[1..cp1][1..N];
dvar boolean R2[1..cp2][1..N];
dvar boolean R3[1..cp3][1..N];
//dvar boolean R[p in P][1..Cp[p]][1..N];
//辅助变量
dvar int j_p1[1..cp1]; 
dvar int j_p2[1..cp2];
//dvar int j[p in {1,2}][1..Cp[p]];
dvar int g_p2[1..cp2][1..sn];
dvar int h_p1[1..cp1][i in 1..4];
dvar int h_p2[1..cp2][i in 1..4];
dvar int h_p3[1..cp3][i in 1..4];

//****************************目标方程****************************\\
minimize 
		sum(k in 1..cp1)sum(i in 1..4) h_p1[k][i] * w[i+2]+
		sum(k in 1..cp2)sum(i in 1..4) h_p2[k][i] * w[i+2]+
		sum(k in 1..cp3)sum(i in 1..4) h_p3[k][i] * w[i+2]+
//		sum(p in P)sum(k in 1..Cp[p])sum(i in 1..4)(h[p][k][i] * w[i+2])+
//		sum(p in {1,2})sum(k in 1..Cp[p])j[p][k] * w[1]+
		sum(k in 1..cp1)j_p1[k] * w[1]+
		sum(k in 1..cp2)j_p2[k] * w[1]+
		sum(k in 1..cp2)sum(s in 1..sn)g_p2[k][s] * w[2];

//****************************约束****************************\\
subject to{
// H1
forall(k in 1..cp1)
  forall(n in 1..N)
    sum(s in 1..sn)X1[k][n][s] <= 1;
forall(k in 1..cp2)
  forall(n in 1..N)
    sum(s in 1..sn)X2[k][n][s] <= 1;
forall(k in 1..cp3)
  forall(n in 1..N)
    sum(s in 1..sn)X3[k][n][s] <= 1;

// H2a/H2b
forall(n in 1..N)
  forall(s in 1..sn)
    sum(k in 1..cp1)X1[k][n][s]+
    sum(k in 1..cp2)X2[k][n][s]+
    sum(k in 1..cp3)X3[k][n][s] >= D_min[n][s];
forall(n in 1..N)
  forall(s in 1..sn)
    sum(k in 1..cp1)X1[k][n][s]+
    sum(k in 1..cp2)X2[k][n][s]+
    sum(k in 1..cp3)X3[k][n][s] <= D_max[n][s];

// H3a
forall(n in 1..N)
  	sum(k in 1..Cp[1])X1[k][n][S[3]] +
  	sum(k in 1..Cp[3])X3[k][n][S[4]] +
  	sum(k in 1..Cp[3])X3[k][n][S[2]] == 0;

//周末只有值班 因为住院医师周末要么休息要么值班
forall(n in weekend)
	sum(k in 1..Cp[2])X2[k][n][S[4]] >= 1; //1

// 正常上下班的白班和夜班; 本例中人数较少，若考虑则结果是无解
//forall(n in weekday)
//	sum(k in 1..Cp[2])X2[k][n][S[1]] >= 0; //1
//forall(n in weekday)
//	sum(k in 1..Cp[2])X2[k][n][S[2]] >= 0; //1 

// H4
forall(p in P)
forall(k in 1..cp1)
  forall(n in nw_p1[k])
    forall(s in 1..sn)
      X1[k][n][s] == 0;
//
forall(k in 1..cp2)
  forall(n in nw_p2[k])
    forall(s in 1..sn)
      X2[k][n][s] == 0;
////
forall(k in 1..cp3)
  forall(n in nw_p3[k])
    forall(s in 1..sn)
      X3[k][n][s] == 0;


// H5
forall(n in weekend)
  sum(k in 1..Cp[1])X1[k][n][S[1]]+
  sum(k in 1..Cp[1])X1[k][n][S[2]] == 0;
  
// H6 职级
forall(p in P)
forall(k in 1..Cp[1])
  sum(n in 1..N)O1[k][n] >= on_all_day_min;
forall(k in 1..Cp[1])
  sum(n in 1..N)O1[k][n] <= on_all_day_max;
forall(k in 1..Cp[2])
  sum(n in 1..N)O2[k][n] >= on_all_day_min;
forall(k in 1..Cp[3])
  sum(n in 1..N)O3[k][n] <= on_all_day_max;

// H7
forall(n in 1..N-1)
    forall(k in 1..Cp[1])
     X1[k][n][S[4]] + O1[k][n+1] <= 1;
forall(n in 1..N-1)
    forall(k in 1..Cp[2])
     X2[k][n][S[4]] + O2[k][n+1] <= 1;
     
// H8
forall(n in 1..N-1)
  forall(k in 1..Cp[1])
   forall(tmp in 1..7)
     X1[k][n][forbidden_S[tmp][1]] + X1[k][n+1][forbidden_S[tmp][2]] != 2;
forall(n in 1..N-1)
  forall(k in 1..Cp[2])
   forall(tmp in 1..7)
     X2[k][n][forbidden_S[tmp][1]] + X2[k][n+1][forbidden_S[tmp][2]] != 2;
forall(n in 1..N-1)
  forall(k in 1..Cp[3])
   forall(tmp in 1..7)
     X3[k][n][forbidden_S[tmp][1]] + X3[k][n+1][forbidden_S[tmp][2]] != 2;

// H9
forall(k in 1..Cp[1])
    forall(s in 1..sn)
      sum(n in 1..N)X1[k][n][s] <= Q_max[1][s]; 
forall(k in 1..Cp[1])
    forall(s in 1..sn)
      sum(n in 1..N)X1[k][n][s] >= Q_min[1][s];
forall(k in 1..Cp[2])
    forall(s in 1..sn)
      sum(n in 1..N)X2[k][n][s] <= Q_max[2][s]; 
forall(k in 1..Cp[3])
    forall(s in 1..sn)
      sum(n in 1..N)X3[k][n][s] >= Q_min[3][s];
//      
// H10
forall(k in 1..Cp[1])
    sum(n in 1..N)sum(s in 1..sn)(X1[k][n][s] * long_shift[s]) 
    <= on_all_hours_max[1];
forall(k in 1..Cp[1])
    sum(n in 1..N)sum(s in 1..sn)(X1[k][n][s] * long_shift[s]) 
    >= on_all_hours_min[1];
    
forall(k in 1..Cp[2])
    sum(n in 1..N)sum(s in 1..sn)(X2[k][n][s] * long_shift[s]) 
    <= on_all_hours_max[2];
forall(k in 1..Cp[2])
    sum(n in 1..N)sum(s in 1..sn)(X2[k][n][s] * long_shift[s]) 
    >= on_all_hours_min[2];
    
forall(k in 1..Cp[3])
    sum(n in 1..N)sum(s in 1..sn)(X3[k][n][s] * long_shift[s]) 
    <= on_all_hours_max[3];
forall(k in 1..Cp[3])
    sum(n in 1..N)sum(s in 1..sn)(X3[k][n][s] * long_shift[s]) 
    >= on_all_hours_min[3];     

     
// S1
forall(k in 1..Cp[1])
    sum(n in 1..N)X1[k][n][S[2]] - j_p1[k] <= duty_max;
forall(k in 1..Cp[2])
    sum(n in 1..N)X2[k][n][S[2]] - j_p2[k] <= duty_max;
    
// S2
forall(s in 1..sn)
   sum(k in 1..Cp[2])(
     abs(sum(n in 1..N)X2[k][n][s] - (sum(n in 1..N)sum(k in 1..Cp[2])X2[k][n][s]) / Cp[2])
     - g_p2[k][s]
     ) <= 0; 
     
// S3
forall(k in 1..Cp[1])
    sum(n in weekend)R1[k][n] + h_p1[k][1] >= rest_weekend_min;
forall(k in 1..Cp[2])
    sum(n in weekend)R2[k][n] + h_p2[k][1] >= rest_weekend_min;
forall(k in 1..Cp[3])
    sum(n in weekend)R3[k][n] + h_p3[k][1] >= rest_weekend_min;

//S4
sum(k in 1..Cp[1])(
  	abs(sum(n in 1..N)sum(s in 1..sn)(X1[k][n][s] * long_shift[s]) - 
  	sum(k in 1..Cp[1])sum(n in 1..N)sum(s in 1..sn)(X1[k][n][s] * long_shift[s]) / Cp[1])
  	- h_p1[k][2]
  ) <= 0;
sum(k in 1..Cp[2])(
  	abs(sum(n in 1..N)sum(s in 1..sn)(X2[k][n][s] * long_shift[s]) - 
  	sum(k in 1..Cp[2])sum(n in 1..N)sum(s in 1..sn)(X2[k][n][s] * long_shift[s]) / Cp[2])
  	- h_p2[k][2]
  ) <= 0;
sum(k in 1..Cp[3])(
  	abs(sum(n in 1..N)sum(s in 1..sn)(X3[k][n][s] * long_shift[s]) - 
  	sum(k in 1..Cp[3])sum(n in 1..N)sum(s in 1..sn)(X3[k][n][s] * long_shift[s]) / Cp[3])
  	- h_p3[k][2]
  ) <= 0;
      
// S5
forall(k in 1..Cp[1])
    forall(n in 1..N-N_max+1)
      sum(i in n..n+N_max-1)X1[k][i][S[2]] - h_p1[k][3] <= N_max;
forall(k in 1..Cp[2])
    forall(n in 1..N-N_max+1)
      sum(i in n..n+N_max-1)X2[k][i][S[2]] - h_p2[k][3] <= N_max;
forall(k in 1..Cp[3])
    forall(n in 1..N-N_max+1)
      sum(i in n..n+N_max-1)X3[k][i][S[2]] - h_p3[k][3] <= N_max;

// S6
forall(k in 1..Cp[1])
    forall(n in 1..N-W_max+1)
      sum(i in n..n+W_max-1)O1[k][i] - h_p1[k][4] <= W_max;
forall(k in 1..Cp[2])
    forall(n in 1..N-W_max+1)
      sum(i in n..n+W_max-1)O2[k][i] - h_p2[k][4] <= W_max;
forall(k in 1..Cp[3])
    forall(n in 1..N-W_max+1)
      sum(i in n..n+W_max-1)O3[k][i] - h_p3[k][4] <= W_max;
};
