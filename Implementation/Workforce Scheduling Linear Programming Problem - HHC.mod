# Workforce Scheduling Linear Programming Formulation - Home Health Care
# Gabriel Ferreira da Costa - 19.1.4047

# PARÂMETROS:
param M := 999999999999999999999999999999999; # Big M
param nT := 6; # Número total de tarefas: T
param nW := 3; # Número total de trabalhadores
set T := 0..nT; # Conjunto de tarefas: T = {t1, ti, ..., tT}
set W := 1..nW; # Conjunto de trabalhadores: W = {w1, wi, ..., wT}
set A within T cross T; # Conjunto de arestas
# Definimos um grafo G = (V,E)
# Onde V é o conjunto de nós e E o conjunto de arestas
param dist{(i,j) in A}; # Distância da tarefa i à tarefa j
param p{T,W}; # Custo do trabalhador w para realizar j
param Dur{j in T}; # Tempo de processamento da tarefa j
param r{j in T}; # Número de trabalhadores necessários para realizar a tarefa 𝑗
param pw{j in T, w in W} >= 0, <= 1; # Nível de satisfação ((pw)j^w ∈ [0,1]) quando o trabalhador w é atribuído à tarefa j
param pa{j in T, w in W} >= 0, <= 1; # Nível de satisfação ((pa)w^j ∈ [0,1]) quando o trabalhador w é atribuído à tarefa j considerando as preferências regionais (a tarefa j está localizada em uma região k)
param ps{j in T, w in W} >= 0, <= 1; # Nível de satisfação da habilidade ((ps)w^j ∈ [0,1]) com (ps)w^j=max((ps)i^j) quando a tarefa j é atribuída ao trabalhador w
param rojw{j in T, w in W}; #= pa[j,w] + pw[j,w] + ps[j,w]; # Qualidade do serviço = pa + pw + ps
param ej{j in T}; # Janela de tempo da tarefa j -> Limite inferior
param lj{j in T}; # Janela de tempo da tarefa j -> Limite superior
param TWinf{w in W}; # Janela de tempo de trabalho do trabalhador w -> Limite inferior
param TWsup{w in W}; # janela de tempo de trabalho do trabalhador w -> Limite superior
# Ordem de prioridade dos pesos: λ4 ≽ λ3 ≽ λ2 ≽ λ1
param lambda1 := 0.4; # Peso 1
param lambda2 := 0.65; # Peso 2
param lambda3 := 0.75; # Peso 3
param lambda4 := 1.0; # Peso 4

# VARIÁVEIS DE DECISÃO:
## Binárias:
var x{(i,j) in A, w in W}, binary; # x[i,j,w] = 1 se o trabalhador w passar da tarefa i para j
var psi{j in T, w in W}, binary; # psi[j] = 1 se o trabalhador w for designado para uma tarefa j situada fora da região de preferência 
var theta{j in T, w in W}, binary; # theta[j] = 1 se a violação da janela de tempo ocorrer quando a tarefa j for atribuída ao trabalhador w 
var c{j in T, w in W}, binary; # c[j,w] = 1 se o trabalhador tiver sido incluído no contrato do cliente

## Contínuas:
var y{j in T} integer >= 0; # Número de trabalhadores não disponíveis para realizar a tarefa j
var t{j in T} >= 0; # Hora de início da tarefa j 
var d{T,W} >= 0; # Hora de saída do trabalhador w da tarefa j
var a{T,W} >= 0; # Hora de chegada do trabalhador w à tarefa j

# FUNÇÃO OBJETIVO:
minimize Objective:
lambda1 * sum{w in W, i in T, j in T: j > 0} (dist[i,j] + p[j,w]) * x[i,j,w] + # Critério 1
lambda2 * sum{j in T: j > 0} (3 * r[j] - sum{i in T, w in W} rojw[i,w] * x[i,j,w]) + # Critério 2
lambda3 * sum{j in T, w in W: j > 0} (psi[j,w] + theta[j,w]) + # Critério 3
lambda4 * sum{j in T: j > 0} y[j] # Critério 4
;

# RESTRIÇÕES: 
## Conjunto 1:
Constraint_1{i in T, w in W}: sum{j in T: (i,j) in A} x[i,j,w] <= 1; 
Constraint_2{j in T, w in W}: sum{i in T: (i,j) in A} x[i,j,w] <= 1;
Constraint_3{j in T, w in W}: sum{i in T: (i,j) in A} x[i,j,w] = sum{u in T: (j,u) in A} x[j,u,w];

## Conjunto 2:
Constraint_4{j in T: j > 0}: sum{w in W, i in T} x[i,j,w] + y[j] = r[j];

## Conjunto 3:
Constraint_5{j in T, w in W: j > 0}: (psi[j,w] + M * pa[j,w]) >= sum{i in T} x[i,j,w];
Constraint_6{j in T, w in W: j > 0}: M * theta[j,w] >= sum{i in T} (x[i,j,w] - 1) * M + t[j] + Dur[j] - TWsup[w];
Constraint_7{j in T, w in W: j > 0}: M * theta[j,w] >= sum{i in T} (x[i,j,w] - 1) * M - t[j] + TWinf[w];

## Conjunto 4:
Constraint_8{j in T, w in W: j > 0}: c[j,w] >= sum{i in T} x[i,j,w];

## Conjunto 5:
Constraint_9{j in T, w in W: j > 0}: d[j,w] >= sum{i in T} (x[i,j,w] - 1) * M + (t[j] + Dur[j]);
Constraint_10{i in T, j in T, w in W: j > 0}: a[j,w] >= (x[i,j,w] - 1) * M + (d[i,w] + dist[i,j]);

## Conjunto 6:
Constraint_11{j in T, w in W: j > 0}: a[j,w] <= t[j];
Constraint_12{j in T: j > 0}: ej[j] <= t[j];
Constraint_13{j in T: j > 0}: lj[j] <= t[j];

# CARREGANDO OS DADOS:
data;

param: A : dist :=
0 1 160.42
0 2 5.64
0 3 1.67
0 4 1.32
0 5 5.19
0 6 112.31
1 1 33.87
1 2 109.95
1 3 125.48
1 4 128.57
1 5 61.04
1 6 7.49
2 1 53.43
2 2 45.68
2 3 8.65
2 4 157.94
2 5 160.78
2 6 122.25
3 1 161.80
3 2 112.23
3 3 96.94
3 4 79.70
3 5 49.43
3 6 170.14
4 1 16.09
4 2 59.11
4 3 38.33
4 4 178.29
4 5 120.03
4 6 205.4
5 1 167.43
5 2 78.75
5 3 0.08
5 4 1.18
5 5 10.15
5 6 168.06
6 1 67.84
6 2 25.43
6 3 33.35
6 4 90.17
6 5 15.85
6 6 20.19
;

param p : 1 2 3 := 
0 125.0 315.0 265.0
1 160.0 75.0 92.0
2 114.0 236.0 85.0
3 100.0 63.0 345.0
4 455.0 367.0 195.0
5 165.0 55.0 72.0
6 200.0 128.0 340.0
;

param Dur := 
0 72.0
1 44.0
2 59.0
3 719.0
4 59.0
5 89.0
6 59.0
;

param r := 
0 1
1 1 
2 1 
3 1 
4 1 
5 1 
6 1
;

param pw : 1 2 3 :=
0 1 0 1
1 0 1 1
2 1 1 1
3 1 0 0
4 0 1 1
5 1 1 1
6 1 0 1
;

param pa : 1 2 3 :=
0 1 0 0
1 1 1 1
2 0 0 0
3 0 1 0
4 0 1 0
5 1 1 0
6 0 1 1
;

param ps : 1 2 3 :=
0 1 1 1
1 1 1 1
2 0 1 0
3 1 1 0
4 0 0 0
5 1 1 1
6 0 1 1
;

param rojw : 1 2 3 :=
0 3 1 2
1 2 3 3
2 1 2 1
3 2 2 0
4 0 2 1
5 3 3 2
6 1 2 3
;

param ej := 
0 265.0
1 720.0 
2 465.0 
3 480.0 
4 720.0 
5 600.0 
6 750.0
;

param lj :=
0 265.0
1 720.0 
2 465.0
3 480.0 
4 720.0 
5 600.0 
6 750.0
;

param TWinf := 
1 120.0
2 140.0
3 150.0
;

param TWsup :=
1 240.0
2 280.0
3 300.0
;

end;