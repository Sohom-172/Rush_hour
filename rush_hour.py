import numpy as np
import pandas as pd
from z3 import *

n_grid=0

s=Solver()
#place the mines in the board by replacing 1 in place of 0 in A
#place the cars in the board by replacing the coordinates as mentioned( 1 in place of 0 ) 
n_mine=0
n_vert=0
n_hor=0
time=0

mines = []            # in the form of (i,j)
vert_car_inp = [] # in the form of ()             # in the form of (i,j)
hor_car_inp = [] # in the form             # in the form of (i,j)

#  INITIAL STATE OF THE BOARD

inputfile = open("inp3.txt","r")
lines = inputfile.readlines()
inputfile.close()

n_grid = int(lines[0].split(",")[0])
time = int(lines[0].split(",")[1])
hor_car_inp.append([int(lines[1].split(",")[0]),int(lines[1].split(",")[1])])
n_hor+=1
lines = lines[2:]

for line in lines:
    x = line.split(",")
    if(int(x[0]) == 0):
        vert_car_inp.append([int(x[1]),int(x[2])])
        n_vert+=1
    
    elif(int(x[0]) == 1):
        hor_car_inp.append([int(x[1]),int(x[2])])
        n_hor+=1

    elif(int(x[0]) == 2):
        mines.append([int(x[1]),int(x[2])])
        n_mine+=1

hor_car = []
for i in range(n_hor) :
    hor_car.append([[hor_car_inp[i][0],hor_car_inp[i][1]]])
    for j in range(1,time) :
        hor_car[i].append([hor_car_inp[i][0],Int("h_"+str(i)+"_"+str(j))])

vert_car = []
for i in range(n_vert) :
    vert_car.append([[vert_car_inp[i][0],vert_car_inp[i][1]]])
    for j in range(1,time) :
        vert_car[i].append([Int("v_"+str(i)+"_"+str(j)),vert_car_inp[i][1]])

#----------------------------------------------------------------

# COLLISION WITH WALLS 

clause_collision_walls = [];

for t in range(time) :
    for q in range(n_hor) :
          phi = And(hor_car[q][t][1] < n_grid-1,hor_car[q][t][1] >= 0 )
          clause_collision_walls.append(phi)
    for q in range(n_vert) :
          phi = And(vert_car[q][t][0] < n_grid-1,vert_car[q][t][0] >= 0 )
          clause_collision_walls.append(phi)
          

#----------------------------------------------------------------


#COLLISION WITH MINES

clause_collision_mine = [];

for t in range(time):
      for p in range(n_mine):
            for q in range(n_hor):
                  inter_hor = Or(mines[p][0] != hor_car[q][t][0], And(mines[p][1] != hor_car[q][t][1], mines[p][1] != hor_car[q][t][1]+1))
                  clause_collision_mine.append(inter_hor)

            for q in range(n_vert):
                  inter_vert = Or(mines[p][1] != vert_car[q][t][1], And(mines[p][0] != vert_car[q][t][0], mines[p][0] != vert_car[q][t][0]+1))
                  clause_collision_mine.append(inter_vert)
                  

#----------------------------------------------------------------


#COLLISION WITH CARS

clause_collision_cars = [];

for t in range(time):
    for p in range(n_hor):
        for q in range(p+1,n_hor):
            inter_hor = Or(hor_car[p][t][0] != hor_car[q][t][0], And(hor_car[p][t][1] != hor_car[q][t][1]+1, hor_car[p][t][1]+1 != hor_car[q][t][1]))
            clause_collision_cars.append(inter_hor)

    for p in range(n_vert):
        for q in range(p+1,n_vert):
            inter_vert = Or(vert_car[p][t][1] != vert_car[q][t][1], And(vert_car[p][t][0] != vert_car[q][t][0]+1, vert_car[p][t][0]+1 != vert_car[q][t][0]))
            clause_collision_cars.append(inter_vert)

    for p in range(n_hor):
        for q in range(n_vert):
            inter_hv = Or(And(hor_car[p][t][0] != vert_car[q][t][0] , hor_car[p][t][0] != vert_car[q][t][0]+1) , And(hor_car[p][t][1] != vert_car[q][t][1] , hor_car[p][t][1]+1 != vert_car[q][t][1]))
            clause_collision_cars.append(inter_hv)


#----------------------------------------------------------------


#TIME STEP

clause_time_step = []

for t in range(time-1):
    temp_clause = []
    for p in range(n_hor):
        inter_time_hor =  Xor(hor_car[p][t][1]+1 == hor_car[p][t+1][1] , hor_car[p][t][1] == hor_car[p][t+1][1]+1)
        temp_clause.append(inter_time_hor)
        
    for p in range(n_vert):
        inter_time_vert = Xor(vert_car[p][t][0]+1 == vert_car[p][t+1][0] , vert_car[p][t][0] == vert_car[p][t+1][0]+1)
        temp_clause.append(inter_time_vert)
    
    temp_clause1 = temp_clause.copy()
    temp_clause1.append(1)
    inter_atmost = AtMost(temp_clause1)
    inter_one = And(inter_atmost,Or(temp_clause))

    temp_clause2 = []

    for p in range(n_hor):
        inter_time_hor =  Xor(Xor(hor_car[p][t][1]+1 == hor_car[p][t+1][1] , hor_car[p][t][1] == hor_car[p][t+1][1]+1),hor_car[p][t][1] == hor_car[p][t+1][1])
        temp_clause2.append(inter_time_hor)
        
    for p in range(n_vert):
        inter_time_vert = Xor(Xor(vert_car[p][t][0]+1 == vert_car[p][t+1][0] , vert_car[p][t][0] == vert_car[p][t+1][0]+1),vert_car[p][t][0] == vert_car[p][t+1][0])
        temp_clause2.append(inter_time_vert)
    
    temp_clause2.append(inter_one)
    clause_time_step.append(Implies(hor_car[0][t][1] < n_grid-2,And(temp_clause2)))

#-----------------------------------------------------------------

# ZERO MOVES

clause_zero_moves = []

for t in range(time-1) :
    temp_clause = []
    for p in range(n_hor):
        temp_clause.append(hor_car[p][t][1] == hor_car[p][t+1][1] )
        
    for p in range(n_vert):
        temp_clause.append(vert_car[p][t][0] == vert_car[p][t+1][0])

    clause_zero_moves.append(Implies(hor_car[0][t][1] == n_grid-2,And(temp_clause)))

clauses = []
clauses.extend(clause_time_step)
clauses.extend(clause_collision_mine)
clauses.extend(clause_collision_walls)
clauses.extend(clause_zero_moves)
clauses.extend(clause_collision_cars)
clauses.append(hor_car[0][time-1][1] == n_grid-2)
#print(clauses)
s.add(And(clauses))

if s.check() == sat:
    m = s.model()
    print("sat")
    #print(m)

    hor_car_final = []
    for i in range(n_hor) :
        hor_car_final.append([[hor_car_inp[i][0],hor_car_inp[i][1]]])
        for j in range(1,time) :
            hor_car_final[i].append([hor_car_inp[i][0],s.model()[hor_car[i][j][1]]])

    vert_car_final = []
    for i in range(n_vert) :
        vert_car_final.append([[vert_car_inp[i][0],vert_car_inp[i][1]]])
        for j in range(1,time) :
            vert_car_final[i].append([s.model()[vert_car[i][j][0]],vert_car_inp[i][1]])
