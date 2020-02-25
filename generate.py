from sys import argv

try:
  nb_choice = int(argv[1])
except:  
  print("Enter Number of Repetition: ") 
  nb_choice = int(input())

string1 = "(recX.k<1>.X)"
string2="l(x).(if x==4 then k<x>.2 else k<x>.1)"
string3 = "rec X.(k<1>.(l<1>.X)+(q<1>.1))"
string4 = "l(x).(if x==4 then k<x>.recX.k<1>.X else k<x>.2)"

counter = 6+(2*(nb_choice-1)) 

# for i in range(nb_choice-1):
#     string1 = string1 + "+ (recX.k<" + str(i+2) + ">.X)"

# string1 = string1 + "+(recX.k<"+ str(nb_choice+1) +">.X)"    

# print(string1)

# if nb_choice == 1:
#   string2 = "l(x).if x==4 then k<x>.2 else k<x>.1"
# else:
#   for i in range(nb_choice-1):
#     temp = "if x mod 2 == 0 then "
#     counter = 6+(2*(i)) 
#     for x in range(i+1):
#         temp = temp + "if x<" + str(counter) + " then " 
#         counter -= 2
#     temp = temp + "if x>2 then k<x>.2 else k<x>.1"
#     for x in range(i+1):
#         temp = temp + " else k<x>.1"
#     temp = temp+" else k<x>.1"
#     string2 = string2 + " + ("+temp+")"

# print(string2) 

# for i in range(nb_choice-1):
#     string3 = string3 + "+ (k<" + str(i+2) + ">.(l<" +str(i+2)+ ">.X)+(q<" +str(i+2)+ ">.1))"

# string3 = string3 + "+(k<"+ str(nb_choice+1) +">.(l<" +str(nb_choice+1)+ ">.X)+(q<" +str(nb_choice+1)+ ">.1))"    

# print(string3)

# if nb_choice == 1:
#   string4 = "l(x).if x==4 then k<x>.recX.k<1>.X else k<x>.2"
# else:
#   for i in range(nb_choice-1):
#     temp = "if x mod 2 == 0 then "
#     temp2 = "(recX.k<1>.X)"
#     counter = 6+(2*(i)) 
#     for x in range(i+1):
#         temp = temp + "if x<" + str(counter) + " then " 
#         counter -= 2
#     for x in range(nb_choice-1):
#         temp2 = temp2 + "+ (recX.k<" + str(x+2) + ">.X)"
#     temp = temp + "if x>2 then k<x>." + temp2 + " else k<x>.2"
#     for x in range(i+1):
#         temp = temp + " else k<x>.2"
#     temp = temp+" else k<x>.2"
#     string4 = string4 + " + ("+temp+")"

# print(string4) 


inner_t = ""
for i in range(nb_choice*3):
  inner_t = inner_t + "(k<" + str(i) + ">.1)+"
inner_t = inner_t + "(k<" + str(nb_choice*3) + ">.1)"

inner_f = ""
for i in range(nb_choice*3):
  inner_f = inner_f + "(k<" + str(i) + ">.2)+"
inner_f = inner_f + "(k<" + str(nb_choice*3) + ">.2)"

if nb_choice == 1:
  string4 = "l(x).if x==4 then k<x>." + inner_t + " else k<x>." + inner_f
else:
  string4 = "l(x).(if x==4 then k<x>." + inner_t + " else k<x>." + inner_f + ")"
  for i in range(nb_choice-1):
    temp = "if x mod 2 == 0 then "
    temp2 = "(recX.k<1>.X)"
    counter = 6+(2*(i)) 
    for x in range(i+1):
        temp = temp + "if x<" + str(counter) + " then " 
        counter -= 2
    temp = temp + "if x>2 then k<x>." + inner_t + " else k<x>." + inner_f
    for x in range(i+1):
        temp = temp + " else " + inner_f
    temp = temp+" else " + inner_f
    string4 = string4 + " + ("+temp+")"

print(string4) 