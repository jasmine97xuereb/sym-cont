from sys import argv

try:
  nb_choice = int(argv[1])
except:  
  print("Enter Number of Repetition: ") 
  nb_choice = int(input())

string = "(recX.k<1>.X)"
string2="l(x).(if x==4 then k<x>.2 else k<x>.1)"
string3 = "rec X.(k<1>.(l<1>.X)+(q<1>.1))"
string4 = "l(x).k<x>."

counter = 6+(2*(nb_choice-1)) 

for i in range(nb_choice-1):
    string = string + "+ (recX.k<" + str(i+2) + ">.X)"

string = string + "+(recX.k<"+ str(nb_choice+1) +">.X)"    

print(string)

# for i in range(nb_choice):
#     if i == 0 and nb_choice == 1:
#         string2 = "l(x).if x==4 then k<x>.2 else k<x>.1"
#     else:
#         temp = "if x mod 2 == 0 then "
#         counter = 6+(2*(i)) 
#         for x in range(i+1):
#             temp = temp + "if x<" + str(counter) + " then " 
#             counter -= 2
#         temp = temp + "if x>2 then k<x>.2 else k<x>.1"
#         for x in range(i+1):
#             temp = temp + " else k<x>.1"
#         temp = temp+" else k<x>.1"
#         string2 = string2 + " + ("+temp+")"

# print(string2) 

for i in range(nb_choice-1):
    string3 = string3 + "+ (k<" + str(i+2) + ">.(l<" +str(i+2)+ ">.X)+(q<" +str(i+2)+ ">.1))"

string3 = string3 + "+(k<"+ str(nb_choice+1) +">.(l<" +str(nb_choice+1)+ ">.X)+(q<" +str(nb_choice+1)+ ">.1))"    

print(string3)

# for i in range(nb_choice-1):
#     string4 += "k<(x+" +str(i+1)+ ")>."
# string4 += "1"

# print(string4)