import os 
import subprocess
import resource # for timing the subprocess
import numpy as np
import pandas as pd
import matplotlib.pyplot as plt
import os
import six
import time

my_env = os.environ.copy()
my_env['DYLD_LIBRARY_PATH'] = "/Users/jasminexuereb/.opam/4.08.0/lib/z3" 
FNULL = open(os.devnull, 'w') # to hide console output of the subprocess

# remove outliers by removing anything which is > or < than the standard deviation (how spread data is around the mean)
# return the mean
def GetMean(df):
  df_clean = df[np.abs(df.Time - df.Time.mean()) <= (df.Time.std())]
  mean = df_clean.Time.mean()
  return mean

def RunToolOnce(mon):
  try: 
    usage_start = resource.getrusage(resource.RUSAGE_CHILDREN)
    # subprocess.run(["./Tool/main.native"] + [mon], env=my_env, stderr=subprocess.STDOUT, timeout=1800) 
    subprocess.run(["./Tool/main.native"] + [mon], env=my_env, stderr=subprocess.STDOUT) 
    usage_end = resource.getrusage(resource.RUSAGE_CHILDREN)
    time = usage_end.ru_utime - usage_start.ru_utime
  except:
    # time = None
    time=float("inf")
#   print(time)
  return time

# run the tool a number of times
# store each running time in a dataframe
# clean the dataframe and return the mean running time
def GetData(mon):
  time_arr = []
#   df = pd.DataFrame(columns=['Time'])
  return RunToolOnce(mon)
#   for i in range (0, 2):
#     time_arr.append(RunToolOnce(mon))
#   df['Time'] = time_arr
#   return GetMean(df)

# get the list of generated monitors
# specify the required number of repetitions by passing this value as a parameter
# run generate.py
# get the tool's mean running time for each monitor in the list
# returns a record with the mean running time for complexity 'repetition'
def AnalyseMonitors(repetition):
  time_record = []  
  output = os.popen("python generate.py "+str(repetition)).read()
  mon_arr = (output.splitlines())
#   print(output)
  for mon in mon_arr:
    print("Monitor being Analysed: ", mon)
    time_record.append(float(GetData(mon)))
  return time_record

def UpToComplexity(complexity):  
#   results = pd.DataFrame(columns=['Choice','NestedIFs','Recursion'])
#   results = pd.DataFrame(columns=['Choice','Recursion'])
  results = pd.DataFrame(columns=['NestedfIFs'])

  for i in range (1, complexity+1):
    print("For complexity ", i)
    record = AnalyseMonitors(i)
    print(record)
    results.loc[len(results)] = record
  results.index += 1 
  return results

def ComplexitySteps(complexity):  
#   results = pd.DataFrame(columns=['Choice','NestedIFs','Recursion'])
#   results = pd.DataFrame(columns=['Choice','Recursion'])
  results = pd.DataFrame(columns=['NestedfIFs'])

  for i in complexity:
    print("For complexity ", i)
    record = AnalyseMonitors(i)
    print(record)
    results.loc[len(results)] = record
  results.index += 1 
  return results

def Plot(df):
#   for column_name in df.columns
#   plt.scatter(df.Choice, df.NestedIFs, df.Recursion)
#   plt.show()
#   plt.savefig('test.png')

#   ax = df.plot(kind='line', subplots=True)  
#   ax2 = df['NestedIFs'].plot(kind='line')    
#   ax3 = df['Recursion'].plot(kind='line')    

#   ax1 = df.plot(kind='line', y='Choice', use_index=True, marker='o', color='g')    
#   ax2 = df.plot(kind='line', y='NestedIFs', use_index=True, marker='o', color='r')    
#   ax3 = df.plot(kind='line', y='Recursion', use_index=True, marker='o', color='b')

#   ax1.set_title("Choice Monitors")
#   ax1.set_xlabel("Complexity")
#   ax1.set_ylabel("Time")
#   ax2.set_title("Nested IFs Monitors")
#   ax2.set_xlabel("Complexity")
#   ax2.set_ylabel("Time")
#   ax3.set_title("Recursion Monitors")
#   ax3.set_xlabel("Complexity")
#   ax3.set_ylabel("Time")
#   plt.show()
#   ax3.savefig("NestedIFS_basic.png")

#   fig = plt.figure()
#   ax = fig.add_subplot(221)
#   plt.plot(df.index, df.Choice, marker='o', color='g')

#   ax = fig.add_subplot(222)
#   plt.plot(df.index, df.Recursion, marker='o', color='b')

#   plt.show()

  plt.figure()
  df.plot(kind='line', y='Choice', use_index=True, marker='o', color='g') 
  plt.legend('')  
  plt.title("Choice Monitors")
  plt.xlabel("Complexity")
  plt.ylabel("Time")
  plt.savefig("choice_base.png")

  plt.figure()
  df.plot(kind='line', y='Recursion', use_index=True, marker='o', color='g') 
  plt.legend('')  
  plt.title("Recursion Monitors")
  plt.xlabel("Complexity")
  plt.ylabel("Time")
  plt.savefig("recursion_base.png")

results = UpToComplexity(1)
# results = ComplexitySteps([1,5,10])
print(results)
# results.to_csv("RunningTimes2.csv")
# Plot(results)
