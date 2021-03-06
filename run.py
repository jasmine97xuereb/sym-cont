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

# return the mean
def GetMean(df):
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

# run the tool a number of times and return the mean running time
def GetData(mon):
  time_arr = []
  df = pd.DataFrame(columns=['Time'])
  for i in range (0, 2):
    time_arr.append(RunToolOnce(mon))
  df['Time'] = time_arr
  return GetMean(df)

# get the list of generated monitors
# specify the required number of repetitions by passing this value as a parameter
# run generate.py
# get the tool's mean running time for each monitor in the list
# returns a record with the mean running time for complexity 'repetition'
def AnalyseMonitors(repetition):
  time_record = []  
  output = os.popen("python generate.py "+str(repetition)).read()
  mon_arr = (output.splitlines())
  for mon in mon_arr:
    print("Monitor being Analysed: ", mon)
    time_record.append(float(GetData(mon)))
  return time_record

def UpToComplexity(complexity):  
  results = pd.DataFrame(columns=['Cnd','Rec','Brc'])
  
  for i in range (1, complexity+1):
    print("For complexity ", i)
    record = AnalyseMonitors(i)
    print(record)
    results.loc[len(results)] = record
  results.index += 1 
  return results

results = UpToComplexity(15)
print(results)
results.to_csv("RunningTimes.csv")