#!/usr/bin/python3
# -*- coding: utf-8 -*-
import sys
from collections import defaultdict
import os
import re
from z3 import *
from collections import defaultdict
import math
import time
import queue  

stime = time.time()

class twinPlant:
	'''
	Class to analyse model.
	1. Get normal diagnoser and fault diagnoser 
	2. Synchronize normal diagnoser and fault diagnoser to twin-plant
	3. Abstract a new structure of twin-plant
	4. Eliminate unobservable events of twin-plant to a new system(represented by FA).
	'''

	modelfile = sys.argv[1]

	model = open(modelfile,"r")
	context = model.readlines()
	model.close()
	transitionList = [] #changed after eliminate shared transition

	nextTransition = []
	synchronize = []
	refindNormalDiagnoser = []
	beforeTransition = []
	ornd = []
	ostate = []
	cp = []

	def __init__(self):
		self.faultDiagnoser = set()
		self.normalDiagnoser = set()
		self.ndClause = []
		self.fdClause = []
		self.sharedTransition = []

		self.state_dict = {}
		self.newtransition = []
		self.newNextTransition = []
		self.initialState = int(self.context[0].split(" ")[1].split("\n")[0])


		self.nextState = []
		self.eventListOpp = {}
		self.shardListTrans = []


		self.ndd = [] # ndd is normal diagnoser'

		for i in range(1,len(self.context)):
			transition = []
			sourceState = int(self.context[i].split(" ")[0]) - int(self.initialState)
			event = self.context[i].split(" ")[1]
			finalState = int(self.context[i].split(" ")[2].split("\n")[0]) - int(self.initialState)

			if event == "f":
				event = 1
			elif "u" in event:
				event = 2
			else:
				event = int(event.strip("o")) + 2

			transition.append(sourceState)
			transition.append(finalState)
			transition.append(event)


			self.transitionList.append(transition)


		self.transitionList.insert(0,[-1,-1,2])

		self.nextTransition = [[] for i in range(len(self.transitionList))]

		for i in range(len(self.transitionList)):
			for j in range(len(self.transitionList)):
				if (self.transitionList[i][1] == self.transitionList[j][0]):
					self.nextTransition[i].append(j)



	def diagnoser(self):

		# only for one fault transition

		fd = set()
		faultTransitions = []

		for i in range(len(self.transitionList)):
			if self.transitionList[i][2] == 1:
				faultTransitions.append(i)
				break

		#get the transitions after fault
		nextLevel = faultTransitions.copy()
		new_level = [1]

		
		while len(nextLevel) != 0 and len(new_level) != 0:
			new_level = []
			for item in nextLevel:
				for transition in self.nextTransition[item]:
					if transition not in fd:
						fd.add(transition)
						nextLevel.append(transition)
						new_level.append(transition)


		#get the transition before fault
		beforeLevel = faultTransitions.copy()
		new_level = [1]
		ffd = set()

		while len(beforeLevel) != 0 and len(new_level) != 0:
			new_level = []
			for item in beforeLevel:
				for i in range(len(self.nextTransition)):
					if item in self.nextTransition[i]:
						if i not in ffd:
							ffd.add(i)
							beforeLevel.append(i)
							new_level.append(i)


		fd = fd | ffd

		for trans in faultTransitions:
			fd.add(trans)

		self.faultDiagnoser = fd


		nd = set()
		mother = []
		for i in range(len(self.transitionList)):
			if self.transitionList[i][0] == self.initialState:
				if self.transitionList[i][2] != 1:
					mother.append(i)


		new_level = [1]
		while len(mother) != 0 and len(new_level) != 0 :
			new_level = []
			for item in mother:
				for node in self.nextTransition[item]:
					if self.transitionList[node][2] != 1:
						if node not in nd:
							nd.add(node)
							mother.append(node)
							new_level.append(node)
		for i in mother:
			nd.add(i)

		self.normalDiagnoser = nd

		fdnextTransition = defaultdict(list)
		ndnextTransition = defaultdict(list)

		for elem in self.faultDiagnoser:
			fdnextTransition[elem] = []
			for nelem in self.nextTransition[elem]:
				if nelem in self.faultDiagnoser:
					fdnextTransition[elem].append(nelem)

		for elem in self.normalDiagnoser:
			ndnextTransition[elem] = []
			for nelem in self.nextTransition[elem]:
				if nelem in self.normalDiagnoser:
					ndnextTransition[elem].append(nelem)			

		def checkEmptylist(one_dict):
			result = True
			for elem in one_dict.keys():
				if one_dict[elem] == []:
					result = elem
					break		
			return result

		empty = checkEmptylist(fdnextTransition)
		while not empty is True:
			del fdnextTransition[empty]
			for elem in fdnextTransition.keys():
				if empty in fdnextTransition[elem]:
					fdnextTransition.remove(empty)
			empty = checkEmptylist(fdnextTransition)


		empty = checkEmptylist(ndnextTransition)
		while not empty is True:
			del ndnextTransition[empty]
			for elem in ndnextTransition.keys():
				if empty in ndnextTransition[elem]:
					ndnextTransition[elem].remove(empty)
			empty = checkEmptylist(ndnextTransition)

		fdClause = set()
		ndClause = set()
		

		for key,value in fdnextTransition.items():
			fdClause.add(key)
			for elem in value:
				fdClause.add(elem)

		for key,value in ndnextTransition.items():
			ndClause.add(key)
			for elem in value:
				ndClause.add(elem)

		sharedTransition = fdClause & ndClause


		self.ndClause = list(ndClause)
		self.fdClause = list(fdClause)
		self.sharedTransition = list(sharedTransition)


		print("fdnextTransition",fdnextTransition)
		print("ndnextTransition",ndnextTransition)

		print("ndClause\n",self.ndClause)
		print("fdClause\n",self.fdClause)

		print("sharedTransition\n",self.sharedTransition)




	def get_keys(self, d, value):
		return [k for k,v in d.items() if v == value]



	def synchronize(self):
		faultLevel = []
		normalLevel = []
		syn = []

		for item in self.fdClause:
			if self.transitionList[item][0] == self.initialState:
				faultLevel.append(item)

		for item in self.ndClause:
			if self.transitionList[item][0] == self.initialState:
				normalLevel.append(item) 



		# initial: syn first level form initial state
		i = 0
		con = []
		repate = set()
		for faultT in faultLevel:
			for normalT in normalLevel:
				couple = []
				couple.append(faultT)
				couple.append(normalT)
				con.append(couple)
				repate.add(str(faultT) + "@" + str(normalT))
				#repate.add(couple)
		syn.append(con)

		cycle = []


		while len(syn[i]) != 0:

			print("syn[i]",syn[i])

			couple = []
			con = []
			con_repeat = set()
			j = 0
			while j < len(syn[i]):
			#for j in range(len(syn[i])):
			#for item in syn[i]:
				print("j",j)
				print("syn[i][j]",syn[i][j])
				faultEvent = int(self.transitionList[syn[i][j][0]][2])
				normalEvent = int(self.transitionList[syn[i][j][1]][2])
				if faultEvent > 2 and normalEvent <= 2:

					for normal in self.nextTransition[syn[i][j][1]]:

						if syn[i][j][0] in self.fdClause and normal in self.ndClause:
							st = str(syn[i][j][0]) + "@" + str(normal)
							b = [str(syn[i][j][0]),str(syn[i][j][0])]
							if st not in repate and syn[i][j][0]:
								couple.append(syn[i][j][0])
								couple.append(normal)
								con.append(couple)
								print("1",couple)
								couple = []
								repate.add(st)
								con_repeat.add(st)
							elif st in repate and st not in con_repeat:
								t = [int(st.split("@")[0]),int(st.split("@")[1])]
								cycle.append(i)
								cycle.append(t)

					j += 1

				elif faultEvent <= 2 and normalEvent > 2:

					for fault in self.nextTransition[syn[i][j][0]]:
						if fault in self.fdClause and syn[i][j][1] in self.ndClause:
							st = str(fault) + "@" + str(syn[i][j][1])
							if st not in repate:
								couple.append(fault)
								couple.append(syn[i][j][1])
								con.append(couple)
								print("2",couple)
								couple = []
								repate.add(st)
								con_repeat.add(st)
							elif st in repate and st not in con_repeat:
								t = [int(st.split("@")[0]),int(st.split("@")[1])]
								cycle.append(i)
								cycle.append(t)
					j += 1

				elif faultEvent > 2 and normalEvent > 2:

					if faultEvent == normalEvent:

						for fault in self.nextTransition[syn[i][j][0]]:
							for normal in self.nextTransition[syn[i][j][1]]:
								if fault in self.fdClause and normal in self.ndClause:
									st = str(fault) + "@" + str(normal)
									if st not in repate:
										couple.append(fault)
										couple.append(normal)
										con.append(couple)
										print("2",couple)
										couple = []
										repate.add(st)
										con_repeat.add(st)
									elif st in repate and st not in con_repeat:
										t = [int(st.split("@")[0]),int(st.split("@")[1])]
										cycle.append(i)
										cycle.append(t)

						j += 1
					else:
						print("5",syn[i][j])
						syn[i].remove(syn[i][j])
						couple = [] 

				elif faultEvent <= 2 and normalEvent <= 2:
					for fault in self.nextTransition[syn[i][j][0]]:
						for normal in self.nextTransition[syn[i][j][1]]:
							if fault in self.fdClause and normal in self.ndClause:
								st = str(fault) + "@" + str(normal)
								if st not in repate:
									couple.append(fault)
									couple.append(normal)
									con.append(couple)
									print("4",couple)
									couple = []
									repate.add(st)
									con_repeat.add(st)
								elif st in repate and st not in con_repeat:
									t = [int(st.split("@")[0]),int(st.split("@")[1])]
									cycle.append(i)
									cycle.append(t)
	
					j += 1
			print("con",con)
			syn.append(con)
			i += 1

		self.synchronize = syn.copy()
		print("synchronize\n",self.synchronize)
		print("cycle\n",cycle)

		s = 0
		e = 2
		pair = cycle[s:e]
		while len(pair) != 0:
			self.synchronize.append([])
			for i in range(pair[0]+1):
				for elem in self.synchronize[i]:
					if pair[1] == elem:
						self.synchronize[pair[0]+1].append(pair[1])
						break
				else:
					continue
				break

			s += 2
			e += 2
			if e <= len(cycle):
				pair = cycle[s:e]
			else:
				pair = []

		self.synchronize = list(filter(None, self.synchronize))



		#critial pair

		# 1 remove a cp synchronize by itself.

		print("syn--------",self.synchronize)
		#exit(0)

		tp = []

		for elem in self.synchronize[0]:
			state = []
			for trans in elem:
				state.append(self.transitionList[trans][0])
			tp.append(state)


		for elem in self.synchronize:
			level = []
			for nelem in elem:
				state = []
				for trans in nelem:
					state.append(self.transitionList[trans][1])
				level.append(state)
			tp.append(level)
		tp.pop(-1)

		print("tp\n",tp)


		#lastlevel = self.synchronize[-1]  # final critical pair

		'''
		#for i in range(len(self.synchronize)):
		#	level = self.synchronize[i].copy()
		#	for cp in level:
		#		if cp[0] == cp[1]:
		#			self.synchronize[i].remove(cp)
		'''



		ele = [] #construction of twin plant
		levellength = 0

		state_dict = {}  # index: state pair
		init = 0
		states = set()

		for i in range(len(self.synchronize)):
			for j in self.synchronize[i]:
				if str(j[0]) + "@" +str(j[1]) not in states:
					states.add(str(j[0]) + "@" +str(j[1])) 
					state_dict[init] = j
					init += 1

		self.state_dict = state_dict
		print("state_dict\n",state_dict)

		print("syn\n",self.synchronize)

		ndd = []

		# get nf from synchornize:
		for couple in self.synchronize:
			level = []
			for item in couple:
				nt = item[1]
				ft = item[0]
				if self.transitionList[ft][2]>2 or (self.transitionList[ft][2]<3 and self.transitionList[nt][2]<3):
					level.append(nt)
			ndd.append(level)

		ndd = list(filter(None, ndd))
		ndd.pop(-1)
		print("ndd-----",ndd) 


		# create twin plant with state.

		twinPlantPair = {}
		twinPlantPair[0] = [[0,0]] #initial twin plant, in the first level, the init node is initstate synchronized with itself.


		for i in range(len(self.synchronize)):
			statePairLevel = []
			for item in self.synchronize[i]:
				statePair = [self.transitionList[item[0]][1], self.transitionList[item[1]][1]]
				statePairLevel.append(statePair)

			twinPlantPair[i+1] = statePairLevel


		print("twinPlantPair",twinPlantPair)

		self.nextState = {}

		for i in range(len(self.transitionList)):
			key = self.transitionList[i][0]
			value = self.transitionList[i][1]
			event = str(self.transitionList[i][2]) + "@"
			if key not in self.nextState.keys():
				self.nextState[key] = []
				self.nextState[key].append(value)
				self.nextState[key].append(event)
			else:
				if value not in self.nextState[key]:
					self.nextState[key].append(value)
					self.nextState[key].append(event)


		print("self.nextState",self.nextState)

		eventList = {}  # key: state@state(pair), value: state(new)
		keySet = set()
		index = 0
		for elemm in twinPlantPair.values():
			print(elemm)
			for elem in elemm:
				elemString = str(elem[0]) + "@" + str(elem[1])
				if elemString not in keySet:
					eventList[elemString] = index
					index += 1
					keySet.add(elemString)


		print("eventList",eventList)

		eventListOpp = {v: k for k, v in eventList.items()}

		print("eventListOpp",eventListOpp)

		self.eventListOpp = eventListOpp



		twinPlantTrans = []


		index = 0

		while index+1 in twinPlantPair.keys():
			for elemSource in twinPlantPair[index]:	

				sourceTrans = eventList[str(elemSource[0]) + "@" + str(elemSource[1])]

				for elemFinal in twinPlantPair[index+1]:

					finalTrans = eventList[str(elemFinal[0]) + "@" + str(elemFinal[1])]

					
					for i in range(len(self.nextState[elemSource[0]])):
						if elemFinal[0] == self.nextState[elemSource[0]][i] or elemFinal[0] == elemSource[0]:
							if elemFinal[0] == elemSource[0]:
								eventFirst = -1
							else:
								eventFirst = self.nextState[elemSource[0]][i+1].split("@")[0]
							for j in range(len(self.nextState[elemSource[1]])):
								if elemFinal[1] == self.nextState[elemSource[1]][j] or elemFinal[1] == elemSource[1]:
									if elemFinal[1] == elemSource[1]:
										eventSecond = -1
									else:
										eventSecond = self.nextState[elemSource[1]][j+1].split("@")[0]
									
									if eventFirst != -1 and eventSecond == eventFirst:
										transition = transition = [sourceTrans, finalTrans, int(eventSecond)]
									elif int(eventFirst) >= 0 and int(eventSecond)>= 0:
										transition = transition = [sourceTrans, finalTrans, min(int(eventSecond),int(eventFirst))]
									elif int(eventFirst) == -1 and int(eventSecond) == -1:

										for k in range(len(self.nextState[elemFinal[1]])):
											if elemFinal[1] == self.nextState[elemFinal[1]][k]:
												event = self.nextState[elemFinal[1]][k+1].split("@")[0]
												transition = [sourceTrans, finalTrans, int(event)]
												break

									else:
										transition = [sourceTrans, finalTrans, max(int(eventSecond),int(eventFirst))]

						
									twinPlantTrans.append(transition)
			index += 1
		print("twinPlantTrans",twinPlantTrans)
		twinPlantTransitions = []

		for trans in twinPlantTrans:
			if trans not in twinPlantTransitions:
				twinPlantTransitions.append(trans)

		print("twinPlantTransitions",twinPlantTransitions)


		def deleteNoSuccessorNode(self,model):
			'''
			model: a list store all transitions
			return: a list store model without nodes which have no successor.

			'''
			newModel = []
			nextStateDict = {}
			for transitions in model:
				start = transitions[0]
				final = transitions[1]
				if start not in nextStateDict.keys():
					nextStateDict[start] = []
					nextStateDict[start].append(final)
				else:
					if final not in nextStateDict[start]:
						nextStateDict[start].append(final)

				if final not in nextStateDict.keys():
					nextStateDict[final] = []



			noSuccessor = []
			nodeDelect = [] #store node have to delete
			for key in nextStateDict.keys():
				if len(nextStateDict[key]) == 0:
					noSuccessor.append(key)
			print("nextStateDict",nextStateDict)
			print("noSuccessor",noSuccessor)


			while noSuccessor:
				deleteNode = noSuccessor[0]
				nodeDelect.append(deleteNode)
				noSuccessor.remove(deleteNode)
				for key in nextStateDict.keys():
					if deleteNode in nextStateDict[key]:
		
						nextStateDict[key].remove(deleteNode)
						if len(nextStateDict[key])==0:
							noSuccessor.append(key)


			for trans in model:
				if trans[0] not in nodeDelect and trans[1] not in nodeDelect:
					newModel.append(trans)

			return newModel


		twinPlantTransitions = deleteNoSuccessorNode(self,twinPlantTransitions)
		print("twinPlantTransitions",twinPlantTransitions)



		for i in range(len(self.synchronize)-1):
			for item in self.synchronize[i]:
				sn = self.get_keys(state_dict,item)
				for n in self.synchronize[i+1]:
					if n[0] in self.nextTransition[item[0]] and n[1] in self.nextTransition[item[1]]:
						en = self.get_keys(state_dict,n)
						ele.append([sn[0],en[0]])
					if n[0] == item[0] and n[1] in self.nextTransition[item[1]]:
						en = self.get_keys(state_dict,n)
						ele.append([sn[0],en[0]])
					if n[1] == item[1] and n[0] in self.nextTransition[item[0]]:
						en = self.get_keys(state_dict,n)
						ele.append([sn[0],en[0]])

		print("ele\n",ele)


		# remove transitions which have no successor.
		#print("lastlevel",lastlevel)
		#final_node_num = len(lastlevel)
		#lasttransition = []

		#sink  = len(state_dict)
		#max_node = len(state_dict) - 1
		#for i in range(final_node_num):
		#	lasttransition.append(max_node)
		#	max_node -= 1

		#print("lasttransition/n",lasttransition)


		#find all transition from init to end
		init = 0
		nextt = [[] for i in range(len(state_dict))]
		for elem in ele:
			index = elem[0]
			value = elem[1]
			nextt[index].append(value)
		print("nextt\n",nextt)

		#nextt = nextt[: -final_node_num]

		stateEmpty = set()
		newEmpty = set()

		newtransition = []
		for elem in ele:
			state = elem[0]
			state_pair = state_dict[state]
			trans = elem

			eventf = self.transitionList[state_pair[0]][2]
			eventn = self.transitionList[state_pair[1]][2]
			if eventf == eventn and eventf > 2:
				trans.append(eventf)
			else:
				trans.append(2)

			newtransition.append(trans)
		newtransition.insert(0,[-1,-1,2])
		print("newtransition\n",newtransition)

		self.newtransition = newtransition.copy()
		print("self.newtransition\n",self.newtransition)

		self.newNextTransition = [[] for i in range(len(self.newtransition))]


		'''
		for i in range(len(self.newtransition)):
			for j in range(len(self.newtransition)):
				if (self.newtransition[i][1] == self.newtransition[j][0]):
					self.newtransition[i].append(j)
		'''


		print("self.newNextTransition\n",self.nextTransition)

		print("self.newtransition\n",self.newtransition)

		self.newtransition = twinPlantTransitions.copy()

		print("self.newtransition\n",self.newtransition)



		# newtransition is the construction of twin-plant(normal-diagnoser)
		# 1. eliminate unobservable transitions on newtransition



	def refindNormalDiagnoser(self):

		self.refindNormalDiagnoser = [i for i in range(1,len(self.newtransition))]
		print("self.refindNormalDiagnoser\n",self.refindNormalDiagnoser)



	#----------eliminate unobservable events---------------------#

	#actually, real refinded normal diagnoser should eliminate unobsvable events.
	#this real_rfd only used to computer max-flow. so next step is unfoding this one, then computer max-flow
	#for get result convernient, we can keep use smt on self.refindNormalDiagnoser.
	

		efnfa={}#保存nfa文件的字典 nfa dictionary
		states={}#map 对应起始状态下标 
		turnlist=[]
		visited={}

		#state
		state_set = set()
		event_set = set()
		final_set = set()

		for item in self.newtransition:
			start_state = item[0]
			state_set.add("q" + str(start_state))
			final_state = item[1]
			state_set.add("q" + str(final_state))
			event = item[2]
			event_set.add(str(event))
			if start_state == final_state:
				final_set.add("q" + str(start_state))


		'''
		for item in self.refindNormalDiagnoser:
			#start_state = self.transitionList[item][0]
			start_state = self.newtransition[item][0]
			state_set.add("q" + str(start_state))

			#final_state = self.transitionList[item][1]
			#final_state = self.nextTransition[item][1]
			final_state = self.newtransition[item][1]
			state_set.add("q" + str(final_state))

			#event = self.transitionList[item][2]
			event = self.newtransition[item][2]
			event_set.add(str(event))

			if start_state == final_state:
				final_set.add("q" + str(start_state))
		'''
		state_list = list(state_set)
		event_list = list(event_set)
		final_list = list(final_set)

		#start_state = ["q" + str(self.initialState)]
		statr_state  = ["q0"]


		efnfa['states']= state_list
		efnfa['alphabet']= event_list
		efnfa['start'] = start_state
		efnfa['final']= final_list
		efnfa['delta']=[]


		for i in range(len(efnfa['states'])):
		        states[efnfa['states'][i]]=i


		tp_sett = set()
		print("tp.faultDiagnoser",tp.faultDiagnoser)
		print("tp.newtransition",tp.newtransition)
		#for e in tp.faultDiagnoser:
		#	#elem = tp.transitionList[e]
		#	elem = tp.newtransition[e]
		#	st = str(elem[0]) + "@" + str(elem[1]) + str(elem[2])
		#	tp_sett.add(st)

		#print("unfold_list_ori",unfold_list_ori)

		shard_set = set()
		a = set(tp.normalDiagnoser)
		shard_set = a & tp.faultDiagnoser
		print("shard_set\n",shard_set)

		shardList = list(shard_set)
		for elem in shardList:
			self.shardListTrans.append(self.transitionList[elem]) 

		print("shardListTrans",self.shardListTrans)

		# change event in shared transition to unobservable.
		'''
		for i in range(len(self.newtransition)):
			trans = self.newtransition[i]
		#for trans in self.newtransition:
			start = self.eventListOpp[trans[0]].split("@")[1]
			final = self.eventListOpp[trans[1]].split("@")[1]
			event = trans[2]
			transition = [int(start),int(final),event]
			print("transition",transition)
			if transition in shardListTrans:
				print("iiiiiiiii")
				self.newtransition[i] = [trans[0],trans[1],2]
				print("trans",trans)
		'''

		print("self.newtransition",self.newtransition)

		print("self.state_dict",self.state_dict)

		for item in self.newtransition:
			trans = []
			fir_state = item[0]
			fin_state = item[1]
			event = int(item[2])
			if event < 3:
				event = '@'
			trans.append("q" + str(fir_state))
			trans.append(str(event))
			trans.append("q" + str(fin_state))

			efnfa['delta'].append(trans)

		'''
		for item in self.refindNormalDiagnoser:
			trans = []
			#fir_state = self.transitionList[item][0]
			#fin_state = self.transitionList[item][1]
			#event = self.transitionList[item][2]
			fir_state = self.newtransition[item][0]
			fin_state = self.newtransition[item][1]
			event = int(self.newtransition[item][2])

			if event < 3 or self.state_dict[fir_state][1] in shard_set:
				event = '@'
			trans.append("q" + str(fir_state))
			trans.append(str(event))
			trans.append("q" + str(fin_state))

			efnfa['delta'].append(trans)
		'''



		def saveToprogram():
		    #保存图的邻接矩阵
		    turnList=[[0 for i in range(len(efnfa['states']))]for j in range(len(efnfa['states']))]
		    for i in efnfa['states']:
		        visited[i]=0

		    for i in efnfa['delta']:
		        turnList[states[i[0]]][states[i[2]]]=i[1]
		saveToprogram()
		#ε-closure： 基于深度优先遍历的算法  based deep-first search
		closure = set() #set集合
		def eps_closure(x):
		    closure.add(x)  #集合的加法， 并
		    for i in range(len(efnfa['delta'])):
		        if efnfa['delta'][i][0]==x and efnfa['delta'][i][1]=='@':#y 是 x 通过 ε 转换到的 y。
		            if visited[efnfa['delta'][i][2]]==0:#如果 y 还没有访问过，就访问 y
		                 visited[efnfa['delta'][i][2]]=1
		                 eps_closure( efnfa['delta'][i][2])

		#新DFA的转移保存
		dfa_delta=[]
		eps_closure('q0')
		A=closure.copy()
		closure.clear()
		Q=set()#转换后的dfa状态
		Q.add(tuple(A))
		worklist=[]
		worklist.append(A)

		for i in efnfa['states']:
		    visited[i]=0
		def nfaTOdfa():
		    while len(worklist)!=0:
		        q=worklist.pop()
		        for i in efnfa['alphabet']:
		            for j in  range(len(efnfa['delta'])):  #  t <- e-closure(delta(q,c))   // delta(q0, a) = {n1}, t = {n1, n2, n3, n4, n6, n9}
		                for k in q:
		                    if efnfa['delta'][j][0]==k and efnfa['delta'][j][1]==i:
		                        for h in efnfa['states']:          # t <- e-closure(delta(q,c)) 
		                            visited[h]=0
		                        eps_closure(efnfa['delta'][j][2])
		                        t=closure.copy()
		                        closure.clear()
		                        temp=[]
		                        temp.append(q)
		                        temp.append(i)
		                        temp.append(t)
		                        dfa_delta.append(tuple(temp))
		                        if tuple(t) not in Q:
		                            Q.add(tuple(t))
		                            worklist.append(t)
		nfaTOdfa()

		ss_state = []
		for item in Q:
			s_set = set()
			for i in item:
				s_set.add(i)
			ss_state.append(s_set)


		#f_state = self.initialState
		ornd = []
		print("dfa_delta",dfa_delta)
		for item in dfa_delta:
			trans = []
			e_set = item[0]
			for i in range(len(ss_state)):
				if e_set == ss_state[i]:
					trans.append(i)
					break
			e_set = item[2]
			for i in range(len(ss_state)):
				if e_set == ss_state[i]:
					trans.append(i)
					break
			trans.append(int(item[1]))
			ornd.append(trans)

		self.initialState_ori = self.initialState


		for i in range(len(ss_state)):
			if "q" + str(self.initialState) in ss_state[i]:
				self.initialState = i
				break
		print("initialState\n",self.initialState)
		print("ss_state",ss_state)

		self.ostate = ss_state.copy()

		self.ornd = ornd.copy()


		

assert(len(sys.argv) == 3)
print("------------")
tp = twinPlant()
#tp.run()
tp.diagnoser()
tp.synchronize()
tp.refindNormalDiagnoser()

#print("transitions:",tp.transitionList)
#print("next_transitions",tp.nextTransition)
print("fd",tp.faultDiagnoser)
print("nd",tp.normalDiagnoser)
print("syn",tp.synchronize)
print("rnd",tp.refindNormalDiagnoser)
print("ornd",tp.ornd)
print("transition",tp.transitionList)



#---------------------Unfolding-------------------------#

'''
Unfolding FA achieved from last step with Breadth-First Search.

'''

normal_path = [] #normal path is elimiated observable events to compute  max-flow
fault_path = []

normal_path = tp.ornd.copy()

for elem in normal_path:
    successor = defaultdict(set)


state_ori = set()
state = set()
for elem in normal_path:
    successor[elem[0]].add(str(elem[1]) + "@" +  str(elem[2]))
    state.add(elem[0])
    state.add(elem[1])


visited = [False for i in range(0,max(state)+1)]

unfold_list = []  #store all transiton of unfolding FSA
unfold_list_ori = []

sink = max(state) + 1

currentPath = [tp.initialState]

extend = []
sink_noloop = set()

def BFS(v):
	q = queue.Queue()
	q.put(v)
	visited[v] = True
	thislevel = set()
	nextlevel = []

	while not q.empty():
		index = q.get()
		if len(nextlevel) == 0 or index == nextlevel[0]:
			thislevel = set()
			nextlevel.clear()


		for w in successor[index]:
			finalstate = int(w.split("@")[0])

			if visited[finalstate] == True:

				if finalstate not in thislevel:
					event = int(w.split("@")[1])
					trans = [index, sink, event, finalstate]

					unfold_list.append(trans)

			elif visited[finalstate] == False:
				visited[finalstate] = True

				thislevel.add(finalstate)
				nextlevel.append(finalstate)
				q.put(finalstate)


BFS(tp.initialState)
print("unfold_list\n",unfold_list)

add_transitions = unfold_list.copy()
print("add_transitions",add_transitions)


for item in normal_path:
    if item not in unfold_list:
        unfold_list.append(item)


for item in extend:
	trans = [item[0],item[3],item[2]]
	unfold_list.remove(trans)


for i in range(len(unfold_list)):
	if unfold_list[i][1] in sink_noloop:
		unfold_list[i] = [unfold_list[i][0],sink,unfold_list[i][2]]

for elem in add_transitions:
	trans = [elem[0],elem[3],elem[2]]
	unfold_list.remove(trans)


print("tp.init",tp.initialState)
print("sink\n",sink)
print("unfold_list\n",unfold_list)


class Graph:


    def __init__(self, graph):
        self.graph = graph  # residual graph
        self.ROW = len(graph)

    # self.COL = len(gr[0])

    '''Returns true if there is a path from source 's' to sink 't' in 
    residual graph. Also fills parent[] to store the path '''

    def BFS(self, s, t, parent):

        # Mark all the vertices as not visited
        visited = [False] * (self.ROW)

        # Create a queue for BFS
        queue = []

        # Mark the source node as visited and enqueue it
        queue.append(s)
        visited[s] = True

        # Standard BFS Loop
        while queue:

            # Dequeue a vertex from queue and print it
            u = queue.pop(0)

            # Get all adjacent vertices of the dequeued vertex u
            # If a adjacent has not been visited, then mark it
            # visited and enqueue it
            for ind, val in enumerate(self.graph[u]):
                if visited[ind] == False and val > 0:
                    queue.append(ind)
                    visited[ind] = True
                    parent[ind] = u

                # If we reached sink in BFS starting from source, then return
        # true, else false
        return True if visited[t] else False

    # Returns tne maximum flow from s to t in the given graph
    def FordFulkerson(self, source, sink):

        # This array is filled by BFS and to store path
        parent = [-1] * (self.ROW)

        max_flow = 0  # There is no flow initially

        # Augment the flow while there is path from source to sink
        while self.BFS(source, sink, parent):

            # Find minimum residual capacity of the edges along the
            # path filled by BFS. Or we can say find the maximum flow
            # through the path found.
            path_flow = float("Inf")
            s = sink
            while (s != source):
                path_flow = min(path_flow, self.graph[parent[s]][s])
                s = parent[s]

            # Add path flow to overall flow
            max_flow += path_flow

            # update residual capacities of the edges and reverse edges
            # along the path
            v = sink
            while (v != source):
                u = parent[v]
                self.graph[u][v] -= path_flow
                self.graph[v][u] += path_flow
                v = parent[v]

        return max_flow

a = set()
for item in unfold_list:
	a.add(item[0])
	a.add(item[1])
length = max(a)



#Function to transform unfolding transing list to graph
def getGraph(unfold_list):
    graph = [[0 for i in range(length+1)] for j in range(length+1)]
    for trans in unfold_list:
        i = trans[0]
        j = trans[1]
        graph[i][j] += 1
    return graph


g = Graph(getGraph(unfold_list))

source = tp.initialState
maxflow = int(g.FordFulkerson(source, sink))


print ("The maximum possible flow is:", maxflow)



#  -------------------------get min-cut through SMT--------------------------#

#Get min-cut through SMT

filesmt = open('mod2smt.smt','w')

filesmt.write("(declare-datatypes (T1) ((Pair (mk-pair (first T1) (second T1) (third T1) ))))\n\n")
filesmt.write("(declare-fun trS (Int) (Pair Int))\n\n")
filesmt.write("(declare-const p0 (Pair Int))\n(assert (= (first p0) 0))\n\n")


source = tp.initialState
terminal_state = sink
print("source",source)

i = 0

for trans in unfold_list:
    i = i + 1
    first_state = trans[0]
    final_state = trans[1]
    flag = trans[2]
    filesmt.write("(declare-const p" + str(i) +" (Pair Int))\n")
    filesmt.write("(assert (= (first p"+str(i) +")"+str(first_state) +"))\n")
    filesmt.write("(assert (= (second p" + str(i) + ")" + str(final_state) + "))\n")
    filesmt.write("(assert (= (third p" + str(i) + ")" + str(flag) + "))\n")
    filesmt.write("(assert (= (trS " + str(i) + ")" + "p" +str(i) + "))\n\n")


state_num = max(state)

trans_num = i
filesmt.write("(define-fun trM ((x Int)) (Pair Int)\n (if (and (<= x "+str(trans_num)+") (> x 0))\n  (trS x)\n  p0))\n\n")

#initial state

filesmt.write(";initial state;\n\n")
filesmt.write("(declare-fun loc (Int) Int)\n(assert (= (loc 0) "+str(source)+"))\n\n")

filesmt.write("(declare-fun setype (Int) Int)\n")
filesmt.write("(assert (= (setype "+str(source)+ ") 1))\n")
filesmt.write("(assert (= (setype "+str(terminal_state)+") 0))\n\n")

#filesmt.write("(define-fun dvalue ((i Int)(j Int)) Int\n(if (not (= (setype i)(setype j)))\n1\n0))\n\n")
filesmt.write("(define-fun dvalue ((i Int)(j Int)) Int\n(if (and (= (setype i) 1)(= (setype j) 0))\n1\n0))\n\n")

filesmt.write("(define-fun value ((i Int)) Int\n(if (> i 0)\n(dvalue (first (trM i)) (second (trM i)))\n0))\n\n")

filesmt.write("(declare-fun sumdvalue (Int) Int)\n(assert (= (sumdvalue 0) 0))\n\n")

filesmt.write("(define-fun progress ((i Int)) Int\n(if (= i 0)\n(sumdvalue 0)\n(+ (sumdvalue (- i 1)) (value i))))\n\n")


for i in range(1,trans_num+1):
    filesmt.write("(assert (exists ((j Int)) (and (= j "+str(i)+")( < (setype (first (trM j))) 2) (< (setype (second (trM j))) 2)(<= (progress j) "+str(maxflow)+"))))\n")


for i in range(1,trans_num+1):
	filesmt.write("(assert (=> (= (value "+str(i)+") 1) ( > (third (trM "+str(i)+")) 2)))\n")


filesmt.write("(assert (and ")
for i in range(1,trans_num+1):
    filesmt.write("(= (progress "+str(i)+") (sumdvalue "+str(i)+"))")
filesmt.write("))\n\n")

filesmt.write("(assert (and ")
for i in range(0,state_num+1):
    filesmt.write("(>= (setype "+str(i)+") 0)")
filesmt.write("))\n\n")

filesmt.write("(assert (and ")
for i in range(1,trans_num+1):
    filesmt.write("(>= (progress "+str(i)+") 0)")
filesmt.write("))\n\n")

filesmt.write("(check-sat)\n\n")

filesmt.write("(get-value (")
for i in range(1,trans_num+1):
    filesmt.write("(value "+str(i)+")")
filesmt.write("))\n\n")
#filesmt.write("(get-info :all-statistics)\n")

filesmt.close()
os.system("z3 -smt2 mod2smt.smt > result.txt")

smt_result = open("result.txt","r")
result = smt_result.readline()
j = 0

cut = {}
key = 0

while result == "sat\n":
    key += 1
    cut[key] = []
    record = []

    for i in range(0,trans_num-1+1):
        a = smt_result.readline()
        record.append(a)


    smt_result.close()

    cut_index = []
        
    for i in range(0,len(record)):
        if record[i].split(")")[1] == " 1":
            #cut_name["cut" + str(j)].append(unfold_list_ori[i])
            cut_index.append(i+1)   
            #cut.append(unfold_list_ori[i])

            #cut.append(unfold_list[i])
            #cut.append(unfold_list[i])
            cut[key].append(unfold_list[i])



    filesmt = open("mod2smt.smt","a")


    if len(cut_index) == 1:
        filesmt.write("(assert (not (= (value "+str(cut_index[0])+") 1)))\n")
    else:
        filesmt.write("(assert (not (and ")
        for index in cut_index:
            filesmt.write("(= (value "+str(index) + ") 1)")
        filesmt.write(")))\n")

    filesmt.write("(check-sat)\n\n")
    filesmt.write("(get-value (")
    for i in range(1,trans_num+1):
        filesmt.write("(value "+str(i)+")")
    filesmt.write("))\n\n")

    filesmt.close()
    os.system("z3 -smt2 mod2smt.smt > result.txt")
    smt_result = open("result.txt","r")

    for k in range(0,(j+1)*(trans_num+1)):
        a = smt_result.readline()

    result = smt_result.readline()
    j += 1

print("min-cut",cut)


for key in cut.keys():
	for i in range(len(cut[key])):
		if len(cut[key][i]) == 4:
			cut[key][i] = [cut[key][i][0],cut[key][i][3],cut[key][i][2]]

print("min-cut",cut)


#find corresponding transition in elimination observable set
ocut = []
print("tp.ostate",tp.ostate)
print("tp.ornd",tp.ornd)

stateDict = {}
for key in tp.state_dict.keys():
	stateDict[key] = []
	for item in tp.state_dict[key]:
		stateDict[key].append(tp.transitionList[item][0])

print("stateDict = {}",stateDict)

#cutReal = []
cutReal = {}

for key in cut.keys():
	cutReal[key] = []
	for trans in cut[key]:
		sourceStateCut = trans[0]
		finalStateCut = trans[1]
		eventCut = trans[2]
		for item_s in tp.ostate[sourceStateCut]:
			sourceStateIndex = int(item_s.split('q')[1])
			#sourceStateOri = stateDict[sourceStateIndex][1]
			sourceStateOri = tp.eventListOpp[sourceStateIndex].split("@")[1]
			for item_f in tp.ostate[finalStateCut]:
				tranOri = []
				finalStateIndex = int(item_f.split('q')[1])
				finalStateOri = tp.eventListOpp[finalStateIndex].split("@")[1]
				tranOri.append(int(sourceStateOri))
				tranOri.append(int(finalStateOri))
				tranOri.append(eventCut)
				cutReal[key].append(tranOri)

print("cutReal",cutReal)
'''
for trans in cut:
	sourceStateCut = trans[0]
	finalStateCut = trans[1]
	eventCut = trans[2]
	for item_s in tp.ostate[sourceStateCut]:
		sourceStateIndex = int(item_s.split('q')[1])
		#sourceStateOri = stateDict[sourceStateIndex][1]
		sourceStateOri = tp.eventListOpp[sourceStateIndex].split("@")[1]
		for item_f in tp.ostate[finalStateCut]:
			tranOri = []
			finalStateIndex = int(item_f.split('q')[1])
			finalStateOri = tp.eventListOpp[finalStateIndex].split("@")[1]
			tranOri.append(int(sourceStateOri))
			tranOri.append(int(finalStateOri))
			tranOri.append(eventCut)
			cutReal.append(tranOri)

print("cutReal",cutReal)
'''

result = {}

for key in cutReal.keys():
	result[key] = []
	for cut in cutReal[key]:
		if cut in tp.transitionList and cut not in result[key]:
			result[key].append(cut)

print("result",result)



print("shard_set", tp.shardListTrans)
delete_key = []

for key in result.keys():
	for trans in result[key]:
		if trans in tp.shardListTrans:
			delete_key.append(key)
			break

print("delete_key",delete_key)


for key in delete_key:
	del result[key]

print("result",result)

i = 0
for key in result.keys():
	i += 1
	print("the "+str(i)+" cut is :")
	for value in result[key]:
		print(value)


ftime = time.time()
print('time',ftime - stime)

















