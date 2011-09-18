# Brindza, Jordan
# Lee, Alexandra
#
# University of Pennsylvania
# 04/29/2010
# CIS 521



from itertools import combinations, permutations
import random;
import numpy;
import copy;
import math;
import time;
import sys;



# NOTES:
# the solution is stored as a list of lab weeks
# the students are ordered by group. depending on group size
# 	e.g. if num_students = 6 and num_groups = 3 then
#			[0 1 2 3 4 5] would be a valid week where
#				group 1 = (0 1)
#				group 2 = (2 3)
#				group 3 = (4 5)




class schoolgirl:


	def __init__(self, students, labs, groups, time_limit):
		''' initializes problem given the total number of students, lab weeks, and groups per week '''

		# initialize variables for groups and labs
		self.num_students = students;
		self.num_labs = labs;
		self.base_group_sizes = copy.deepcopy(groups);
		self.__expand_group_sizes(groups);
		self.__build_swap_list();

		# initialize solution to none
		self.solution = [];
		self.conflicts = [];

		# initialize taboo variables
		self.taboo_limit = 400;
		self.best_error = sys.maxint;
		self.best_sol = None;

		self.time_limit = time_limit;


	def __expand_group_sizes(self, groups):
		''' determines groups sizes, correctly handling uneven class sizes '''
		
		self.group_size = [];
		self.num_groups = [];
		w = 0;
		while (w < self.num_labs):
			gs = groups[w];
			ngroups = int(self.num_students / gs);
			group_sizes = [gs] * ngroups;

			if (group_sizes):

				excess = self.num_students % gs;

				if (excess < gs):
					# add excess group members to existing groups
					group_index = 0;

					while (excess > 0):
						group_sizes[ group_index % ngroups ] += 1;
						excess -= 1;
						group_index += 1;
					
			else:
				# if the gs is greater than the num students then the group size is the number of students
				group_sizes = [self.num_students];

			self.group_size.append(group_sizes);
			self.num_groups.append(len(group_sizes));
			w += 1;


	def __build_gm_lut(self):
		''' builds a table indexed by week, group id to retrieve the group members '''

		self.gm_lut = [];

		for lab_week in range(self.num_labs):
			
			g = [];
			for gind in range(self.num_groups[lab_week]):
				g.append([]);

			# iterate over solution adding students to the group lists
			s = 0;
			while (s < self.num_students):
				g[self.group_ids[lab_week][s]].append(self.solution[lab_week][s]);
				s += 1;

			self.gm_lut.append(copy.deepcopy(g));

	
	def __update_gm_lut_and_conflicts(self, lab_week, s):
		''' updates the lab group lut for the given swap '''

		# get the current group assignment and the actual student ids
		s0 = self.solution[lab_week][s[0]];
		s1 = self.solution[lab_week][s[1]];

		# get the group index ids
		g0 = self.group_ids[lab_week][s[0]];
		g1 = self.group_ids[lab_week][s[1]];
		
		# remove the students we want to swap
		self.gm_lut[lab_week][g0].remove(s0);
		self.gm_lut[lab_week][g1].remove(s1);

		# update conflicts matrix
		for student in self.gm_lut[lab_week][g0]:
			self.conflicts[min(s0, student)][max(s0, student)] -= 1;
			self.conflicts[min(s1, student)][max(s1, student)] += 1;

		for student in self.gm_lut[lab_week][g1]:
			self.conflicts[min(s0, student)][max(s0, student)] += 1;
			self.conflicts[min(s1, student)][max(s1, student)] -= 1;

		# add the students to thier new group
		self.gm_lut[lab_week][g0].append(s1);
		self.gm_lut[lab_week][g1].append(s0);


	def __build_conflict_matrix(self):
		''' creates the matrix of conflicts for the given solution '''

		# initialize to zeros
		self.conflicts = numpy.zeros([self.num_students, self.num_students]);

		# iterate over lab week and tally the number of times the students work together
		w = 0;
		for lab in self.solution:

			# for each group
			group_offset = 0;
			for gs in self.group_size[w]:

				# for each group member
				for i in combinations(range(gs), 2):

					# increment counter
					s0 = lab[group_offset+i[0]];
					s1 = lab[group_offset+i[1]];

					self.conflicts[min(s0,s1), max(s0,s1)] += 1;

				group_offset += gs;

			w += 1;
				

	def __max_conflict(self, conflicts):
		''' returns the student pair with the maximum conflicts/overlaps '''

		# find pair with the max conflicts/overlap
		max_con_flat_index = numpy.argmax(conflicts);
		# get the col/row indices
		return numpy.unravel_index(max_con_flat_index, conflicts.shape);


	def __conflict_error(self, conflicts):
		''' returns the number of bad conflicts (greater than 1) '''

		return numpy.sum(conflicts[conflicts>1]) - numpy.sum(conflicts>1);


	def __is_solved(self):
		''' returns true or false depending on if the solution has no conflicts '''

		return (not numpy.any(self.conflicts > 1));


	def __init_taboo(self):
		''' initializes the taboo matrix '''

		self.taboo = numpy.ones([self.num_labs, self.num_students, self.num_students]) * -(self.taboo_limit+1);


	def __is_taboo(self, lab_week, s):
		''' returns true or false whether the swap is taboo '''
		
		# get actual assignment
		assignment = self.solution[lab_week];

		s0 = min(assignment[s[0]], assignment[s[1]]);
		s1 = max(assignment[s[0]], assignment[s[1]]);

		return (self.taboo[lab_week][s0][s1] + self.taboo_limit > self.count);


	def __update_taboo(self, lab_week, s):
		''' update the taboo matrix for the given count '''		

		assignment = self.solution[lab_week];

		s0 = min(assignment[s[0]], assignment[s[1]]);
		s1 = max(assignment[s[0]], assignment[s[1]]);

		self.taboo[lab_week][s0][s1] = self.count;


	def __build_swap_list(self):
		''' determines all possible inter-group swaps '''

		self.pswap = [];
		self.group_ids = [];


		# build combinations list and remove inner group swaps
		w = 0;
		while (w < self.num_labs):
			# generate all possible swaps
			swaps = list(combinations(range(self.num_students), 2));


			# assign group ids for each index
			gids = numpy.zeros(self.num_students, 'int');
			gid = 0;
			gind = 0;
			for gs in self.group_size[w]:
				for ind in range(gs):
					gids[gind + ind] = gid;
				gid += 1;
				gind += gs;

			# iterate over possible swaps and remove any that are swaps in the same group
			c = len(swaps)-1;
			while (c >= 0):
				s = swaps[c];

				# if the belong to the same group delete it
				if (gids[s[0]] == gids[s[1]]):
					del swaps[c]

				c -= 1;

			self.group_ids.append(gids);
			self.pswap.append(swaps);
			w += 1;			

		# create random swap set
		# this is a set of (w, s) tuples
		self.rswap = [];
		w = 0;
		while (w < self.num_labs):
			for s in self.pswap[w]:
				self.rswap.append( (w, copy.deepcopy(s)) );	
			w += 1;


	def __swap(self, lab_week, s):
		''' swap the given students '''
		# update gm_lut
		self.__update_gm_lut_and_conflicts(lab_week, s);
		
		t = self.solution[lab_week][s[0]];
		self.solution[lab_week][s[0]] = self.solution[lab_week][s[1]];
		self.solution[lab_week][s[1]] = t;


	def __swap_random(self):
		''' swap two students in some week of the solution '''
		
		random.shuffle(self.rswap);
		for ws in self.rswap:
			if (not self.__is_taboo(ws[0], ws[1])):
				# swap students
				self.__swap(ws[0], ws[1]);
				self.error = self.__conflict_error(self.conflicts);

				# add to taboo list
				self.__update_taboo(ws[0], ws[1]);

				return;

		# if every swap is taboo, just do a ranom one
		# probably should lower taboo limit
		ws = self.rswap[0];
		self.__swap(ws[0], ws[1]);
		self.error = self.__conflict_error(self.conflicts);

		# update taboo
		self.__update_taboo(ws[0], ws[1]);

		print 'no possible swap, all are taboo'
		# halve the taboo limit (it is too large)
		self.taboo_limit /= 2;

		

	def __test_swap(self, lab_week, s):
		''' determines new conflict error if the given swap is taken (sol is not actually changed) '''

		# determine current groups
		# subtract from each student in current groups
		# add to new groups
		
		# get the current group assignment and the actual student ids
		s0 = self.solution[lab_week][s[0]];
		s1 = self.solution[lab_week][s[1]];

		# get the group index ids
		g0 = self.group_ids[lab_week][s[0]];
		g1 = self.group_ids[lab_week][s[1]];

		test_error = self.error;
	
		for g0_student in self.gm_lut[lab_week][g0]:

			# decrease test error if needed
			if (s0 != g0_student):
				
				if (self.conflicts[min(s0, g0_student)][max(s0, g0_student)] > 1):
					test_error -= 1;
				# increase test error if needed
				if (self.conflicts[min(s1, g0_student)][max(s1, g0_student)] >= 1):
					test_error += 1;

		for g1_student in self.gm_lut[lab_week][g1]:

			if (s1 != g1_student):

				# decrease test error if needed
				if (self.conflicts[min(s1, g1_student)][max(s1, g1_student)] > 1):
					test_error -= 1;
				# increase test error if needed
				if (self.conflicts[min(s0, g1_student)][max(s0, g1_student)] >= 1):
					test_error += 1;

		return test_error


	def __swap_best(self):
		''' swap the two students that lower the conflict count the most '''
		''' uses the new test swap that determines the new error without 
			actually swapping and rebuilding the conflicts matrix '''		

		cerror = self.error;

		# init best swap
		best_week = -1;
		best_swap = (0,0);
		best_error = self.best_error;

		# iterate over lab weeks
		w = 0;
		while (w < self.num_labs):

			# iterate over possible swaps
			# s a tuple of indices (not students)
			for s in self.pswap[w]:

				# determine error if we took this swap
				terror = self.__test_swap(w, s);

				# if the move is not taboo
				if (not self.__is_taboo(w, s)):

					# check if the new assignment has lower error
					if (terror < cerror):

						best_week = w;
						best_swap = s;
						cerror = terror;
						best_error = min(cerror, best_error);
				else:
					
					# even if this swap is taboo, if it is the best solution we have ever seen keep it
					if (terror < best_error):
					
						best_week = w;
						best_swap = s;
						best_error = terror;
						cerror = terror;
					
			w += 1;


		if (best_week >= 0):
			self.__swap(best_week, best_swap);
			#self.conflicts = self.__build_conflict_matrix(self.solution);
			self.error = self.__conflict_error(self.conflicts);
			
			if (cerror < self.best_error):
				self.best_sol = copy.deepcopy(self.solution);
				self.best_error = self.error;

				print 'Found solution with %d conflicts after %d iterations' % (self.best_error, self.count)

			
		else:
			self.__swap_random();
		


	def __swap_best_use_build_conflicts(self, sol, conflicts, cerror):
		''' ********* DEPRECATED ********** very slow, rebuilds conflicts matrix every time '''
		''' swap the two students that lower the conflict count the most '''

		# init best swap
		best_week = -1;
		best_swap = (0,0);
		best_error = self.best_error;

		ctime = 0.0;
		# iterate over lab weeks
		w = 0;
		while (w < self.num_labs):

			# iterate over possible swaps
			# s a tuple of indices (not students)
			for s in self.pswap[w]:

				self.__swap(sol, w, s);

				#tconflicts = self.__build_conflict_matrix(sol);
				terror = self.__conflict_error(tconflicts);
				

				# if the move is not taboo
				if (not self.__is_taboo(w, s)):

					# check if the new assignment has lower error
					if (terror < cerror):

						best_week = w;
						best_swap = s;
						cerror = terror;
						best_error = min(cerror, best_error);
				else:
					
					# even if this swap is taboo, if it is the best solution we have ever seen keep it
					if (terror < best_error):
					
						best_week = w;
						best_swap = s;
						best_error = terror;
						cerror = terror;
						#print '**********ignoring taboo'
						
						

				# swap the students back
				self.__swap(sol, w, s);
						
					
			w += 1;


		if (best_week >= 0):
			self.__swap(sol, best_week, best_swap);
			#self.conflicts = self.__build_conflict_matrix(sol);
			self.error = self.__conflict_error(self.conflicts);
			
			if (cerror < self.best_error):
				self.best_sol = copy.deepcopy(sol);
				self.best_error = self.error;
			
		else:
			self.__swap_random(sol);
		


	def solve(self):
		''' solves the schoolgirl problem using hill climbing local search method '''

		random.seed(time.time());

		# initialize a random solution
		self.soltion = []
		week = 0;
		while (week < self.num_labs):
			self.solution.append(range(self.num_students));
			random.shuffle(self.solution[week]);
			week += 1;
		
		self.__build_gm_lut();

		# initialize taboo counts		
		self.__init_taboo();

		# initialize conflicts matrix
		self.__build_conflict_matrix();
		self.error = self.__conflict_error(self.conflicts);

		# initialize best solution
		self.best_sol = copy.deepcopy(self.solution);
		self.best_error = self.error;

		# loop count	
		self.count = 0;

		start_time = time.time();
		end_time = start_time + (self.time_limit * 60);
		# loop until the we reach a solution or the iteration limit
		if (self.rswap):
			while (not self.__is_solved() and time.time() < end_time):

				self.__swap_best();
			
				# increment loop counter
				self.count += 1;
			
		if (time.time() >= end_time):
			print 'Unable to find a solution within time limit, using best solution found'
			self.solution = copy.deepcopy(self.best_sol);
			self.error = self.best_error;

		return self.__is_solved();
	

	def solution_to_str(self):
		''' prints out the solution in a readable format '''

		s = '';

		# print to std out
		lab_week = 0;
		for lab in self.best_sol:

			s += '-'*20;
			s += ' week %d ' % (lab_week+1);
			s += '-'*20;
			s += '\n';

			gid = 0;
			group_offset = 0;
			for gs in self.group_size[lab_week]: 
				s += 'group %d:\t' % (gid+1);

				for m in range(gs):
					s += '%d\t' % (lab[group_offset + m]+1);
				s += '\n';

				gid += 1;
				group_offset += gs;

			lab_week += 1;
			s += '\n';

		return s;


# command line interface
if __name__ == "__main__":
	''' prompt the user for the needed inputs '''

	def get_int_input(prompt_str):
		''' prompts the user for integer input handling incorrect entries '''
		while (1):
			i = raw_input(prompt_str);
			if (i.isdigit()):
				return int(i);
			else:
				print 'Input must be an integer.'

	
	# get number of students
	nstudents = get_int_input('Enter the total number of students in the class/section: ');

	# get number of labs/weeks
	nlabs = get_int_input('Enter the total number of labs for the semester: ');

	# get the group size for each week
	group_sizes = [];
	l = 0;
	while (l < nlabs):

		gs = get_int_input('Enter the base group size for lab %d: ' % (l+1)); 

		l += 1;
		group_sizes.append(gs);

	# get the output file name
	outfile = raw_input('Enter the file name you wish the results to be saved (press enter to just print to the screen): ');
		
	# prompt for max time to look for a solution
	time_limit = get_int_input('Enter the maximum amount of time to run (in minutes): ');

	# run the solver
	sgd = schoolgirl(nstudents, nlabs, group_sizes, time_limit);

	t1 = time.time();
	isSolved = sgd.solve();
	t2 = time.time();

	
	pstr = '';
	pstr += 'Lab assignments for a section with %d students, %d lab weeks and base group sizes %s.\n' % (sgd.num_students, sgd.num_labs, str(sgd.base_group_sizes));
	pstr += 'Finished after %d minutes and %d seconds (%d iterations).\n' % (int(t2-t1)/60, int(t2-t1) % 60, sgd.count);
	if (isSolved):
		pstr += 'Complete assignment found with no conflicts.\n';
	else:
		pstr += 'Reached time limit after %d minutes. The best solution found has %d conflicts.\n' % (sgd.time_limit, sgd.best_error);
	pstr += '\n\n';
	pstr += 'Group Assignments by Week:\n';
	pstr += sgd.solution_to_str();


	# if output file was specified, write to it
	if (outfile):

		# open file
		fid = open(outfile, 'w');
		fid.write(pstr);
		fid.close();
		
	else:
		print pstr;


