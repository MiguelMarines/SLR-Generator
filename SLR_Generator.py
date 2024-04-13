# =================================================================================================================== #
#                                                     PROJECT: SLR                                                    #
# =================================================================================================================== #
# Project: SLR                                                                                                        #
# Developer: Miguel Marines                                                                                           #
# =================================================================================================================== #


# Library ------------------------------------------------------------------------------------------------------------
import copy


# =================================================================================================================== #
#                                                 	ADJUST GRAMMAR                                                    #
# =================================================================================================================== #
def adjust_grammar(grammar_final, NonTerminal, start_symbol):

	new_grammar = []

	# Symbol ' to represent new start symbol. -----------------------------------------------------------------------
	new_char = start_symbol + "'"
	while(new_char in NonTerminal):
		new_char += "'"

	# Add productions to bring start symbol to right hand side (RHS). -----------------------------------------------
	new_grammar.append([new_char, ['.', start_symbol]])

	# Divide each prodction on Left Hand Side and Right Hand Side, with the help of the divider "->". ---------------
	# New grammar format => [LHS,[.RHS]]
	for prodction in grammar_final:
		s = prodction.split("->")
		lhs = s[0].strip()
		rhs = s[1].strip()
	
		# Divide productions at '|'. --------------------------------------------------------------------------------
		multirhs = rhs.split('|')
		for rhs1 in multirhs:
			rhs1 = rhs1.strip().split()
			
			# ADD dot pointer at start of RHS. ----------------------------------------------------------------------
			rhs1.insert(0, '.')
			new_grammar.append([lhs, rhs1])

	return new_grammar


# =================================================================================================================== #
#	                                                  CLOSURE                                                    	  #
# =================================================================================================================== #
def closure(input_state, dot_symbol):

	global start_symbol, separated_prodction_list, states_dictionary

	closure_list = []

	# If the function is called for the 1st time (for I0), then LHS is received in "dot_symbol". --------------------
	# Add all productions starting with LHS symbol to "closure_list". -----------------------------------------------
	# For states higher than I0, initial state is set as the received input_state. ----------------------------------
	if dot_symbol == start_symbol:
		for prodction in separated_prodction_list:
			if prodction[0] == dot_symbol:
				closure_list.append(prodction)
	else:
		closure_list = input_state

	# Iteration until the new states are added to the "closure_list". ------------------------------------------------
	len_prev = -1

	while len_prev != len(closure_list):
		
		len_prev = len(closure_list)
		temp_closure_list = []

		# Eliminate concurrent modification error. -------------------------------------------------------------------
		for prodction in closure_list:
			dot_index = prodction[1].index('.')
			if prodction[1][-1] != '.':
				dot_point_location = prodction[1][dot_index + 1]
				for in_production in separated_prodction_list:
					if dot_point_location == in_production[0] and in_production not in temp_closure_list:
						temp_closure_list.append(in_production)
		
		# Add new closures to "closure_list. -------------------------------------------------------------------------
		for prodction in temp_closure_list:
			if prodction not in closure_list:
				closure_list.append(prodction)

	return closure_list


# =================================================================================================================== #
#	                                                COMPUTE GOTO                                                   	  #
# =================================================================================================================== #
def compute_GOTO(state):

	global states_dictionary, states_count
	computed_states = []

	# Find symbols on which to call function GOTO -------------------------------------------------------------------
	for production in states_dictionary[state]:
		if production[1][-1] != '.':
			dot_index = production[1].index('.')
			dot_point_location = production[1][dot_index + 1]
			if dot_point_location not in computed_states:
				computed_states.append(dot_point_location)

	# Call function GOTO on all symbols pointed by dot iteratively --------------------------------------------------
	if len(computed_states) != 0:
		for symbol in computed_states:
			GOTO(state, symbol)

	return


# =================================================================================================================== #
#	                                               		GOTO                                                   	  	  #
# =================================================================================================================== #
def GOTO(state, next_dot):

	global states_dictionary, states_count, states_goto
	
	# Computation of new states. ------------------------------------------------------------------------------------
	new_state = []
	for production in states_dictionary[state]:
		dot_index = production[1].index('.')
		if production[1][-1] != '.':
			if production[1][dot_index + 1] == next_dot:
				shifted_production = copy.deepcopy(production)
				shifted_production[1][dot_index] = shifted_production[1][dot_index + 1]
				shifted_production[1][dot_index + 1] = '.'
				new_state.append(shifted_production)

	# Store new productions temporarily to prevent concurrent modification error. ------------------------------------
	add_closure_productions = []
	for production in new_state:
		dot_index = production[1].index('.')
		if production[1][-1] != '.':
			closureRes = closure(new_state, production[1][dot_index + 1])
			for production in closureRes:
				if production not in add_closure_productions and production not in new_state:
					add_closure_productions.append(production)
	
	# Add closure result to "new_State. ------------------------------------------------------------------------------
	for prodction in add_closure_productions:
		new_state.append(prodction)

	# Find if the new state is already in Dictionary. ----------------------------------------------------------------
	state_exists = -1
	for state_num in states_dictionary:
		if states_dictionary[state_num] == new_state:
			state_exists = state_num
			break

	# If the new_state is not in the dictionary, then create a new state. --------------------------------------------
	# If the a state repetition is found, then assign previous state number. -----------------------------------------
	if state_exists == -1:
		states_count += 1
		states_dictionary[states_count] = new_state
		states_goto[(state, next_dot)] = states_count
	else:
		states_goto[(state, next_dot)] = state_exists

	return


# =================================================================================================================== #
#	                                               	COMPUTE STATES                                                    #
# =================================================================================================================== #
def compute_states(states_dictionary):
	prev_len = -1
	called_GOTO_on = []

	# Compute and add new states to the states sictionary. ---------------------------------------------------------
	while (len(states_dictionary) != prev_len):
		prev_len = len(states_dictionary)
		keys = list(states_dictionary.keys())

		# Call thte function compute_GOTO on all states in the dictionary. -----------------------------------------
		for key in keys:
			if key not in called_GOTO_on:
				called_GOTO_on.append(key)
				compute_GOTO(key)
	return


# =================================================================================================================== #
#	                                               			FIRSTS                                                    #
# =================================================================================================================== #
def first(production):
	global grammar_final, NonTerminal, Terminal, dictionary
	
	# Condition for recursionrecursion (terminal or epsilon). -------------------------------------------------------
	if len(production) != 0 and (production is not None):
		if production[0] in Terminal:
			return production[0]
		elif production[0] == '#':
			return '#'

	# Condition for nonterminals. -----------------------------------------------------------------------------------
	if len(production) != 0:
		if production[0] in list(dictionary.keys()):
			firsts = []
			rhs_productions = dictionary[production[0]]
			for itr in rhs_productions:
				indiv_first = first(itr)
				if type(indiv_first) is list:
					for i in indiv_first:
						firsts.append(i)
				else:
					firsts.append(indiv_first)

			# There is no epsilon in result received return firsts. -------------------------------------------------
			if '#' not in firsts:
				return firsts
			else:
			# There is epsilon in result received return firsts. ----------------------------------------------------
				newList = []
				firsts.remove('#')
				if len(production) > 1:
					ansNew = first(production[1:])
					if ansNew != None:
						if type(ansNew) is list:
							newList = firsts + ansNew
						else:
							newList = firsts + [ansNew]
					else:
						newList = firsts
					return newList
				
				# If eplison still persists keep it in result of first. ---------------------------------------------
				firsts.append('#')

	return firsts


# =================================================================================================================== #
#	                                               		  FOLOW                                                    	  #
# =================================================================================================================== #
def follow(nonterminal):

	global start_symbol, grammar_final, NonTerminal, Terminal, dictionary
	
	# Start symbol --------------------------------------------------------------------------------------------------
	folows = set()
	if nonterminal == start_symbol:
		folows.add('$')

	# Compute follows -----------------------------------------------------------------------------------------------
	for cur_nonterminal in dictionary:
		rhs = dictionary[cur_nonterminal]
		for sub_production in rhs:
			if nonterminal in sub_production:
				while nonterminal in sub_production:
					index_nonterminal = sub_production.index(nonterminal)
					sub_production = sub_production[index_nonterminal + 1:]
					if len(sub_production) != 0:
						firsts = first(sub_production)
						# If epsilon is in thte result --------------------------------------------------------------
						if '#' in firsts:
							newList = []
							firsts.remove('#')
							ansNew = follow(cur_nonterminal)
							if ansNew != None:
								if type(ansNew) is list:
									newList = firsts + ansNew
								else:
									newList = firsts + [ansNew]
							else:
								newList = firsts
							firsts = newList
					else:
						if nonterminal != cur_nonterminal:
							firsts = follow(cur_nonterminal)

					# Add follows to the result list ----------------------------------------------------------------
					if firsts is not None:
						if type(firsts) is list:
							for i in firsts:
								folows.add(i)
						else:
							folows.add(firsts)
	return list(folows)


# =================================================================================================================== #
#		                                               CREATE TABLE                                                   #
# =================================================================================================================== #
def create_parse_table(states_dictionary, states_goto, terminlas, nonterminals):
	
	global separated_prodction_list, dictionary

	# Create rows and columns headers -------------------------------------------------------------------------------
	rows = list(states_dictionary.keys())
	columns = terminlas + ['$'] + nonterminals

	# Create table --------------------------------------------------------------------------------------------------
	Table = []
	temp_row = []

	for y in range(len(columns)):
		temp_row.append('')
	
	for x in range(len(rows)):
		Table.append(copy.deepcopy(temp_row))

	# Shift and GOTO entries in the table. --------------------------------------------------------------------------
	for entry in states_goto:
		state = entry[0]
		symbol = entry[1]

		a = rows.index(state)
		b = columns.index(symbol)

		if symbol in nonterminals:
			Table[a][b] = Table[a][b]\
				+ f"{states_goto[entry]} "

		elif symbol in terminlas:
			Table[a][b] = Table[a][b]\
				+ f"S{states_goto[entry]} "

	# Reduces -------------------------------------------------------------------------------------------------------
	numbered_dictionary = {}
	key_count = 0
	for prodction in separated_prodction_list:
		temp_prodction = copy.deepcopy(prodction)
		temp_prodction[1].remove('.')
		numbered_dictionary[key_count] = temp_prodction
		key_count += 1

	# Compute reduces. ----------------------------------------------------------------------------------------------
	addedR = f"{separated_prodction_list[0][0]} -> " f"{separated_prodction_list[0][1][1]}"
	grammar_final.insert(0, addedR)
	for prodction in grammar_final:
		k = prodction.split("->")

		k[0] = k[0].strip()
		k[1] = k[1].strip()
		
		rhs = k[1]
		
		multirhs = rhs.split('|')
		
		# Remove spaces ---------------------------------------------------------------------------------------------
		for i in range(len(multirhs)):
			multirhs[i] = multirhs[i].strip()
			multirhs[i] = multirhs[i].split()
		dictionary[k[0]] = multirhs

	# find 'handle' items and calculate follow.
	for state_n in states_dictionary:
		for prodction in states_dictionary[state_n]:
			if prodction[1][-1] == '.':
				temp = copy.deepcopy(prodction)
				temp[1].remove('.')
				for key in numbered_dictionary:
					if numbered_dictionary[key] == temp:
						follow_result = follow(prodction[0])
						for col in follow_result:
							index = columns.index(col)
							if key == 0:
								Table[state_n][index] = "Accept"
							else:
								Table[state_n][index] = Table[state_n][index] + f"R{key} "

	# Print Table ---------------------------------------------------------------------------------------------------
	print("\nSTATE                        ACTION                                   GOTO\n")
	
	frmt1 = "{:>10}" * len(columns)
	print(" ", frmt1.format(*columns), "\n")
	j = 0
	for y in Table:
		frmt2 = "{:>10}" * len(y)
		print(f"{{:>3}} {frmt2.format(*y)}"
			.format('I'+str(j)))
		j += 1
	
	print()


# =================================================================================================================== #
#		                                               HTML FORMAT                                                    #
# =================================================================================================================== #
def build_html_row(columns, isHeader = False):
	result = "<tr>"

	if isHeader:
		rowStart = "<th style=\"border: 1px solid black\">"
		rowEnd = "</th>"

	else:
		rowStart = "<td style=\"border: 1px solid black\">"
		rowEnd = "</td>"
	
	for _, value in enumerate(columns) :
		result += f"\n{rowStart} {value} {rowEnd}\n"
	
	result += "</tr>\n"

	return result


# =================================================================================================================== #
#			                                           TABLE HTML                                                  	  #
# =================================================================================================================== #
def  generate_table(header_table):
    
	tabla = {}

	for state in states_dictionary:
		tabla[state] = {}

	html_output = ''' 
		<!DOCTYPE html>
		<html>
		<body>
		<table style="border: 1px solid black"> '''
	
	
    # html_output += BuildHtmlRow(header_table_1, True)
	header = []
	header.append("State")
	
	
	for h in header_table:
		header.append(h)
	
	html_output += build_html_row(header, True)

	for key, values in tabla.items():
		elements = []
		elements.append(key)
		for index, terminal in enumerate(header):
			if index != 0:
				element = ''
		html_output +=  build_html_row(elements)

    
	html_output += '''
		</table>
		</body>
		</html> '''
    
	file = open('output.html', "w")
	file.write(html_output)
	file.close()

	return tabla






# =================================================================================================================== #
#                                                     	MAIN                                                   		  #
# =================================================================================================================== #

# Lists to store user's inputs. -------------------------------------------------------------------------------------
grammar = []
strings = []

# Lists to divide user's inputs on left and right hand side (LHS and RHS). ------------------------------------------
left = []
right = []

# Number of inpts.  -------------------------------------------------------------------------------------------------
number_productions_aux, number_strings_aux = input().split(" ")

number_productions = int(number_productions_aux)
number_strings = int(number_strings_aux)

# Store productions in the corresponding list. -----------------------------------------------------------------------
for i in range(0, number_productions):
    _production_aux = input()
    _production = _production_aux.replace("' '", "#" )
    grammar.append(_production)

# Store strings in the corresponding list. --------------------------------------------------------------------------
for i in range(0, number_strings):
    _string = input()
    strings.append(_string)

# LHS and RHS division ----------------------------------------------------------------------------------------------
# Dive each production of the grammar on left and right hand side (LHS and RHS)
# with the help of the indicator "->".
# Auxiliary list to evaluate each production from the gramar. -------------------------------------------------------
aux_list = []
for production in grammar:
    aux_list = production.split()
    flag_separator = False
    for word in aux_list:
        if word == '->':
            flag_separator = True
        else:
            if flag_separator:
                if not word in left:
                    left.append(word)
            else :
                if not word in right:
                    right.append(word)

# Eliminate epsilon (#). --------------------------------------------------------------------------------------------
if "#" in right:
    right.remove("#")
if "#" in left:
    left.remove("#")

# Lists to store Terminals and Non Terminals. ------------------------------------------------------------------------
Terminal = []
NonTerminal = []

# Determine Terminals. -----------------------------------------------------------------------------------------------
for word in left:
    if not word in right:
        Terminal.append(word)

# Determine Non Terminals. -------------------------------------------------------------------------------------------
for word in right:
    if not word in Terminal:
        NonTerminal.append(word)



# Prepare Grammar productions for SLR --------------------------------------------------------------------------------
grammar_1 = []
grammar_2 = copy.deepcopy(grammar)

for i in range(len(grammar) - 1):
    aux_list_1 = grammar[i].split()
    aux_list_2 = grammar[i+1].split()
    if (aux_list_1[0] == aux_list_2[0]):
        temp_array = grammar_2[i+1].split()    
        del temp_array[0]
        del temp_array[0]
        temp_str = " ".join(temp_array)
        aux_prodction = grammar[i] + " | " + temp_str
        grammar_1.append(aux_prodction)
    print()

grammar_final = []

for i in range(len(NonTerminal)):
    flag = True
    for j in grammar_1:
        temp_array_1 = j.split()
        if( NonTerminal[i] == temp_array_1[0]) and (flag == True):
            grammar_final.append(j)
            flag = False
    for k in grammar:
        temp_array_2 = k.split()
        if( NonTerminal[i] == temp_array_2[0]) and (flag == True):
            grammar_final.append(k)
            flag = False


# Adjust productions for analysis ------------------------------------------------------------------------------------
start_symbol = NonTerminal[0]
separated_prodction_list = adjust_grammar(grammar_final, NonTerminal, start_symbol)


# Closure ------------------------------------------------------------------------------------------------------------
start_symbol = separated_prodction_list[0][0]
I0 = closure(0, start_symbol)


# Dictionaries to store states and gotos -----------------------------------------------------------------------------
states_dictionary = {}
states_goto = {}


# Aadd first state to states_dictionary and declare state count ------------------------------------------------------
states_dictionary[0] = I0
states_count = 0


# Compute states with GOTO -------------------------------------------------------------------------------------------
compute_states(states_dictionary)

dictionary = {}

# Create parse table -------------------------------------------------------------------------------------------------
create_parse_table(states_dictionary, states_goto, Terminal, NonTerminal)


# Create html parse table --------------------------------------------------------------------------------------------
header_table = copy.deepcopy(Terminal)
header_table.append("$")
header_table_1 = ["STATE", "ACTION", "GOTO"]

for i in NonTerminal:
	header_table.append(i)

tabla = generate_table(header_table)
