//Vasillen Chizhov & Denis Lubomirov, 30.01.2015
//Creates a NFSA from a regular expression, then writes down the output in an extrenal file ("output.txt")
//to be visualized with DOT

#include <vector>   //for storing delta function's state + symbol
#include <map>      //for mirroring of the structure - tree copying
#include <string>   //...
#include <utility>  //for std::pair
#include <iostream> //...
#include <assert.h> //just in case
#include <stack>    //for balanced brackets
#include <fstream>  //for file writing
#include <set>      //for DFA
#include <sstream>  //for int to string

//just in case you want a wchar_t or something more complex
//it must support the char operations though
typedef char SymbolClass;

//A little info:
//1)Each branch represents a state in a automaton
//2)Each branch contains the information about the delta function from itself and to itself

//abstract class Branch from the user
class Branch
{
	//I know it's not nice - but my design requires it
	//The user is not supposed to touch class Branch anyways
	friend class Tree;
	friend class DFA;
private:
	std::vector<std::pair<Branch*, SymbolClass>> children;
	std::vector<std::pair<Branch*, SymbolClass>> parents;
	std::vector<SymbolClass> loops; //loops: q, such that delta(q,x) = q, loop symbol: x
	static int counter;
	int num;

private:
	Branch(int number)
		:num(number)
	{
	}
	Branch(const Branch& another)
	{}
	~Branch()
	{}

private:
	void add(Branch& another, const SymbolClass symbol)
	{
		//if we're trying to make a loop
		if (this == &another)
		{
			//check for duplication
			for (auto loopIter = loops.begin(); loopIter != loops.end(); loopIter++)
			{
				assert(*loopIter != symbol);
			}
			//update delta function
			loops.push_back(symbol);
		}
		else
		{
			//check for duplication
			for (auto childIter = children.begin(); childIter != children.end(); childIter++)
			{
				assert((*childIter).first != &another || (*childIter).second != symbol);
			}

			for (auto parentIter = another.parents.begin(); parentIter != another.parents.end(); parentIter++)
			{
				assert((*parentIter).first != &another || (*parentIter).second != symbol);
			}

			//update delta function
			children.push_back(std::make_pair(&another, symbol));
			another.parents.push_back(std::make_pair(this, symbol));
		}
	}

	void copyParentsLinks(const Branch& another)
	{
		assert(this != &another);

		bool copy = true;
		//copy the parents' links
		for (auto parentIter = another.parents.begin(); parentIter != another.parents.end(); parentIter++)
		{
			//if we're trying to make a loop - it shouldn't happen
			assert(this != (*parentIter).first);

			for (auto iter2 = parents.begin(); iter2 != parents.end(); iter2++)
			{
				//if the the current parent link of another is already in this parents' links
				if ((*iter2).first == (*parentIter).first && (*iter2).second == (*parentIter).second)
				{
					copy = false;
				}
			}

			/*for (auto childIter = (*parentIter).first->children.begin(); childIter != (*parentIter).first->children.end(); childIter++)
			{
			//if this branch is present as a link in the current parent of another's children vector - shouldn't happen
			assert((*childIter).first != this);
			}
			*/

			if (copy)
			{
				//update the parents' list
				parents.push_back(*parentIter);
				//update the children's list
				(*parentIter).first->children.push_back(std::make_pair(this, (*parentIter).second));
			}
			else
			{
				copy = true;
			}
		}

	}

	void copyLoopsLinks(const Branch& another)
	{
		assert(this != &another);

		bool copy = true;
		//copy the loops
		for (auto iter = another.loops.begin(); iter != another.loops.end(); iter++)
		{
			for (auto iter2 = loops.begin(); iter2 != loops.end(); iter2++)
			{
				//if this link already exists in this branch's children do not copy it
				if (*iter2 == *iter)
				{
					copy = false;
					break;
				}
			}

			if (copy)
			{
				loops.push_back(*iter);
			}
			else
			{
				copy = true;
			}
		}
		return;
	}

	void copyChildrenLinks(const Branch& another)
	{
		assert(this != &another);

		bool copy = true;
		//copy the children
		for (auto iter = another.children.begin(); iter != another.children.end(); iter++)
		{
			//if we're trying to make a loop
			if (this == (*iter).first)
			{
				for (auto iter2 = loops.begin(); iter2 != loops.end(); iter2++)
				{
					if (*iter2 == (*iter).second)
					{
						copy = false;
						break;
					}
				}
				if (copy)
				{
					loops.push_back((*iter).second);
				}
				else
				{
					copy = true;
				}
			}
			else
			{
				for (auto iter2 = children.begin(); iter2 != children.end(); iter2++)
				{
					//if this link already exists in this branch's children do not copy it
					if ((*iter2).first == (*iter).first && (*iter2).second == (*iter).second)
					{
						copy = false;
						break;
					}
				}

				if (copy)
				{
					//update the children
					children.push_back(*iter);
					for (auto iter3 = (*iter).first->parents.begin(); iter3 != (*iter).first->parents.end(); iter3++)
					{
						//if the child link doesn't exist but the parent one does
						assert((*iter3).first != this || (*iter3).second != (*iter).second);
					}
					//update the parent
					(*iter).first->parents.push_back(std::make_pair(this, (*iter).second));
				}
				else
				{
					copy = true;
				}
			}
		}
		return;
	}

	void removeLinks()
	{
		//update the parents
		for (auto iter = parents.begin(); iter != parents.end(); iter++)
		{
			for (auto iter2 = (*iter).first->children.begin(); iter2 != (*iter).first->children.end(); iter2++)
			{
				if ((*iter2).first == this)
					iter2 = (*iter).first->children.erase(iter2);
			}
		}

		//update the children
		for (auto iter4 = children.begin(); iter4 != children.end(); iter4++)
		{
			for (auto iter3 = (*iter4).first->parents.begin(); iter3 != (*iter4).first->parents.end(); iter3++)
			{
				if ((*iter3).first == this)
					iter3 = (*iter4).first->parents.erase(iter3);
			}
		}
	}
};


//A tree is basically a tree of branches
//it is our nondeterministic finite state automaton
//it keeps track of the branches associated with it with the vector branches
class Tree
{
	friend class DFA;
private:

	std::vector<Branch*> branches;

	//start state
	Branch* root;
	//final state
	Branch* convergence;

	bool epsilon;

	static int counter;

private:

	//returns std::make_pair(clonedRoot, clonedConvergence)
	//where clonedRoot is the clone of the root of another and clonedConvergence is the clone of the convergence of another
	std::pair<Branch*, Branch*> copyTree(const Tree& another)
	{
		//used to mirror the delta function
		std::map<Branch*, Branch*> links;

		Branch* clonedBranch = nullptr;
		//clone the states
		for (auto branchIter = another.branches.begin(); branchIter != another.branches.end(); branchIter++)
		{
			//recreate the same number of branches (without any info)
			counter++;
			clonedBranch = new Branch(counter);
			branches.push_back(clonedBranch);
			//copy the loops even here btw
			clonedBranch->loops = (*branchIter)->loops;
			//link the original branch to the copied one for future reference
			links.insert(std::make_pair((*branchIter), clonedBranch));
		}

		//clone delta function
		for (auto branchIter = another.branches.begin(); branchIter != another.branches.end(); branchIter++)
		{
			//update children
			for (auto childIter = (*branchIter)->children.begin(); childIter != (*branchIter)->children.end(); childIter++)
			{
				//clonedBranch->children.push_back( std::make_pair(clonedChild, symbol) )
				links.at((*branchIter))->children.push_back(std::make_pair(links.at((*childIter).first), (*childIter).second));
			}

			//update parents
			for (auto parentIter = (*branchIter)->parents.begin(); parentIter != (*branchIter)->parents.end(); parentIter++)
			{
				//clonedBranch->children.push_back( std::make_pair(clonedChild, symbol) )
				links.at((*branchIter))->parents.push_back(std::make_pair(links.at((*parentIter).first), (*parentIter).second));
			}

			//loops were copied at state cloning
		}
		return std::make_pair(links.at(another.root), links.at(another.convergence));
	}

	void removeBranch(Branch* branch)
	{
		branch->removeLinks();
		for (auto iter = branches.begin(); iter != branches.end(); iter++)
		{

			if (branch == *iter)
			{
				branches.erase(iter);
				break;
			}
		}
		delete branch;
	}

	Tree()
		:epsilon(true)
	{
		root = new Branch(1);
		branches.push_back(root);
		convergence = new Branch(2);
		counter = 2;
		branches.push_back(convergence);
	}


public:

	Tree(const SymbolClass symbol)
		:epsilon(false)
	{
		root = new Branch(1);
		branches.push_back(root);
		convergence = new Branch(2);
		counter = 2;
		branches.push_back(convergence);
		root->add(*convergence, symbol);
	}

	Tree(const Tree& another)
		:epsilon(another.epsilon)
	{
		//root convergence pair
		std::pair<Branch*, Branch*> rcPair = copyTree(another);
		root = rcPair.first;
		convergence = rcPair.second;
	}

	~Tree()
	{
		for (auto branchIter = branches.begin(); branchIter != branches.end(); branchIter++)
		{
			delete *branchIter;
		}
	}

	//care the word should be reversed
	bool recognize(Branch& branch, std::vector<SymbolClass> word)
	{
		//end of word bottom
		if (word.empty())
		{
			if (convergence == &branch)
			{
				return true;
			}
			else
			{
				return false;
			}
		}

		for (auto iter = branch.children.begin(); iter != branch.children.end(); iter++)
		{
			if ((*iter).second == word.back())
			{
				std::vector<SymbolClass> wordT = word;
				wordT.pop_back();
				if (recognize(*(*iter).first, wordT))
					return true;
			}
		}

		for (auto iter = branch.loops.begin(); iter != branch.loops.end(); iter++)
		{
			if (*iter == word.back())
			{
				std::vector<SymbolClass> wordT = word;
				wordT.pop_back();
				if (recognize(branch, wordT))
					return true;
			}
		}
		//end of children bottom
		return false;
	}

public:

	//concatenation
	Tree* operator && (const Tree& another)
	{
		//the root of the new Tree becomes the root of the left hand side Tree
		//the majestic new tree is created directly from our lhs Tree
		Tree* temp = new Tree(*this);//s = s1

		//store the lhs convergence point so we can remap it later
		Branch* storeConvergence = temp->convergence;
		//Copy the rhs tree into the new tree and
		//store the root and convergence cloned branches of the rhs tree
		std::pair<Branch*, Branch*> rcPair = temp->copyTree(another);
		//overwrite the convergence point with the final state of the rhs tree
		temp->convergence = rcPair.second;//F = F2

		if (this->epsilon)
		{
			//delta(s1,a) = delta(s2,a)
			temp->root->copyChildrenLinks(*rcPair.first);
			for (auto iter = rcPair.first->loops.begin(); iter != rcPair.first->loops.end(); iter++)
			{
				temp->root->add(*rcPair.first, *iter);
			}
		}
		
		

		//remap the lhs convergence to the rhs root
		//s2 = s2+F1
		rcPair.first->copyParentsLinks(*storeConvergence);
		rcPair.first->copyChildrenLinks(*storeConvergence);
		rcPair.first->copyLoopsLinks(*storeConvergence);

		//remove the convergence branch of the lhs tree
		temp->removeBranch(storeConvergence);

		
		if (another.epsilon)
		{
			//F=F1VF2
			temp->convergence->copyParentsLinks(*rcPair.first);

		}

		temp->epsilon = this->epsilon&&another.epsilon;

		return temp;
	}

	//union
	Tree* operator || (const Tree& another)
	{
		Tree* temp = new Tree();

		temp->epsilon = this->epsilon || another.epsilon;

		std::pair<Branch*, Branch*> lhs = temp->copyTree(*this);
		std::pair<Branch*, Branch*> rhs = temp->copyTree(another);

		//link so that: delta(s,x) = delta(s1,x)
		temp->root->copyChildrenLinks(*(lhs.first));
		temp->root->copyParentsLinks(*(lhs.first));
		//link so that: delta(s,x) = delta(s2,x)
		temp->root->copyChildrenLinks(*(rhs.first));
		temp->root->copyParentsLinks(*(rhs.first));

		//for s1 and s2: s->s1, s->s2

		//if there are loops on the lhs root, link the root of the new tree
		//to the root of the lhs tree with the symbols from these loops
		if (!lhs.first->loops.empty())
		{
			for (auto iter = lhs.first->loops.begin(); iter != lhs.first->loops.end(); iter++)
			{
				temp->root->add(*(lhs.first), *iter);
			}
		}
		else
		{
			// else remove s1
			temp->removeBranch(lhs.first);
		}

		//if there are loops on the rhs root, link the root of the new tree
		//to the root of the rhs tree with the symbols from these loops
		if (!rhs.first->loops.empty())
		{
			for (auto iter = rhs.first->loops.begin(); iter != rhs.first->loops.end(); iter++)
			{
				temp->root->add(*(rhs.first), *iter);
			}
		}
		else
		{
			// else remove s2
			temp->removeBranch(rhs.first);
		}


		//for F1 and F2: F1->F, F2->F
		temp->convergence->copyParentsLinks(*lhs.second);
		temp->convergence->copyChildrenLinks(*lhs.second);
		temp->convergence->copyParentsLinks(*rhs.second);
		temp->convergence->copyChildrenLinks(*rhs.second);

		//if there are loops on the lhs convergence, link the the convergence of the lhs tree 
		//with the symbols from these loops to the convergence of the new tree
		if (!lhs.second->loops.empty())
		{
			for (auto iter = lhs.second->loops.begin(); iter != lhs.second->loops.end(); iter++)
			{
				lhs.second->add(*(temp->convergence), *iter);
			}
		}
		else
		{
			// else remove F1
			temp->removeBranch(lhs.second);
		}

		//if there are loops on the rhs convergence, link the the convergence of the rhs tree 
		//with the symbols from these loops to the convergence of the new tree
		if (!rhs.second->loops.empty())
		{
			for (auto iter = rhs.second->loops.begin(); iter != rhs.second->loops.end(); iter++)
			{
				rhs.second->add(*(temp->convergence), *iter);
			}
		}
		else
		{
			// else remove F2
			temp->removeBranch(rhs.second);
		}

		return temp;
	}

	//Kleene star
	Tree* operator + ()
	{
		epsilon = true;
		//delta(F,x) = delta(s,x)
		convergence->copyChildrenLinks(*root);

		//if there is a x such that: delta(s,x) = s => delta(F,x) = s
		if (!root->loops.empty())
		{
			for (auto iter = root->loops.begin(); iter != root->loops.end(); iter++)
			{
				convergence->add(*(root), *iter);
			}
		}

		//root->add(*convergence, ' ');

		return this;
	}

	bool recognize(std::string word)
	{
		std::vector<SymbolClass> revWord;
		for (int k = word.size() - 1; k >= 0; k--)
		{
			revWord.push_back(word[k]);
		}
		return recognize(*root, revWord);
	}

	void printTree(std::ostream& os)
	{
		for (auto iter = branches.begin(); iter != branches.end(); iter++)
		{
			for (auto iter2 = (*iter)->loops.begin(); iter2 != (*iter)->loops.end(); iter2++)
			{
				os << (*iter)->num << " -> " << (*iter)->num << "[label=\"" << (*iter2) << "\"];" << std::endl;
			}
		}

		for (auto iter = branches.begin(); iter != branches.end(); iter++)
		{
			for (auto iter2 = (*iter)->children.begin(); iter2 != (*iter)->children.end(); iter2++)
			{
				os << (*iter)->num << " -> " << (*iter2).first->num << "[label=\"" << (*iter2).second << "\"];" << std::endl;
			}
		}
	}

	void printTreeDOT(std::ostream& os)
	{
		os << "digraph{" << std::endl;
		os << "node[shape = point, color = white, fontcolor = white]; start;" << std::endl;
		os << "node [shape = doublecircle, color=black, fontcolor=black]; " << convergence->num << ";" << std::endl;
		os << "node[shape = circle]; " << root->num << ";" << std::endl;
		os << "start -> " << root->num << ";" << std::endl;
		for (auto iter = branches.begin(); iter != branches.end(); iter++)
		{
			for (auto iter2 = (*iter)->loops.begin(); iter2 != (*iter)->loops.end(); iter2++)
			{
				os << (*iter)->num << " -> " << (*iter)->num << "[label=\"" << (*iter2) << "\"];" << std::endl;
			}
		}

		for (auto iter = branches.begin(); iter != branches.end(); iter++)
		{
			for (auto iter2 = (*iter)->children.begin(); iter2 != (*iter)->children.end(); iter2++)
			{
				os << (*iter)->num << " -> " << (*iter2).first->num << "[label=\"" << (*iter2).second << "\"];" << std::endl;
			}
		}

		os << "}" << std::endl;
	}

};

int Tree::counter = 0;

class Node
{
	friend class DFA;
	friend class MDFA;
private:
	std::set<int> num;
	std::map<SymbolClass, std::set<int>> children;
	bool isFinal;
	static int counter;
	int actualNum;
public:
	Node(std::set<int> num, bool isFinal = false)
		:num(num), isFinal(isFinal)
	{
		counter++;
		actualNum = counter;
	}
};

int Node::counter = 0;



class DFA
{
	friend class MDFA;
private:
	std::map<std::set<int>, Node*> branches;
	Node* root;
	std::set<Node*> finalStates;
	

	//helpers for building
	const Tree* tree;
	std::map < int, Branch* > treeBranches;
private:
	void spawnChildren(std::set<int> sign)
	{
		auto currFound = branches.find(sign);
		assert(currFound != branches.end());
		Node* curr = currFound->second;
		//if it was already built
		if (!curr->children.empty())
			return;

		Branch* temp = nullptr;
		//iterate over the ids of the branches of the tree this node represents
		for (auto iter = sign.begin(); iter != sign.end(); iter++)
		{
			//create a map from the children's links
			//it must  exist!
			auto found = treeBranches.find(*iter);
			assert(found != treeBranches.end());
			temp = found->second;

			//if the final state of the nfa is present in the set -> make this node final
			if (*iter == tree->convergence->num)
			{
				finalStates.insert(curr);
				curr->isFinal = true;
			}

			
			//iterate over the children of the branch in the tree
			for (auto iter2 = temp->children.begin(); iter2 != temp->children.end(); iter2++)
			{
				//if there's no such symbol make it
				if (curr->children.find(iter2->second) == curr->children.end())
				{
					curr->children.insert(std::make_pair(iter2->second, std::set<int>()));
				}
				//add link
				curr->children.find(iter2->second)->second.insert(iter2->first->num);

			}
			//iterate over the loops of the branch in the tree
			for (auto iter2 = temp->loops.begin(); iter2 != temp->loops.end(); iter2++)
			{
				//if there's no such symbol make it
				if (curr->children.find(*iter2) == curr->children.end())
				{
					curr->children.insert(std::make_pair(*iter2, std::set<int>()));
				}
				//add link
				curr->children.find(*iter2)->second.insert(temp->num);
			}

		}

		//after the children are fully referenced - create them
		//iterate over the children of the node of the DFA
		for (auto iter2 = curr->children.begin(); iter2 != curr->children.end(); iter2++)
		{
			//if there's a node that doesn't exist - create it
			if (branches.find(iter2->second) == branches.end())
			{
				branches.insert(std::make_pair(iter2->second, new Node(iter2->second)));
			}
		}

		//iterate over the children of the node of the DFA to go deeper
		for (auto iter2 = curr->children.begin(); iter2 != curr->children.end(); iter2++)
		{
			//then go deeper
			spawnChildren(iter2->second);
		}
		//nothing more to do?
		return;
	}

	//care the word should be reversed
	bool recognize(Node& branch, std::vector<SymbolClass> word)
	{
		//end of word bottom
		if (word.empty())
		{
			return branch.isFinal;
		}

		for (auto iter = branch.children.begin(); iter != branch.children.end(); iter++)
		{
			if ((*iter).first == word.back())
			{
				std::vector<SymbolClass> wordT = word;
				wordT.pop_back();
				if (recognize(*branches.find((*iter).second)->second, wordT))
					return true;
			}
		}

		//end of children bottom
		return false;
	}

public:

	DFA(const Tree& tree)
	{
		//make a root
		this->tree = &tree;
		std::set<int> tempVec;
		tempVec.insert(tree.root->num);
		root = new Node(tempVec);
		//register it
		branches.insert(std::make_pair(tempVec, root));
		if (tree.epsilon == true)
		{
			root->isFinal = true;
			finalStates.insert(root);
		}

		//make a map of the tree's branches, that will be accessible by id
		for (auto iter = tree.branches.begin(); iter != tree.branches.end(); iter++)
		{
			//ids must be unique
			assert(treeBranches.find((*iter)->num)==treeBranches.end());
			
			treeBranches.insert(std::make_pair((*iter)->num, *iter));
		}

		spawnChildren(tempVec);

	}

	~DFA()
	{
		for (auto branchIter = branches.begin(); branchIter != branches.end(); branchIter++)
		{
			delete branchIter->second;
		}
	}


public:

	std::string makeString(std::set<int> num)
	{
		std::string temp = "";
		std::ostringstream convert;
		if (num.size() == 1)
		{
			convert << "{" << *num.begin() << "}";
		}
		else if (num.size() > 1)
		{
			convert << "{" << *num.begin();
		}
		for (auto iter = ++num.begin(); iter != num.end(); iter++)
		{
			convert << ", " << *iter;
		}
		if (num.size() > 1)
		{
			convert << "}";
		}
		temp = convert.str();
		return temp;
	}

	void printDFADOT(std::ostream& os)
	{
		os << "digraph{" << std::endl;
		os << "node[shape = point, color = white, fontcolor = white]; start;" << std::endl;
		for (auto iter = finalStates.begin(); iter != finalStates.end(); iter++)
		{
			os << "node [shape = doublecircle, color=black, fontcolor=black]; " << (*iter)->actualNum << ";" << std::endl;
		}
		if (!root->isFinal)
		{
			os << "node[shape = circle]; " << root->actualNum << ";" << std::endl;
		}
		//so all of the nodes wouldn't look final in DOT we need to
		//set things right
		for (auto iter = branches.begin(); iter != branches.end(); iter++)
		{
			if (!iter->second->isFinal)
			{
				os << "node[shape = circle]; " << (iter->second)->actualNum << ";" << std::endl;
				break;
			}
		}

		os << "start -> " << root->actualNum<< ";" << std::endl;

		for (auto iter = branches.begin(); iter != branches.end(); iter++)
		{
			
			for (auto iter2 = (iter->second)->children.begin(); iter2 != (iter->second)->children.end(); iter2++)
			{
				os << (iter->second)->actualNum << " -> " << branches.find((*iter2).second)->second->actualNum << "[label=\"" << (*iter2).first << "\"];" << std::endl;
			}
		}

		os << "}" << std::endl;
	}

	void printDFA(std::ostream& os)
	{
		for (auto iter = branches.begin(); iter != branches.end(); iter++)
		{
			for (auto iter2 = (iter->second)->children.begin(); iter2 != (iter->second)->children.end(); iter2++)
			{
				os << makeString((iter->second)->num) << " -> " << makeString(iter2->second) << "[label=\"" << (*iter2).first << "\"];" << std::endl;
			}
		}
	}

	bool recognize(std::string word)
	{
		std::vector<SymbolClass> revWord;
		for (int k = word.size() - 1; k >= 0; k--)
		{
			revWord.push_back(word[k]);
		}
		return recognize(*root, revWord);
	}
private:
	DFA(const DFA& another){}
	DFA& operator=(const DFA& another){}

};

template<class T>
bool equalSets(std::set<T> A, std::set<T> B)
{
	if (A.size() != B.size())
		return false;
	for (auto iter = A.begin(); iter != A.end(); iter++)
	{
		if (B.find(*iter) == B.end())
			return false;
	}

	return true;
}

class MDFA
{
private:
	std::map<std::set<int>, Node*> branches;
	Node* root;
	std::set<Node*> finalStates;
	std::set<SymbolClass> alphabet;

private:

	//care the word should be reversed
	bool recognize(Node& branch, std::vector<SymbolClass> word)
	{
		//end of word bottom
		if (word.empty())
		{
			return branch.isFinal;
		}
		for (auto iter = branch.children.begin(); iter != branch.children.end(); iter++)
		{
			if ((*iter).first == word.back())
			{
				std::vector<SymbolClass> wordT = word;
				wordT.pop_back();
				if (recognize(*branches.find((*iter).second)->second, wordT))
					return true;
			}
		}

		//end of children bottom
		return false;
	}

	std::string makeString(std::set<int> num)
	{
		std::string temp = "";
		std::ostringstream convert;
		if (num.size() == 1)
		{
			convert << "{" << *num.begin() << "}";
		}
		else if (num.size() > 1)
		{
			convert << "{" << *num.begin();
		}
		for (auto iter = ++num.begin(); iter != num.end(); iter++)
		{
			convert << ", " << *iter;
		}
		if (num.size() > 1)
		{
			convert << "}";
		}
		temp = convert.str();
		return temp;
	}

public:

	MDFA(const DFA& dfa)
	{
		Node* curr = nullptr;
		//1. Analyze nodes, to find out the used alphabet
		for (auto iter = dfa.branches.begin(); iter != dfa.branches.end(); iter++)
		{
			curr = iter->second;
			//we can find this from the links to the children of the nodes
			for (auto iter2 = curr->children.begin(); iter2 != curr->children.end(); iter2++)
			{
				alphabet.insert(iter2->first);
			}
		}

		//after we have the alphabet
		//2. Split the branches into final and non final sets(and add an error state)
		std::set<int> tempSet;
		tempSet.insert(-1);
		Node* errorState = new Node(tempSet);
		tempSet.clear();
		//set of the sets
		std::set<std::set<Node*>> prevSet;
		std::set<Node*> Q;
		std::set<Node*> F;
		for (auto iter = dfa.branches.begin(); iter != dfa.branches.end(); iter++)
		{
			if (iter->second->isFinal)
			{
				F.insert(iter->second);
			}
			else
			{
				Q.insert(iter->second);
			}
		}
		Q.insert(errorState);
		prevSet.insert(Q);
		prevSet.insert(F);

		//3. Continue splitting the sets till we can't anymore, by testing letters
		
		
		std::set<std::set<Node*>>* backBuffer = &prevSet;
		//the table used for splitting sets:
		// key: (node, symbol)
		// value: (set where the node leads with symbol)
		std::map < std::pair<Node*, SymbolClass>, std::set<Node*> > splittingTable;
		//column accumulator of sets(accumulates the sets on a single column of the splitting table
		std::vector< std::set<Node*> > columnAccumulator;
		//split set map - the new sets
		//key: <ParentSet, signatureOfTheSet>
		//value: the new set
		//if no set gets split into more set at some iteration -> the algorithm ends
		std::map<std::pair<std::set<Node*>,std::vector<std::set<Node*>>>, std::set<Node*>> splitSet;
		//utility
		curr = nullptr;
		Node* leadsTo = nullptr;
		std::map<SymbolClass, std::set<int>>::iterator found;
		bool split = false;
		do
		{
			split = false;
			//for each set - try to split it
			for (auto iter = backBuffer->begin(); iter != backBuffer->end(); iter++)
			{
				//for each node in the set - calculate where each letter leads
				for (auto iter2 = iter->begin(); iter2 != iter->end(); iter2++)
				{
					curr = *iter2;
					//for each symbol in the alphabet
					for (auto iter3 = alphabet.begin(); iter3 != alphabet.end(); iter3++)
					{
						//see where each symbol leads from the current node
						found = curr->children.find(*iter3);
						//if the symbol leads nowhere -> make it as if it leads to errorState
						if (found == curr->children.end())
						{
							leadsTo = errorState;
						}
						else
						{
							leadsTo = dfa.branches.find(found->second)->second;
						}
						//after finding the node it leads to, find where this node is located at (in which set)
						for (auto iter4 = backBuffer->begin(); iter4 != backBuffer->end(); iter4++)
						{
							//if it leads to *iter4 set register this
							if (iter4->find(leadsTo) != iter4->end())
							{
								//update splitting table!
								//the current node with the current symbol
								//leads to set *iter4
								splittingTable.insert(std::make_pair(std::make_pair(curr, *iter3), *iter4));
								//update columnAccumulator - accumulate sets for this column arranged by rows
								columnAccumulator.push_back(*iter4);
							}
						}

					}
					//having a whole column from the splitting table - we could check in which set to send this node
					//if there's no such set yet -> make it
					//search by (current set, column signature)
					if (splitSet.find(std::make_pair(*iter, columnAccumulator)) == splitSet.end())
					{
						splitSet.insert(std::make_pair(std::make_pair(*iter, columnAccumulator), std::set<Node*>()));
					}
					//insert the current node into the new set
					//(we're grouping nodes by sets)
					splitSet.find(std::make_pair(*iter, columnAccumulator))->second.insert(curr);
					columnAccumulator.clear();
				}
			}
			//after the splitSet map has been made and the splittingTable map is ready
			//we should have the new sets + a table to tell us where a set leads to

			//check whether a certain set has split
			if (splitSet.size() != backBuffer->size())
			{
				split = true;
			}

			//if the sets are the same => split == false => we get out of the while
			//else - clear things up for the next iteration
			if (split)
			{
				backBuffer->clear();
				//copy the new sets into backBuffer
				for (auto iter = splitSet.begin(); iter != splitSet.end(); iter++)
				{
					backBuffer->insert(iter->second);
				}
				splitSet.clear();
				splittingTable.clear();
			}
		} while (split);

		//after we have split the sets to minimal sets
		//we need to build the states mirroring these sets
		std::map < std::set<Node*>, Node* > mirror;
		
		Node* actualNode = nullptr;
		std::set<int> expendable;
		bool isFinal = false;
		bool isRoot = false;
		bool isErrorState = false;
		//for each set create a node
		//and if the set contains the root node, make the new node root
		//if the set contains final nodes, make the node final
		//check whether the node is the error state -> in which case mark the set as errorState set
		std::set<Node*> errorStateSet;
		for (auto iter = backBuffer->begin(); iter != backBuffer->end(); iter++)
		{
			
			isFinal = false;
			isRoot  = false;
			isErrorState = false;
			//for each node in the set accumulate the id
			//and check whether it's root or final
			for (auto iter2 = iter->begin(); iter2 != iter->end(); iter2++)
			{
				//create number
				expendable.insert((*iter2)->actualNum);
				//is final?
				if ((*iter2)->isFinal)
				{
					isFinal = true;
				}
				//is root?
				if ((*iter2) == dfa.root)
				{
					isRoot = true;
				}
				//is errorState?
				if ((*iter2) == errorState)
				{
					errorStateSet = (*iter);
					isErrorState = true;
				}
			}

			if (!isErrorState)
			{
				actualNode = new Node(expendable);
				//register it in the mirror and in the MDFA list
				branches.insert(std::make_pair(expendable, actualNode));
				mirror.insert(std::make_pair(*iter, actualNode));
				//make it final if the set is final
				actualNode->isFinal = isFinal;
				if (isFinal)
					finalStates.insert(actualNode);
				//make it root if the set is root
				if (isRoot)
				{
					MDFA::root = actualNode;
				}
			}
			expendable.clear();
			
		}

		//clear the error state set from the backBuffer
		backBuffer->erase(errorStateSet);
		


		//after having created all the nodes and having determined which are final and which is the root 
		//link them
		//for each set in the previous iteration
		Node* correspondingNode = nullptr;
		Node* someNodeFromTheSet = nullptr;
		Node* goesTo = nullptr;
		std::set<Node*> stFound;
		for (auto iter = backBuffer->begin(); iter != backBuffer->end(); iter++)
		{
			//find which node this set corresponds to
			correspondingNode = mirror.find(*iter)->second;
			//take one node of this set and check where it leads with the letters from the alphabet
			someNodeFromTheSet = *(iter->begin());
			//using the splitting table - find out where this node leads with each letter
			for (auto iter2 = alphabet.begin(); iter2 != alphabet.end(); iter2++)
			{
				stFound = splittingTable.find(std::make_pair(someNodeFromTheSet, *iter2))->second;
				
				//only if it's not the error state set
				if (stFound != errorStateSet)
				{
					goesTo = mirror.find(stFound)->second;
					//register in children
					correspondingNode->children.insert(std::make_pair(*iter2, goesTo->num));
				}
			}
			
		}

		/*
		for (auto iter = MDFA::branches.begin(); iter != MDFA::branches.end(); iter++)
		{
			std::cout << "\nState" << iter->second->actualNum << ":\n";
			if (root == iter->second)
				std::cout << "\nRoot\n";
			if (finalStates.find(iter->second) != finalStates.end())
				std::cout << "\nFinal\n";
			for (auto iter2 = iter->second->children.begin(); iter2 != iter->second->children.end(); iter2++)
			{
				std::cout << "\nTransition" << iter2->first << ": " << MDFA::branches.find(iter2->second)->second->actualNum << "\n";
			}
			if (iter->second->children.empty())
			{
			}
		}
		*/
		delete errorState;
	}

	~MDFA()
	{
		for (auto iter = branches.begin(); iter != branches.end(); iter++)
		{
			delete iter->second;
		}
	}

public:

	void printMDFADOT(std::ostream& os)
	{
		os << "digraph{" << std::endl;
		os << "node[shape = point, color = white, fontcolor = white]; start;" << std::endl;
		for (auto iter = finalStates.begin(); iter != finalStates.end(); iter++)
		{
			os << "node [shape = doublecircle, color=black, fontcolor=black]; " << (*iter)->actualNum << ";" << std::endl;
		}
		if (!root->isFinal)
		{
			os << "node[shape = circle]; " << root->actualNum << ";" << std::endl;
		}
		//so all of the nodes wouldn't look final in DOT we need to
		//set things right
		for (auto iter = branches.begin(); iter != branches.end(); iter++)
		{
			if (!iter->second->isFinal)
			{
				os << "node[shape = circle]; " << (iter->second)->actualNum << ";" << std::endl;
				break;
			}
		}

		os << "start -> " << root->actualNum << ";" << std::endl;

		for (auto iter = branches.begin(); iter != branches.end(); iter++)
		{

			for (auto iter2 = (iter->second)->children.begin(); iter2 != (iter->second)->children.end(); iter2++)
			{
				os << (iter->second)->actualNum << " -> " << branches.find((*iter2).second)->second->actualNum << "[label=\"" << (*iter2).first << "\"];" << std::endl;
			}
		}

		os << "}" << std::endl;
	}

	void printMDFA(std::ostream& os)
	{

		for (auto iter = branches.begin(); iter != branches.end(); iter++)
		{
			for (auto iter2 = (iter->second)->children.begin(); iter2 != (iter->second)->children.end(); iter2++)
			{
				os << makeString((iter->second)->num) << " -> " << makeString(iter2->second) << "[label=\"" << (*iter2).first << "\"];" << std::endl;
			}
		}
	}

	bool recognize(std::string word)
	{
		std::vector<SymbolClass> revWord;
		for (int k = word.size() - 1; k >= 0; k--)
		{
			revWord.push_back(word[k]);
		}
		return MDFA::recognize(*root, revWord);
	}

private:
	MDFA(const MDFA& another){}
	MDFA& operator=(const MDFA& another){}

};

class Parser
{
private:
	std::string expression;
	Tree* nfsa;
	DFA*  dfsa;
	MDFA* mdfsa;

private:
	std::string removeSpaces(std::string str)
	{
		std::string temp;
		for (int k = 0; k < str.length(); k++)
		{
			if (str[k] == ' ')
				continue;
			temp += str[k];
		}
		return temp;
	}

	//expression types:
	//1) a
	//2) a*
	//3) (...)
	//4) (...)*
	std::string getExpression(std::string str)
	{
		if (str[0] == '|' || str[0] == '*')
		{
			std::cout << "Syntax error, expecting an expression not an operator: " << str[0] << "." << std::endl;
			return "";
		}
		else if (str[0] == ')')
		{
			std::cout << "Mismatched brackets." << std::endl;
			return "";
		}

		std::string expression;
		std::stack<char> brackets;

		if (str[0] == '(')
		{
			for (unsigned int k = 0; k < str.size(); k++)
			{
				expression += str[k];

				if (str[k] == '(')
				{
					brackets.push(str[k]);
				}

				if (str[k] == ')')
				{
					if (brackets.empty())
					{
						std::cout << "Mismatched brackets." << std::endl;
						return "";
					}

					brackets.pop();

					if (brackets.empty())
					{
						if (str.size() > k + 1)
						{
							if (str[k + 1] == '*')
								expression += str[k + 1];
						}
						return expression;
					}
				}
			}

			if (!brackets.empty())
			{
				std::cout << "Mismatched brackets." << std::endl;
				return "";
			}
		}
		else//symbol
		{
			expression = str[0];
			if (str.size() > 1)
			{
				if (str[1] == '*')
					expression += str[1];
			}
		}

		return expression;
	}

	std::string removeBrackets(std::string str)
	{
		if (str[0] != '(' || str[str.size() - 1] != ')')
		{
			return "";
		}
		std::string output;
		std::stack < char > brackets;
		for (int k = 0; k < str.size(); k++)
		{
			if (str[k] == '(')
			{
				brackets.push(str[k]);
			}
			else if (str[k] == ')')
			{
				if (brackets.empty())
				{
					//std::cout << "Mismatched brackets." << std::endl;
					return "";
				}

				brackets.pop();

				if (brackets.empty())
				{
					if (k = str.size() - 1)
					{
						return str.substr(1, str.size() - 2);
					}
					else
					{
						return "";
					}
				}
			}
		}

		//std::cout << "Mismatched brackets." << std::endl;
		return "";

	}

	std::string eval(std::string input)
	{
		std::stack<char>brackets;
		for (int k = 0; k < input.length(); k++)
		{
			if (input[k] == '(')
			{
				brackets.push(input[k]);
			}

			if (input[k] == ')')
			{
				if (brackets.empty())
					return "";

				brackets.pop();
				if (brackets.empty())
				{
					return input.substr(1, k - 1);
				}
			}
		}

		return "";
	}

	Tree* parse(std::string input)
	{
		Tree* result = nullptr;

		//if there are no symbols
		//(could be at the bottom)
		if (input.empty())
		{
			std::cout << "(Syntax error? - brackets?) Cannot parse empty expression." << std::endl;
			return nullptr;
		}

		//at the bottom
		//if it's one symbol
		if (input.size() == 1)
		{
			if (input[0] == '*' || input[0] == '|')
			{
				std::cout << "Syntax error, was expecting a symbol, not operator: " << input[0] << "." << std::endl;
				return nullptr;
			}

			if (input[0] == '(' || input[0] == ')')
			{
				std::cout << "Mismatched brackets." << std::endl;
				return nullptr;
			}
			result = new Tree(input[0]);
			return result;

		}


		std::string lhsString;


		if (input == "()")
		{
			std::cout << "Cannot parse empty expression." << std::endl;
			return nullptr;
		}
		//if it's an expression in brackets - extract it and parse it
		//std::cout << input << std::endl;
		lhsString = removeBrackets(input);
		if (!lhsString.empty())
		{
			return parse(lhsString);
		}



		Tree* lhsTree = nullptr;
		Tree* rhsTree = nullptr;
		std::string rhsString;


		//normally
		lhsString = getExpression(input);
		if (lhsString.empty())
			return nullptr;


		if (lhsString[lhsString.size() - 1] == '*')
		{
			lhsTree = parse(lhsString.substr(0, lhsString.size() - 1));
			lhsTree = +*lhsTree;
		}
		else
		{
			lhsTree = parse(lhsString);
		}

		if (lhsTree == nullptr)
			return nullptr;

		//if that't the whole input string return it
		if (lhsString.size() == input.size())
			return lhsTree;

		if (lhsString.size() + 1 == input.size())
		{
			rhsTree = parse(input.substr(lhsString.size(), 1));
			if (lhsTree == nullptr)
				return nullptr;
			result = *lhsTree&&*rhsTree;
			delete lhsTree;
			delete rhsTree;
			return result;
		}

		if (lhsString.size() + 1 < input.size())
		{
			if (input[lhsString.size()] == '|')
			{
				rhsTree = parse(input.substr(lhsString.size() + 1, input.size() - lhsString.size() - 1));
				if (rhsTree == nullptr)
					return nullptr;
				result = *lhsTree || *rhsTree;
				delete lhsTree;
				delete rhsTree;
				return result;
			}
			else
			{
				rhsTree = parse(input.substr(lhsString.size(), input.size() - lhsString.size()));
				if (rhsTree == nullptr)
					return nullptr;
				result = *lhsTree && *rhsTree;
				delete lhsTree;
				delete rhsTree;
				return result;
			}
		}

		bool defaultCase = false;
		assert(defaultCase);
		return nullptr;
	}

public:
	Parser(std::string input)
		:expression(removeSpaces(input))
	{
		dfsa = nullptr;
		nfsa = parse(expression);
		//assert(nfsa != nullptr);
		if (nfsa == nullptr)
		{
			std::cout << "Press a key to exit." << std::endl;
			std::cin.sync();
			std::cin.ignore();
			exit(0);
		}
		nfsa->printTree(std::cout);
		std::ofstream file;
		file.open("output.txt");
		nfsa->printTreeDOT(file);
		file.close();
		dfsa = new DFA(*nfsa);
		std::cout << "\nDFA:" << std::endl;
		dfsa->printDFA(std::cout);
		file.open("outputDFA.txt");
		dfsa->printDFADOT(file);
		file.close();
		mdfsa = new MDFA(*dfsa);
		std::cout << "\nMDFA:" << std::endl;
		mdfsa->printMDFA(std::cout);
		file.open("outputMDFA.txt");
		mdfsa->printMDFADOT(file);
		file.close();
	}


	~Parser()
	{
		if (nfsa != nullptr)
			delete nfsa;
		if (dfsa != nullptr)
			delete dfsa;
		if (mdfsa != nullptr)
			delete mdfsa;
	}

	bool recognize(std::string word)
	{
		return nfsa->recognize(word);
	}
	bool recognizeDFA(std::string word)
	{
		return dfsa->recognize(word);
	}
	bool recognizeMDFA(std::string word)
	{
		return mdfsa->recognize(word);
	}

};

int main()
{
	std::string regularExpression;
	std::cout << "Please enter a regular expression:" << std::endl;
	std::getline(std::cin, regularExpression);
	Parser myParser(regularExpression);
	std::string recognizeWord;
	std::cout << std::endl << std::endl << std::endl;
	char prompt = 'y';
	while (prompt == 'y')
	{
		std::cout << std::endl << "Enter a word you want the automaton to recognize: ";
		std::cin >> recognizeWord;
		if (myParser.recognize(recognizeWord))
		{
			std::cout << "The automaton recognizes the word." << std::endl;
		}
		else
		{
			std::cout << "The automaton doesn't recognize the word." << std::endl;
		}
		if (myParser.recognizeDFA(recognizeWord))
		{
			std::cout << "The DFA automaton recognizes the word." << std::endl;
		}
		else
		{
			std::cout << "The DFA automaton doesn't recognize the word." << std::endl;
		}
		if (myParser.recognizeMDFA(recognizeWord))
		{
			std::cout << "The MDFA automaton recognizes the word." << std::endl;
		}
		else
		{
			std::cout << "The MDFA automaton doesn't recognize the word." << std::endl;
		}
		
		std::cout << std::endl << "Would you like to input another word? (y/n): ";
		std::cin >> prompt;
	}

	/*
	std::string recognize = "000000";
	Parser myParser("(0|(1(01*(00)*0)*1)*)*");
	std::cout << "Recognized " << recognize << " ?: " << myParser.recognize(recognize) << std::endl;
	/*
	/*
	Tree t1('0');
	Tree t2('1');
	Tree* temp1 = (t1&&*+t2);//01*
	Tree* temp2 = +*(t1&&t1); //(00)*
	Tree* temp3 = *temp2||t1; //(00)*|0
	delete temp1;
	delete temp2;
	delete temp3;
	*/

	std::cin.sync();
	std::cin.ignore();
	return 0;
}