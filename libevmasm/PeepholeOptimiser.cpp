/*
	This file is part of solidity.

	solidity is free software: you can redistribute it and/or modify
	it under the terms of the GNU General Public License as published by
	the Free Software Foundation, either version 3 of the License, or
	(at your option) any later version.

	solidity is distributed in the hope that it will be useful,
	but WITHOUT ANY WARRANTY; without even the implied warranty of
	MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
	GNU General Public License for more details.

	You should have received a copy of the GNU General Public License
	along with solidity.  If not, see <http://www.gnu.org/licenses/>.
*/
/**
 * @file PeepholeOptimiser.cpp
 * Performs local optimising code changes to assembly.
 */

#include "PeepholeOptimiser.h"

#include <libevmasm/AssemblyItem.h>
#include <libevmasm/SemanticInformation.h>
#include <unordered_map>
#include <stack>
#include <iostream>

using namespace std;
using namespace dev::eth;
using namespace dev;

// TODO: Extend this to use the tools from ExpressionClasses.cpp

namespace
{

struct OptimiserState
{
	AssemblyItems const& items;
	size_t i;
	std::back_insert_iterator<AssemblyItems> out;
};

template <class Method, size_t Arguments>
struct ApplyRule
{
};
template <class Method>
struct ApplyRule<Method, 5>
{
	static bool applyRule(AssemblyItems::const_iterator _in, std::back_insert_iterator<AssemblyItems> _out)
	{
		return Method::applySimple(_in[0], _in[1], _in[2], _in[3], _in[4], _out);
	}
};
template <class Method>
struct ApplyRule<Method, 4>
{
	static bool applyRule(AssemblyItems::const_iterator _in, std::back_insert_iterator<AssemblyItems> _out)
	{
		return Method::applySimple(_in[0], _in[1], _in[2], _in[3], _out);
	}
};
template <class Method>
struct ApplyRule<Method, 3>
{
	static bool applyRule(AssemblyItems::const_iterator _in, std::back_insert_iterator<AssemblyItems> _out)
	{
		return Method::applySimple(_in[0], _in[1], _in[2], _out);
	}
};
template <class Method>
struct ApplyRule<Method, 2>
{
	static bool applyRule(AssemblyItems::const_iterator _in, std::back_insert_iterator<AssemblyItems> _out)
	{
		return Method::applySimple(_in[0], _in[1], _out);
	}
};
template <class Method>
struct ApplyRule<Method, 1>
{
	static bool applyRule(AssemblyItems::const_iterator _in, std::back_insert_iterator<AssemblyItems> _out)
	{
		return Method::applySimple(_in[0], _out);
	}
};

template <class Method, size_t WindowSize>
struct SimplePeepholeOptimizerMethod
{
	static bool apply(OptimiserState& _state)
	{
		if (
			_state.i + WindowSize <= _state.items.size() &&
			ApplyRule<Method, WindowSize>::applyRule(_state.items.begin() + _state.i, _state.out)
		)
		{
			_state.i += WindowSize;
			return true;
		}
		else
			return false;
	}
};

struct Identity: SimplePeepholeOptimizerMethod<Identity, 1>
{
	static bool applySimple(AssemblyItem const& _item, std::back_insert_iterator<AssemblyItems> _out)
	{
		*_out = _item;
		return true;
	}
};

struct PushPop: SimplePeepholeOptimizerMethod<PushPop, 2>
{
	static bool applySimple(AssemblyItem const& _push, AssemblyItem const& _pop, std::back_insert_iterator<AssemblyItems>)
	{
		auto t = _push.type();
		return _pop == Instruction::POP && (
			SemanticInformation::isDupInstruction(_push) ||
			t == Push || t == PushString || t == PushTag || t == PushSub ||
			t == PushSubSize || t == PushProgramSize || t == PushData || t == PushLibraryAddress
		);
	}
};

struct OpPop: SimplePeepholeOptimizerMethod<OpPop, 2>
{
	static bool applySimple(
		AssemblyItem const& _op,
		AssemblyItem const& _pop,
		std::back_insert_iterator<AssemblyItems> _out
	)
	{
		if (_pop == Instruction::POP && _op.type() == Operation)
		{
			Instruction instr = _op.instruction();
			if (instructionInfo(instr).ret == 1 && !instructionInfo(instr).sideEffects)
			{
				for (int j = 0; j < instructionInfo(instr).args; j++)
					*_out = {Instruction::POP, _op.location()};
				return true;
			}
		}
		return false;
	}
};

struct DoubleSwap: SimplePeepholeOptimizerMethod<DoubleSwap, 2>
{
	static size_t applySimple(AssemblyItem const& _s1, AssemblyItem const& _s2, std::back_insert_iterator<AssemblyItems>)
	{
		return _s1 == _s2 && SemanticInformation::isSwapInstruction(_s1);
	}
};

struct DoublePush: SimplePeepholeOptimizerMethod<DoublePush, 2>
{
	static bool applySimple(AssemblyItem const& _push1, AssemblyItem const& _push2, std::back_insert_iterator<AssemblyItems> _out)
	{
		if (_push1.type() == Push && _push2.type() == Push && _push1.data() == _push2.data())
		{
			*_out = _push1;
			*_out = {Instruction::DUP1, _push2.location()};
			return true;
		}
		else
			return false;
	}
};

struct CommutativeSwap: SimplePeepholeOptimizerMethod<CommutativeSwap, 2>
{
	static bool applySimple(AssemblyItem const& _swap, AssemblyItem const& _op, std::back_insert_iterator<AssemblyItems> _out)
	{
		// Remove SWAP1 if following instruction is commutative
		if (
			_swap.type() == Operation &&
			_swap.instruction() == Instruction::SWAP1 &&
			SemanticInformation::isCommutativeOperation(_op)
		)
		{
			*_out = _op;
			return true;
		}
		else
			return false;
	}
};

struct SwapComparison: SimplePeepholeOptimizerMethod<SwapComparison, 2>
{
	static bool applySimple(AssemblyItem const& _swap, AssemblyItem const& _op, std::back_insert_iterator<AssemblyItems> _out)
	{
		map<Instruction, Instruction> swappableOps{
			{ Instruction::LT, Instruction::GT },
			{ Instruction::GT, Instruction::LT },
			{ Instruction::SLT, Instruction::SGT },
			{ Instruction::SGT, Instruction::SLT }
		};

		if (
			_swap.type() == Operation &&
			_swap.instruction() == Instruction::SWAP1 &&
			_op.type() == Operation &&
			swappableOps.count(_op.instruction())
		)
		{
			*_out = swappableOps.at(_op.instruction());
			return true;
		}
		else
			return false;
	}
};

struct JumpToNext: SimplePeepholeOptimizerMethod<JumpToNext, 3>
{
	static size_t applySimple(
		AssemblyItem const& _pushTag,
		AssemblyItem const& _jump,
		AssemblyItem const& _tag,
		std::back_insert_iterator<AssemblyItems> _out
	)
	{
		if (
			_pushTag.type() == PushTag &&
			(_jump == Instruction::JUMP || _jump == Instruction::JUMPI) &&
			_tag.type() == Tag &&
			_pushTag.data() == _tag.data()
		)
		{
			if (_jump == Instruction::JUMPI)
				*_out = AssemblyItem(Instruction::POP, _jump.location());
			*_out = _tag;
			return true;
		}
		else
			return false;
	}
};

struct TagConjunctions: SimplePeepholeOptimizerMethod<TagConjunctions, 3>
{
	static bool applySimple(
		AssemblyItem const& _pushTag,
		AssemblyItem const& _pushConstant,
		AssemblyItem const& _and,
		std::back_insert_iterator<AssemblyItems> _out
	)
	{
		if (
			_pushTag.type() == PushTag &&
			_and == Instruction::AND &&
			_pushConstant.type() == Push &&
			(_pushConstant.data() & u256(0xFFFFFFFF)) == u256(0xFFFFFFFF)
		)
		{
			*_out = _pushTag;
			return true;
		}
		else
			return false;
	}
};

/// Removes everything after a JUMP (or similar) until the next JUMPDEST.
struct UnreachableCode
{
	static bool apply(OptimiserState& _state)
	{
		auto it = _state.items.begin() + _state.i;
		auto end = _state.items.end();
		if (it == end)
			return false;
		if (
			it[0] != Instruction::JUMP &&
			it[0] != Instruction::RETURN &&
			it[0] != Instruction::STOP &&
			it[0] != Instruction::INVALID &&
			it[0] != Instruction::SELFDESTRUCT &&
			it[0] != Instruction::REVERT
		)
			return false;

		size_t i = 1;
		while (it + i != end && it[i].type() != Tag)
			i++;
		if (i > 1)
		{
			*_state.out = it[0];
			_state.i += i;
			return true;
		}
		else
			return false;
	}
};

// modified by sun
//P2 — {swap(X), dup(X+1), swap1} → {dup1, swap(X+1)}, 1 ≤ X ≤ 15
struct PatternTwo: SimplePeepholeOptimizerMethod<PatternTwo, 3>
{
	static bool applySimple(AssemblyItem const& _swap, AssemblyItem const& _dup, AssemblyItem const& _swap1, std::back_insert_iterator<AssemblyItems> _out)
	{
		if (SemanticInformation::isSwapInstruction(_swap) && 
			SemanticInformation::isDupInstruction(_dup) && 
			getSwapNumber(_swap.instruction()) == (getDupNumber(_dup.instruction()) - 1)
			&& _swap1 == Instruction::SWAP1
		)
		{
			size_t n = getSwapNumber(_swap.instruction());
			*_out = {Instruction::DUP1, _swap.location()};
			*_out = {Instruction(0x90 + n), _dup.location()};	
			cout << "pattern 2" << endl;
			return true;
		}
		return false;
	}
};

//P7 — {swap(X), swap(Y), Y consecutive pops} →  {X consecutive pops, swap(Y-X), (Y-X) consecutive pops}, 1 ≤ X ≤ 15, X < Y
struct PatternSeven
{
	static bool apply(OptimiserState& _state)
	{
		auto it = _state.items.begin() + _state.i;	
		auto end = _state.items.end();
		if (it == end || !SemanticInformation::isSwapInstruction(it[0]))
			return false;
		size_t x_swap =  getSwapNumber(it[0].instruction());
		if (it + 1 == end || !SemanticInformation::isSwapInstruction(it[1]))
			return false;
		size_t y_swap = getSwapNumber(it[1].instruction());
		size_t n_pop = 0;
		if (it + 2 != end)
		{
			size_t i = 2;
			while (n_pop < y_swap)
			{
				if (it[i] != Instruction::POP)
					return false;
				n_pop++; i++;
			}
		}	
		if (n_pop == y_swap && x_swap < n_pop)
		{
			for (size_t i = 0; i < x_swap; i++)
				*_state.out = Instruction::POP;
			*_state.out = Instruction(0x90 + n_pop - x_swap - 1);
			for (size_t i = 0; i < n_pop - x_swap; i++)
				*_state.out = Instruction::POP;
			_state.i += n_pop + 2;
			cout << "pattern 7" << endl;
			return true;
		}		
		else
			return false;
	}
};

//P13 — {N consecutive push(X)，M consecutive swap(Y)} → {N consecutive push(X)}, Y < N, 1 ≤ X ≤ 32, 1 ≤ Y ≤ 16
struct PatternThirteen
{
	static bool apply(OptimiserState& _state)
	{
		auto it = _state.items.begin() + _state.i;
		auto end = _state.items.end();
		vector<AssemblyItems::const_iterator> vPushOp, vSwapOp;
		size_t index = 0, swapNum = 0;
		bool bOpt = false;

		while ((it + index != end) && it[index].type() == Push)
		{
			vPushOp.push_back(it+index);
			index++;
		}
		while ((it + index != end) && SemanticInformation::isSwapInstruction(it[index]))
		{
			vSwapOp.push_back(it+index);
			index++;
		}
		for (auto& swapOp : vSwapOp)
		{
			size_t y = getSwapNumber(swapOp[0].instruction());
			size_t sz = vPushOp.size();
			if (y < vPushOp.size())
			{
				swap(vPushOp.back(), vPushOp[sz-y-1]);
				bOpt = true;
				swapNum++;
			}
			else break;
		}
		if (bOpt)
		{
			for (auto& pushOp : vPushOp)
			{
				*_state.out = pushOp[0];
			}
			_state.i += vPushOp.size();
			_state.i += swapNum;
			cout << "pattern 13" << endl;
		}
		return bOpt;
	}
};

//P23 — {OP, stop} → {stop},OP can be any operation except JUMPDEST/JUMP/JUMPI/MSTORE/MSTORE8/SSTORE/CREATE/CALL/CALLCODE/DELEGETECALL/SELFDESTRUCT/LOGx/EXTCODECOPY/CODECOPY/CALLDATACOPY/
struct PatternTwentyThree: SimplePeepholeOptimizerMethod<PatternTwentyThree, 2>
{
	static bool applySimple(AssemblyItem const& _op, AssemblyItem const& _stop, std::back_insert_iterator<AssemblyItems> _out)
	{
		if (_op.type() != Operation)
			return false;
		unordered_map<Instruction, bool> ins;
		ins[Instruction::JUMPDEST] = true;
		ins[Instruction::JUMP] = true;
		ins[Instruction::JUMPI] = true;
		ins[Instruction::MSTORE] = true;
		ins[Instruction::MSTORE8] = true;
		ins[Instruction::SSTORE] = true;
		ins[Instruction::CREATE] = true;
		ins[Instruction::CALL] = true;
		ins[Instruction::CALLCODE] = true;
		ins[Instruction::DELEGATECALL] = true;
		ins[Instruction::SELFDESTRUCT] = true;
		ins[Instruction::LOG1] = true;
		ins[Instruction::LOG2] = true;
		ins[Instruction::LOG3] = true;
		ins[Instruction::LOG4] = true;
		ins[Instruction::EXTCODECOPY] = true;
		ins[Instruction::CODECOPY] = true;
		ins[Instruction::CALLDATACOPY] = true;
		if(!ins[_op.instruction()] && _stop == Instruction::STOP)
		{
			*_out = {Instruction::STOP, _op.location()};
			cout << "pattern 23" << endl;
			return true;
		}
		return false;
	}
};

//P26 — {dup1, swap(X), dup2, swap1} → {dup1, dup2, swap(X+1)}, 1 ≤ X ≤ 15
struct PatternTwentySix: SimplePeepholeOptimizerMethod<PatternTwentySix, 4>
{
	static bool applySimple(AssemblyItem const& _dup1, AssemblyItem const& _swapn, AssemblyItem const& _dup2, AssemblyItem const& _swap1, std::back_insert_iterator<AssemblyItems> _out)
	{
		if (
			_dup1 == Instruction::DUP1 &&
			SemanticInformation::isSwapInstruction(_swapn) && (getSwapNumber(_swapn.instruction()) < 16) &&
			_dup2 == Instruction::DUP2 &&
			_swap1 == Instruction::SWAP1
		)
		{
			size_t n = getSwapNumber(_swapn.instruction());
			*_out = _dup1;
			*_out = {Instruction::DUP2, _swapn.location()};
			*_out = {Instruction(0x90 + n), _dup2.location()};
			cout << "pattern 26" << endl;
			return true;		
		}
		return false;
	}
};
//end, by sun


// modify by wh 
//dupN/swapN-1/swap1/dupN/swap1(N>2)=======>dupN/dup1/swapN/swap2
struct PatternTwentyEight
{
	static bool apply(OptimiserState& _state)
	{
		size_t WindowSize = 0;
		auto it = _state.items.begin() + _state.i;
		auto end = _state.items.end();
		if (it == end)
			return false;
		if( it[0].type() == Operation  &&  isDupInstruction(it[0].instruction()) == true )
		{
			size_t DupNumber = getDupNumber(it[0].instruction());
			if( DupNumber > 2 )
			{
				WindowSize = 5;
				if(
					_state.i + WindowSize <= _state.items.size()  &&
					applyrule(_state.items.begin()+_state.i,_state.out,DupNumber)
				)
				{
					_state.i += WindowSize;
					return true;
				}
				else
					return false;
			}
			else
			return false;
		}
		else
		{
			return false;
		}       
	}
	static bool applyrule(AssemblyItems::const_iterator _in,back_insert_iterator<AssemblyItems> _out,size_t DupNumber)
	{
		return applySimple(_in,_out,DupNumber);
	}
	                        
	static bool applySimple(AssemblyItems::const_iterator _in,back_insert_iterator<AssemblyItems> _out,size_t DupNumber)
	{
		if
		(
			_in[1].type() != Operation ||
			isSwapInstruction(_in[1].instruction() ) == false ||
			getSwapNumber(_in[1].instruction()) != DupNumber - 1  		
		)
		return false;
		else
		{
			if(_in[2] != Instruction::SWAP1) return false;
			else
			{
				if
				(
					_in[3].type() != Operation ||
					isDupInstruction(_in[3].instruction() ) == false ||
					getDupNumber(_in[3].instruction() ) != DupNumber  
				)
				return false;
				else
				{
					if(_in[4] != Instruction::SWAP1) return false;
					else
					{
						*_out = _in[0];
						*_out = AssemblyItem(Instruction::DUP1,_in[1].location());
						*_out = AssemblyItem(swapInstruction(DupNumber),_in[2].location());
						*_out = AssemblyItem(Instruction::SWAP2,_in[3].location());
						cout << "pattern 28" << endl;
						return true;
					}
				}
		return false;
			}
		}
	}
};

//swapN,N+1pop====>N+1pop
struct PatternSix
{
	static bool apply(OptimiserState& _state)
	{
		size_t WindowSize = 0;
		auto it = _state.items.begin() + _state.i;
		auto end = _state.items.end();
		if (it == end)
			return false;
		if(SemanticInformation::isSwapInstruction(it[0]))
		{
			WindowSize = getSwapNumber(it[0].instruction()) + 1 + 1;  //SwapN needs N+1 POP,So WindowSize = N + 1 + 1;
			if(
				_state.i + WindowSize <= _state.items.size()  &&
				applyrule(_state.items.begin()+_state.i,_state.out,WindowSize)
				)
				{
					_state.i += WindowSize;
					return true;
				}
			else
				return false;
		}
		else{
			return false;
		}
	}
	static bool applyrule(AssemblyItems::const_iterator _in,back_insert_iterator<AssemblyItems> _out,size_t WindowSize)
	{
		return applySimple(_in,_out,WindowSize);
	}
	                        
	static bool applySimple(AssemblyItems::const_iterator _in,back_insert_iterator<AssemblyItems> _out,size_t WindowSize)
	{
		bool satisfied = true;
		for(int i = 1;i<int(WindowSize);i++)
		{
			if(_in[i]!= Instruction::POP)
			{
				satisfied = false;
			}
		}
		if(satisfied == true)
		{
			for(int i = 0;i<int(WindowSize-1);i++)
			{
				*_out = {Instruction::POP,_in[i].location()};
			}
			cout << "pattern 6" << endl;
			return true;
		}
		else
			return false;
	}
};

struct PatternTwentyFive
{
	static bool apply(OptimiserState& _state)
	{	
		size_t WindowSize = 0;
		auto it = _state.items.begin() + _state.i;
		auto end = _state.items.end();
		if (it == end)
			return false;
		if ( it[0].type()!= Operation || SemanticInformation::isSwapInstruction(it[0])==false )
			return false;
		else
		{
			size_t NumberOfSwap = getSwapNumber(it[0].instruction());
			size_t SumOfPushAndDup = 0;
			size_t ptr = 1;
			while(it + ptr != end)
			{
				if(it[ptr].type() == Operation && isSwapInstruction(it[ptr].instruction()) )
				{
					ptr += 1;
					SumOfPushAndDup +=1;
				}
				else if( it[ptr].type()==Push )
				{
					ptr += 1;
					SumOfPushAndDup +=1;
				}
				else
					break;
			}
			WindowSize = NumberOfSwap + SumOfPushAndDup + SumOfPushAndDup +1 ;
			if(
				_state.i + WindowSize <= _state.items.size()  &&
				applyrule(_state.items.begin()+_state.i,_state.out,WindowSize,SumOfPushAndDup)
				)
				{
					_state.i += WindowSize;
					cout << "pattern 25" << endl;
					return true;
				}
			else
				return false;
		}	
	}
	static bool applyrule(AssemblyItems::const_iterator _in,back_insert_iterator<AssemblyItems> _out,size_t WindowSize,size_t SumOfPushAndDup)
	{
		
		return applySimple(_in,_out,WindowSize,SumOfPushAndDup);
	}
	static bool applySimple(AssemblyItems::const_iterator _in,back_insert_iterator<AssemblyItems> _out,size_t WindowSize,size_t SumOfPushAndDup)
	{
		bool satisfied = true;
		if(	_in[SumOfPushAndDup + 1].type() != Operation )
			return false;
		else if
		(
			_in[SumOfPushAndDup + 1].instruction() != Instruction::ADD &&
			_in[SumOfPushAndDup + 1].instruction() != Instruction::MUL &&
			_in[SumOfPushAndDup + 1].instruction() != Instruction::AND &&
			_in[SumOfPushAndDup + 1].instruction() != Instruction::XOR &&
			_in[SumOfPushAndDup + 1].instruction() != Instruction::OR 
		)
			return false;
		else
		{
			for(size_t i = SumOfPushAndDup + 1; i < WindowSize ; i++)
			{
				if(_in[i] != _in[SumOfPushAndDup + 1])
					satisfied = false;
			}
		}
		if(satisfied == true)
		{
			for(size_t i = 1;i< WindowSize;i++)
			{
				*_out = _in[i];
			}
			return true;
		}
		else
			return false;
	}
};

//   swap1,...,swapN,...swap1, (N-1)  pop====>(N-1) pop, swap1     
struct PatternTwelve
{
	static bool apply(OptimiserState& _state)
	{
		size_t WindowSize = 0;
		auto it = _state.items.begin() + _state.i;
		auto end = _state.items.end();
		if (it == end)
			return false;
		if ( it[0].type()!= Operation || it[0].instruction()!= Instruction::SWAP1 )
			return false;
		else
		{
			size_t MaxNumberOfSwap = 0;
			while(it + MaxNumberOfSwap != end )
			{	
				if (it + MaxNumberOfSwap + 1 == end )
					return false;
				if
				( 
					it[MaxNumberOfSwap].type() == Operation && it[MaxNumberOfSwap + 1].type() == Operation && 
					SemanticInformation::isSwapInstruction(it[MaxNumberOfSwap]) && 
					SemanticInformation::isSwapInstruction(it[MaxNumberOfSwap + 1 ]) &&
					(
						int(getSwapNumber(it[MaxNumberOfSwap+1].instruction())) - int(getSwapNumber(it[MaxNumberOfSwap].instruction()))  == 1
					)
				)
				{
				MaxNumberOfSwap += 1;
				}
				else
				{
					break;
				}
			}
			if(SemanticInformation::isSwapInstruction(it[MaxNumberOfSwap + 1 ]) == false) return false;
			MaxNumberOfSwap += 1;
			WindowSize = 3*MaxNumberOfSwap - 2;
			if(
				_state.i + WindowSize <= _state.items.size()  &&
				applyrule(_state.items.begin()+_state.i,_state.out,WindowSize,MaxNumberOfSwap)
				)
				{
					_state.i += WindowSize;
					cout << "pattern 12" << endl;
					return true;
				}
			else
				return false;
		}
	}
	static bool applyrule(AssemblyItems::const_iterator _in,back_insert_iterator<AssemblyItems> _out,size_t WindowSize,size_t MaxNumberOfSwap)
	{
		
		return applySimple(_in,_out,WindowSize,MaxNumberOfSwap);
	}
	                        
	static bool applySimple(AssemblyItems::const_iterator _in,back_insert_iterator<AssemblyItems> _out,size_t WindowSize,size_t MaxNumberOfSwap)
	{
		bool satisfied = true;
		size_t swap_fall_start = MaxNumberOfSwap;
		size_t swap_fall_end = 2 * ( MaxNumberOfSwap - 1 );
		size_t pop_start = swap_fall_end + 1;
		for(size_t i = swap_fall_start;i <= swap_fall_end;i++)
		{
			if(_in[i].type() != Operation   ||    isSwapInstruction(_in[i].instruction() ) == false   )
			{
				satisfied = false;
			}
			if( int(getSwapNumber(_in[i].instruction())) - int(getSwapNumber(_in[i-1].instruction())) != -1)
			{
				// printf("It is me!!!!!!!!! %d %d\n",int(getSwapNumber(_in[i].instruction())),int(getSwapNumber(_in[i-1].instruction())));
				satisfied = false;
				// printf("It is mine!!!!!!!!! %d\n",int(satisfied));
			}
		}
		
		for(size_t i = pop_start;i < WindowSize ; i++)
		{
			if(_in[i]!= Instruction::POP)
			{
				satisfied = false;
			}
		}
		if( satisfied == true )
		{	
			size_t i=0;
			for(i=0 ; i < MaxNumberOfSwap - 1 ;i++)
			{
				*_out = {Instruction::POP,_in[i].location()};
			}
			*_out = {Instruction::SWAP1,_in[i].location()};
			cout << "pattern 12" << endl;
			return true;
		}
		else
			return false;
	}
};

//     OP/ISZERO/ISZERO========>OP          OP: LT/GT/SLT/SGT/EQ
struct PatternTwenty: SimplePeepholeOptimizerMethod<PatternTwenty, 3>
{
	static bool applySimple(AssemblyItem const& _op, AssemblyItem const& _zore_1, AssemblyItem const& _zore_2,std::back_insert_iterator<AssemblyItems> _out)
	{	
		if(
			_op.type() == Operation && _zore_1.type() == Operation && _zore_2.type()==Operation &&
			(_op == Instruction::LT ||_op == Instruction::GT || _op == Instruction::SLT || _op == Instruction::EQ) &&
			_zore_1 == Instruction::ISZERO && _zore_2 ==Instruction::ISZERO
		)
		{
			*_out = _op;\
			cout << "pattern 20" << endl;
			return true;
		}
		else
			return false;
	}
};
//end, modify by wh 

//modified by luo
//P3 — {push(X), swap(Y), Y consecutive pops} → {Y consecutive pops, push(X)}, 1 ≤ X ≤ 32, 1 ≤ Y ≤ 16
struct PatternThree
{
	static bool apply(OptimiserState& _state)
	{
		auto it = _state.items.begin() + _state.i;
		auto end = _state.items.end();
		if (it == end || it[0].type() != Push)
			return false;
		if (it + 1 == end || !SemanticInformation::isSwapInstruction(it[1]))
		    return false;
		size_t n = getSwapNumber(it[1].instruction());
		size_t count = 0;

		for (size_t i = 2; count < n; i++)
		{
			if (it + i == end || it[i] != Instruction::POP)
				return false;
			count++;
		}

		if (count == n)
		{
			for (size_t i = 0; i < n; i++)
				*_state.out = Instruction::POP;
			*_state.out = it[0];
			_state.i += count + 2;
			cout << "pattern 3" << endl;
			return true;
		}
		return false;
		
	}
};

//P8 — {push(X), swap(Y), push(M), swap1} → {push(M), push(X), swap(Y+1)}, 1 ≤ X ≤ 32, 1 ≤ Y ≤ 15, 1 ≤ M ≤ 32
struct PatternEight: SimplePeepholeOptimizerMethod<PatternEight, 4>
{
	static bool applySimple(AssemblyItem const& _push1, AssemblyItem const& _swap, AssemblyItem const& _push2, AssemblyItem const& _swap1, std::back_insert_iterator<AssemblyItems> _out)
	{
		auto t = _push1.type();
		auto s = _push2.type();
		if (t == Push && s==Push &&
			SemanticInformation::isSwapInstruction(_swap) &&
			_swap1 == Instruction::SWAP1
		)
		{
			*_out = _push2;
			*_out = _push1;
			size_t n = getSwapNumber(_swap.instruction());
			*_out = {Instruction(0x90 + n), _push2.location()};
			cout << "pattern 8" << endl;
			return true;
		}
		return false;
	}
};

//P11 — {dup(X), swap(X)} → {dup(X)}, 1 ≤ X ≤ 16
struct PatternEleven: SimplePeepholeOptimizerMethod<PatternEleven, 2>
{
	static bool applySimple(AssemblyItem const& _dup, AssemblyItem const& _swap, std::back_insert_iterator<AssemblyItems> _out)
	{
		if (
			SemanticInformation::isDupInstruction(_dup) &&
			SemanticInformation::isSwapInstruction(_swap) &&
			getDupNumber(_dup.instruction()) ==  getSwapNumber(_swap.instruction())
		)
		{
			*_out = _dup;
			cout << "pattern 11" << endl;
			return true;
		}
		return false;
	}
};

//P24 — {consecutive X push(N), dup(Y), swap(Z)} → {combination of X push(N) and dup(M)}, Y<=X, Z<=X, M<=X, 1 ≤ N ≤ 32, 1 ≤ Y ≤ 16, 1 ≤ Z ≤ 16, 1 ≤ M ≤ 16
struct PatternTwentyFour
{
	static bool apply(OptimiserState& _state)
	{
		auto it = _state.items.begin() + _state.i;
		auto end = _state.items.end();
		if (it == end || it[0].type() != Push)
			return false;

		size_t pushCount = 0;
		while (it + pushCount != end && it[pushCount].type() == Push)
			pushCount++;

		if (!SemanticInformation::isDupInstruction(it[pushCount]) || !SemanticInformation::isSwapInstruction(it[pushCount + 1]))
			return false;

		size_t dupNum = getDupNumber(it[pushCount].instruction());
		size_t swapNum = getSwapNumber(it[pushCount + 1].instruction());

		//dupNum = swapNum -> PatternEleven
		if (dupNum == swapNum || dupNum > pushCount || swapNum > pushCount)
			return false;
		
		stack<AssemblyItem> s;
		for (size_t i = 0; i < pushCount + 2; i++)
		{
			if (it[i].type() == Push)
				s.push(it[i]);
			else if (SemanticInformation::isDupInstruction(it[i]))
				s.push(it[i - dupNum]);
			else if (SemanticInformation::isSwapInstruction(it[i]))
			{
				for (size_t j = 0; j <= swapNum; j++)
					s.pop();
				s.push(it[i - dupNum - 1]);
				if (swapNum > 1)
				{
					for (size_t k = 0, index = i - swapNum; k <= swapNum - 2; k++, index++)
						s.push(it[index]);
				}
				s.push(it[i - swapNum - 1]);
			}
				
		}
		stack<AssemblyItem> s2;
		size_t n = s.size();
		for (size_t i = 0; i < n; i++)
		{
			s2.push(s.top());
			s.pop();
		}

		int counts[pushCount] = {};
		while (s2.size() > 0)
		{
			for (size_t i = 0; i < pushCount; i++)
			{
				if (s2.top() == it[i] && counts[i] == 0)
				{
					*_state.out = s2.top();
					counts[i]++;
					s2.pop();
				}
				else if (s2.top() == it[i] && counts[i] == 1)
				{
					*_state.out = Instruction(0x80 + (dupNum > swapNum ? dupNum - swapNum : swapNum - dupNum) - 1);
					s2.pop();
				}
				if (s2.size() == 0)
					break;
			}
		}
		_state.i += pushCount + 2;
		cout << "pattern 24" << endl;
		return true;	
	}
};

//P27 — {swap1, swap(X), OP, dup(X), OP} → {dup2, swap(X+1), OP, OP}, 2 ≤ X ≤ 15, OP ∈ {add, mul, and, or, xor}
struct PatternTwentySeven: SimplePeepholeOptimizerMethod<PatternTwentySeven, 5>
{
	static bool applySimple(AssemblyItem const& _swap1, AssemblyItem const& _swap, AssemblyItem const& _op1, AssemblyItem const& _dup, AssemblyItem const& _op2, std::back_insert_iterator<AssemblyItems> _out)
	{
		if (_swap.type() != Operation || _op1.type() != Operation || _op2.type() != Operation || _dup.type() != Operation)
			return false;
		unordered_map<Instruction, bool> ins;
		ins[Instruction::ADD] = true;
		ins[Instruction::MUL] = true;
		ins[Instruction::AND] = true;
		ins[Instruction::OR] = true;
		ins[Instruction::XOR] = true;
		if (_swap1 == Instruction::SWAP1 && 
			SemanticInformation::isSwapInstruction(_swap) &&
			(getSwapNumber(_swap.instruction()) <= 15) &&
		    SemanticInformation::isDupInstruction(_dup) &&
			getSwapNumber(_swap.instruction()) == (getDupNumber(_dup.instruction())) &&
			ins[_op1.instruction()] && ins[_op2.instruction()]
		)
		{
			size_t n = getSwapNumber(_swap.instruction());
			*_out = {Instruction::DUP2, _swap1.location()};
			*_out = {Instruction(0x90+n), _swap.location()};
			*_out = _op1;
			*_out = _op2;
			cout << "pattern 27" << endl;
			return true;
		}
		return false;
	}
};
//end, by luo

void applyMethods(OptimiserState&)
{
	assertThrow(false, OptimizerException, "Peephole optimizer failed to apply identity.");
}

template <typename Method, typename... OtherMethods>
void applyMethods(OptimiserState& _state, Method, OtherMethods... _other)
{
	if (!Method::apply(_state))
		applyMethods(_state, _other...);
}

size_t numberOfPops(AssemblyItems const& _items)
{
	return std::count(_items.begin(), _items.end(), Instruction::POP);
}

}

bool PeepholeOptimiser::optimise()
{
	OptimiserState state {m_items, 0, std::back_inserter(m_optimisedItems)};
	while (state.i < m_items.size())
		applyMethods(state, PushPop(), OpPop(), DoublePush(), DoubleSwap(), CommutativeSwap(), SwapComparison(), JumpToNext(), UnreachableCode(), TagConjunctions(), 
		PatternTwo(), PatternSeven(), PatternThirteen(), PatternTwentyThree(), PatternTwentySix(), //sun
		PatternSix(), PatternTwelve(), PatternTwenty(), PatternTwentyFive(), PatternTwentyEight(), //wu
		PatternThree(), PatternEight(), PatternEleven(), PatternTwentyFour(), PatternTwentySeven(), //luo
		Identity());
	if (m_optimisedItems.size() < m_items.size() || (
		m_optimisedItems.size() == m_items.size() && (
			eth::bytesRequired(m_optimisedItems, 3) < eth::bytesRequired(m_items, 3) ||
			numberOfPops(m_optimisedItems) > numberOfPops(m_items)
		)
	))
	{
		m_items = std::move(m_optimisedItems);
		return true;
	}
	else
		return false;
}
