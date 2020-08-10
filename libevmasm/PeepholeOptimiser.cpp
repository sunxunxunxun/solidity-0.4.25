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
#include <iostream>

#include <unordered_map>

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
// modified by sun
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
			return true;
		}
		return false;
	}
};

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
			return true;
		}
		return false;
	}
};

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
			return true;		
		}
		return false;
	}
};

struct PatternSeven
{
	static bool apply(OptimiserState& _state)
	{
		auto it = _state.items.begin() + _state.i;	//i=0
		auto end = _state.items.end();
		if (it == end || !SemanticInformation::isSwapInstruction(it[0]))
			return false;
		size_t x_swap =  getSwapNumber(it[0].instruction());
		if (it + 1 == end || !SemanticInformation::isSwapInstruction(it[1]))
			return false;
		size_t y_swap = getSwapNumber(it[1].instruction());
		cout << "swapx: " << it[0].instruction() << "; swapy: " << it[1].instruction() << endl;
		size_t n_pop = 0;
		if (it + 2 != end)
		{
			size_t i = 2;
			while ( n_pop < y_swap)
			{
				if (it[i] != Instruction::POP)
					return false;
				n_pop++; i++;
				cout << n_pop << endl;
			}
		}	
		cout << "number of pop: " << n_pop << endl;
		if (n_pop == y_swap && x_swap < n_pop)
		{
			for (size_t i = 0; i < x_swap; i++)
				*_state.out = Instruction::POP;
			*_state.out = Instruction(0x90 + n_pop - x_swap - 1);
			for (size_t i = 0; i < n_pop - x_swap; i++)
				*_state.out = Instruction::POP;
			cout << "n_pop - x_swap" << n_pop - x_swap << endl;
			_state.i += n_pop + 2;
			return true;
		}		
		else
			return false;
	}
};

// while op is Push:
// 	pushData.append(op.data)
// 	op++
// if op is not Swap:
// 	return false
// while op is Swap:
// 	swapData(pushData)
// return true

struct PatternThirteen
{
	static bool apply(OptimiserState& _state)
	{
		auto it = _state.items.begin() + _state.i;
		auto end = _state.items.end();
		vector<AssemblyItems::const_iterator> vPushOp, vSwapOp;
		int index = 0, swapNum = 0;
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
			unsigned int y = getSwapNumber(swapOp[0].instruction());
			if (y < vPushOp.size())
			{
				swap(vPushOp[0], vPushOp[y]);
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
		}
		return bOpt;
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
		applyMethods(state, PushPop(), OpPop(), DoublePush(), DoubleSwap(), CommutativeSwap(), SwapComparison(), JumpToNext(), UnreachableCode(), TagConjunctions(), PatternTwo(), PatternSeven(), PatternThirteen(), PatternTwentyThree(), PatternTwentySix(), Identity());
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
