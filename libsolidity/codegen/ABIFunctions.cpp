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
 * @author Christian <chris@ethereum.org>
 * @date 2017
 * Routines that generate JULIA code related to ABI encoding, decoding and type conversions.
 */

#include <libsolidity/codegen/ABIFunctions.h>

#include <libdevcore/Whiskers.h>

#include <libsolidity/ast/AST.h>

using namespace std;
using namespace dev;
using namespace dev::solidity;

ABIFunctions::~ABIFunctions()
{
	// This throws an exception and thus might cause immediate termination, but hey,
	// it's a failed assertion anyway :-)
//TODO	solAssert(m_requestedFunctions.empty(), "Forgot to call ``requestedFunctions()``.");
}

string ABIFunctions::tupleEncoder(
	TypePointers const& _givenTypes,
	TypePointers const& _tos,
	bool _encodeAsLibraryTypes
)
{
	// stack: <$value0> <$value1> ... <$value(n-1)> <$headStart>

	string encoder = R"(
		let dynFree := add($headStart, <headSize>)
		<#values>
			dynFree := <abiEncode>(
				$value<i>,
				$headStart,
				add($headStart, <headPos>),
				dynFree
			)
		</values>
		$value0 := dynFree
	)";
	solAssert(!_givenTypes.empty(), "");
	size_t headSize = 0;
	for (auto const& t: _tos)
	{
		solAssert(t->calldataEncodedSize() > 0, "");
		headSize += t->calldataEncodedSize();
	}
	Whiskers templ(encoder);
	templ("headSize", to_string(headSize));
	vector<Whiskers::StringMap> values(_givenTypes.size());
	map<string, pair<TypePointer, TypePointer>> requestedEncodingFunctions;
	size_t headPos = 0;
	for (size_t i = 0; i < _givenTypes.size(); ++i)
	{
		solUnimplementedAssert(_givenTypes[i]->sizeOnStack() == 1, "");
		solAssert(_givenTypes[i], "");
		solAssert(_tos[i], "");
		values[i]["fromTypeID"] = _givenTypes[i]->identifier();
		values[i]["toTypeID"] = _tos[i]->identifier();
		values[i]["i"] = to_string(i);
		values[i]["headPos"] = to_string(headPos);
		values[i]["abiEncode"] =
			abiEncodingFunction(*_givenTypes[i], *_tos[i], _encodeAsLibraryTypes);
		headPos += _tos[i]->calldataEncodedSize();
	}
	solAssert(headPos == headSize, "");
	templ("values", values);

	return templ.render();
}

string ABIFunctions::requestedFunctions()
{
	string result;
	for (auto const& f: m_requestedFunctions)
		result += f.second;
	m_requestedFunctions.clear();
	return result;
}

string ABIFunctions::cleanupFunction(Type const& _type, bool _revertOnFailure)
{
	string functionName = string("cleanup_") + (_revertOnFailure ? "revert_" : "assert_") + _type.identifier();
	return createFunction(functionName, [&]() {
		Whiskers templ(R"(
			function <functionName>(value) -> cleaned {
				<body>
			}
		)");
		templ("functionName", functionName);
		switch (_type.category())
		{
		case Type::Category::Integer:
		{
			IntegerType const& type = dynamic_cast<IntegerType const&>(_type);
			if (type.numBits() == 256)
				templ("body", "cleaned := value");
			else if (type.isSigned())
				templ("body", "cleaned := signextend(" + to_string(type.numBits() / 8 - 1) + ", value)");
			else
				templ("body", "cleaned := and(value, " + toCompactHexWithPrefix((u256(1) << type.numBits()) - 1) + ")");
			break;
		}
		case Type::Category::RationalNumber:
			templ("body", "cleaned := value");
			break;
		case Type::Category::Bool:
			templ("body", "cleaned := iszero(iszero(value))");
			break;
		case Type::Category::FixedPoint:
			solUnimplemented("Fixed point types not implemented.");
			break;
		case Type::Category::Array:
			solAssert(false, "Array cleanup requested.");
			break;
		case Type::Category::Struct:
			solAssert(false, "Struct cleanup requested.");
			break;
		case Type::Category::FixedBytes:
		{
			FixedBytesType const& type = dynamic_cast<FixedBytesType const&>(_type);
			if (type.numBytes() == 32)
				templ("body", "cleaned := value");
			else if (type.numBytes() == 0)
				templ("body", "cleaned := 0");
			else
			{
				size_t numBits = type.numBytes() * 8;
				u256 mask = ((u256(1) << numBits) - 1) << (256 - numBits);
				templ("body", "cleaned := and(value, " + toCompactHexWithPrefix(mask) + ")");
			}
			break;
		}
		case Type::Category::Contract:
			templ("body", "cleaned := " + cleanupFunction(IntegerType(120, IntegerType::Modifier::Address)) + "(value)");
			break;
		case Type::Category::Enum:
		{
			size_t members = dynamic_cast<EnumType const&>(_type).numberOfMembers();
			solAssert(members > 0, "empty enum should have caused a parser error.");
			Whiskers w("switch lt(value, <members>) case 0 { <failure> }");
			w("members", to_string(members));
			if (_revertOnFailure)
				w("failure", "revert(0, 0)");
			else
				w("failure", "invalid()");
			templ("body", w.render());
			break;
		}
		default:
			solAssert(false, "Cleanup of type " + _type.identifier() + " requested.");
		}

		return templ.render();
	});
}

string ABIFunctions::conversionFunction(Type const& _from, Type const& _to)
{
	string functionName =
		"convert_" +
		_from.identifier() +
		"_to_" +
		_to.identifier();
	return createFunction(functionName, [&]() {
		Whiskers templ(R"(
			function <functionName>(value) -> converted {
				<body>
			}
		)");
		templ("functionName", functionName);
		string body;
		auto toCategory = _to.category();
		auto fromCategory = _from.category();
		switch (fromCategory)
		{
		case Type::Category::Integer:
		case Type::Category::RationalNumber:
		case Type::Category::Contract:
		{
			if (RationalNumberType const* rational = dynamic_cast<RationalNumberType const*>(&_from))
				solUnimplementedAssert(!rational->isFractional(), "Not yet implemented - FixedPointType.");
			if (toCategory == Type::Category::FixedBytes)
			{
				solAssert(
					fromCategory == Type::Category::Integer || fromCategory == Type::Category::RationalNumber,
					"Invalid conversion to FixedBytesType requested."
				);
				FixedBytesType const& toBytesType = dynamic_cast<FixedBytesType const&>(_to);
				body =
					Whiskers("converted := <shiftLeft>(<clean>(value)")
					("shiftLeft", shiftLeftFunction(256 - toBytesType.numBytes() * 8))
					("clean", cleanupFunction(_from))
					.render();
			}
			else if (toCategory == Type::Category::Enum)
			{
				solAssert(_from.mobileType(), "");
				body =
					Whiskers("converted := <cleanEnum>(<cleanInt>(value))")
					("cleanEnum", cleanupFunction(_to, false))
					// "mobileType()" returns integer type for rational
					("cleanInt", cleanupFunction(*_from.mobileType()))
					.render();
			}
			else if (toCategory == Type::Category::FixedPoint)
			{
				solUnimplemented("Not yet implemented - FixedPointType.");
			}
			else
			{
				solAssert(
					toCategory == Type::Category::Integer ||
					toCategory == Type::Category::Contract,
				"");
				IntegerType const addressType(0, IntegerType::Modifier::Address);
				IntegerType const& to =
					toCategory == Type::Category::Integer ?
					dynamic_cast<IntegerType const&>(_to) :
					addressType;

				// Clean according to the "to" type, except if this is
				// a widening conversion.
				IntegerType const* cleanupType = &to;
				if (fromCategory != Type::Category::RationalNumber)
				{
					IntegerType const& from =
						fromCategory == Type::Category::Integer ?
						dynamic_cast<IntegerType const&>(_from) :
						addressType;
					if (to.numBits() > from.numBits())
						cleanupType = &from;
				}
				body =
					Whiskers("converted := <cleanInt>(value)")
					("cleanInt", cleanupFunction(*cleanupType))
					.render();
			}
			break;
		}
		case Type::Category::Bool:
		{
			solAssert(_from == _to, "Invalid conversion for bool.");
			body =
				Whiskers("converted := <clean>(value)")
				("clean", cleanupFunction(_from))
				.render();
			break;
		}
		case Type::Category::FixedPoint:
			solUnimplemented("Fixed point types not implemented.");
			break;
		case Type::Category::Array:
			solUnimplementedAssert(false, "Array conversion not implemented.");
			break;
		case Type::Category::Struct:
			solUnimplementedAssert(false, "Struct conversion not implemented.");
			break;
		case Type::Category::FixedBytes:
		{
			FixedBytesType const& from = dynamic_cast<FixedBytesType const&>(_from);
			if (toCategory == Type::Category::Integer)
				body =
					Whiskers("converted := <convert>(<shift>(value))")
					("shift", shiftRightFunction(256 - from.numBytes() * 8, false))
					("convert", conversionFunction(IntegerType(from.numBytes() * 8), _to))
					.render();
			else
			{
				// clear for conversion to longer bytes
				solAssert(toCategory == Type::Category::FixedBytes, "Invalid type conversion requested.");
				body =
					Whiskers("converted := <clean>(value)")
					("clean", cleanupFunction(from))
					.render();
			}
			break;
		}
		case Type::Category::Function:
		{
			solUnimplementedAssert(false, "Function conversion not implemented.");
			break;
		}
		case Type::Category::Enum:
		{
			solAssert(toCategory == Type::Category::Integer || _from == _to, "");
			EnumType const& enumType = dynamic_cast<decltype(enumType)>(_from);
			body =
				Whiskers("converted := <clean>(value)")
				("clean", cleanupFunction(enumType))
				.render();
		}
		case Type::Category::Tuple:
		{
			solUnimplementedAssert(false, "Tuple conversion not implemented.");
			break;
		}
		default:
			solAssert(false, "");
		}

		solAssert(!body.empty(), "");
		templ("body", body);
		return templ.render();
	});
}

string ABIFunctions::abiEncodingFunction(
	Type const& _from,
	Type const& _to,
	bool _encodeAsLibraryTypes
)
{
	string functionName =
		"abi_encode_" +
		_from.identifier() +
		"_to_" +
		_to.identifier() +
		(_encodeAsLibraryTypes ? "_lib" : "");
	return createFunction(functionName, [&]() {
		Whiskers templ(R"(
			function <functionName>(value, headStart, headPos, dyn) -> newDyn {
				<body>
			}
		)");
		templ("functionName", functionName);

		string body;
		if (_to.isDynamicallySized())
		{
			if (_from.category() == Type::Category::StringLiteral)
			{
				// TODO this can make use of CODECOPY for large strings once we have that in JULIA
				auto const& strType = dynamic_cast<StringLiteralType const&>(_from);
				Whiskers bodyTempl(R"(
					mstore(headPos, sub(dyn, headStart))
					mstore(dyn, <length>)
					<#word>
						mstore(add(dyn, <offset>), <wordValue>)
					</word>
					newDyn := add(dyn, <overallSize>)
				)");
				string const& value = strType.value();
				size_t words = (value.size() + 31) / 32;
				bodyTempl("overallSize", to_string(32 + words * 32));
				bodyTempl("length", to_string(value.size()));
				vector<map<string, string>> wordParams(words);
				for (size_t i = 0; i < words; ++i)
				{
					wordParams[i]["offset"] = to_string(32 + i * 32);
					wordParams[i]["wordValue"] = "0x" + h256(value.substr(32 * i, 32), h256::AlignLeft).hex();
				}
				bodyTempl("words", wordParams);
				body = bodyTempl.render();
			}
			else
			{
				solAssert(_from.category() == Type::Category::Array, "Unknown dynamic type.");
				auto const& arrayType = dynamic_cast<ArrayType const&>(_from);
				if (arrayType.location() == DataLocation::Storage)
				{
					if (arrayType.isByteArray())
					{
						solUnimplemented("");
					}
					solUnimplemented("");
				}
				else if (arrayType.location() == DataLocation::Memory)
				{
					solUnimplementedAssert(_from == _to, "");
					if (arrayType.isByteArray())
					{
						Whiskers bodyTempl(R"(
							mstore(headPos, sub(dyn, headStart))
							let length := <lengthFun>(value)
							mstore(dyn, length)
							let destPtr := add(dyn, 32)
							let srcPtr := add(value, 32)
							for { let i := 0 } lt(add(i, 32), length) { i := add(i, 32) }
							{
								mstore(add(destPtr, i), mload(add(srcPtr, i))
							}
							switch iszero(length)
							case 0 {

							}
						)");
						bodyTempl("lengthFun", arrayLengthFunction(arrayType));
					}
					Whiskers bodyTempl(R"(
						mstore(headPos, sub(dyn, headStart))
						let length := <lengthFun>(value)
						mstore(dyn, length)
						let destPtr := add(dyn, 32)
						let srcPtr := add(value, 32)
						newDyn := add(destPtr, mul(length, <elementEncodedSize>))
						for { let i := 0 } lt(i, length) { i := add(i, 1) }
						{
							newDyn := <encodeToMemoryFun>(mload(srcPtr), destPtr, destPtr, newDyn)
							srcPtr := add(srcPtr, 32)
							destPtr := add(destPtr, <elementEncodedSize>)
						}
					)");
					solAssert(arrayType.baseType(), "");
					bodyTempl("lengthFun", arrayLengthFunction(arrayType));
					bodyTempl("elementEncodedSize", toCompactHexWithPrefix(arrayType.baseType()->calldataEncodedSize()));
					bodyTempl("encodeToMemoryFun", abiEncodingFunction(
						*arrayType.baseType(),
						*arrayType.baseType(),
						_encodeAsLibraryTypes
					));
					body = bodyTempl.render();
				}
				else
					solUnimplemented("");
			}
		}
		else
		{
			body = "newDyn := dyn\n";
			solUnimplementedAssert(_from.sizeOnStack() == 1, "");
			if (_from.dataStoredIn(DataLocation::Storage) && _to.isValueType())
			{
				// special case: convert storage reference type to value type - this is only
				// possible for library calls where we just forward the storage reference
				solAssert(_encodeAsLibraryTypes, "");
				solAssert(_from.sizeOnStack() == 1, "");
				solAssert(_to == IntegerType(256), "");
				body += "mstore(headPos, value)";
			}
			else if (
				_from.dataStoredIn(DataLocation::Storage) ||
				_from.dataStoredIn(DataLocation::CallData) ||
				_from.category() == Type::Category::StringLiteral ||
				_from.category() == Type::Category::Function
			)
			{
				// This used to delay conversion
				solUnimplemented("");
			}
			else if (dynamic_cast<ArrayType const*>(&_to))
			{
				// This used to perform a conversion first and then call
				// ArrayUtils(m_context).copyArrayToMemory(*arrayType, _padToWordBoundaries);
				solUnimplemented("");
			}
			else if (dynamic_cast<StructType const*>(&_to))
			{
				solUnimplemented("");
			}
			else
			{
				solAssert(_to.isValueType(), "");
				solAssert(_to.calldataEncodedSize() == 32, "");
				if (_from == _to)
					body += "mstore(headPos, " + cleanupFunction(_from) + "(value))\n";
				else
					body += "mstore(headPos, " + conversionFunction(_from, _to) + "(value))\n";
			}
		}
		templ("body", body);
		return templ.render();
	});
}

string ABIFunctions::shiftLeftFunction(size_t _numBits)
{
	string functionName = "shift_left_" + to_string(_numBits);
	return createFunction(functionName, [&]() {
		solAssert(_numBits < 256, "");
		return
			Whiskers(R"(function <functionName>(value) -> newValue {
					newValue := mul(value, <multiplier>)
			})")
			("functionName", functionName)
			("multiplier", (u256(1) << _numBits).str())
			.render();
	});
}

string ABIFunctions::shiftRightFunction(size_t _numBits, bool _signed)
{
	string functionName = "shift_right_" + to_string(_numBits) + (_signed ? "_signed" : "_unsigned");
	return createFunction(functionName, [&]() {
		solAssert(_numBits < 256, "");
		return
			Whiskers(R"(function <functionName>(value) -> newValue {
					newValue := <div>(value, <multiplier>)
			})")
			("functionName", functionName)
			("div", _signed ? "sdiv" : "div")
			("multiplier", (u256(1) << _numBits).str())
			.render();
	});
}

string ABIFunctions::arrayLengthFunction(ArrayType const& _type)
{
	string functionName = "array_length_" + _type.identifier();
	return createFunction(functionName, [&]() {
		Whiskers w(R"(
			function <functionName>(value) -> length {
				<body>
			}
		)");
		w("functionName", functionName);
		string body;
		if (!_type.isDynamicallySized())
			body = "length := " + toCompactHexWithPrefix(_type.length());
		else
		{
			switch (_type.location())
			{
			case DataLocation::CallData:
				solUnimplementedAssert(false, "calldata arrays not yet supported");
				break;
			case DataLocation::Memory:
				body = "length := mload(value)";
				break;
			case DataLocation::Storage:
				if (_type.isByteArray())
				{
					// Retrieve length both for in-place strings and off-place strings:
					// Computes (x & (0x100 * (ISZERO (x & 1)) - 1)) / 2
					// i.e. for short strings (x & 1 == 0) it does (x & 0xff) / 2 and for long strings it
					// computes (x & (-1)) / 2, which is equivalent to just x / 2.
					w("retrieveLength", R"(
						length := sload(value)
						let mask := sub(mul(0x100, iszero(and(length, 1))), 1)
						length := div(and(length, mask), 2)
					)");
				}
				else
					w("retrieveLength", "sload(value)");
				break;
			}
		}
		solAssert(!body.empty(), "");
		w("body", body);
		return w.render();
	});
}

string ABIFunctions::createFunction(string const& _name, function<string ()> const& _creator)
{
	if (!m_requestedFunctions.count(_name))
	{
		auto fun = _creator();
		solAssert(!fun.empty(), "");
		m_requestedFunctions[_name] = fun;
	}
	return _name;
}
