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

#pragma once

#include <libsolidity/ast/ASTForward.h>

#include <vector>
#include <functional>
#include <map>

namespace dev {
namespace solidity {

class Type;
class ArrayType;
using TypePointer = std::shared_ptr<Type const>;
using TypePointers = std::vector<TypePointer>;

///
/// Class to generate encoding and decoding functions. Also maintains a collection
/// of "functions to be generated" in order to avoid generating the same function
/// multiple times.
///
/// Make sure to include the result of ``requestedFunctions()`` to a block that
/// is visible from the code that was generated here.
class ABIFunctions
{
public:
	~ABIFunctions();

	/// @returns TODO
	std::string tupleEncoder(
		TypePointers const& _givenTypes,
		TypePointers const& _targetTypes,
		bool _encodeAsLibraryTypes = false
	);

	std::string requestedFunctions();

private:
	/// @returns the name of the cleanup function for the given type and
	/// adds its implementation to the requested functions.
	/// @param _revertOnFailure if true, causes revert on invalid data,
	/// otherwise an assertion failure.
	std::string cleanupFunction(Type const& _type, bool _revertOnFailure = false);

	/// @returns the name of the function that converts a value of type @a _from
	/// to a value of type @a _to. The resulting vale is guaranteed to be in range
	/// (i.e. "clean"). Asserts on failure.
	std::string conversionFunction(Type const& _from, Type const& _to);

	// @returns the name of the ABI encoding function with the given type
	// and queues the generation of the function to the requested functions.
	std::string abiEncodingFunction(
		Type const& _givenType,
		Type const& _targetType,
		bool _encodeAsLibraryTypes
	);

	// @returns the name of the ABI encoding function with the given type
	// and queues the generation of the function to the requested functions.
	// Case for _givenType being a string literal
	std::string abiEncodingFunctionStringLiteral(
		Type const& _givenType,
		Type const& _targetType,
		bool _encodeAsLibraryTypes
	);


	std::string shiftLeftFunction(size_t _numBits);
	std::string shiftRightFunction(size_t _numBits, bool _signed);

	std::string arrayLengthFunction(ArrayType const& _Type);

	/// Helper function that uses @a _creator to create a function and add it to
	/// @a m_requestedFunctions if it has not been created yet and returns @a _name in both
	/// cases.
	std::string createFunction(std::string const& _name, std::function<std::string()> const& _creator);

	/// Map from function name to code for a multi-use function.
	std::map<std::string, std::string> m_requestedFunctions;
};

}
}
