#pragma once

namespace llvm {
	class Instruction;
	class raw_ostream;
	class Twine;
	class Value;
} // namespace llvm


class Diagnostic {
public:
	Diagnostic();

	llvm::raw_ostream &os() { return OS; }

	void bug(const llvm::Twine &);
	void classify(llvm::Value *);

	void backtrace(llvm::Instruction *);
	void status(int);

	template <typename T> Diagnostic &
	operator <<(const T &Val) {
		OS << Val;
		return *this;
	}

private:
	llvm::raw_ostream &OS;
};
