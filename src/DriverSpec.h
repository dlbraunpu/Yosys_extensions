#include "kernel/yosys.h"

#ifndef DRIVER_SPEC_H
#define DRIVER_SPEC_H

// An enhanced version of Yosys::RTLIL::SigSpec.
// It describes collections of constants, cell port bits, and wire bits
// (which represent module input ports): the things that can actually
// drive a signal.  SigSpec represents only wire bits and constants.
// There are also helper structs DriverChunk and DriverBit.


struct DriverBit;
struct DriverSpec;

struct DriverChunk
{
	Yosys::RTLIL::Wire *wire; // Only one of wire and cell will be non-null
	Yosys::RTLIL::Cell *cell;
        Yosys::RTLIL::IdString port;  // Only valid if cell is set.
	std::vector<Yosys::RTLIL::State> data; // only used if wire and cell == nullptr, LSB at index 0
	int width, offset;

	DriverChunk();
	DriverChunk(const Yosys::RTLIL::Const &value);
	DriverChunk(Yosys::RTLIL::Wire *wire);
	DriverChunk(Yosys::RTLIL::Wire *wire, int offset, int width = 1);
	DriverChunk(Yosys::RTLIL::Cell *cell, const Yosys::RTLIL::IdString& port);
	DriverChunk(Yosys::RTLIL::Cell *cell, const Yosys::RTLIL::IdString& port, int offset, int width = 1);
	DriverChunk(const std::string &str);
	DriverChunk(int val, int width = 32);
	DriverChunk(Yosys::RTLIL::State bit, int width = 1);
	DriverChunk(const DriverBit &bit);
	DriverChunk(const DriverChunk &driverchunk);
	DriverChunk &operator =(const DriverChunk &other) = default;

	DriverChunk extract(int offset, int length) const;
	inline int size() const { return width; }
	inline bool is_wire() const { return wire != nullptr; }
	inline bool is_cell() const { return cell != nullptr; }
	inline bool is_object() const { return cell != nullptr || wire != nullptr; }
	inline bool is_data() const { return !is_object(); }

        int object_width() const;  // Width of wire or port (possibly different than our width)

	bool operator <(const DriverChunk &other) const;
	bool operator ==(const DriverChunk &other) const;
	bool operator !=(const DriverChunk &other) const;
};



struct DriverBit
{
	Yosys::RTLIL::Wire *wire; // Only one of wire and cell will be non-null
	Yosys::RTLIL::Cell *cell;
        Yosys::RTLIL::IdString port;  // Only valid if cell is set.
	union {
		Yosys::RTLIL::State data; // used if wire and cell == nullptr
		int offset;        // used if wire or cell != nullptr
	};

	DriverBit();
	DriverBit(Yosys::RTLIL::State bit);
	explicit DriverBit(bool bit);
	DriverBit(Yosys::RTLIL::Wire *wire);
	DriverBit(Yosys::RTLIL::Wire *wire, int offset);
	DriverBit(Yosys::RTLIL::Cell *cell, const Yosys::RTLIL::IdString& port);
	DriverBit(Yosys::RTLIL::Cell *cell, const Yosys::RTLIL::IdString& port, int offset);
	DriverBit(const DriverChunk &chunk);
	DriverBit(const DriverChunk &chunk, int index);
	DriverBit(const DriverSpec &sig);
	DriverBit(const DriverBit &driverbit) = default;
	DriverBit &operator =(const DriverBit &other) = default;

	inline bool is_wire() const { return wire != nullptr; }
	inline bool is_cell() const { return cell != nullptr; }
	inline bool is_object() const { return cell != nullptr || wire != nullptr; }
	inline bool is_data() const { return !is_object(); }

	bool operator <(const DriverBit &other) const;
	bool operator ==(const DriverBit &other) const;
	bool operator !=(const DriverBit &other) const;
	unsigned int hash() const;
};

struct DriverSpecIterator : public std::iterator<std::input_iterator_tag, DriverSpec>
{
	DriverSpec *sig_p;
	int index;

	inline DriverBit &operator*() const;
	inline bool operator!=(const DriverSpecIterator &other) const { return index != other.index; }
	inline bool operator==(const DriverSpecIterator &other) const { return index == other.index; }
	inline void operator++() { index++; }
};

struct DriverSpecConstIterator : public std::iterator<std::input_iterator_tag, DriverSpec>
{
	const DriverSpec *sig_p;
	int index;

	inline const DriverBit &operator*() const;
	inline bool operator!=(const DriverSpecConstIterator &other) const { return index != other.index; }
	inline bool operator==(const DriverSpecIterator &other) const { return index == other.index; }
	inline void operator++() { index++; }
};


struct DriverSpec
{
private:
	int width_;
	unsigned long hash_;
	std::vector<DriverChunk> chunks_; // LSB at index 0
	std::vector<DriverBit> bits_; // LSB at index 0

	void pack() const;
	void unpack() const;
	void updhash() const;

	inline bool packed() const {
		return bits_.empty();
	}

	inline void inline_unpack() const {
		if (!chunks_.empty())
			unpack();
	}

	// Only used by Module::remove(const pool<Wire*> &wires)
	// but cannot be more specific as it isn't yet declared
	friend struct Yosys::RTLIL::Module;

public:
	DriverSpec();
	DriverSpec(const DriverSpec &other);
	DriverSpec(std::initializer_list<DriverSpec> parts);
	DriverSpec &operator=(const DriverSpec &other);

	DriverSpec(const Yosys::RTLIL::Const &value);
	DriverSpec(const DriverChunk &chunk);
	DriverSpec(Yosys::RTLIL::Wire *wire);
	DriverSpec(Yosys::RTLIL::Wire *wire, int offset, int width = 1);
	DriverSpec(Yosys::RTLIL::Cell *cell, const Yosys::RTLIL::IdString& port);
	DriverSpec(Yosys::RTLIL::Cell *cell, const Yosys::RTLIL::IdString& port, int offset, int width = 1);
	DriverSpec(const std::string &str);
	DriverSpec(int val, int width = 32);
	DriverSpec(Yosys::RTLIL::State bit, int width = 1);
	DriverSpec(const DriverBit &bit, int width = 1);
	DriverSpec(const std::vector<DriverChunk> &chunks);
	DriverSpec(const std::vector<DriverBit> &bits);
	DriverSpec(const Yosys::pool<DriverBit> &bits);
	DriverSpec(const std::set<DriverBit> &bits);
	explicit DriverSpec(bool bit);

	DriverSpec(DriverSpec &&other) {
		width_ = other.width_;
		hash_ = other.hash_;
		chunks_ = std::move(other.chunks_);
		bits_ = std::move(other.bits_);
	}

	const DriverSpec &operator=(DriverSpec &&other) {
		width_ = other.width_;
		hash_ = other.hash_;
		chunks_ = std::move(other.chunks_);
		bits_ = std::move(other.bits_);
		return *this;
	}

	size_t get_hash() const {
		if (!hash_) hash();
		return hash_;
	}

	inline const std::vector<DriverChunk> &chunks() const { pack(); return chunks_; }
	inline const std::vector<DriverBit> &bits() const { inline_unpack(); return bits_; }

	inline int size() const { return width_; }
	inline bool empty() const { return width_ == 0; }

	inline DriverBit &operator[](int index) { inline_unpack(); return bits_.at(index); }
	inline const DriverBit &operator[](int index) const { inline_unpack(); return bits_.at(index); }

	inline DriverSpecIterator begin() { DriverSpecIterator it; it.sig_p = this; it.index = 0; return it; }
	inline DriverSpecIterator end() { DriverSpecIterator it; it.sig_p = this; it.index = width_; return it; }

	inline DriverSpecConstIterator begin() const { DriverSpecConstIterator it; it.sig_p = this; it.index = 0; return it; }
	inline DriverSpecConstIterator end() const { DriverSpecConstIterator it; it.sig_p = this; it.index = width_; return it; }

	void sort();
	void sort_and_unify();

	void replace(const DriverSpec &pattern, const DriverSpec &with);
	void replace(const DriverSpec &pattern, const DriverSpec &with, DriverSpec *other) const;

	void replace(const Yosys::dict<DriverBit, DriverBit> &rules);
	void replace(const Yosys::dict<DriverBit, DriverBit> &rules, DriverSpec *other) const;

	void replace(const std::map<DriverBit, DriverBit> &rules);
	void replace(const std::map<DriverBit, DriverBit> &rules, DriverSpec *other) const;

	void replace(int offset, const DriverSpec &with);

	void remove(const DriverSpec &pattern);
	void remove(const DriverSpec &pattern, DriverSpec *other) const;
	void remove2(const DriverSpec &pattern, DriverSpec *other);

	void remove(const Yosys::pool<DriverBit> &pattern);
	void remove(const Yosys::pool<DriverBit> &pattern, DriverSpec *other) const;
	void remove2(const Yosys::pool<DriverBit> &pattern, DriverSpec *other);
	void remove2(const std::set<DriverBit> &pattern, DriverSpec *other);

	void remove(int offset, int length = 1);
	void remove_const();

	DriverSpec extract(const DriverSpec &pattern, const DriverSpec *other = nullptr) const;
	DriverSpec extract(const Yosys::pool<DriverBit> &pattern, const DriverSpec *other = nullptr) const;
	DriverSpec extract(int offset, int length = 1) const;
	DriverSpec extract_end(int offset) const { return extract(offset, width_ - offset); }

	void append(const DriverSpec &signal);
	inline void append(Yosys::RTLIL::Wire *wire) { append(DriverSpec(wire)); }
	inline void append(Yosys::RTLIL::Cell *cell, const Yosys::RTLIL::IdString& port) { append(DriverSpec(cell, port)); }
	inline void append(const DriverChunk &chunk) { append(DriverSpec(chunk)); }
	inline void append(const Yosys::RTLIL::Const &const_) { append(DriverSpec(const_)); }

	void append(const DriverBit &bit);
	inline void append(Yosys::RTLIL::State state) { append(DriverBit(state)); }
	inline void append(bool bool_) { append(DriverBit(bool_)); }

	void extend_u0(int width, bool is_signed = false);

	DriverSpec repeat(int num) const;

	void reverse() { inline_unpack(); std::reverse(bits_.begin(), bits_.end()); }

	bool operator <(const DriverSpec &other) const;
	bool operator ==(const DriverSpec &other) const;
	inline bool operator !=(const DriverSpec &other) const { return !(*this == other); }

	bool is_wire() const;
	bool is_cell() const;
	bool is_chunk() const;
	inline bool is_bit() const { return width_ == 1; }

	bool is_fully_const() const;
	bool is_fully_zero() const;
	bool is_fully_ones() const;
	bool is_fully_def() const;
	bool is_fully_undef() const;
	bool has_const() const;
	bool has_marked_bits() const;
	bool is_onehot(int *pos = nullptr) const;

	bool as_bool() const;
	int as_int(bool is_signed = false) const;
	std::string as_string() const;
	Yosys::RTLIL::Const as_const() const;
	Yosys::RTLIL::Wire *as_wire() const;
        // as_cell() returns both cell and port
	Yosys::RTLIL::Cell *as_cell(Yosys::RTLIL::IdString& port) const;
	DriverChunk as_chunk() const;
	DriverBit as_bit() const;

	bool match(const char* pattern) const;

	std::set<DriverBit> to_driverbit_set() const;
        Yosys::pool<DriverBit> to_driverbit_pool() const;
	std::vector<DriverBit> to_driverbit_vector() const;
	std::map<DriverBit, DriverBit> to_driverbit_map(const DriverSpec &other) const;
        Yosys::dict<DriverBit, DriverBit> to_driverbit_dict(const DriverSpec &other) const;

	operator std::vector<DriverChunk>() const { return chunks(); }
	operator std::vector<DriverBit>() const { return bits(); }
	const DriverBit &at(int offset, const DriverBit &defval) { return offset < width_ ? (*this)[offset] : defval; }

	unsigned int hash() const { if (!hash_) updhash(); return hash_; };

#ifndef NDEBUG
	void check(Yosys::RTLIL::Module *mod = nullptr) const;
#else
	void check(Yosys::RTLIL::Module *mod = nullptr) const { (void)mod; }
#endif
};


inline DriverBit::DriverBit() : wire(nullptr), cell(nullptr), data(Yosys::RTLIL::State::S0) { }
inline DriverBit::DriverBit(Yosys::RTLIL::State bit) : wire(nullptr), cell(nullptr), data(bit) { }
inline DriverBit::DriverBit(bool bit) : wire(nullptr), cell(nullptr), data(bit ? Yosys::RTLIL::State::S1 : Yosys::RTLIL::State::S0) { }
inline DriverBit::DriverBit(Yosys::RTLIL::Wire *wire) : wire(wire), cell(nullptr), offset(0) { log_assert(wire && wire->width == 1); }
inline DriverBit::DriverBit(Yosys::RTLIL::Wire *wire, int offset) : wire(wire), cell(nullptr), offset(offset) { log_assert(wire != nullptr); }
inline DriverBit::DriverBit(const DriverChunk &chunk) : wire(chunk.wire) { log_assert(chunk.width == 1); if (wire) offset = chunk.offset; else data = chunk.data[0]; }
inline DriverBit::DriverBit(const DriverChunk &chunk, int index) : wire(chunk.wire) { if (wire) offset = chunk.offset + index; else data = chunk.data[index]; }

inline bool DriverBit::operator<(const DriverBit &other) const {
	if (wire == other.wire)
		return wire ? (offset < other.offset) : (data < other.data);
	if (wire != nullptr && other.wire != nullptr)
		return wire->name < other.wire->name;
	return (wire != nullptr) < (other.wire != nullptr);
}

inline bool DriverBit::operator==(const DriverBit &other) const {
	return (wire == other.wire) && (wire ? (offset == other.offset) : (data == other.data));
}

inline bool DriverBit::operator!=(const DriverBit &other) const {
	return (wire != other.wire) || (wire ? (offset != other.offset) : (data != other.data));
}

inline unsigned int DriverBit::hash() const {
	if (wire)
		return Yosys::hashlib::mkhash_add(wire->name.hash(), offset);
        else if (cell)
		return Yosys::hashlib::mkhash_add(cell->name.hash(), Yosys::hashlib::mkhash_add(port.hash(), offset));
	return data;
}

inline DriverBit &DriverSpecIterator::operator*() const {
	return (*sig_p)[index];
}

inline const DriverBit &DriverSpecConstIterator::operator*() const {
	return (*sig_p)[index];
}

inline DriverBit::DriverBit(const DriverSpec &sig) {
	log_assert(sig.size() == 1 && sig.chunks().size() == 1);
	*this = DriverBit(sig.chunks().front());
}


#endif
