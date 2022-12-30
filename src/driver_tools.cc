#include "driver_tools.h"


#include "kernel/rtlil.h"
#include "backends/rtlil/rtlil_backend.h"


USING_YOSYS_NAMESPACE  // Does "using namespace"


DriverBit::DriverBit(RTLIL::Cell *cell, const RTLIL::IdString& port) :
        wire(nullptr), cell(cell), port(port), offset(0)
{
        log_assert(cell != nullptr && !port.empty() &&
                   cell->hasPort(port) && cell->getPort(port).size() == 1);
}


DriverBit::DriverBit(RTLIL::Cell *cell, const RTLIL::IdString& port, int offset) :
        wire(nullptr), cell(cell), port(port), offset(offset)
{
        log_assert(cell != nullptr && !port.empty() && cell->hasPort(port));
}

DriverBit::DriverBit(const DriverChunk &chunk) :
        wire(chunk.wire), cell(chunk.cell), port(chunk.port)
{
        log_assert(chunk.width == 1);
        if (chunk.is_object()) offset = chunk.offset; else data = chunk.data[0];
}

DriverBit::DriverBit(const DriverChunk &chunk, int index) :
        wire(chunk.wire), cell(chunk.cell), port(chunk.port)
{
        if (chunk.is_object()) offset = chunk.offset + index; else data = chunk.data[index];
}


// If neither thing has an object, this return false
bool DriverChunk::has_same_object(const DriverBit& bit) const
{
        return is_object() &&
               (bit.wire == wire && bit.cell == cell && bit.port == port);
}


DriverChunk::DriverChunk()
{
	wire = nullptr;
        cell = nullptr;
	width = 0;
	offset = 0;
}

DriverChunk::DriverChunk(const RTLIL::Const &value)
{
	wire = nullptr;
        cell = nullptr;
	data = value.bits;
	width = GetSize(data);
	offset = 0;
}

DriverChunk::DriverChunk(RTLIL::Wire *wire)
{
	log_assert(wire != nullptr);
	this->wire = wire;
        this->cell = nullptr;
	this->width = wire->width;
	this->offset = 0;
}

DriverChunk::DriverChunk(RTLIL::Wire *wire, int offset, int width)
{
        // Doug:  check that offset/width are not beyond wire width?
	log_assert(wire != nullptr);
	this->wire = wire;
        this->cell = nullptr;
	this->width = width;
	this->offset = offset;
}

DriverChunk::DriverChunk(RTLIL::Cell *cell, const RTLIL::IdString& port)
{
	log_assert(cell != nullptr);
	log_assert(!port.empty());
        log_assert(cell->hasPort(port));
	this->wire = nullptr;
        this->cell = cell;
        this->port = port;
	this->width = cell->getPort(port).size();
	this->offset = 0;
}

DriverChunk::DriverChunk(RTLIL::Cell *cell, const RTLIL::IdString& port, int offset, int width)
{
        // Doug:  check that offset/width are not beyond port width?
	log_assert(cell != nullptr);
	log_assert(!port.empty());
        log_assert(cell->hasPort(port));
	this->wire = nullptr;
        this->cell = nullptr;
	this->width = width;
	this->offset = offset;
}


DriverChunk::DriverChunk(const std::string &str)
{
	wire = nullptr;
        cell = nullptr;
	data = RTLIL::Const(str).bits;
	width = GetSize(data);
	offset = 0;
}

DriverChunk::DriverChunk(int val, int width)
{
	wire = nullptr;
        cell = nullptr;
	data = RTLIL::Const(val, width).bits;
	this->width = GetSize(data);
	offset = 0;
}

DriverChunk::DriverChunk(RTLIL::State bit, int width)
{
	wire = nullptr;
        cell = nullptr;
	data = RTLIL::Const(bit, width).bits;
	this->width = GetSize(data);
	offset = 0;
}

DriverChunk::DriverChunk(const DriverBit &bit)
{
	wire = bit.wire;
        cell = bit.cell;
        port = bit.port;
	offset = 0;
	if (is_data())
		data = RTLIL::Const(bit.data).bits;
	else
		offset = bit.offset;
	width = 1;
}

DriverChunk::DriverChunk(const DriverChunk &sigchunk)
{
	*this = sigchunk;
}

DriverChunk DriverChunk::extract(int offset, int length) const
{
	DriverChunk ret;
	if (wire) {
		ret.wire = wire;
		ret.offset = this->offset + offset;
		ret.width = length;
        } else if (cell) {
		ret.cell = cell;
		ret.port = port;
		ret.offset = this->offset + offset;
		ret.width = length;
	} else {
		for (int i = 0; i < length; i++)
			ret.data.push_back(data[offset+i]);
		ret.width = length;
	}
	return ret;
}

bool DriverChunk::operator <(const DriverChunk &other) const
{
	if (wire && other.wire)
		if (wire->name != other.wire->name)
			return wire->name < other.wire->name;

	if (wire != other.wire)
		return wire < other.wire;

	if (cell && other.cell)
		if (cell->name != other.cell->name)
			return cell->name < other.cell->name;  

	if (cell != other.cell)
		return cell < other.cell;

        if (port != other.port) 
                return port < other.port;  

	if (offset != other.offset)
		return offset < other.offset;

	if (width != other.width)
		return width < other.width;

	return data < other.data;
}

bool DriverChunk::operator ==(const DriverChunk &other) const
{
	return wire == other.wire && cell == other.cell && port == other.port &&
               width == other.width && offset == other.offset && data == other.data;
}

bool DriverChunk::operator !=(const DriverChunk &other) const
{
	if (*this == other)
		return false;
	return true;
}


// Width of wire or port (possibly different than our width)
int DriverChunk::object_width() const
{
  log_assert(is_object());
  if (is_wire()) {
    return wire->width;
  } else {
    return cell->getPort(port).size();
  }
}



DriverSpec::DriverSpec()
{
	width_ = 0;
	hash_ = 0;
}

DriverSpec::DriverSpec(const DriverSpec &other)
{
	*this = other;
}

DriverSpec::DriverSpec(std::initializer_list<DriverSpec> parts)
{
	cover("driverspec.init.list");

	width_ = 0;
	hash_ = 0;

	log_assert(parts.size() > 0);
	auto ie = parts.begin();
	auto it = ie + parts.size() - 1;
	while (it >= ie)
		append(*it--);
}

DriverSpec &DriverSpec::operator=(const DriverSpec &other)
{
	cover("driverspec.assign");

	width_ = other.width_;
	hash_ = other.hash_;
	chunks_ = other.chunks_;
	bits_ = other.bits_;
	return *this;
}

DriverSpec::DriverSpec(const RTLIL::Const &value)
{
	cover("driverspec.init.const");

	if (GetSize(value) != 0) {
		chunks_.emplace_back(value);
		width_ = chunks_.back().width;
	} else {
		width_ = 0;
	}
	hash_ = 0;
	check();
}

DriverSpec::DriverSpec(const DriverChunk &chunk)
{
	cover("driverspec.init.chunk");

	if (chunk.width != 0) {
		chunks_.emplace_back(chunk);
		width_ = chunks_.back().width;
	} else {
		width_ = 0;
	}
	hash_ = 0;
	check();
}

DriverSpec::DriverSpec(RTLIL::Wire *wire)
{
	cover("driverspec.init.wire");

	if (wire->width != 0) {
		chunks_.emplace_back(wire);
		width_ = chunks_.back().width;
	} else {
		width_ = 0;
	}
	hash_ = 0;
	check();
}

DriverSpec::DriverSpec(RTLIL::Wire *wire, int offset, int width)
{
	cover("driverspec.init.wire_part");

	if (width != 0) {
		chunks_.emplace_back(wire, offset, width);
		width_ = chunks_.back().width;
	} else {
		width_ = 0;
	}
	hash_ = 0;
	check();
}


DriverSpec::DriverSpec(RTLIL::Cell *cell, const RTLIL::IdString& port)
{
	cover("driverspec.init.wire");
        log_assert(cell && cell->hasPort(port));

	if (cell->getPort(port).size() != 0) {
		chunks_.emplace_back(cell, port);
		width_ = chunks_.back().width;
	} else {
		width_ = 0;
	}
	hash_ = 0;
	check();
}

DriverSpec::DriverSpec(RTLIL::Cell *cell, const RTLIL::IdString& port, int offset, int width)
{
	cover("driverspec.init.wire_part");
        log_assert(cell && cell->hasPort(port));

	if (width != 0) {
		chunks_.emplace_back(cell, port, offset, width);
		width_ = chunks_.back().width;
	} else {
		width_ = 0;
	}
	hash_ = 0;
	check();
}

DriverSpec::DriverSpec(const std::string &str)
{
	cover("driverspec.init.str");

	if (str.size() != 0) {
		chunks_.emplace_back(str);
		width_ = chunks_.back().width;
	} else {
		width_ = 0;
	}
	hash_ = 0;
	check();
}

DriverSpec::DriverSpec(int val, int width)
{
	cover("driverspec.init.int");

	if (width != 0)
		chunks_.emplace_back(val, width);
	width_ = width;
	hash_ = 0;
	check();
}

DriverSpec::DriverSpec(RTLIL::State bit, int width)
{
	cover("driverspec.init.state");

	if (width != 0)
		chunks_.emplace_back(bit, width);
	width_ = width;
	hash_ = 0;
	check();
}

DriverSpec::DriverSpec(const DriverBit &bit, int width)
{
	cover("driverspec.init.bit");

	if (width != 0) {
		if (bit.wire == nullptr && bit.cell == nullptr)
			chunks_.emplace_back(bit.data, width);
		else
			for (int i = 0; i < width; i++)
				chunks_.push_back(bit);
	}
	width_ = width;
	hash_ = 0;
	check();
}

DriverSpec::DriverSpec(const std::vector<DriverChunk> &chunks)
{
	cover("driverspec.init.stdvec_chunks");

	width_ = 0;
	hash_ = 0;
	for (const auto &c : chunks)
		append(c);
	check();
}

DriverSpec::DriverSpec(const std::vector<DriverBit> &bits)
{
	cover("driverspec.init.stdvec_bits");

	width_ = 0;
	hash_ = 0;
	for (const auto &bit : bits)
		append(bit);
	check();
}

DriverSpec::DriverSpec(const pool<DriverBit> &bits)
{
	cover("driverspec.init.pool_bits");

	width_ = 0;
	hash_ = 0;
	for (const auto &bit : bits)
		append(bit);
	check();
}

DriverSpec::DriverSpec(const std::set<DriverBit> &bits)
{
	cover("driverspec.init.stdset_bits");

	width_ = 0;
	hash_ = 0;
	for (const auto &bit : bits)
		append(bit);
	check();
}

DriverSpec::DriverSpec(bool bit)
{
	cover("driverspec.init.bool");

	width_ = 0;
	hash_ = 0;
	append(DriverBit(bit));
	check();
}

void DriverSpec::pack() const
{
	DriverSpec *that = (DriverSpec*)this;

	if (that->bits_.empty())
		return;

	cover("driverspec.convert.pack");
	log_assert(that->chunks_.empty());

	std::vector<DriverBit> old_bits;
	old_bits.swap(that->bits_);

	DriverChunk *last = nullptr;
	int last_end_offset = 0;

	for (auto &bit : old_bits) {
		if (last) {
                        if (bit.is_data() && last->is_data()) {
                                last->data.push_back(bit.data);
                                last->width++;
                                continue;
                        } else if (last->has_same_object(bit) && last_end_offset == bit.offset) {
                                last_end_offset++;
                                last->width++;
                                continue;
                        }
                }
		that->chunks_.push_back(bit);
		last = &that->chunks_.back();
		last_end_offset = bit.offset + 1;
	}

	check();
}

void DriverSpec::unpack() const
{
	DriverSpec *that = (DriverSpec*)this;

	if (that->chunks_.empty())
		return;

	cover("driverspec.convert.unpack");
	log_assert(that->bits_.empty());

	that->bits_.reserve(that->width_);
	for (auto &c : that->chunks_)
		for (int i = 0; i < c.width; i++)
			that->bits_.emplace_back(c, i);

	that->chunks_.clear();
	that->hash_ = 0;
}

void DriverSpec::updhash() const
{
	DriverSpec *that = (DriverSpec*)this;

	if (that->hash_ != 0)
		return;

	cover("driverspec.hash");
	that->pack();

	that->hash_ = mkhash_init;
	for (auto &c : that->chunks_)
		if (c.wire == nullptr && c.cell == nullptr) {
			for (auto &v : c.data)
				that->hash_ = mkhash(that->hash_, v);
		} else if (c.cell == nullptr) {
                        // A wire
			that->hash_ = mkhash(that->hash_, c.wire->name.index_);
			that->hash_ = mkhash(that->hash_, c.offset);
			that->hash_ = mkhash(that->hash_, c.width);
		} else {
                        // A cell/port
			that->hash_ = mkhash(that->hash_, c.cell->name.index_);
			that->hash_ = mkhash(that->hash_, c.port.index_);
			that->hash_ = mkhash(that->hash_, c.offset);
			that->hash_ = mkhash(that->hash_, c.width);
		}

	if (that->hash_ == 0)
		that->hash_ = 1;
}

void DriverSpec::sort()
{
	unpack();
	cover("driverspec.sort");
	std::sort(bits_.begin(), bits_.end());
}

void DriverSpec::sort_and_unify()
{
	unpack();
	cover("driverspec.sort_and_unify");

	// A copy of the bits vector is used to prevent duplicating the logic from
	// DriverSpec::DriverSpec(std::vector<DriverBit>).  This incurrs an extra copy but
	// that isn't showing up as significant in profiles.
	std::vector<DriverBit> unique_bits = bits_;
	std::sort(unique_bits.begin(), unique_bits.end());
	auto last = std::unique(unique_bits.begin(), unique_bits.end());
	unique_bits.erase(last, unique_bits.end());

	*this = unique_bits;
}

void DriverSpec::replace(const DriverSpec &pattern, const DriverSpec &with)
{
	replace(pattern, with, this);
}

void DriverSpec::replace(const DriverSpec &pattern, const DriverSpec &with, DriverSpec *other) const
{
	log_assert(other != nullptr);
	log_assert(width_ == other->width_);
	log_assert(pattern.width_ == with.width_);

	pattern.unpack();
	with.unpack();
	unpack();
	other->unpack();

	for (int i = 0; i < GetSize(pattern.bits_); i++) {
		if (pattern.bits_[i].wire != nullptr || pattern.bits_[i].cell != nullptr) {
			for (int j = 0; j < GetSize(bits_); j++) {
				if (bits_[j] == pattern.bits_[i]) {
					other->bits_[j] = with.bits_[i];
				}
			}
		}
	}

	other->check();
}

void DriverSpec::replace(const dict<DriverBit, DriverBit> &rules)
{
	replace(rules, this);
}

void DriverSpec::replace(const dict<DriverBit, DriverBit> &rules, DriverSpec *other) const
{
	cover("driverspec.replace_dict");

	log_assert(other != nullptr);
	log_assert(width_ == other->width_);

	if (rules.empty()) return;
	unpack();
	other->unpack();

	for (int i = 0; i < GetSize(bits_); i++) {
		auto it = rules.find(bits_[i]);
		if (it != rules.end())
			other->bits_[i] = it->second;
	}

	other->check();
}

void DriverSpec::replace(const std::map<DriverBit, DriverBit> &rules)
{
	replace(rules, this);
}

void DriverSpec::replace(const std::map<DriverBit, DriverBit> &rules, DriverSpec *other) const
{
	cover("driverspec.replace_map");

	log_assert(other != nullptr);
	log_assert(width_ == other->width_);

	if (rules.empty()) return;
	unpack();
	other->unpack();

	for (int i = 0; i < GetSize(bits_); i++) {
		auto it = rules.find(bits_[i]);
		if (it != rules.end())
			other->bits_[i] = it->second;
	}

	other->check();
}

void DriverSpec::remove(const DriverSpec &pattern)
{
	remove2(pattern, nullptr);
}

void DriverSpec::remove(const DriverSpec &pattern, DriverSpec *other) const
{
	DriverSpec tmp = *this;
	tmp.remove2(pattern, other);
}

void DriverSpec::remove2(const DriverSpec &pattern, DriverSpec *other)
{
	if (other)
		cover("driverspec.remove_other");
	else
		cover("driverspec.remove");

	unpack();
	if (other != nullptr) {
		log_assert(width_ == other->width_);
		other->unpack();
	}

	for (int i = GetSize(bits_) - 1; i >= 0; i--)
	{
                DriverBit& b = bits_[i];  // for conciseness

		if (!b.is_object()) continue;

		for (auto &pchunk : pattern.chunks())
			if ((b.wire == pchunk.wire || (b.cell == pchunk.cell && b.port == pchunk.port)) &&
				b.offset >= pchunk.offset &&
				b.offset < pchunk.offset + pchunk.width) {
				bits_.erase(bits_.begin() + i);
				width_--;
				if (other != nullptr) {
					other->bits_.erase(other->bits_.begin() + i);
					other->width_--;
				}
				break;
			}
	}

	check();
}

void DriverSpec::remove(const pool<DriverBit> &pattern)
{
	remove2(pattern, nullptr);
}

void DriverSpec::remove(const pool<DriverBit> &pattern, DriverSpec *other) const
{
	DriverSpec tmp = *this;
	tmp.remove2(pattern, other);
}

void DriverSpec::remove2(const pool<DriverBit> &pattern, DriverSpec *other)
{
	if (other)
		cover("driverspec.remove_other");
	else
		cover("driverspec.remove");

	unpack();

	if (other != nullptr) {
		log_assert(width_ == other->width_);
		other->unpack();
	}

	for (int i = GetSize(bits_) - 1; i >= 0; i--) {
		if (bits_[i].is_object() && pattern.count(bits_[i])) {
			bits_.erase(bits_.begin() + i);
			width_--;
			if (other != nullptr) {
				other->bits_.erase(other->bits_.begin() + i);
				other->width_--;
			}
		}
	}

	check();
}

void DriverSpec::remove2(const std::set<DriverBit> &pattern, DriverSpec *other)
{
	if (other)
		cover("driverspec.remove_other");
	else
		cover("driverspec.remove");

	unpack();

	if (other != nullptr) {
		log_assert(width_ == other->width_);
		other->unpack();
	}

	for (int i = GetSize(bits_) - 1; i >= 0; i--) {
		if (bits_[i].is_object() && pattern.count(bits_[i])) {
			bits_.erase(bits_.begin() + i);
			width_--;
			if (other != nullptr) {
				other->bits_.erase(other->bits_.begin() + i);
				other->width_--;
			}
		}
	}

	check();
}


static bool extractable(const DriverBit& bit, const DriverChunk& chunk)
{
        return chunk.has_same_object(bit) &&
                bit.offset >= chunk.offset &&
                bit.offset < chunk.offset + chunk.width;
}


DriverSpec DriverSpec::extract(const DriverSpec &pattern, const DriverSpec *other) const
{
	if (other)
		cover("driverspec.extract_other");
	else
		cover("driverspec.extract");

	log_assert(other == nullptr || width_ == other->width_);

	DriverSpec ret;
	std::vector<DriverBit> bits_match = to_driverbit_vector();

	for (auto& pattern_chunk : pattern.chunks()) {
		if (other) {
			std::vector<DriverBit> bits_other = other->to_driverbit_vector();
			for (int i = 0; i < width_; i++)
                                // Doug: Simplified!
                                if (extractable(bits_match[i], pattern_chunk))
					ret.append(bits_other[i]);
		} else {
			for (int i = 0; i < width_; i++)
                                if (extractable(bits_match[i], pattern_chunk))
					ret.append(bits_match[i]);
		}
	}

	ret.check();
	return ret;
}

DriverSpec DriverSpec::extract(const pool<DriverBit> &pattern, const DriverSpec *other) const
{
	if (other)
		cover("driverspec.extract_other");
	else
		cover("driverspec.extract");

	log_assert(other == nullptr || width_ == other->width_);

	std::vector<DriverBit> bits_match = to_driverbit_vector();
	DriverSpec ret;

	if (other) {
		std::vector<DriverBit> bits_other = other->to_driverbit_vector();
		for (int i = 0; i < width_; i++)
			if (bits_match[i].is_object() && pattern.count(bits_match[i]))
				ret.append(bits_other[i]);
	} else {
		for (int i = 0; i < width_; i++)
			if (bits_match[i].is_object() && pattern.count(bits_match[i]))
				ret.append(bits_match[i]);
	}

	ret.check();
	return ret;
}

void DriverSpec::replace(int offset, const DriverSpec &with)
{
	cover("driverspec.replace_pos");

	unpack();
	with.unpack();

	log_assert(offset >= 0);
	log_assert(with.width_ >= 0);
	log_assert(offset+with.width_ <= width_);

	for (int i = 0; i < with.width_; i++)
		bits_.at(offset + i) = with.bits_.at(i);

	check();
}

void DriverSpec::remove_const()
{
	if (packed())
	{
		cover("driverspec.remove_const.packed");

		std::vector<DriverChunk> new_chunks;
		new_chunks.reserve(GetSize(chunks_));

		width_ = 0;
		for (auto &chunk : chunks_)
			if (chunk.is_object()) {
				if (!new_chunks.empty() &&
					new_chunks.back().wire == chunk.wire &&
					new_chunks.back().cell == chunk.cell &&
					new_chunks.back().port == chunk.port &&
					new_chunks.back().offset + new_chunks.back().width == chunk.offset) {
					new_chunks.back().width += chunk.width;
				} else {
					new_chunks.push_back(chunk);
				}
				width_ += chunk.width;
			}

		chunks_.swap(new_chunks);
	}
	else
	{
		cover("driverspec.remove_const.unpacked");

		std::vector<DriverBit> new_bits;
		new_bits.reserve(width_);

		for (auto &bit : bits_)
			if (bit.is_object())
				new_bits.push_back(bit);

		bits_.swap(new_bits);
		width_ = bits_.size();
	}

	check();
}

void DriverSpec::remove(int offset, int length)
{
	cover("driverspec.remove_pos");

	unpack();

	log_assert(offset >= 0);
	log_assert(length >= 0);
	log_assert(offset + length <= width_);

	bits_.erase(bits_.begin() + offset, bits_.begin() + offset + length);
	width_ = bits_.size();

	check();
}

DriverSpec DriverSpec::extract(int offset, int length) const
{
	unpack();
	cover("driverspec.extract_pos");
	return std::vector<DriverBit>(bits_.begin() + offset, bits_.begin() + offset + length);
}

void DriverSpec::append(const DriverSpec &signal)
{
	if (signal.width_ == 0)
		return;

	if (width_ == 0) {
		*this = signal;
		return;
	}

	cover("driverspec.append");

	if (packed() != signal.packed()) {
		pack();
		signal.pack();
	}

	if (packed())
		for (auto &other_c : signal.chunks_)
		{
			auto &my_last_c = chunks_.back();
			if (!my_last_c.is_object() && !other_c.is_object()) {
				auto &this_data = my_last_c.data;
				auto &other_data = other_c.data;
				this_data.insert(this_data.end(), other_data.begin(), other_data.end());
				my_last_c.width += other_c.width;
			} else if (my_last_c.wire == other_c.wire && my_last_c.offset + my_last_c.width == other_c.offset) {
				my_last_c.width += other_c.width;
			} else if (my_last_c.cell == other_c.cell && my_last_c.port == other_c.port &&
                                   my_last_c.offset + my_last_c.width == other_c.offset) {
				my_last_c.width += other_c.width;
			} else
				chunks_.push_back(other_c);
		}
	else
		bits_.insert(bits_.end(), signal.bits_.begin(), signal.bits_.end());

	width_ += signal.width_;
	check();
}

void DriverSpec::append(const DriverBit &bit)
{
	if (packed())
	{
		cover("driverspec.append_bit.packed");

		if (chunks_.size() == 0) {
			chunks_.push_back(bit);
                } else {
			if (bit.is_data()) {
				if (chunks_.back().is_data()) {
					chunks_.back().data.push_back(bit.data);
					chunks_.back().width++;
				} else {
					chunks_.push_back(bit);
                                }
                        } else {
				if (chunks_.back().has_same_object(bit) && chunks_.back().offset + chunks_.back().width == bit.offset) {
					chunks_.back().width++;  // Efficiently merge additional bits of the same object
                                } else {
					chunks_.push_back(bit);
                                }
                        }
                }
	}
	else
	{
		cover("driverspec.append_bit.unpacked");
		bits_.push_back(bit);
	}

	width_++;
	check();
}

void DriverSpec::extend_u0(int width, bool is_signed)
{
	cover("driverspec.extend_u0");

	pack();

	if (width_ > width)
		remove(width, width_ - width);

	if (width_ < width) {
		DriverBit padding = width_ > 0 ? (*this)[width_ - 1] : RTLIL::State::Sx;
		if (!is_signed)
			padding = RTLIL::State::S0;
		while (width_ < width)
			append(padding);
	}

}

DriverSpec DriverSpec::repeat(int num) const
{
	cover("driverspec.repeat");

	DriverSpec sig;
	for (int i = 0; i < num; i++)
		sig.append(*this);
	return sig;
}

#ifndef NDEBUG
void DriverSpec::check(Module *mod) const
{
	if (width_ > 64)
	{
		cover("driverspec.check.skip");
	}
	else if (packed())
	{
		cover("driverspec.check.packed");

		int w = 0;
		for (size_t i = 0; i < chunks_.size(); i++) {
			const DriverChunk &chunk = chunks_[i];
			log_assert(chunk.width != 0);
			if (chunk.is_wire()) {
                                // See if this chunk ought to be a continuation of the previous chunk
				if (i > 0 && chunks_[i-1].wire == chunk.wire)
					log_assert(chunk.offset != chunks_[i-1].offset + chunks_[i-1].width);
				log_assert(chunk.offset >= 0);
				log_assert(chunk.width >= 0);
				log_assert(chunk.offset + chunk.width <= chunk.object_width());
				log_assert(chunk.data.size() == 0);
				if (mod != nullptr)
					log_assert(chunk.wire->module == mod);
                        } else if (chunk.is_cell()) {
                                log_assert(!chunk.port.empty());
                                log_assert(chunk.cell->hasPort(chunk.port));
                                // See if this chunk ought to be a continuation of the previous chunk
				if (i > 0 && chunks_[i-1].cell == chunk.cell && chunks_[i-1].port == chunk.port)
					log_assert(chunk.offset != chunks_[i-1].offset + chunks_[i-1].width);
				log_assert(chunk.offset >= 0);
				log_assert(chunk.width >= 0);
				log_assert(chunk.offset + chunk.width <= chunk.object_width());
				log_assert(chunk.data.size() == 0);
				if (mod != nullptr)
					log_assert(chunk.cell->module == mod);
			} else {
				log_assert(chunk.is_data());
                                // Two data chunks in a row, which should have been combined
				if (i > 0)
					log_assert(!chunks_[i-1].is_data());
				log_assert(chunk.offset == 0);
				log_assert(chunk.data.size() == (size_t)chunk.width);
			}
			w += chunk.width;
		}
		log_assert(w == width_);
		log_assert(bits_.empty());
	}
	else
	{
		cover("driverspec.check.unpacked");

		if (mod != nullptr) {
			for (size_t i = 0; i < bits_.size(); i++) {
				if (bits_[i].wire != nullptr) {
					log_assert(bits_[i].wire->module == mod);
                                }
				if (bits_[i].cell != nullptr) {
					log_assert(!bits_[i].port.empty());
                                        log_assert(bits_[i].cell->hasPort(bits_[i].port));
					log_assert(bits_[i].cell->module == mod);
                                }
                        }
		}

		log_assert(width_ == GetSize(bits_));
		log_assert(chunks_.empty());
	}
}
#endif

bool DriverSpec::operator <(const DriverSpec &other) const
{
	cover("driverspec.comp_lt");

	if (this == &other)
		return false;

	if (width_ != other.width_)
		return width_ < other.width_;

	pack();
	other.pack();

	if (chunks_.size() != other.chunks_.size())
		return chunks_.size() < other.chunks_.size();

	updhash();
	other.updhash();

	if (hash_ != other.hash_)
		return hash_ < other.hash_;

	for (size_t i = 0; i < chunks_.size(); i++)
		if (chunks_[i] != other.chunks_[i]) {
			cover("driverspec.comp_lt.hash_collision");
			return chunks_[i] < other.chunks_[i];
		}

	cover("driverspec.comp_lt.equal");
	return false;
}

bool DriverSpec::operator ==(const DriverSpec &other) const
{
	cover("driverspec.comp_eq");

	if (this == &other)
		return true;

	if (width_ != other.width_)
		return false;

	// Without this, DriverSpec() == DriverSpec(State::S0, 0) will fail
	//   since the RHS will contain one DriverChunk of width 0 causing
	//   the size check below to fail
	if (width_ == 0)
		return true;

	pack();
	other.pack();

	if (chunks_.size() != other.chunks_.size())
		return false;

	updhash();
	other.updhash();

	if (hash_ != other.hash_)
		return false;

	for (size_t i = 0; i < chunks_.size(); i++)
		if (chunks_[i] != other.chunks_[i]) {
			cover("driverspec.comp_eq.hash_collision");
			return false;
		}

	cover("driverspec.comp_eq.equal");
	return true;
}

// The driverSpec has exactly one chunk, which is a wire of the full width.
bool DriverSpec::is_wire() const
{
	cover("driverspec.is_wire");

	pack();
	return GetSize(chunks_) == 1 && chunks_[0].wire && chunks_[0].object_width() == width_;
}

// The driverSpec has exactly one chunk, which is a cell/port of the full width.
bool DriverSpec::is_cell() const
{
	cover("driverspec.is_cell");

	pack();
	return GetSize(chunks_) == 1 && chunks_[0].cell && chunks_[0].object_width() == width_; 
}

bool DriverSpec::is_chunk() const
{
	cover("driverspec.is_chunk");

	pack();
	return GetSize(chunks_) == 1;
}

bool DriverSpec::is_fully_const() const
{
	cover("driverspec.is_fully_const");

	pack();
	for (auto it = chunks_.begin(); it != chunks_.end(); it++)
		if (it->width > 0 && it->wire != nullptr)
			return false;
	return true;
}

bool DriverSpec::is_fully_zero() const
{
	cover("driverspec.is_fully_zero");

	pack();
	for (auto it = chunks_.begin(); it != chunks_.end(); it++) {
		if (it->width > 0 && it->wire != nullptr)
			return false;
		for (size_t i = 0; i < it->data.size(); i++)
			if (it->data[i] != RTLIL::State::S0)
				return false;
	}
	return true;
}

bool DriverSpec::is_fully_ones() const
{
	cover("driverspec.is_fully_ones");

	pack();
	for (auto it = chunks_.begin(); it != chunks_.end(); it++) {
		if (it->width > 0 && it->is_object())
			return false;
		for (size_t i = 0; i < it->data.size(); i++)
			if (it->data[i] != RTLIL::State::S1)
				return false;
	}
	return true;
}

bool DriverSpec::is_fully_def() const
{
	cover("driverspec.is_fully_def");

	pack();
	for (auto it = chunks_.begin(); it != chunks_.end(); it++) {
		if (it->width > 0 && it->is_object())
			return false;
		for (size_t i = 0; i < it->data.size(); i++)
			if (it->data[i] != RTLIL::State::S0 && it->data[i] != RTLIL::State::S1)
				return false;
	}
	return true;
}

bool DriverSpec::is_fully_undef() const
{
	cover("driverspec.is_fully_undef");

	pack();
	for (auto it = chunks_.begin(); it != chunks_.end(); it++) {
		if (it->width > 0 && it->is_object())
			return false;
		for (size_t i = 0; i < it->data.size(); i++)
			if (it->data[i] != RTLIL::State::Sx && it->data[i] != RTLIL::State::Sz)
				return false;
	}
	return true;
}

bool DriverSpec::has_const() const
{
	cover("driverspec.has_const");

	pack();
	for (auto it = chunks_.begin(); it != chunks_.end(); it++)
		if (it->width > 0 && it->is_data())
			return true;
	return false;
}

bool DriverSpec::has_marked_bits() const
{
	cover("driverspec.has_marked_bits");

	pack();
	for (auto it = chunks_.begin(); it != chunks_.end(); it++)
		if (it->width > 0 && it->is_data()) {
			for (size_t i = 0; i < it->data.size(); i++)
				if (it->data[i] == RTLIL::State::Sm)
					return true;
		}
	return false;
}

bool DriverSpec::is_onehot(int *pos) const
{
	cover("driverspec.is_onehot");

	pack();
	if (!is_fully_const())
		return false;
	log_assert(GetSize(chunks_) <= 1);
	if (width_)
		return RTLIL::Const(chunks_[0].data).is_onehot(pos);
	return false;
}

bool DriverSpec::as_bool() const
{
	cover("driverspec.as_bool");

	pack();
	log_assert(is_fully_const() && GetSize(chunks_) <= 1);
	if (width_)
		return RTLIL::Const(chunks_[0].data).as_bool();
	return false;
}

int DriverSpec::as_int(bool is_signed) const
{
	cover("driverspec.as_int");

	pack();
	log_assert(is_fully_const() && GetSize(chunks_) <= 1);
	if (width_)
		return RTLIL::Const(chunks_[0].data).as_int(is_signed);
	return 0;
}

std::string DriverSpec::as_string() const
{
	cover("driverspec.as_string");

	pack();
	std::string str;
	str.reserve(size());
	for (size_t i = chunks_.size(); i > 0; i--) {
		const DriverChunk &chunk = chunks_[i-1];
		if (chunk.is_object())
			str.append(chunk.width, '?');
		else
			str += RTLIL::Const(chunk.data).as_string();
	}
	return str;
}

RTLIL::Const DriverSpec::as_const() const
{
	cover("driverspec.as_const");

	pack();
	log_assert(is_fully_const() && GetSize(chunks_) <= 1);
	if (width_)
		return chunks_[0].data;
	return RTLIL::Const();
}

RTLIL::Wire *DriverSpec::as_wire() const
{
	cover("driverspec.as_wire");

	pack();
	log_assert(is_wire());
	return chunks_[0].wire;
}

// also return port 
RTLIL::Cell *DriverSpec::as_cell(RTLIL::IdString& port) const
{
	cover("driverspec.as_cell");

	pack();
	log_assert(is_cell());
        port = chunks_[0].port;
	return chunks_[0].cell;
}


DriverChunk DriverSpec::as_chunk() const
{
	cover("driverspec.as_chunk");

	pack();
	log_assert(is_chunk());
	return chunks_[0];
}

DriverBit DriverSpec::as_bit() const
{
	cover("driverspec.as_bit");

	log_assert(width_ == 1);
	if (packed())
		return DriverBit(*chunks_.begin());
	else
		return bits_[0];
}

bool DriverSpec::match(const char* pattern) const
{
	cover("driverspec.match");

	unpack();
	log_assert(int(strlen(pattern)) == GetSize(bits_));

	for (auto it = bits_.rbegin(); it != bits_.rend(); it++, pattern++) {
		if (*pattern == ' ')
			continue;
		if (*pattern == '*') {
			if (*it != State::Sz && *it != State::Sx)
				return false;
			continue;
		}
		if (*pattern == '0') {
			if (*it != State::S0)
				return false;
		} else
		if (*pattern == '1') {
			if (*it != State::S1)
				return false;
		} else
			log_abort();
	}

	return true;
}

std::set<DriverBit> DriverSpec::to_driverbit_set() const
{
	cover("driverspec.to_driverbit_set");

	pack();
	std::set<DriverBit> sigbits;
	for (auto &c : chunks_)
		for (int i = 0; i < c.width; i++)
			sigbits.insert(DriverBit(c, i));
	return sigbits;
}

pool<DriverBit> DriverSpec::to_driverbit_pool() const
{
	cover("driverspec.to_driverbit_pool");

	pack();
	pool<DriverBit> sigbits;
	sigbits.reserve(size());
	for (auto &c : chunks_)
		for (int i = 0; i < c.width; i++)
			sigbits.insert(DriverBit(c, i));
	return sigbits;
}

std::vector<DriverBit> DriverSpec::to_driverbit_vector() const
{
	cover("driverspec.to_driverbit_vector");

	unpack();
	return bits_;
}

std::map<DriverBit, DriverBit> DriverSpec::to_driverbit_map(const DriverSpec &other) const
{
	cover("driverspec.to_driverbit_map");

	unpack();
	other.unpack();

	log_assert(width_ == other.width_);

	std::map<DriverBit, DriverBit> new_map;
	for (int i = 0; i < width_; i++)
		new_map[bits_[i]] = other.bits_[i];

	return new_map;
}

dict<DriverBit, DriverBit> DriverSpec::to_driverbit_dict(const DriverSpec &other) const
{
	cover("driverspec.to_driverbit_dict");

	unpack();
	other.unpack();

	log_assert(width_ == other.width_);

	dict<DriverBit, DriverBit> new_map;
	new_map.reserve(size());
	for (int i = 0; i < width_; i++)
		new_map[bits_[i]] = other.bits_[i];

	return new_map;
}





DriverFinder::DriverFinder(Yosys::RTLIL::Module *mod)
{
  build(mod);
}

void DriverFinder::clear()
{
  sigmap.clear();
  canonical_sigbit_to_driving_cell_table.clear();
  canonical_sigbit_to_driving_wire_table.clear();
  module = nullptr;
}


void DriverFinder::build(RTLIL::Module *mod)
{
  clear();

  module = mod;

  sigmap.set(module);

  for (auto cell : module->cells()) {
    for (auto& conn : cell->connections()) {
      // conn.first is the signal IdString, conn.second is its SigSpec
      if (cell->output(conn.first)) {
        RTLIL::SigSpec canonical_sig = sigmap(conn.second);
        //log("\nCell %s port %s -> ", cell->name.c_str(),  conn.first.c_str());
        //my_log_sigspec(conn.second);
        //log("\ncanonical: ");
        //my_log_sigspec(canonical_sig);
        int idx = 0;
        for (auto& bit : canonical_sig.to_sigbit_vector()) {
          // sigmap(conn.second) is the canonical SigSpec.
          // bit is a canonical SigBit
          //log("  ");
          //my_log_sigbit(bit);
          log_assert(bit.is_wire());  // A cell can't drive a constant!
          log_assert(canonical_sigbit_to_driving_cell_table.count(bit) == 0);
          canonical_sigbit_to_driving_cell_table.emplace(bit, CellPortBit{cell, conn.first, idx});
          ++idx;
        }
      }
    }
  }

  for (auto wire : module->wires()) {
    if (wire->port_input) {
      RTLIL::SigSpec canonical_sig = sigmap(wire);
      //log("\nport_input wire :\n");
      //my_log_wire(wire);
      //log("\ncanonical sigspec:\n");
      //my_log_sigspec(canonical_sig);
      int idx = 0;
      for (auto& bit : canonical_sig.to_sigbit_vector()) {
        // sigmap(wire) is the canonical SigSpec.
        // bit is a canonical SigBit
        log_assert(canonical_sigbit_to_driving_wire_table.count(bit) == 0);  // Multi-driven?
        canonical_sigbit_to_driving_wire_table.emplace(bit, WireBit{wire, idx});
        ++idx;
      }
    }
  }
}



DriverFinder::WireBit*
DriverFinder::getDrivingWire(const RTLIL::SigBit& sigbit)
{
  RTLIL::SigBit canonicalSigbit = sigmap(sigbit);

  //log("getDrivingWire:  ");
  //my_log_sigbit(sigbit);
  //log("canonical:  ");
  //my_log_sigbit(canonicalSigbit);

  auto iter = canonical_sigbit_to_driving_wire_table.find(canonicalSigbit);
  if (iter != canonical_sigbit_to_driving_wire_table.end()) {
    return &(iter->second);
  }
  return nullptr;  // Not driven by a wire
}



DriverFinder::CellPortBit*
DriverFinder::getDrivingCell(const RTLIL::SigBit& sigbit)
{
  RTLIL::SigBit canonicalSigbit = sigmap(sigbit);

  //log("getDrivingCell:  ");
  //my_log_sigbit(sigbit);
  //log("canonical:  ");
  //my_log_sigbit(canonicalSigbit);

  auto iter = canonical_sigbit_to_driving_cell_table.find(canonicalSigbit);
  if (iter != canonical_sigbit_to_driving_cell_table.end()) {
    return &(iter->second);
  }
  return nullptr;  // Not driven by a cell
}


// Get a description of what drives the given cell (input) port.
void
DriverFinder::buildDriverOf(const RTLIL::Cell *cell, const RTLIL::IdString& port, DriverSpec& driver)
{
  log_assert(cell->module == module);
  RTLIL::SigSpec sigspec = cell->getPort(port);
  buildDriverOf(sigspec, driver);
}




// Get a description of what drives the given module (output) port.
void
DriverFinder::buildDriverOf(RTLIL::Wire *wire, DriverSpec& driver)
{
  log_assert(wire->module == module);
  RTLIL::SigSpec sigspec = sigmap(wire);
  buildDriverOf(sigspec, driver);
}


// Get a description of what drives the given SigSpec.
void
DriverFinder::buildDriverOf(const RTLIL::SigSpec& sigspec, DriverSpec& driver)
{
  driver = DriverSpec();  // Clear

  for (auto& bit : sigspec.to_sigbit_vector()) {
    DriverBit dBit;

    if (!bit.is_wire()) {
      // A constant data value
      dBit = DriverBit(bit.data);
    } else {
      // See if the driver is a module input port (represented by a wire)
      WireBit *wb = getDrivingWire(bit);
      if (wb) {
        dBit = DriverBit(wb->wire, wb->bit);
      } else {
        // See if the driver is a cell output port (represented by a cell/portname)
        CellPortBit *cpb = getDrivingCell(bit);
        if (cpb) {
          dBit = DriverBit(cpb->cell, cpb->port, cpb->bit);
        } else {
          // No connection!
          dBit = DriverBit(RTLIL::State::Sx);
        }
      }
    }

    driver.append(dBit);
  }

}


size_t DriverFinder::size() const
{
  return canonical_sigbit_to_driving_cell_table.size() +
         canonical_sigbit_to_driving_wire_table.size();
}




void dump_driverchunk(std::ostream &f, const DriverChunk &chunk, bool autoint)
{
        if (chunk.wire != nullptr) {
                if (chunk.wire->port_input) f << "input port ";
                if (chunk.wire->port_output) f << "output port ";
                f << "wire ";
		if (chunk.width == chunk.object_width() && chunk.offset == 0)
			f << stringf("%s", chunk.wire->name.c_str());
		else if (chunk.width == 1)
			f << stringf("%s [%d]", chunk.wire->name.c_str(), chunk.offset);
		else
			f << stringf("%s [%d:%d]", chunk.wire->name.c_str(), chunk.offset+chunk.width-1, chunk.offset);
        } else if (chunk.cell != nullptr) {
                f << "cell port ";
		if (chunk.width == chunk.object_width() && chunk.offset == 0)
			f << stringf("%s %s", chunk.cell->name.c_str(), chunk.port.c_str());
		else if (chunk.width == 1)
			f << stringf("%s %s [%d]", chunk.cell->name.c_str(), chunk.port.c_str(), chunk.offset);
		else
			f << stringf("%s %s [%d:%d]", chunk.cell->name.c_str(), chunk.port.c_str(), chunk.offset+chunk.width-1, chunk.offset);
	} else {
                f << "const ";
                RTLIL_BACKEND::dump_const(f, chunk.data, chunk.width, chunk.offset, autoint);
        }
        f << stringf(" (width %d)", chunk.width);
}

void dump_driverspec(std::ostream &f, const DriverSpec &driver, bool autoint)
{
	if (driver.is_chunk()) {
		dump_driverchunk(f, driver.as_chunk(), autoint);
	} else {
		f << stringf("{ ");
		for (auto it = driver.chunks().rbegin(); it != driver.chunks().rend(); ++it) {
			dump_driverchunk(f, *it, false);
			f << stringf(" ");
		}
		f << stringf("}");
	}
}


void log_driverchunk(const DriverChunk &chunk, bool autoint)
{
  std::stringstream buf;
  dump_driverchunk(buf, chunk, autoint);
  log("driver chunk: %s\n", buf.str().c_str());
}



void log_driverspec(const DriverSpec &driver, bool autoint)
{
  std::stringstream buf;
  dump_driverspec(buf, driver, autoint);
  log("driver spec: %s\n", buf.str().c_str());
}
