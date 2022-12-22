#include "DriverSpec.h"
#include "kernel/yosys.h"


DriverChunk::DriverChunk()
{
	wire = NULL;
        cell = NULL;
	width = 0;
	offset = 0;
}

DriverChunk::DriverChunk(const RTLIL::Const &value)
{
	wire = NULL;
        cell = NULL;
	data = value.bits;
	width = GetSize(data);
	offset = 0;
}

DriverChunk::DriverChunk(RTLIL::Wire *wire)
{
	log_assert(wire != nullptr);
	this->wire = wire;
        this->cell = NULL;
	this->width = wire->width;
	this->offset = 0;
}

DriverChunk::DriverChunk(RTLIL::Wire *wire, int offset, int width)
{
	log_assert(wire != nullptr);
	this->wire = wire;
        this->cell = NULL;
	this->width = width;
	this->offset = offset;
}

DriverChunk::DriverChunk(RTLIL::Cell *cell, const RTLIL::IdString& port)
{
	log_assert(cell != nullptr);
	log_assert(!port.empty());
        log_assert(cell->hasPort(port));
	this->wire = NULL;
        this->cell = cell;
        this->port = port;
	this->width = wire->width;
	this->offset = 0;
}

DriverChunk::DriverChunk(RTLIL::Cell *cell, const RTLIL::IdString& port, int offset, int width)
{
	log_assert(cell != nullptr);
	log_assert(!port.empty());
        log_assert(cell->hasPort(port));
	this->wire = NULL;
        this->cell = NULL;
	this->width = width;
	this->offset = offset;
}


DriverChunk::DriverChunk(const std::string &str)
{
	wire = NULL;
        cell = NULL;
	data = RTLIL::Const(str).bits;
	width = GetSize(data);
	offset = 0;
}

DriverChunk::DriverChunk(int val, int width)
{
	wire = NULL;
        cell = NULL;
	data = RTLIL::Const(val, width).bits;
	this->width = GetSize(data);
	offset = 0;
}

DriverChunk::DriverChunk(RTLIL::State bit, int width)
{
	wire = NULL;
        cell = NULL;
	data = RTLIL::Const(bit, width).bits;
	this->width = GetSize(data);
	offset = 0;
}

DriverChunk::DriverChunk(const DriverBit &bit)
{
	wire = bit.wire;
        cell = NULL;
	offset = 0;
	if (wire == NULL)
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
  // Doug TODO
	if (wire && other.wire)
		if (wire->name != other.wire->name)
			return wire->name < other.wire->name;

	if (wire != other.wire)
		return wire < other.wire;

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

        // Doug TODO
	if (wire->width != 0) {
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
		if (bit.wire == NULL && bit.cell == NULL)
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

	DriverChunk *last = NULL;
	int last_end_offset = 0;

	for (auto &bit : old_bits) {
                // Doug TODO
		if (last && bit.wire == last->wire) {
			if (bit.wire == NULL) {
				last->data.push_back(bit.data);
				last->width++;
				continue;
			} else if (last_end_offset == bit.offset) {
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
		if (c.wire == NULL && c.cell == NULL) {
			for (auto &v : c.data)
				that->hash_ = mkhash(that->hash_, v);
		} else if (c.cell == NULL) {
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
	log_assert(other != NULL);
	log_assert(width_ == other->width_);
	log_assert(pattern.width_ == with.width_);

	pattern.unpack();
	with.unpack();
	unpack();
	other->unpack();

	for (int i = 0; i < GetSize(pattern.bits_); i++) {
		if (pattern.bits_[i].wire != NULL || pattern.bits_[i].cell != NULL) {
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

	log_assert(other != NULL);
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

	log_assert(other != NULL);
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
	remove2(pattern, NULL);
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
	if (other != NULL) {
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
				if (other != NULL) {
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
	remove2(pattern, NULL);
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

	if (other != NULL) {
		log_assert(width_ == other->width_);
		other->unpack();
	}

	for (int i = GetSize(bits_) - 1; i >= 0; i--) {
		if (bits_[i].is_object() && pattern.count(bits_[i])) {
			bits_.erase(bits_.begin() + i);
			width_--;
			if (other != NULL) {
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

	if (other != NULL) {
		log_assert(width_ == other->width_);
		other->unpack();
	}

	for (int i = GetSize(bits_) - 1; i >= 0; i--) {
		if (bits_[i].is_object() && pattern.count(bits_[i])) {
			bits_.erase(bits_.begin() + i);
			width_--;
			if (other != NULL) {
				other->bits_.erase(other->bits_.begin() + i);
				other->width_--;
			}
		}
	}

	check();
}

DriverSpec DriverSpec::extract(const DriverSpec &pattern, const DriverSpec *other) const
{
	if (other)
		cover("driverspec.extract_other");
	else
		cover("driverspec.extract");

	log_assert(other == NULL || width_ == other->width_);

	DriverSpec ret;
	std::vector<DriverBit> bits_match = to_sigbit_vector();

	for (auto& pattern_chunk : pattern.chunks()) {
		if (other) {
			std::vector<DriverBit> bits_other = other->to_sigbit_vector();
			for (int i = 0; i < width_; i++)
                                // Doug TODO
				if (bits_match[i].wire &&
					bits_match[i].wire == pattern_chunk.wire &&
					bits_match[i].offset >= pattern_chunk.offset &&
					bits_match[i].offset < pattern_chunk.offset + pattern_chunk.width)
					ret.append(bits_other[i]);
		} else {
			for (int i = 0; i < width_; i++)
				if (bits_match[i].wire &&
					bits_match[i].wire == pattern_chunk.wire &&
					bits_match[i].offset >= pattern_chunk.offset &&
					bits_match[i].offset < pattern_chunk.offset + pattern_chunk.width)
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

	log_assert(other == NULL || width_ == other->width_);

	std::vector<DriverBit> bits_match = to_sigbit_vector();
	DriverSpec ret;

	if (other) {
		std::vector<DriverBit> bits_other = other->to_sigbit_vector();
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

		if (chunks_.size() == 0)
			chunks_.push_back(bit);
		else
			if (bit.is_data()) {
				if (chunks_.back().is_data()) {
					chunks_.back().data.push_back(bit.data);
					chunks_.back().width++;
				} else {
					chunks_.push_back(bit);
                                }
                        } else {
				if (chunks_.back().wire == bit.wire && chunks_.back().offset + chunks_.back().width == bit.offset) {
					chunks_.back().width++;
                                } else if (chunks_.back().cell == bit.cell && chunks_.back().port == bit.port &&
                                           chunks_.back().offset + chunks_.back().width == bit.offset) {
					chunks_.back().width++;
                                } else {
					chunks_.push_back(bit);
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
			if (chunk.wire != NULL) {
				if (i > 0 && chunks_[i-1].wire == chunk.wire)
					log_assert(chunk.offset != chunks_[i-1].offset + chunks_[i-1].width);
				log_assert(chunk.offset >= 0);
				log_assert(chunk.width >= 0);
				log_assert(chunk.offset + chunk.width <= chunk.wire->width);
				log_assert(chunk.data.size() == 0);
				if (mod != nullptr)
					log_assert(chunk.wire->module == mod);
                        } else if (chunk.cell != NULL) {
                                log_assert(!chunk.port.empty());
                                log_assert(chunk.cell->hasPort(chunk.port));
				if (i > 0 && chunks_[i-1].cell == chunk.cell && chunks_[i-1].port == chunk.port)
					log_assert(chunk.offset != chunks_[i-1].offset + chunks_[i-1].width);
				log_assert(chunk.offset >= 0);
				log_assert(chunk.width >= 0);
				log_assert(chunk.offset + chunk.width <= chunk.wire->width); // Doug TODO port_width
				log_assert(chunk.data.size() == 0);
				if (mod != nullptr)
					log_assert(chunk.cell->module == mod);
			} else {
				if (i > 0)
					log_assert(chunks_[i-1].is_object());
				log_assert(chunk.offset == 0);
				log_assert(chunk.data.size() == (size_t)chunk.width);
			} else {
			w += chunk.width;
		}
		log_assert(w == width_);
		log_assert(bits_.empty());
	}
	else
	{
		cover("driverspec.check.unpacked");

		if (mod != nullptr) {
			for (size_t i = 0; i < bits_.size(); i++)
				if (bits_[i].wire != nullptr)
					log_assert(bits_[i].wire->module == mod);
				if (bits_[i].cell != nullptr) {
					log_assert(!bits_[i].port.empty());
                                        log_assert(bits_[i].cell->hasPort(bits_[i].port));
					log_assert(bits_[i].cell->module == mod);
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
	return GetSize(chunks_) == 1 && chunks_[0].wire && chunks_[0].wire->width == width_;
}

// The driverSpec has exactly one chunk, which is a cell/port of the full width.
bool DriverSpec::is_cell() const
{
	cover("driverspec.is_cell");

	pack();
	return GetSize(chunks_) == 1 && chunks_[0].cell && chunks_[0].wire->width == width_; // Doug TODO port_width
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
		if (it->width > 0 && it->wire != NULL)
			return false;
	return true;
}

bool DriverSpec::is_fully_zero() const
{
	cover("driverspec.is_fully_zero");

	pack();
	for (auto it = chunks_.begin(); it != chunks_.end(); it++) {
		if (it->width > 0 && it->wire != NULL)
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
        port = this->port;
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

std::set<DriverBit> DriverSpec::to_sigbit_set() const
{
	cover("driverspec.to_sigbit_set");

	pack();
	std::set<DriverBit> sigbits;
	for (auto &c : chunks_)
		for (int i = 0; i < c.width; i++)
			sigbits.insert(DriverBit(c, i));
	return sigbits;
}

pool<DriverBit> DriverSpec::to_sigbit_pool() const
{
	cover("driverspec.to_sigbit_pool");

	pack();
	pool<DriverBit> sigbits;
	sigbits.reserve(size());
	for (auto &c : chunks_)
		for (int i = 0; i < c.width; i++)
			sigbits.insert(DriverBit(c, i));
	return sigbits;
}

std::vector<DriverBit> DriverSpec::to_sigbit_vector() const
{
	cover("driverspec.to_sigbit_vector");

	unpack();
	return bits_;
}

std::map<DriverBit, DriverBit> DriverSpec::to_sigbit_map(const DriverSpec &other) const
{
	cover("driverspec.to_sigbit_map");

	unpack();
	other.unpack();

	log_assert(width_ == other.width_);

	std::map<DriverBit, DriverBit> new_map;
	for (int i = 0; i < width_; i++)
		new_map[bits_[i]] = other.bits_[i];

	return new_map;
}

dict<DriverBit, DriverBit> DriverSpec::to_sigbit_dict(const DriverSpec &other) const
{
	cover("driverspec.to_sigbit_dict");

	unpack();
	other.unpack();

	log_assert(width_ == other.width_);

	dict<DriverBit, DriverBit> new_map;
	new_map.reserve(size());
	for (int i = 0; i < width_; i++)
		new_map[bits_[i]] = other.bits_[i];

	return new_map;
}

static void sigspec_parse_split(std::vector<std::string> &tokens, const std::string &text, char sep)
{
	size_t start = 0, end = 0;
	while ((end = text.find(sep, start)) != std::string::npos) {
		tokens.push_back(text.substr(start, end - start));
		start = end + 1;
	}
	tokens.push_back(text.substr(start));
}

static int sigspec_parse_get_dummy_line_num()
{
	return 0;
}


