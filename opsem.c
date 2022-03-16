#include <math.h>
#include "all.h"

uint64_t
opsemint(int op, int w, uint64_t a, uint64_t b)
{
	union {
		int32_t iw;
		int64_t il;
		uint32_t uw;
		uint64_t ul;
		float fs;
		double fd;
	} l, r;
	uint64_t x;

	l.ul = a;
	r.ul = b;

	assert(!((op == Odiv || op == Oudiv || op == Orem || op == Ourem)
		&& ((w ? r.ul : r.uw) == 0)));
	assert(!((op == Odiv || op == Orem)
		&& (w ? l.ul == INT64_MIN && r.il == -1
			: l.uw == INT32_MIN && r.iw == -1)));

	switch (op) {
	case Oadd:  x = l.ul + r.ul; break;
	case Osub:  x = l.ul - r.ul; break;
	case Oneg:  x = -l.ul; break;
	case Odiv:  x = w ? l.il / r.il : l.iw / r.iw; break;
	case Orem:  x = w ? l.il % r.il : l.iw % r.iw; break;
	case Oudiv: x = w ? l.ul / r.ul : l.uw / r.uw; break;
	case Ourem: x = w ? l.ul % r.ul : l.uw % r.uw; break;
	case Omul:  x = l.ul * r.ul; break;
	case Oand:  x = l.ul & r.ul; break;
	case Oor:   x = l.ul | r.ul; break;
	case Oxor:  x = l.ul ^ r.ul; break;
	case Osar:  x = (w ? l.il : l.iw) >> (r.uw & (w ? 63 : 31)); break;
	case Oshr:  x = (w ? l.ul : l.uw) >> (r.uw & (w ? 63 : 31)); break;
	case Oshl:  x = l.ul << (r.uw & (w ? 63 : 31)); break;
	case Oextsb: x = (int8_t)l.ul;   break;
	case Oextub: x = (uint8_t)l.ul;  break;
	case Oextsh: x = (int16_t)l.ul;  break;
	case Oextuh: x = (uint16_t)l.ul; break;
	case Oextsw: x = (int32_t)l.ul;  break;
	case Oextuw: x = (uint32_t)l.ul; break;
	case Ostosi: x = w ? (int64_t)l.fs : (int32_t)l.fs; break;
	case Ostoui: x = w ? (uint64_t)l.fs : (uint32_t)l.fs; break;
	case Odtosi: x = w ? (int64_t)l.fd : (int32_t)l.fd; break;
	case Odtoui: x = w ? (uint64_t)l.fd : (uint32_t)l.fd; break;
	case Ocast:  x = l.ul; break;
	default:
		if (Ocmpw <= op && op <= Ocmpl1) {
			if (op <= Ocmpw1) {
				l.ul = (int32_t)l.ul;
				r.ul = (int32_t)r.ul;
			} else
				op -= Ocmpl - Ocmpw;
			switch (op - Ocmpw) {
			case Ciule: x = l.ul <= r.ul; break;
			case Ciult: x = l.ul < r.ul;  break;
			case Cisle: x = l.il <= r.il; break;
			case Cislt: x = l.il < r.il;  break;
			case Cisgt: x = l.il > r.il;  break;
			case Cisge: x = l.il >= r.il; break;
			case Ciugt: x = l.ul > r.ul;  break;
			case Ciuge: x = l.ul >= r.ul; break;
			case Cieq:  x = l.ul == r.ul; break;
			case Cine:  x = l.ul != r.ul; break;
			default: assert(0);
			}
		}
		else if (Ocmps <= op && op <= Ocmps1) {
			switch (op - Ocmps) {
			case Cfle: x = l.fs <= r.fs; break;
			case Cflt: x = l.fs < r.fs;  break;
			case Cfgt: x = l.fs > r.fs;  break;
			case Cfge: x = l.fs >= r.fs; break;
			case Cfne: x = l.fs != r.fs; break;
			case Cfeq: x = l.fs == r.fs; break;
			case Cfo: x = !isunordered(l.fs, r.fs); break;
			case Cfuo: x = isunordered(l.fs, r.fs); break;
			default: assert(0);
			}
		}
		else if (Ocmpd <= op && op <= Ocmpd1) {
			switch (op - Ocmpd) {
			case Cfle: x = l.fd <= r.fd; break;
			case Cflt: x = l.fd < r.fd;  break;
			case Cfgt: x = l.fd > r.fd;  break;
			case Cfge: x = l.fd >= r.fd; break;
			case Cfne: x = l.fd != r.fd; break;
			case Cfeq: x = l.fd == r.fd; break;
			case Cfo: x = !isunordered(l.fd, r.fd); break;
			case Cfuo: x = isunordered(l.fd, r.fd); break;
			default: assert(0);
			}
		}
		else
			assert(0);
	}
	return w ? x : (uint32_t)x;
}

uint64_t
opsemflt(int op, int w, uint64_t a, uint64_t b)
{
	union {
		int32_t iw;
		int64_t il;
		uint32_t uw;
		uint64_t ul;
		float fs;
		double fd;
	} l, r, x;

	l.ul = a;
	r.ul = b;

	if (w)  {
		switch (op) {
		case Oadd: x.fd = l.fd + r.fd; break;
		case Osub: x.fd = l.fd - r.fd; break;
		case Oneg: x.fd = -l.fd; break;
		case Odiv: x.fd = l.fd / r.fd; break;
		case Omul: x.fd = l.fd * r.fd; break;
		case Oswtof: x.fd = l.iw; break;
		case Ouwtof: x.fd = l.uw; break;
		case Osltof: x.fd = l.il; break;
		case Oultof: x.fd = l.ul; break;
		case Oexts: x.fd = l.fs; break;
		case Ocast: x.fd = l.fd; break;
		default: assert(0);
		}
	} else {
		switch (op) {
		case Oadd: x.fs = l.fs + r.fs; break;
		case Osub: x.fs = l.fs - r.fs; break;
		case Oneg: x.fs = -l.fs; break;
		case Odiv: x.fs = l.fs / r.fs; break;
		case Omul: x.fs = l.fs * r.fs; break;
		case Oswtof: x.fs = l.iw; break;
		case Ouwtof: x.fs = l.uw; break;
		case Osltof: x.fs = l.il; break;
		case Oultof: x.fs = l.ul; break;
		case Otruncd: x.fs = l.fd; break;
		case Ocast: x.fs = l.fs; break;
		default: assert(0);
		}
	}
	return w ? x.ul : x.uw;
}
