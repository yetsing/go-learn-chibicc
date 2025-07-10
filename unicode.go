package main

// Encode a given character in UTF-8.
func encodeUTF8(c uint32) []byte {
	if c < 0x80 {
		return []byte{byte(c)}
	} else if c < 0x800 {
		return []byte{
			byte(0xc0 | (c >> 6)),
			byte(0x80 | (c & 0x3f)),
		}
	} else if c < 0x10000 {
		return []byte{
			byte(0xe0 | (c >> 12)),
			byte(0x80 | ((c >> 6) & 0x3f)),
			byte(0x80 | (c & 0x3f)),
		}
	} else if c < 0x110000 {
		return []byte{
			byte(0xf0 | (c >> 18)),
			byte(0x80 | ((c >> 12) & 0x3f)),
			byte(0x80 | ((c >> 6) & 0x3f)),
			byte(0x80 | (c & 0x3f)),
		}
	}
	panic("Invalid Unicode code point")
}

// Read a UTF-8-encoded Unicode code point from a source file.
// We assume that source files are always in UTF-8.
//
// UTF-8 is a variable-width encoding in which one code point is
// encoded in one to four bytes. One byte UTF-8 code points are
// identical to ASCII. Non-ASCII characters are encoded using more
// than one byte.
func decodeUTF8(p string) (uint32, int) {
	if p[0] < 128 {
		return uint32(p[0]), 1
	}

	var len int
	var c uint32

	if p[0] >= 0b11110000 {
		len = 4
		c = uint32(p[0] & 0b111)
	} else if p[0] >= 0b11100000 {
		len = 3
		c = uint32(p[0] & 0b1111)
	} else if p[0] >= 0b11000000 {
		len = 2
		c = uint32(p[0] & 0b11111)
	} else {
		panic("invalid UTF-8 sequence")
	}

	for i := 1; i < len; i++ {
		if (p[i] >> 6) != 0b10 {
			panic("invalid UTF-8 sequence")
		}
		c = (c << 6) | uint32(p[i]&0b00111111)
	}
	return c, len
}
