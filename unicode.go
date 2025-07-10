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
