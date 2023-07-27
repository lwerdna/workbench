import struct

# given a, b, compute gcd(a,b), x, y where:
# x*a + y*b = gcd(a,b)
def extended_euclidean(a, b):
    s, old_s = 0, 1
    r, old_r = b, a

    while r:
        quotient = old_r // r
        old_r, r = r, old_r - quotient*r
        old_s, s = s, old_s - quotient*s

    if b:
        bezout_t = (old_r - old_s*a) // b
    else:
        bezout_t = 0

    return old_r, old_s, bezout_t

def gcd(a, b):
    result, _, _ = extended_euclidean(a, b)
    return result

# given x, N, compute the y such that x*y = 1 (mod N)
def multiplicative_inverse(a, N):
    gcd, x, y = extended_euclidean(a, N)
    assert gcd == 1
    return x % N # normalize negative x's to positive

# given an list of bytes, convert to integer
# eg: [0xDE, 0xAD, 0xBE, 0xEF, 0x01, 0x02] -> 0xDEADBEEF0102
def bytes_to_num(data):
    result = 0
    for byte in data:
        result = (result << 8) | byte
    return result

def num_to_bytes(num, len_bytes=None):
    result = []
    while num:
        result.append(num & 0xFF)
        num = num >> 8

    if len_bytes:
        missing = len_bytes - len(result)
        if missing > 0:
            result = result + [0]*missing
   
    return list(reversed(result))

def read(fp):
    def slurp(begin, end, fmt):
        fp.seek(begin)
        data = fp.read(end-begin)
        match fmt:
            case 'raw': return data
            case 'none': return None
            case _: return struct.unpack(fmt, data)[0]

    return {
        'AvbVBMetaImageHeader': {
            'blob': slurp(0x0, 0x100, 'raw'),
            'magic': slurp(0x0, 0x4, 'raw'),
            'required_libavb_version_major': slurp(0x4, 0x8, '>I'),
            'required_libavb_version_minor': slurp(0x8, 0xC, '>I'),
            'authentication_data_block_size': slurp(0xC, 0x14, '>Q'),
            'auxiliary_data_block_size': slurp(0x14, 0x1C, '>Q'),
            'algorithm_type': slurp(0x1C, 0x20, '>I'),
            'hash_offset': slurp(0x20, 0x28, '>Q'),
            'hash_size': slurp(0x28, 0x30, '>Q'),
            'signature_offset': slurp(0x30, 0x38, '>Q'),
            'signature_size': slurp(0x38, 0x40, '>Q'),
            'public_key_offset': slurp(0x40, 0x48, '>Q'),
            'public_key_size': slurp(0x48, 0x50, '>Q'),
            'public_key_metadata_offset': slurp(0x50, 0x58, '>Q'),
            'public_key_metadata_size': slurp(0x58, 0x60, '>Q'),
            'descriptors_offset': slurp(0x60, 0x68, '>Q'),
            'descriptors_size': slurp(0x68, 0x70, '>Q'),
            'rollback_index': slurp(0x70, 0x78, '>Q'),
            'flags': slurp(0x78, 0x7C, '>I'),
            'rollback_index_location': slurp(0x7C, 0x80, '>I'),
            'release_string': slurp(0x80, 0xB0, 'raw'),
            'reserved': slurp(0xB0, 0x100, 'raw')
        },
        'Authentication': {
            'hash': slurp(0x100, 0x120, 'raw'),
            'signature': slurp(0x120, 0x320, 'raw'),
            'fragment': slurp(0x320, 0x340, 'raw')
        },
        'Auxiliary': {
            'blob': slurp(0x340, 0x16C0, 'raw'),
            'descriptor0': {
                'AvbDescriptor': {
                    'tag': slurp(0x340, 0x348, '>Q'),
                    'num_bytes_following': slurp(0x348, 0x350, '>Q')
                },
                'data': slurp(0x350, 0x7B8, 'raw')
            },
            'descriptor1': {
                'AvbDescriptor': {
                    'tag': slurp(0x7B8, 0x7C0, '>Q'),
                    'num_bytes_following': slurp(0x7C0, 0x7C8, '>Q')
                },
                'data': slurp(0x7C8, 0x840, 'raw')
            },
            'descriptor2': {
                'AvbDescriptor': {
                    'tag': slurp(0x840, 0x848, '>Q'),
                    'num_bytes_following': slurp(0x848, 0x850, '>Q')
                },
                'data': slurp(0x850, 0x888, 'raw')
            },
            'descriptor3': {
                'AvbDescriptor': {
                    'tag': slurp(0x888, 0x890, '>Q'),
                    'num_bytes_following': slurp(0x890, 0x898, '>Q')
                },
                'data': slurp(0x898, 0x8E0, 'raw')
            },
            'descriptor4': {
                'AvbDescriptor': {
                    'tag': slurp(0x8E0, 0x8E8, '>Q'),
                    'num_bytes_following': slurp(0x8E8, 0x8F0, '>Q')
                },
                'data': slurp(0x8F0, 0x968, 'raw')
            },
            'descriptor5': {
                'AvbDescriptor': {
                    'tag': slurp(0x968, 0x970, '>Q'),
                    'num_bytes_following': slurp(0x970, 0x978, '>Q')
                },
                'data': slurp(0x978, 0x9B0, 'raw')
            },
            'descriptor6': {
                'AvbDescriptor': {
                    'tag': slurp(0x9B0, 0x9B8, '>Q'),
                    'num_bytes_following': slurp(0x9B8, 0x9C0, '>Q')
                },
                'data': slurp(0x9C0, 0xA08, 'raw')
            },
            'descriptor7': {
                'AvbDescriptor': {
                    'tag': slurp(0xA08, 0xA10, '>Q'),
                    'num_bytes_following': slurp(0xA10, 0xA18, '>Q')
                },
                'data': slurp(0xA18, 0xA98, 'raw')
            },
            'descriptor8': {
                'AvbDescriptor': {
                    'tag': slurp(0xA98, 0xAA0, '>Q'),
                    'num_bytes_following': slurp(0xAA0, 0xAA8, '>Q')
                },
                'data': slurp(0xAA8, 0xB20, 'raw')
            },
            'descriptor9': {
                'AvbDescriptor': {
                    'tag': slurp(0xB20, 0xB28, '>Q'),
                    'num_bytes_following': slurp(0xB28, 0xB30, '>Q')
                },
                'data': slurp(0xB30, 0xB68, 'raw')
            },
            'descriptor10': {
                'AvbDescriptor': {
                    'tag': slurp(0xB68, 0xB70, '>Q'),
                    'num_bytes_following': slurp(0xB70, 0xB78, '>Q')
                },
                'data': slurp(0xB78, 0xBC0, 'raw')
            },
            'descriptor11': {
                'AvbDescriptor': {
                    'tag': slurp(0xBC0, 0xBC8, '>Q'),
                    'num_bytes_following': slurp(0xBC8, 0xBD0, '>Q')
                },
                'data': slurp(0xBD0, 0xC48, 'raw')
            },
            'descriptor12': {
                'AvbDescriptor': {
                    'tag': slurp(0xC48, 0xC50, '>Q'),
                    'num_bytes_following': slurp(0xC50, 0xC58, '>Q')
                },
                'data': slurp(0xC58, 0xC98, 'raw')
            },
            'descriptor13': {
                'AvbDescriptor': {
                    'tag': slurp(0xC98, 0xCA0, '>Q'),
                    'num_bytes_following': slurp(0xCA0, 0xCA8, '>Q')
                },
                'data': slurp(0xCA8, 0xCF0, 'raw')
            },
            'descriptor14': {
                'AvbDescriptor': {
                    'tag': slurp(0xCF0, 0xCF8, '>Q'),
                    'num_bytes_following': slurp(0xCF8, 0xD00, '>Q')
                },
                'data': slurp(0xD00, 0xD78, 'raw')
            },
            'descriptor15': {
                'AvbDescriptor': {
                    'tag': slurp(0xD78, 0xD80, '>Q'),
                    'num_bytes_following': slurp(0xD80, 0xD88, '>Q')
                },
                'data': slurp(0xD88, 0xE40, 'raw')
            },
            'descriptor16': {
                'AvbDescriptor': {
                    'tag': slurp(0xE40, 0xE48, '>Q'),
                    'num_bytes_following': slurp(0xE48, 0xE50, '>Q')
                },
                'data': slurp(0xE50, 0xF08, 'raw')
            },
            'descriptor17': {
                'AvbDescriptor': {
                    'tag': slurp(0xF08, 0xF10, '>Q'),
                    'num_bytes_following': slurp(0xF10, 0xF18, '>Q')
                },
                'data': slurp(0xF18, 0xFD8, 'raw')
            },
            'descriptor18': {
                'AvbDescriptor': {
                    'tag': slurp(0xFD8, 0xFE0, '>Q'),
                    'num_bytes_following': slurp(0xFE0, 0xFE8, '>Q')
                },
                'data': slurp(0xFE8, 0x10C8, 'raw')
            },
            'descriptor19': {
                'AvbDescriptor': {
                    'tag': slurp(0x10C8, 0x10D0, '>Q'),
                    'num_bytes_following': slurp(0x10D0, 0x10D8, '>Q')
                },
                'data': slurp(0x10D8, 0x11C0, 'raw')
            },
            'descriptor20': {
                'AvbDescriptor': {
                    'tag': slurp(0x11C0, 0x11C8, '>Q'),
                    'num_bytes_following': slurp(0x11C8, 0x11D0, '>Q')
                },
                'data': slurp(0x11D0, 0x12B0, 'raw')
            },
            'AvbRSAPublicKey': {
                'AvbRSAPublicKeyHeader': {
                    'key_num_bits': slurp(0x12B0, 0x12B4, '>I'),
                    'n0inv': slurp(0x12B4, 0x12B8, '>I')
                },
                'n': slurp(0x12B8, 0x14B8, 'raw'),
                'rr': slurp(0x14B8, 0x16B8, 'raw')
            },
            'fragment': slurp(0x16B8, 0x16C0, 'raw')
        }
    }
