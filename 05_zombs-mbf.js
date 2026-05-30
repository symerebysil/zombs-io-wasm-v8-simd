/*
 * This is free and unencumbered software released into the public domain.
 *
 * Anyone is free to copy, modify, publish, use, compile, sell, or distribute
 * this software, either in source code form or as a compiled binary, for any
 * purpose, commercial or non-commercial, and by any means.
 *
 * In jurisdictions that recognize copyright laws, the author or authors of
 * this software dedicate any and all copyright interest in the software to
 * the public domain. We make this dedication for the benefit of the public
 * at large and to the detriment of our heirs and successors. We intend this
 * dedication to be an overt act of relinquishment in perpetuity of all
 * present and future rights to this software under copyright law.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS
 * OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
 * IN NO EVENT SHALL THE AUTHORS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
 * DEALINGS IN THE SOFTWARE.
 *
 * For more information, please refer to <https://unlicense.org>
 *
 * benji/symere <symere@fbi.systems>
 */
// src/core/mt19937.ts
var N = 624;
var M = 397;
var MATRIX_A = 2567483615;
var UPPER_MASK = 2147483648;
var LOWER_MASK = 2147483647;
var INIT_MULT = 1812433253;

class Mt19937 {
  mt = new Uint32Array(N);
  index = N + 1;
  constructor(seed = 5489) {
    this.seed(seed);
  }
  seed(s) {
    this.mt[0] = s >>> 0;
    for (let i = 1;i < N; i++) {
      const prev = this.mt[i - 1] ^ this.mt[i - 1] >>> 30;
      this.mt[i] = Math.imul(INIT_MULT, prev) + i >>> 0;
    }
    this.index = N;
  }
  twist() {
    for (let i = 0;i < N; i++) {
      const y = this.mt[i] & UPPER_MASK | this.mt[(i + 1) % N] & LOWER_MASK;
      let next = this.mt[(i + M) % N] ^ y >>> 1;
      if (y & 1)
        next ^= MATRIX_A;
      this.mt[i] = next >>> 0;
    }
    this.index = 0;
  }
  nextUint32() {
    if (this.index >= N)
      this.twist();
    let y = this.mt[this.index++];
    y ^= y >>> 11;
    y ^= y << 7 & 2636928640;
    y ^= y << 15 & 4022730752;
    y ^= y >>> 18;
    return y >>> 0;
  }
  uniformInt(lo, hi) {
    const size = hi - lo + 1 >>> 0;
    if (size === 0)
      return this.nextUint32();
    if (size === 1)
      return lo;
    const bits = 32 - Math.clz32(size - 1);
    const mask = bits >= 32 ? 4294967295 : (1 << bits) - 1 >>> 0;
    let r;
    do {
      r = this.nextUint32() & mask;
    } while (r >= size);
    return lo + r >>> 0;
  }
}
// src/core/u32.ts
var u32 = (x) => x >>> 0;
function rotl32(x, n) {
  n &= 31;
  if (n === 0)
    return x >>> 0;
  return (x << n | x >>> 32 - n) >>> 0;
}
var bswap32 = (x) => (x << 24 | (x & 65280) << 8 | x >>> 8 & 65280 | x >>> 24) >>> 0;
function toHex(bytes) {
  let s = "";
  for (let i = 0;i < bytes.length; i++)
    s += bytes[i].toString(16).padStart(2, "0");
  return s;
}
function fromHex(hex) {
  const clean = hex.length % 2 ? "0" + hex : hex;
  const out = new Uint8Array(clean.length / 2);
  for (let i = 0;i < out.length; i++)
    out[i] = parseInt(clean.slice(i * 2, i * 2 + 2), 16);
  return out;
}

// src/core/sha1.ts
var F = {
  CH: (b, c, d) => b & c | ~b & d,
  PARITY: (b, c, d) => b ^ c ^ d,
  MAJ: (b, c, d) => b & c | b & d | c & d
};
var STOCK_SHA1_IV = [1732584193, 4023233417, 2562383102, 271733878, 3285377520];
var K = [1518500249, 1859775393, 2400959708, 3395469782];
function pad(bytes) {
  const ml = bytes.length;
  const out = new Uint8Array((ml + 8 >> 6 << 6) + 64);
  out.set(bytes);
  out[ml] = 128;
  const bitLen = ml * 8;
  const dv = new DataView(out.buffer);
  dv.setUint32(out.length - 4, bitLen >>> 0, false);
  dv.setUint32(out.length - 8, Math.floor(bitLen / 4294967296), false);
  return out;
}
function sha1WithIv(bytes, iv) {
  let h0 = iv[0], h1 = iv[1], h2 = iv[2], h3 = iv[3], h4 = iv[4];
  const padded = pad(bytes);
  const dv = new DataView(padded.buffer);
  const w = new Uint32Array(80);
  for (let off = 0;off < padded.length; off += 64) {
    for (let i = 0;i < 16; i++)
      w[i] = dv.getUint32(off + i * 4, false);
    for (let i = 16;i < 80; i++)
      w[i] = rotl32(w[i - 3] ^ w[i - 8] ^ w[i - 14] ^ w[i - 16], 1);
    let a = h0, b = h1, c = h2, d = h3, e = h4;
    for (let i = 0;i < 80; i++) {
      let f, k;
      if (i < 20) {
        f = F.CH(b, c, d);
        k = K[0];
      } else if (i < 40) {
        f = F.PARITY(b, c, d);
        k = K[1];
      } else if (i < 60) {
        f = F.MAJ(b, c, d);
        k = K[2];
      } else {
        f = F.PARITY(b, c, d);
        k = K[3];
      }
      const t = u32(rotl32(a, 5) + (f >>> 0) + e + k + w[i]);
      e = d;
      d = c;
      c = rotl32(b, 30);
      b = a;
      a = t;
    }
    h0 = u32(h0 + a);
    h1 = u32(h1 + b);
    h2 = u32(h2 + c);
    h3 = u32(h3 + d);
    h4 = u32(h4 + e);
  }
  const out = new Uint8Array(20);
  const odv = new DataView(out.buffer);
  odv.setUint32(0, h0, false);
  odv.setUint32(4, h1, false);
  odv.setUint32(8, h2, false);
  odv.setUint32(12, h3, false);
  odv.setUint32(16, h4, false);
  return out;
}
function leWords(beDigest) {
  const le = new Uint8Array(20);
  for (let w = 0;w < 5; w++) {
    for (let j = 0;j < 4; j++)
      le[4 * w + j] = beDigest[4 * w + (3 - j)];
  }
  return le;
}
var sha1WithIvLeWords = (bytes, iv) => leWords(sha1WithIv(bytes, iv));
// src/core/bits.ts
function leadingZeroBitsBE(digest, max = digest.length * 8) {
  let n = 0;
  for (let i = 0;i < digest.length; i++) {
    const b = digest[i];
    if (b === 0) {
      n += 8;
      if (n >= max)
        return max;
      continue;
    }
    n += Math.clz32(b) - 24;
    break;
  }
  return n > max ? max : n;
}
function leadingZeroBitsLE32(word) {
  const bytes = [word & 255, word >>> 8 & 255, word >>> 16 & 255, word >>> 24 & 255];
  let n = 0;
  for (const x of bytes) {
    for (let k = 7;k >= 0; k--) {
      if (x >> k & 1)
        return n;
      n++;
    }
  }
  return n;
}
// src/core/bytes.ts
function reverseRange(buf, lo, hi) {
  for (let i = lo, j = hi - 1;i < j; i++, j--) {
    const t = buf[i];
    buf[i] = buf[j];
    buf[j] = t;
  }
}
function reversed(buf) {
  const out = new Uint8Array(buf.length);
  for (let i = 0;i < buf.length; i++)
    out[i] = buf[buf.length - 1 - i];
  return out;
}
function concatBytes(...parts) {
  let total = 0;
  for (const p of parts)
    total += p.length;
  const out = new Uint8Array(total);
  let off = 0;
  for (const p of parts) {
    out.set(p, off);
    off += p.length;
  }
  return out;
}
var _enc = new TextEncoder;
var utf8 = (s) => _enc.encode(s);
// src/protocol/opcodes.ts
var Opcode = {
  PRE_ENTER_WORLD: 5,
  ENTER_WORLD: 4,
  ENTER_WORLD2: 6,
  BLEND: 10,
  PING: 7
};
var OPCODE_INFO = {
  PRE_ENTER_WORLD: {
    opcode: Opcode.PRE_ENTER_WORLD,
    name: "PRE_ENTER_WORLD",
    direction: "server-to-client",
    description: "Server opening move carrying the 132-byte Proof-of-Work challenge as its payload."
  },
  ENTER_WORLD: {
    opcode: Opcode.ENTER_WORLD,
    name: "ENTER_WORLD",
    direction: "bidirectional",
    description: "Client to server: varint(nameLen) then UTF-8 name then the 64-byte response. " + "Server to client: allowed as little-endian uint32 then uid as little-endian uint32."
  },
  ENTER_WORLD2: {
    opcode: Opcode.ENTER_WORLD2,
    name: "ENTER_WORLD2",
    direction: "client-to-server",
    description: "Client follow-up with a 16-byte payload sent after admission."
  },
  BLEND: {
    opcode: Opcode.BLEND,
    name: "BLEND",
    direction: "bidirectional",
    description: "Ongoing re-validation: server sends a fresh challenge, client returns the 64-byte response (a transform of the challenge, not an echo)."
  },
  PING: {
    opcode: Opcode.PING,
    name: "PING",
    direction: "bidirectional",
    description: "Keepalive packet with no meaningful payload."
  }
};
// src/protocol/challenge.ts
var CHALLENGE_LENGTH = 132;
var BLEND_REGION_START = 4;
var BLEND_REGION_END = 68;
var FIELD_REGION_START = 68;
var FIELD_REGION_END = 132;
var DEFAULT_VALIDATOR_COUNT = 25;
function parseChallenge(bytes, validatorCount = DEFAULT_VALIDATOR_COUNT) {
  if (bytes.length !== CHALLENGE_LENGTH) {
    throw new RangeError(`challenge must be ${CHALLENGE_LENGTH} bytes (opcode ${Opcode.PRE_ENTER_WORLD} payload), got ${bytes.length}`);
  }
  const header = bytes.subarray(0, BLEND_REGION_START);
  const blendRegion = bytes.subarray(BLEND_REGION_START, BLEND_REGION_END);
  const fieldRegion = bytes.subarray(FIELD_REGION_START, FIELD_REGION_END);
  const view = new DataView(bytes.buffer, bytes.byteOffset, bytes.byteLength);
  const difficulty = view.getUint32(0, true);
  const selectorByte = bytes[BLEND_REGION_START];
  return {
    header,
    difficulty,
    blendRegion,
    fieldRegion,
    selector(n = validatorCount) {
      return selectorByte % n;
    }
  };
}
// src/versions/v1/solve.ts
var MBF_CLASSIC_IV = [1462051585, 2949495689, 2297093374, 271733875, 4090683890];
var classicDigest = (bytes) => sha1WithIvLeWords(bytes, MBF_CLASSIC_IV);
var V1_SEED_K = (() => {
  const dv = new DataView(new ArrayBuffer(8));
  dv.setUint32(0, 1103231820, false);
  dv.setUint32(4, 352321536, false);
  return dv.getFloat64(0, false);
})();
var seedFromNow = (nowMs) => Math.trunc(nowMs + V1_SEED_K) >>> 0;
var V1_SEED_ORACLE = seedFromNow(1000);
function difficultyV1(challenge2, env = {}) {
  const base = (challenge2[0] | challenge2[1] << 8 | challenge2[2] << 16 | challenge2[3] << 24) >>> 0;
  return base + (env.windowUndefined ?? false ? 10 : 0) + (env.processDefined ?? false ? 10 : 0) + (env.networkConnected ?? true ? 0 : 10) + (env.timingPenalty ?? false ? 1 : 0);
}
function combineV1(challenge2) {
  const b = Uint8Array.from(challenge2);
  const L = b.length;
  reverseRange(b, 4, 68);
  const d1 = classicDigest(b.subarray(4, 68));
  const fieldLen = L - 68;
  if (fieldLen > 0) {
    for (let i = 0;i < fieldLen; i++) {
      const idx = 68 + i;
      const r = i % 20;
      if (r === 3)
        b[idx] = b[idx] + d1[0] & 255;
      else if (r === 8)
        b[idx] ^= d1[5];
      else if (r === 15)
        b[idx] ^= d1[8];
      else if (r === 18)
        b[idx] = b[idx] - d1[3] & 255;
      else
        b[idx] ^= d1[r];
    }
    for (let i = 0;i < fieldLen; i++) {
      const idx = 68 + i;
      b[idx] = (-95 - b[idx] & 255 ^ 85) & 255;
    }
    reverseRange(b, 68, 68 + fieldLen);
  }
  return b;
}
function solveV1(challenge2, hostname = "", opts = {}) {
  const seed = opts.seed ?? (opts.nowMs != null ? seedFromNow(opts.nowMs) : V1_SEED_ORACLE);
  const maxIterations = opts.maxIterations ?? 1e9;
  const difficulty = difficultyV1(challenge2, opts.env ?? {});
  const combinedField = combineV1(challenge2);
  const fieldLen = challenge2.length - 68;
  const hostBytes = utf8(hostname);
  const field = fieldLen > 0 ? combinedField.subarray(68, 68 + fieldLen) : new Uint8Array(0);
  const prefixLen = hostBytes.length + field.length;
  const msg = new Uint8Array(prefixLen + 64);
  msg.set(hostBytes, 0);
  msg.set(field, hostBytes.length);
  const work = msg.subarray(prefixLen);
  const mt = new Mt19937(seed);
  let iterations = 0;
  do {
    const value = mt.nextUint32() & 255;
    const pos = mt.nextUint32() & 63;
    work[pos] = value;
    const digest = classicDigest(msg);
    iterations++;
    if (leadingZeroBitsBE(digest, difficulty) >= difficulty) {
      return { response: Uint8Array.from(work), iterations, difficulty, combinedField };
    }
  } while (iterations < maxIterations);
  throw new Error(`solveV1: no solution within ${maxIterations} iterations (difficulty=${difficulty})`);
}
// src/versions/v2/solve.ts
var difficultyV2 = difficultyV1;
function combineV2(challenge2) {
  const b = Uint8Array.from(challenge2);
  const L = b.length;
  reverseRange(b, 4, 68);
  const d1 = classicDigest(b.subarray(4, 68));
  const fieldLen = L - 68;
  if (fieldLen > 0) {
    for (let i = 0;i < fieldLen; i++) {
      const idx = 68 + i;
      const r = i % 20;
      if (r === 3)
        b[idx] = b[idx] + d1[0] & 255;
      else if (r === 8)
        b[idx] ^= d1[5];
      else if (r === 15)
        b[idx] ^= d1[8];
      else if (r === 18)
        b[idx] = b[idx] - d1[3] & 255;
      else
        b[idx] ^= d1[r];
    }
    for (let i = 0;i < fieldLen; i++) {
      const idx = 68 + i;
      let t = b[idx] - 35 & 255;
      t = (t ^ 166) & 255;
      t = t + 36 & 255;
      t = (t ^ 204) & 255;
      b[idx] = t;
    }
    reverseRange(b, 68, 68 + fieldLen);
  }
  return b;
}
function solveV2(challenge2, hostname = "", myUid = 0, opts = {}) {
  const seed = opts.seed ?? (opts.nowMs != null ? seedFromNow(opts.nowMs) : V1_SEED_ORACLE);
  const maxIterations = opts.maxIterations ?? 1e9;
  const uid = myUid >>> 0;
  const u0 = uid & 255;
  const u1 = uid >>> 8 & 255;
  const u2 = uid >>> 16 & 255;
  const u3 = uid >>> 24 & 255;
  const difficulty = difficultyV2(challenge2, opts.env ?? {});
  const combinedField = combineV2(challenge2);
  const fieldLen = challenge2.length - 68;
  const hostBytes = utf8(hostname);
  const field = fieldLen > 0 ? combinedField.subarray(68, 68 + fieldLen) : new Uint8Array(0);
  const prefixLen = hostBytes.length + field.length;
  const msg = new Uint8Array(prefixLen + 64);
  msg.set(hostBytes, 0);
  msg.set(field, hostBytes.length);
  const work = msg.subarray(prefixLen);
  const mt = new Mt19937(seed);
  let iterations = 0;
  do {
    const value = mt.nextUint32() & 255;
    const pos = mt.nextUint32() & 63;
    work[pos] = value;
    work[10] = work[0] + work[23] + u0 & 255;
    work[11] = work[40] + work[25] + u1 & 255;
    work[12] = work[51] + work[50] + u2 & 255;
    work[13] = work[4] + work[45] + u3 & 255;
    const digest = classicDigest(msg);
    iterations++;
    if (leadingZeroBitsBE(digest, difficulty) >= difficulty) {
      return { response: Uint8Array.from(work), iterations, difficulty, combinedField };
    }
  } while (iterations < maxIterations);
  throw new Error(`solveV2: no solution within ${maxIterations} iterations (difficulty=${difficulty})`);
}
// src/versions/v3/solve.ts
var combineV3 = combineV2;
var difficultyV3 = difficultyV2;
var MT_PREBURN = 6;
function solveV3(challenge2, hostname = "", myUid = 0, opts = {}) {
  const seed = opts.seed ?? (opts.nowMs != null ? seedFromNow(opts.nowMs) : V1_SEED_ORACLE);
  const maxIterations = opts.maxIterations ?? 1e9;
  const preburn = opts.preburn ?? MT_PREBURN;
  const uid = myUid >>> 0;
  const u0 = uid & 255;
  const u1 = uid >>> 8 & 255;
  const u2 = uid >>> 16 & 255;
  const u3 = uid >>> 24 & 255;
  const difficulty = difficultyV3(challenge2, opts.env ?? {});
  const combinedField = combineV3(challenge2);
  const fieldLen = challenge2.length - 68;
  const hostBytes = utf8(hostname);
  const field = fieldLen > 0 ? combinedField.subarray(68, 68 + fieldLen) : new Uint8Array(0);
  const prefixLen = hostBytes.length + field.length;
  const msg = new Uint8Array(prefixLen + 64);
  msg.set(hostBytes, 0);
  msg.set(field, hostBytes.length);
  const work = msg.subarray(prefixLen);
  const mt = new Mt19937(seed);
  for (let i = 0;i < preburn; i++)
    mt.nextUint32();
  let iterations = 0;
  do {
    const value = mt.nextUint32() & 255;
    const pos = mt.nextUint32() & 63;
    work[pos] = value;
    work[10] = work[0] + work[23] + u0 & 255;
    work[11] = work[40] + work[25] + u1 & 255;
    work[12] = work[51] + work[50] + u2 & 255;
    work[13] = work[4] + work[45] + u3 & 255;
    const digest = classicDigest(msg);
    iterations++;
    if (leadingZeroBitsBE(digest, difficulty) >= difficulty) {
      return { response: Uint8Array.from(work), iterations, difficulty, combinedField };
    }
  } while (iterations < maxIterations);
  throw new Error(`solveV3: no solution within ${maxIterations} iterations (difficulty=${difficulty})`);
}
// src/versions/v4/solve.ts
var digestV4 = classicDigest;
var seedForValidator = (v) => 2734070802 + 16 * v >>> 0;
var SEED_TABLE = Array.from({ length: 10 }, (_, v) => seedForValidator(v));
var WARMUP_DRAWS = 5;
function casV4(b) {
  let t = b + 7 & 255;
  t = (t ^ 16) & 255;
  t = t + 24 & 255;
  t = (t ^ 162) & 255;
  return t;
}
var CASCADE_TABLE = (() => {
  const t = new Uint8Array(256);
  for (let b = 0;b < 256; b++)
    t[b] = casV4(b);
  return t;
})();
function combineV4(challenge2) {
  const b = Uint8Array.from(challenge2);
  const L = b.length;
  reverseRange(b, 4, 68);
  const d1 = digestV4(b.subarray(4, 68));
  const fieldLen = L - 68;
  if (fieldLen > 0) {
    for (let i = 0;i < fieldLen; i++) {
      const idx = 68 + i;
      const r = i % 20;
      if (r === 3)
        b[idx] = b[idx] + d1[0] & 255;
      else if (r === 8)
        b[idx] ^= d1[5];
      else if (r === 15)
        b[idx] ^= d1[8];
      else if (r === 18)
        b[idx] = b[idx] - d1[3] & 255;
      else
        b[idx] ^= d1[r];
    }
    for (let i = 0;i < fieldLen; i++) {
      const idx = 68 + i;
      b[idx] = CASCADE_TABLE[b[idx]];
    }
    reverseRange(b, 68, 68 + fieldLen);
  }
  return b;
}
function difficultyV4(challenge2) {
  return (challenge2[0] | challenge2[1] << 8 | challenge2[2] << 16 | challenge2[3] << 24) >>> 0;
}
function searchCore(challenge2, opts) {
  const { seed } = opts;
  const hostname = opts.hostname ?? "";
  const warmup = opts.warmup ?? WARMUP_DRAWS;
  const maxIterations = opts.maxIterations ?? 5000000;
  const difficulty = difficultyV4(challenge2);
  const target = difficulty + 1;
  const uid = (opts.myUid ?? 0) >>> 0;
  const u0 = uid & 255, u1 = uid >>> 8 & 255, u2 = uid >>> 16 & 255, u3 = uid >>> 24 & 255;
  const combinedField = combineV4(challenge2);
  const fieldLen = challenge2.length - 68;
  const mix = [combinedField[79], combinedField[80], combinedField[81], combinedField[82]];
  const hostBytes = utf8(hostname);
  const field = fieldLen > 0 ? combinedField.subarray(68, 68 + fieldLen) : new Uint8Array(0);
  const prefixLen = hostBytes.length + field.length;
  const msg = new Uint8Array(prefixLen + 64);
  msg.set(hostBytes, 0);
  msg.set(field, hostBytes.length);
  const work = msg.subarray(prefixLen);
  const mt = new Mt19937(seed);
  for (let i = 0;i < warmup; i++)
    mt.uniformInt(10, 32);
  let iterations = 0;
  do {
    const value = mt.uniformInt(0, 255);
    const pos = mt.uniformInt(0, 63);
    work[pos] = value;
    work[10] = work[0] + work[23] + u0 & 255;
    work[11] = work[40] + work[25] + u1 & 255;
    work[12] = work[51] + work[50] + u2 & 255;
    work[13] = work[4] + work[45] + u3 & 255;
    work[14] = work[41] ^ mix[0];
    work[15] = work[22] ^ mix[1];
    work[16] = work[35] ^ mix[2];
    work[17] = work[39] ^ mix[3];
    const digest = digestV4(msg);
    iterations++;
    if (leadingZeroBitsBE(digest, target) >= target) {
      return { response: Uint8Array.from(work), iterations, difficulty, target, combinedField };
    }
  } while (iterations < maxIterations);
  throw new Error(`solveV4: no solution in ${maxIterations} iterations (difficulty=${difficulty})`);
}
function v9ShouldEmit(challenge2) {
  return combineV4(Uint8Array.from(challenge2))[4] % 10 === 9;
}
function solveV4(challenge2, opts = {}) {
  const ch = Uint8Array.from(challenge2);
  const v = ch[4] % 10;
  const seed = opts.seed ?? SEED_TABLE[v];
  const core = searchCore(ch, { hostname: opts.hostname, myUid: opts.myUid, seed, warmup: opts.warmup, maxIterations: opts.maxIterations });
  if (v === 9) {
    const emit = opts.v9Emit === true || v9ShouldEmit(ch);
    return {
      ...core,
      response: emit ? core.response : new Uint8Array(64),
      validator: 9,
      seed,
      suppressed: !emit,
      coreResponse: core.response
    };
  }
  return { ...core, validator: v, seed, suppressed: false, coreResponse: core.response };
}
// src/versions/v5/solve.ts
var combineV5 = combineV4;
var difficultyV5 = difficultyV4;
function solveV5(challenge2, opts = {}) {
  const ch = Uint8Array.from(challenge2);
  const v = ch[4] % 10;
  const seed = opts.seed ?? SEED_TABLE[v];
  const core = searchCore(ch, {
    hostname: opts.ipAddress ?? "",
    myUid: opts.myUid,
    seed,
    warmup: opts.warmup,
    maxIterations: opts.maxIterations
  });
  const emit = v !== 9 || opts.v9Emit === true || v9ShouldEmit(ch);
  return {
    ...core,
    response: emit ? core.response : new Uint8Array(64),
    validator: v,
    seed,
    suppressed: !emit,
    coreResponse: core.response
  };
}
// src/versions/v8/digest.ts
var CMP = {
  lt: (x, t) => x < t,
  le: (x, t) => x <= t,
  gt: (x, t) => x > t,
  ge: (x, t) => x >= t
};
function applyOp(op, v) {
  switch (op.kind) {
    case "add":
      return u32(v + op.val);
    case "sub":
      return u32(v - op.val);
    case "xor":
      return u32(v ^ op.val);
    case "replace":
      return u32(op.val);
    default:
      throw new Error("unknown gated op: " + op.kind);
  }
}
var exprCache = new WeakMap;
function applyTweak(tw, v) {
  if (!tw)
    return u32(v);
  v = u32(v);
  const t = tw;
  switch (t.kind) {
    case "expr": {
      let f = exprCache.get(t);
      if (!f) {
        f = new Function("v", "u32", "return (" + t.js + ") >>> 0;");
        exprCache.set(t, f);
      }
      return f(v, u32);
    }
    case "xor":
      return u32(v ^ t.val);
    case "add":
      return u32(v + t.val);
    case "sub":
      return u32(v - t.val);
    case "replace":
      return u32(t.val);
    case "condSub":
      return v > u32(t.gt) ? u32(v - t.sub) : v;
    case "condReplace":
      return v === u32(t.eq) ? u32(t.repl) : v;
    case "gated": {
      const x = u32(v ^ t.xorM >>> 0);
      return CMP[t.cmp](x, u32(t.thr)) ? applyOp(t.op, v) : v;
    }
    case "gatedXor": {
      if (v < u32(t.lt))
        return v;
      if (u32(v ^ t.xor1) < u32(t.lt2))
        return v;
      const r = u32(v ^ t.xorK);
      return r > u32(t.gt) ? v : r;
    }
    default:
      throw new Error("unknown finalize tweak kind: " + t.kind);
  }
}
function tweakOf(fz) {
  if (!fz)
    return null;
  if (fz.tweak)
    return fz.tweak;
  return fz;
}
var coreFinalizeCache = new WeakMap;
function compileCoreFinalize(arr) {
  if (!arr)
    return null;
  const cached = coreFinalizeCache.get(arr);
  if (cached)
    return cached;
  const fns = arr.map((s) => new Function("a", "b", "c", "d", "e", "h0", "h1", "h2", "h3", "h4", "BW", "u32", /;/.test(s) ? s : "return (" + s + ") >>> 0;"));
  coreFinalizeCache.set(arr, fns);
  return fns;
}
var wrapperFinalizeCache = new WeakMap;
function compileWrapperFinalize(arr) {
  if (!arr)
    return null;
  const cached = wrapperFinalizeCache.get(arr);
  if (cached)
    return cached;
  const fns = arr.map((s) => new Function("s0", "s1", "s2", "s3", "s4", "BW", "u32", /;/.test(s) ? s : "return (" + s + ") >>> 0;"));
  wrapperFinalizeCache.set(arr, fns);
  return fns;
}
function makeSha1Core(cfg) {
  const { rounds, schedule, bigEndianLoad, rotlA, rotlB, bands, finalize, coreFinalizeJs } = cfg;
  const taps = schedule.taps;
  const schedRotl = schedule.rotl;
  const finJs = compileCoreFinalize(coreFinalizeJs);
  const K2 = new Uint32Array(rounds);
  const fn = new Array(rounds);
  for (let i = 0;i < rounds; i++) {
    const band = bands.find((bd) => i <= bd.upTo);
    if (!band)
      throw new Error(`no band covers round ${i} (rounds=${rounds})`);
    K2[i] = u32(band.K);
    const f = F[band.f];
    if (!f)
      throw new Error(`unknown f-function "${band.f}" in band upTo=${band.upTo}`);
    fn[i] = f;
  }
  return function compress(state, block) {
    const dv = new DataView(block.buffer, block.byteOffset, block.byteLength);
    const W = new Uint32Array(rounds);
    for (let i = 0;i < 16; i++)
      W[i] = dv.getUint32(i * 4, !bigEndianLoad);
    for (let i = 16;i < rounds; i++) {
      let x = 0;
      for (let t = 0;t < taps.length; t++)
        x ^= W[i - taps[t]];
      W[i] = rotl32(u32(x), schedRotl);
    }
    let a = state[0], b = state[1], c = state[2], d = state[3], e = state[4];
    for (let i = 0;i < rounds; i++) {
      const t = u32(rotl32(a, rotlA) + (fn[i](b, c, d) >>> 0) + e + K2[i] + W[i]);
      e = d;
      d = c;
      c = rotl32(b, rotlB);
      b = a;
      a = t;
    }
    if (finJs) {
      const h0 = state[0], h1 = state[1], h2 = state[2], h3 = state[3], h4 = state[4];
      const BW = new Array(16);
      for (let k = 0;k < 16; k++)
        BW[k] = dv.getUint32(k * 4, true);
      for (let w = 0;w < 5; w++)
        state[w] = finJs[w](a, b, c, d, e, h0, h1, h2, h3, h4, BW, u32);
      return state;
    }
    const vars = [a, b, c, d, e];
    for (let w = 0;w < 5; w++) {
      const tw = tweakOf(finalize ? finalize[w] : null);
      state[w] = u32(applyTweak(tw, vars[w]) + state[w]);
    }
    return state;
  };
}
var digestCache = new WeakMap;
function makeDigest(config) {
  const cached = digestCache.get(config);
  if (cached)
    return cached;
  const { coreConfig, wrapper } = config;
  const compress = makeSha1Core(coreConfig);
  const { iv, transform, pad: pad2, finalize, outEndian = "le", wrapperFinalizeJs } = wrapper;
  const tbl = transform === "identity" || transform == null ? null : Uint8Array.from(transform);
  const wfJs = compileWrapperFinalize(wrapperFinalizeJs);
  const digest = function digestImpl(msg) {
    const body = tbl ? Uint8Array.from(msg, (b) => tbl[b]) : Uint8Array.from(msg);
    const marker = Uint8Array.from(pad2.marker);
    const baseLen = body.length + marker.length;
    const padLen = Math.ceil(baseLen / 64) * 64;
    const padded = new Uint8Array(padLen).fill(pad2.fill);
    padded.set(body, 0);
    padded.set(marker, body.length);
    const state = Uint32Array.from(iv.map(u32));
    let lastBlock = null;
    for (let off = 0;off < padded.length; off += 64) {
      lastBlock = padded.subarray(off, off + 64);
      compress(state, lastBlock);
    }
    const out = new Uint8Array(20);
    const odv = new DataView(out.buffer);
    if (wfJs) {
      const block = lastBlock;
      const dv = new DataView(block.buffer, block.byteOffset, block.byteLength);
      const BW = [];
      for (let k = 0;k < 16; k++)
        BW.push(dv.getUint32(k * 4, true));
      const s0 = state[0], s1 = state[1], s2 = state[2], s3 = state[3], s4 = state[4];
      for (let w = 0;w < 5; w++) {
        const v = wfJs[w](s0, s1, s2, s3, s4, BW, u32);
        odv.setUint32(w * 4, v, outEndian !== "be");
      }
      return out;
    }
    for (let w = 0;w < 5; w++) {
      const v = applyTweak(tweakOf(finalize ? finalize[w] : null), state[w]);
      odv.setUint32(w * 4, v, outEndian !== "be");
    }
    return out;
  };
  digestCache.set(config, digest);
  return digest;
}

// src/versions/v8/blend-field.ts
var MUL = 0x2545f4914f6cdd1dn;
var M64 = (1n << 64n) - 1n;
function genU64(byteOffset, SUB) {
  let x = BigInt(byteOffset) - SUB & M64;
  x = (x ^ x >> 12n) & M64;
  x = (x ^ x << 25n & M64) & M64;
  x = (x ^ x >> 27n) & M64;
  return x * MUL & M64;
}
function makeBlendField(SUB) {
  const store = new Map;
  return {
    get(idx) {
      const stored = store.get(idx);
      if (stored !== undefined)
        return stored;
      const u = genU64(idx & ~7, SUB);
      const b = Number(u >> BigInt(8 * (idx & 7)) & 0xffn);
      return b;
    },
    set(idx, v) {
      store.set(idx, v & 255);
    }
  };
}

// src/versions/v8/diffuse.ts
function diffuseWork(work, uid, key) {
  work[10] = work[23] + work[0] + (uid & 255) & 255;
  work[11] = work[25] + work[40] + (uid >>> 8 & 255) & 255;
  work[12] = work[50] + work[51] + (uid >>> 16 & 255) & 255;
  work[13] = work[45] + work[4] + (uid >>> 24 & 255) & 255;
  work[14] = key[0] ^ work[41];
  work[15] = key[1] ^ work[22];
  work[16] = key[2] ^ work[35];
  work[17] = key[3] ^ work[39];
}
// src/versions/v8/data/shared-wiring.json
var shared_wiring_default = {
  OP1: [
    "xor",
    "xor",
    "xor",
    "add",
    "xor",
    "xor",
    "xor",
    "xor",
    "xor",
    "xor",
    "xor",
    "xor",
    "xor",
    "xor",
    "xor",
    "xor",
    "xor",
    "xor",
    "sub",
    "xor"
  ],
  KIDX: [
    0,
    1,
    2,
    0,
    4,
    5,
    6,
    7,
    5,
    9,
    10,
    11,
    12,
    13,
    14,
    8,
    16,
    17,
    3,
    19
  ],
  cascade: {
    chain: [
      {
        op: "sub",
        c: 153
      },
      {
        op: "xor",
        c: 111
      },
      {
        op: "add",
        c: 72
      },
      {
        op: "xor",
        c: 221
      }
    ],
    note: "shared with idx7 (99 6f 48 dd)"
  }
};

// src/versions/v8/combine.ts
var OP1 = shared_wiring_default.OP1;
var KIDX = shared_wiring_default.KIDX;
var CASCADE = shared_wiring_default.cascade.chain;
function applyCascade(v) {
  for (const s of CASCADE) {
    if (s.op === "add")
      v = v + s.c & 255;
    else if (s.op === "sub")
      v = v - s.c & 255;
    else
      v ^= s.c;
  }
  return v;
}
function combine(challenge2, digestFn) {
  const blend = challenge2.subarray(4, 68);
  const field = challenge2.subarray(68, 132);
  const d1 = digestFn(reversed(blend));
  const b = new Uint8Array(64);
  for (let pos = 0;pos < 64; pos++) {
    const r = pos % 20;
    const k = d1[KIDX[r]];
    let v = field[pos];
    const op = OP1[r];
    if (op === "xor")
      v ^= k;
    else if (op === "add")
      v = v + k & 255;
    else
      v = v - k & 255;
    b[pos] = applyCascade(v);
  }
  return reversed(b);
}

// src/versions/v8/idx22.ts
var IV5 = new Uint32Array([2600729063, 2815544247, 509931162, 2499285373, 193672288]);
function func51(p) {
  const W = new Uint32Array(104);
  for (let i = 0;i < 16; i++) {
    const w = p[5 + i] >>> 0;
    W[i] = u32(w << 24 | (w & 65280) << 8 | w >>> 8 & 65280 | w >>> 24);
  }
  for (let i = 16;i < 104; i++)
    W[i] = rotl32(u32(W[i - 16] ^ W[i - 14] ^ W[i - 8] ^ W[i - 3]), 1);
  const o0 = p[0] >>> 0, o1 = p[1] >>> 0, o2 = p[2] >>> 0, o3 = p[3] >>> 0, o4 = p[4] >>> 0;
  let l9 = o4, l3 = o3, l4 = o2, l2 = o1, l8 = o0, l1 = 0, l5 = 0, l10 = 0;
  for (let l6 = 0;l6 < 104; l6++) {
    l10 = l8;
    l5 = l4;
    l1 = l3;
    const Wi = W[l6];
    let f, K2;
    if (l6 <= 19) {
      f = u32(l1 & ~l2 | l2 & l5);
      K2 = 2115527438;
    } else if (l6 <= 39) {
      f = u32(l2 ^ l5 ^ l1);
      K2 = 2474983467;
    } else if (l6 <= 59) {
      f = u32((l1 | l5) & l2 | l1 & l5);
      K2 = 1799268564;
    } else if (l6 <= 79) {
      f = u32(l2 ^ l5 ^ l1);
      K2 = 2158724593;
    } else {
      f = u32(l2 ^ l5 ^ l1);
      K2 = l6 < 100 ? 1415510629 : 3404864840;
    }
    l8 = u32(Wi + K2 + f + l9 + rotl32(l10, 5));
    l4 = rotl32(l2, 30);
    l9 = l1;
    l3 = l5;
    l2 = l10;
  }
  let h4 = l1;
  if (!(u32(l1 ^ 1556319504) > 1395997415 || l1 < 1427347847 || u32(l1 ^ 2157738716) < 3736732699)) {
    const R = u32(l1 ^ 4021413472) < 252651751 ? 3258059997 : l1;
    h4 = l1 === 3258059997 ? R : l1;
  }
  p[4] = u32(h4 + o4);
  p[0] = u32(l8 + o0);
  p[3] = u32(l3 + o3 + 307218999);
  p[2] = u32(l4 + o2 + 771149088);
  let v = u32(l2 ^ 887296560) < 3061017796 ? u32(l2 + 2090069385) : l2;
  v = u32(l2 ^ 3545673717) < 2474395071 ? v : l2;
  p[1] = u32(v + o1);
}
function func176(msgBytes, iv) {
  const ivv = iv || IV5;
  const st = new Uint32Array(21);
  for (let i = 0;i < 5; i++)
    st[i] = ivv[i];
  const buf = new Uint8Array(64);
  let bp = 0;
  const compress = () => {
    for (let i = 0;i < 16; i++)
      st[5 + i] = u32(buf[4 * i] | buf[4 * i + 1] << 8 | buf[4 * i + 2] << 16 | buf[4 * i + 3] << 24);
    func51(st);
  };
  const feed = (b) => {
    buf[bp++] = b;
    if (bp === 64) {
      compress();
      bp = 0;
    }
  };
  for (let i = 0;i < msgBytes.length; i++)
    feed(msgBytes[i]);
  if (bp !== 0) {
    do {
      feed(231);
    } while (bp !== 0);
  }
  const out = new Uint32Array(5);
  out[0] = st[0];
  let o1 = st[1];
  if (u32(st[1] ^ 1563231393) < 1989576360)
    o1 = u32(st[1] ^ 1563231393);
  if (st[1] < 1989576360)
    o1 = st[1];
  out[1] = o1;
  out[2] = u32(st[2] + 2842696648);
  out[3] = st[3] >= 2635077790 ? u32(st[3] + 1584434432) : st[3];
  out[4] = u32(st[4] ^ 1634346899);
  const d = new Uint8Array(20);
  const dv = new DataView(d.buffer);
  for (let w = 0;w < 5; w++)
    dv.setUint32(w * 4, out[w], true);
  return d;
}
function makeFunc176Gate(prefix, gateBits) {
  const workOff = prefix.length;
  const dataLen = workOff + 64;
  const padLen = Math.ceil(dataLen / 64) * 64;
  const blocks = padLen / 64;
  const mutBlock = Math.floor(workOff / 64);
  const buf = new Uint8Array(padLen);
  buf.set(prefix, 0);
  for (let i = dataLen;i < padLen; i++)
    buf[i] = 231;
  const W = new Uint32Array(104);
  const st = new Uint32Array(5);
  const pre = new Uint32Array(5);
  const compressBlock = (off) => {
    for (let i = 0;i < 16; i++)
      W[i] = u32(buf[off + 4 * i] << 24 | buf[off + 4 * i + 1] << 16 | buf[off + 4 * i + 2] << 8 | buf[off + 4 * i + 3]);
    for (let i = 16;i < 104; i++)
      W[i] = rotl32(u32(W[i - 16] ^ W[i - 14] ^ W[i - 8] ^ W[i - 3]), 1);
    const o0 = st[0], o1 = st[1], o2 = st[2], o3 = st[3], o4 = st[4];
    let l9 = o4, l3 = o3, l4 = o2, l2 = o1, l8 = o0, l1 = 0, l5 = 0, l10 = 0;
    for (let l6 = 0;l6 < 104; l6++) {
      l10 = l8;
      l5 = l4;
      l1 = l3;
      const Wi = W[l6];
      let f, K2;
      if (l6 <= 19) {
        f = u32(l1 & ~l2 | l2 & l5);
        K2 = 2115527438;
      } else if (l6 <= 39) {
        f = u32(l2 ^ l5 ^ l1);
        K2 = 2474983467;
      } else if (l6 <= 59) {
        f = u32((l1 | l5) & l2 | l1 & l5);
        K2 = 1799268564;
      } else if (l6 <= 79) {
        f = u32(l2 ^ l5 ^ l1);
        K2 = 2158724593;
      } else {
        f = u32(l2 ^ l5 ^ l1);
        K2 = l6 < 100 ? 1415510629 : 3404864840;
      }
      l8 = u32(Wi + K2 + f + l9 + rotl32(l10, 5));
      l4 = rotl32(l2, 30);
      l9 = l1;
      l3 = l5;
      l2 = l10;
    }
    let h4 = l1;
    if (!(u32(l1 ^ 1556319504) > 1395997415 || l1 < 1427347847 || u32(l1 ^ 2157738716) < 3736732699)) {
      const R = u32(l1 ^ 4021413472) < 252651751 ? 3258059997 : l1;
      h4 = l1 === 3258059997 ? R : l1;
    }
    st[4] = u32(h4 + o4);
    st[0] = u32(l8 + o0);
    st[3] = u32(l3 + o3 + 307218999);
    st[2] = u32(l4 + o2 + 771149088);
    let v = u32(l2 ^ 887296560) < 3061017796 ? u32(l2 + 2090069385) : l2;
    v = u32(l2 ^ 3545673717) < 2474395071 ? v : l2;
    st[1] = u32(v + o1);
  };
  for (let i = 0;i < 5; i++)
    st[i] = IV5[i];
  for (let b = 0;b < mutBlock; b++)
    compressBlock(b * 64);
  pre.set(st);
  return (work) => {
    buf.set(work, workOff);
    st.set(pre);
    for (let b = mutBlock;b < blocks; b++)
      compressBlock(b * 64);
    if (gateBits === 17)
      return (st[0] & 8454143) === 0;
    const d = new Uint8Array(20);
    const dv = new DataView(d.buffer);
    dv.setUint32(0, st[0], true);
    let o1 = st[1];
    if (u32(st[1] ^ 1563231393) < 1989576360)
      o1 = u32(st[1] ^ 1563231393);
    if (st[1] < 1989576360)
      o1 = st[1];
    dv.setUint32(4, o1, true);
    dv.setUint32(8, u32(st[2] + 2842696648), true);
    dv.setUint32(12, st[3] >= 2635077790 ? u32(st[3] + 1584434432) : st[3], true);
    dv.setUint32(16, u32(st[4] ^ 1634346899), true);
    return leadingZeroBitsBE(d) >= gateBits;
  };
}

// src/versions/v8/idx1.ts
var K2 = [1689633247, -615979838 >>> 0, 1373374373, -932238712 >>> 0, 989616438, 1349072467, 673357564];
var CUSTOM_IV = Uint32Array.from([141610294, 3252919944, 3612375973, 3971832002, 36320735]);
var ADD = 86;
var MARKER = [65, 173, 146, 194];
var H0_FINAL_SUB = 1950853420;
var W4_THRESH = 2147483648;
var W4_ADD = 3751073898;
function customSha1Compress(H, block, off) {
  const W = new Uint32Array(133);
  for (let i = 0;i < 16; i++) {
    W[i] = (block[off + 4 * i] << 24 | block[off + 4 * i + 1] << 16 | block[off + 4 * i + 2] << 8 | block[off + 4 * i + 3]) >>> 0;
  }
  for (let i = 16;i < 133; i++)
    W[i] = rotl32((W[i - 3] ^ W[i - 8] ^ W[i - 14] ^ W[i - 16]) >>> 0, 1);
  let l2 = H[0], l3 = H[1], l9 = H[2], l1 = H[3], l8 = H[4];
  for (let i = 0;i < 133; i++) {
    const l6 = l2, l4 = l9, Wi = W[i];
    let f, k;
    if (i <= 19) {
      f = (l1 & ~l3 | l3 & l4) >>> 0;
      k = K2[0];
    } else if (i <= 39) {
      f = (l3 ^ l4 ^ l1) >>> 0;
      k = K2[1];
    } else if (i <= 59) {
      f = ((l1 | l4) & l3 | l1 & l4) >>> 0;
      k = K2[2];
    } else if (i <= 79) {
      f = (l3 ^ l4 ^ l1) >>> 0;
      k = K2[3];
    } else if (i <= 99) {
      f = (l3 ^ l4 ^ l1) >>> 0;
      k = K2[4];
    } else {
      f = (l3 ^ l4 ^ l1) >>> 0;
      k = i < 120 ? K2[5] : K2[6];
    }
    l2 = l8 + rotl32(l6, 5) + f + k + Wi >>> 0;
    l9 = rotl32(l3, 30);
    l8 = l1;
    l1 = l4;
    l3 = l6;
  }
  H[0] = H[0] + l2 >>> 0;
  H[1] = H[1] + l3 >>> 0;
  H[2] = H[2] + l9 >>> 0;
  H[3] = H[3] + l1 + 136540528 >>> 0;
  H[4] = H[4] + l8 >>> 0;
  return H;
}
function mbfHashData(data) {
  const baseLen = data.length + MARKER.length;
  const padLen = Math.ceil(baseLen / 64) * 64;
  const buf = new Uint8Array(padLen).fill(189);
  for (let i = 0;i < data.length; i++)
    buf[i] = data[i] + ADD & 255;
  for (let i = 0;i < MARKER.length; i++)
    buf[data.length + i] = MARKER[i];
  const H = Uint32Array.from(CUSTOM_IV);
  for (let o = 0;o < buf.length; o += 64)
    customSha1Compress(H, buf, o);
  return H;
}
function func327digest20(data) {
  const H = mbfHashData(data);
  const w0 = H[0] - H0_FINAL_SUB >>> 0;
  let w4 = H[4] >>> 0;
  if (w4 >= W4_THRESH)
    w4 = w4 + W4_ADD >>> 0;
  const out = new Uint8Array(20);
  const dv = new DataView(out.buffer);
  dv.setUint32(0, w0, true);
  dv.setUint32(4, H[1] >>> 0, true);
  dv.setUint32(8, H[2] >>> 0, true);
  dv.setUint32(12, H[3] >>> 0, true);
  dv.setUint32(16, w4, true);
  return out;
}
function makeIdx1Gate(prefix, gateBits) {
  const dataLen = prefix.length + 64;
  const baseLen = dataLen + MARKER.length;
  const padLen = Math.ceil(baseLen / 64) * 64;
  const buf = new Uint8Array(padLen);
  const workOff = prefix.length;
  const mutBlock = Math.floor(workOff / 64);
  const W = new Uint32Array(133);
  const H = new Uint32Array(5);
  const pre = new Uint32Array(5);
  let p = 0;
  for (let i = 0;i < prefix.length; i++)
    buf[p++] = prefix[i] + ADD & 255;
  for (let i = 0;i < 64; i++)
    buf[p++] = ADD;
  for (let i = 0;i < MARKER.length; i++)
    buf[p++] = MARKER[i];
  for (;p < padLen; p++)
    buf[p] = 189;
  const compress = (off) => {
    for (let i = 0, q = off;i < 16; i++, q += 4) {
      W[i] = (buf[q] << 24 | buf[q + 1] << 16 | buf[q + 2] << 8 | buf[q + 3]) >>> 0;
    }
    for (let i = 16;i < 133; i++)
      W[i] = rotl32((W[i - 3] ^ W[i - 8] ^ W[i - 14] ^ W[i - 16]) >>> 0, 1);
    let l2 = H[0], l3 = H[1], l9 = H[2], l1 = H[3], l8 = H[4];
    for (let i = 0;i < 133; i++) {
      const l6 = l2, l4 = l9, Wi = W[i];
      let f, k;
      if (i <= 19) {
        f = (l1 & ~l3 | l3 & l4) >>> 0;
        k = K2[0];
      } else if (i <= 39) {
        f = (l3 ^ l4 ^ l1) >>> 0;
        k = K2[1];
      } else if (i <= 59) {
        f = ((l1 | l4) & l3 | l1 & l4) >>> 0;
        k = K2[2];
      } else if (i <= 79) {
        f = (l3 ^ l4 ^ l1) >>> 0;
        k = K2[3];
      } else if (i <= 99) {
        f = (l3 ^ l4 ^ l1) >>> 0;
        k = K2[4];
      } else {
        f = (l3 ^ l4 ^ l1) >>> 0;
        k = i < 120 ? K2[5] : K2[6];
      }
      l2 = l8 + rotl32(l6, 5) + f + k + Wi >>> 0;
      l9 = rotl32(l3, 30);
      l8 = l1;
      l1 = l4;
      l3 = l6;
    }
    H[0] = H[0] + l2 >>> 0;
    H[1] = H[1] + l3 >>> 0;
    H[2] = H[2] + l9 >>> 0;
    H[3] = H[3] + l1 + 136540528 >>> 0;
    H[4] = H[4] + l8 >>> 0;
  };
  H[0] = CUSTOM_IV[0];
  H[1] = CUSTOM_IV[1];
  H[2] = CUSTOM_IV[2];
  H[3] = CUSTOM_IV[3];
  H[4] = CUSTOM_IV[4];
  for (let off = 0;off < mutBlock * 64; off += 64)
    compress(off);
  pre.set(H);
  return (work) => {
    for (let i = 0, q = workOff;i < 64; i++, q++)
      buf[q] = work[i] + ADD & 255;
    H.set(pre);
    for (let off = mutBlock * 64;off < padLen; off += 64)
      compress(off);
    const w0 = H[0] - H0_FINAL_SUB >>> 0;
    return gateBits === 17 ? (w0 & 8454143) === 0 : leadingZeroBitsLE32(w0) >= gateBits;
  };
}
var DIFF_T = [352, 353, 354, 355, 348, 349, 350, 351, 4, 5, 6, 7, null, 1, 2, 3, 336, 337, 338, 339, 332, 333, 334, 335, 344, 345, 346, 347, 340, 341, 342, 343, 320, 321, 322, 323, 316, 317, 318, 319, 328, 329, 330, 331, 324, 325, 326, 327, 304, 305, 306, 307, 300, 301, 302, 303, 312, 313, 314, 315, 308, 309, 310, 311, 288, 289, 290, 291, 284, 285, 286, 287, 296, 297, 298, 299, 292, 293, 294, 295, 272, 273, 274, 275, 268, 269, 270, 271, 280, 281, 282, 283, 276, 277, 278, 279, 256, 257, 258, 259, 252, 253, 254, 255, 264, 265, 266, 267, 260, 261, 262, 263, 240, 241, 242, 243, 236, 237, 238, 239, 248, 249, 250, 251, 244, 245, 246, 247, 124, 125, 126, 127, 120, 121, 122, 123, 132, 133, 134, 135, 128, 129, 130, 131, 108, 109, 110, 111, 104, 105, 106, 107, 116, 117, 118, 119, 112, 113, 114, 115, 92, 93, 94, 95, 88, 89, 90, 91, 100, 101, 102, 103, 96, 97, 98, 99, 76, 77, 78, 79, 72, 73, 74, 75, 84, 85, 86, 87, 80, 81, 82, 83, 60, 61, 62, 63, 56, 57, 58, 59, 68, 69, 70, 71, 64, 65, 66, 67, 44, 45, 46, 47, 40, 41, 42, 43, 52, 53, 54, 55, 48, 49, 50, 51, 28, 29, 30, 31, 24, 25, 26, 27, 36, 37, 38, 39, 32, 33, 34, 35, 12, 13, 14, 15, 8, 9, 10, 11, 20, 21, 22, 23, 16, 17, 18, 19];
var DIFF_VALID3 = new Set([2, 3, 8, 9, 12, 13, 14, 15]);
function decodeIdx1Difficulty(ch) {
  const h0 = ch[0], h1 = ch[1], h3 = ch[3];
  if (!DIFF_VALID3.has(h3 & 15))
    return null;
  if (h1 & 1)
    return null;
  const base = DIFF_T[h0];
  return base == null ? null : base;
}

// src/versions/v8/data/keys.json
var keys_default = {
  "0": {
    digest: "family",
    seed: 3700993783,
    SUB: "0xaa8792762d22b4e4",
    gateBits: 17,
    maskSuffix: "00000000",
    maskDerivable: true,
    winIter: 336753,
    KEY: [
      49,
      193,
      104,
      97
    ]
  },
  "1": {
    digest: "func327",
    seed: 3700993799,
    SUB: "0xdbe3acad117ccb88",
    gateBits: 17,
    maskSuffix: "74538690",
    maskDerivable: false
  },
  "2": {
    digest: "family",
    seed: 3700993815,
    SUB: "0x6508211bb2c79215",
    gateBits: 17,
    maskSuffix: "00000000",
    maskDerivable: true,
    winIter: 123117,
    KEY: [
      28,
      64,
      46,
      82
    ]
  },
  "3": {
    digest: "family",
    seed: 3700993831,
    SUB: "0xa671592b3b279cee",
    gateBits: 17,
    maskSuffix: "00000000",
    maskDerivable: true,
    winIter: 65502,
    KEY: [
      214,
      189,
      233,
      102
    ]
  },
  "4": {
    digest: "family",
    seed: 3700993847,
    SUB: "0x185ad9ad1a7ed529",
    gateBits: 17,
    maskSuffix: "00000000",
    maskDerivable: true,
    winIter: 88018,
    KEY: [
      9,
      127,
      69,
      37
    ]
  },
  "5": {
    digest: "family",
    seed: 3700993863,
    SUB: "0x2d010c92601def2b",
    gateBits: 17,
    maskSuffix: "c8116e3b",
    maskDerivable: false,
    winIter: 41639,
    KEY: [
      17,
      213,
      246,
      207
    ]
  },
  "6": {
    digest: "family",
    seed: 3700993879,
    SUB: "0x99b1a2963e14a1fe",
    gateBits: 17,
    maskSuffix: "00000000",
    maskDerivable: true,
    winIter: 57297,
    KEY: [
      132,
      22,
      92,
      67
    ]
  },
  "7": {
    digest: "family",
    seed: 3700993895,
    SUB: "0xa2e20f7611aa6505",
    gateBits: 17,
    maskSuffix: "00000000",
    maskDerivable: true,
    winIter: 131324,
    KEY: [
      110,
      204,
      79,
      251
    ]
  },
  "8": {
    digest: "family",
    seed: 3700993911,
    SUB: "0x558736c95c7e34d8",
    gateBits: 17,
    maskSuffix: "00000000",
    maskDerivable: true,
    winIter: 152801,
    KEY: [
      59,
      192,
      188,
      255
    ]
  },
  "9": {
    digest: "family",
    seed: 3700993927,
    SUB: "0x6e5518d86dec5c65",
    gateBits: 17,
    maskSuffix: "a0f6244d",
    maskDerivable: false,
    winIter: 29895,
    KEY: [
      48,
      88,
      247,
      253
    ]
  },
  "10": {
    digest: "family",
    seed: 3700993943,
    SUB: "0x5c531bb03f248898",
    gateBits: 17,
    maskSuffix: "00000000",
    maskDerivable: true,
    winIter: 386218,
    KEY: [
      50,
      32,
      66,
      86
    ]
  },
  "11": {
    digest: "family",
    seed: 3700993959,
    SUB: "0x5c291ae4fd9fc70b",
    gateBits: 17,
    maskSuffix: "00000000",
    maskDerivable: true,
    winIter: 65604,
    KEY: [
      163,
      126,
      69,
      250
    ]
  },
  "12": {
    digest: "family",
    seed: 3700993975,
    SUB: "0xbd7cdbe91e5d99be",
    gateBits: 17,
    maskSuffix: "00000000",
    maskDerivable: true,
    winIter: 14999,
    KEY: [
      79,
      243,
      46,
      91
    ]
  },
  "13": {
    digest: "family",
    seed: 3700993991,
    SUB: "0x555a4fa923b8cfc",
    gateBits: 17,
    maskSuffix: "00000000",
    maskDerivable: true,
    winIter: 22368,
    KEY: [
      246,
      171,
      78,
      229
    ]
  },
  "14": {
    digest: "family",
    seed: 3700994007,
    SUB: "0x322751366746e92",
    gateBits: 17,
    maskSuffix: "bbaf2531",
    maskDerivable: false,
    winIter: 215866,
    KEY: [
      217,
      163,
      144,
      11
    ]
  },
  "15": {
    digest: "family",
    seed: 3700994023,
    SUB: "0x4f35fc78346e8df9",
    gateBits: 17,
    maskSuffix: "00000000",
    maskDerivable: true,
    winIter: 60431,
    KEY: [
      105,
      71,
      80,
      216
    ]
  },
  "16": {
    digest: "family",
    seed: 3700994039,
    SUB: "0x3deadd2afe83d72c",
    gateBits: 17,
    maskSuffix: "00000000",
    maskDerivable: true,
    winIter: 148199,
    KEY: [
      147,
      105,
      65,
      208
    ]
  },
  "17": {
    digest: "family",
    seed: 3700994055,
    SUB: "0x621e3d4d998628e0",
    gateBits: 17,
    maskSuffix: "00000000",
    maskDerivable: true,
    winIter: 155302,
    KEY: [
      94,
      223,
      14,
      55
    ]
  },
  "18": {
    digest: "family",
    seed: 3700994071,
    SUB: "0x3d983095e2239b4d",
    gateBits: 17,
    maskSuffix: "99b8e382",
    maskDerivable: false,
    winIter: 245075,
    KEY: [
      102,
      232,
      86,
      250
    ]
  },
  "19": {
    digest: "family",
    seed: 3700994087,
    SUB: "0x2309526993838da3",
    gateBits: 17,
    maskSuffix: "2fb1e2a3",
    maskDerivable: false,
    winIter: 339641,
    KEY: [
      63,
      73,
      76,
      200
    ]
  },
  "20": {
    digest: "family",
    seed: 3700994103,
    SUB: "0x57bd05c5a858f656",
    gateBits: 17,
    maskSuffix: "52c385c2",
    maskDerivable: false,
    winIter: 53910,
    KEY: [
      246,
      238,
      83,
      121
    ]
  },
  "21": {
    digest: "family",
    seed: 3700994119,
    SUB: "0x433cb3ffed9f9294",
    gateBits: 17,
    maskSuffix: "f0375db6",
    maskDerivable: false,
    winIter: 103692,
    KEY: [
      168,
      121,
      212,
      219
    ]
  },
  "22": {
    digest: "func176",
    seed: 3700994135,
    SUB: "0x4E65731D7B08EF81",
    gateBits: 17,
    maskSuffix: "00000000",
    maskDerivable: true
  },
  "23": {
    digest: "family",
    seed: 3700994151,
    SUB: "0x5f4784d1f281ab3a",
    gateBits: 17,
    maskSuffix: "00000000",
    maskDerivable: true,
    winIter: 83104,
    KEY: [
      91,
      93,
      55,
      128
    ]
  },
  "24": {
    digest: "family",
    seed: 3700994167,
    SUB: "0xa4417cdee9971d1b",
    gateBits: 17,
    maskSuffix: "00000000",
    maskDerivable: true,
    winIter: 135580,
    KEY: [
      140,
      20,
      6,
      69
    ]
  }
};

// src/versions/v8/data/digest-configs.json
var digest_configs_default = {
  "0": { ok: true, wrapperFuncidx: 663, coreFuncidx: 57, coreConfig: { funcidx: 57, rounds: 106, schedule: { taps: [16, 14, 8, 3], rotl: 1 }, bigEndianLoad: true, rotlA: 5, rotlB: 30, bands: [{ upTo: 19, K: 1449452748, f: "CH" }, { upTo: 39, K: 1808908777, f: "PARITY" }, { upTo: 59, K: 2168364806, f: "MAJ" }, { upTo: 79, K: 2527820835, f: "PARITY" }, { upTo: 99, K: 3128344939, f: "PARITY" }, { upTo: 105, K: 822731854, f: "PARITY" }], finalize: [null, null, { tweak: { kind: "xor", val: 2265348228 } }, null, { tweak: { kind: "xor", val: 2581607102 } }], coreFinalizeJs: ["u32(a + h0)", "u32(b + h1)", "u32(u32(c ^ 0x87067884) + h2)", "u32(u32(d + h3) - 0xe44089c)", "u32(u32(e ^ 0x99e032be) + h4)"] }, wrapper: { iv: [2892683521, 2149469557, 4138823768, 2868381615, 562768530], transform: "identity", pad: { marker: [], fill: 247 }, wrapperFinalizeJs: ["s0", "(((s1 >>> 0) < (0x6599bf23 >>> 0)) ? u32(s1 + 0x1a070dad) : s1)", "(((u32(s2 ^ 0x7a4edb2c) >>> 0) < (0x8985897a >>> 0)) ? (((u32(s2 ^ 0xe0ff8894) >>> 0) < (0x8985897a >>> 0)) ? s2 : u32(s2 ^ 0x9ab153b8)) : s2)", "u32(s3 - 0x5bfdcd10)", "(((s4 >>> 0) > (0x67c0f890 >>> 0)) ? (((u32(s4 ^ 0x76f8a8ca) >>> 0) > (0x67c0f890 >>> 0)) ? s4 : u32(s4 ^ 0x76f8a8ca)) : s4)"], outEndian: "le" } },
  "2": { ok: true, wrapperFuncidx: 90, coreFuncidx: 42, coreConfig: { funcidx: 42, rounds: 84, schedule: { taps: [16, 14, 8, 3], rotl: 1 }, bigEndianLoad: true, rotlA: 5, rotlB: 30, bands: [{ upTo: 19, K: 2484516498, f: "CH" }, { upTo: 39, K: 2843972527, f: "PARITY" }, { upTo: 59, K: 2168257624, f: "MAJ" }, { upTo: 79, K: 2527713653, f: "PARITY" }, { upTo: 83, K: 4009125121, f: "PARITY" }], finalize: [null, null, null, null, null], coreFinalizeJs: ["u32(a + h0)", "u32(b + h1)", "u32(c + h2)", "u32(d + h3)", "u32(e + h4)"] }, wrapper: { iv: [822234475, 959907875, 2949262086, 643649001, 2633003212], transform: [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 14, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255], pad: { marker: [], fill: 239 }, wrapperFinalizeJs: ["s0", "u32(s1 + 0x406ae8a1)", "const t0=(s2^0x73e90040);const t1=(u32(t0));const t2=(t1>>>0);const t3=(0x1fe506e>>>0);const t4=(t2<t3);const t5=(!t4);const t6=(s2^0xdb0bf6dc);const t7=(u32(t6));const t8=(t7>>>0);const t9=(0x39876381>>>0);const t10=(t8<t9);const t11=(!t10);const t12=(t5&&t11);const t13=(s2+0x3c280546);const t14=(u32(t13));const t15=(t14^0xdb0bf6dc);const t16=(u32(t15));const t17=(t16>>>0);const t18=(t17<t9);const t19=(t12&&t18);const t20=(!t19);const t21=(t5&&t10);const t22=(s2+0x78500a8c);const t23=(u32(t22));const t24=(t23^0x73e90040);const t25=(u32(t24));const t26=(t21?t1:t25);const t27=(t4?t1:t26);const t28=(t27>>>0);const t29=(t28<t3);const t30=(t20&&t29);const t31=(t21?s2:t23);const t32=(t4?s2:t31);const t33=(!t29);const t34=(t20&&t33);const t35=(t23^0xdb0bf6dc);const t36=(u32(t35));const t37=(t21?t7:t36);const t38=(t4?t7:t37);const t39=(t38>>>0);const t40=(t39<t9);const t41=(t34&&t40);const t42=(t32+0x3c280546);const t43=(u32(t42));const t44=(t43^0xdb0bf6dc);const t45=(u32(t44));const t46=(t45>>>0);const t47=(0x39876380>>>0);const t48=(t46>t47);const t49=(t32+0x78500a8c);const t50=(u32(t49));const t51=(t48?t50:t43);const t52=(t41?t32:t51);const t53=(t30?t32:t52);const t54=(t19?t14:t53);return (t54)>>>0;", "s3", "(((s4 >>> 0) < (0x179f19c0 >>> 0)) ? u32(s4 + 0x5307b3b5) : s4)"], outEndian: "le" } },
  "3": { ok: true, wrapperFuncidx: 64, coreFuncidx: 37, coreConfig: { funcidx: 37, rounds: 91, schedule: { taps: [16, 14, 8, 3], rotl: 1 }, bigEndianLoad: true, rotlA: 5, rotlB: 30, bands: [{ upTo: 19, K: 1749050373, f: "CH" }, { upTo: 39, K: 3738404584, f: "PARITY" }, { upTo: 59, K: 2467962431, f: "MAJ" }, { upTo: 79, K: 162349346, f: "PARITY" }, { upTo: 90, K: 1049033564, f: "PARITY" }], finalize: [null, { tweak: { kind: "xor", val: 1733322224 } }, null, { tweak: { kind: "condSub", gt: 1300433049, sub: 739026592 } }, null], coreFinalizeJs: ["u32(a + h0)", "u32((((u32(b ^ 0xfdef2542) >>> 0) > (0xbb3c7141 >>> 0)) ? u32(b ^ 0x675065f0) : b) + h1)", "u32(c + h2)", "u32((((u32(d ^ 0xd3156b08) >>> 0) > (0x4d830899 >>> 0)) ? u32(d - 0x2c0ca6a0) : d) + h3)", "u32((((e >>> 0) === (0x5c824825 >>> 0)) ? 0xfb14b562 : e) + h4)"] }, wrapper: { iv: [527212032, 2449067182, 2808523211, 2132808308, 2492264337], transform: [37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 232, 233, 234, 235, 236, 237, 238, 239, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36], pad: { marker: [36, 25, 213, 227], fill: 228 }, finalize: [null, null, { kind: "expr", js: "u32(v + 0x4dfb6d43)" }, { kind: "expr", js: "u32(v + 0x5b9fd742)" }, { kind: "expr", js: "u32(v + 0x7e016178)" }], outEndian: "le" } },
  "4": { ok: true, wrapperFuncidx: 670, coreFuncidx: 61, coreConfig: { funcidx: 61, rounds: 102, schedule: { taps: [16, 14, 8, 3], rotl: 1 }, bigEndianLoad: true, rotlA: 5, rotlB: 30, bands: [{ upTo: 19, K: 2543933624, f: "CH" }, { upTo: 39, K: 2903389653, f: "PARITY" }, { upTo: 59, K: 3262845682, f: "MAJ" }, { upTo: 79, K: 3622301711, f: "PARITY" }, { upTo: 99, K: 3065699055, f: "PARITY" }, { upTo: 101, K: 760085970, f: "PARITY" }], finalize: [null, null, { tweak: { kind: "xor", val: 1554640856 } }, { tweak: { kind: "xor", val: 3992906688 } }, { tweak: { kind: "xor", val: 2273552914 } }], coreFinalizeJs: ["((((((a >>> 0) <= (0xec9ee5d6 >>> 0))) || ((!(((a >>> 0) <= (0xec9ee5d6 >>> 0))))))) ? (u32(u32(a + h0) - 0x45597836)) : (h0))", "((((((a >>> 0) <= (0xec9ee5d6 >>> 0))) || ((!(((a >>> 0) <= (0xec9ee5d6 >>> 0))))))) ? (u32(u32(b + h1) - 0x690ae42a)) : (h1))", "((((((a >>> 0) <= (0xec9ee5d6 >>> 0))) || ((!(((a >>> 0) <= (0xec9ee5d6 >>> 0))))))) ? (u32(u32(c ^ 0x5ca9efd8) + h2)) : (h2))", "((((((d >>> 0) <= (0xec9ee5d6 >>> 0))) || ((!(((d >>> 0) <= (0xec9ee5d6 >>> 0))))))) ? (u32(((((d >>> 0) <= (0xec9ee5d6 >>> 0))) ? ((((d >>> 0) === (0xc01dd876 >>> 0)) ? (((u32(d ^ 0xedfeebc0) >>> 0) < (0xe6fbcfb0 >>> 0)) ? 0xb1c0a0aa : d) : d)) : (d)) + h3)) : (h3))", "((((((a >>> 0) <= (0xec9ee5d6 >>> 0))) || ((!(((a >>> 0) <= (0xec9ee5d6 >>> 0))))))) ? (u32(u32(e ^ 0x8783aa12) + h4)) : (h4))"] }, wrapper: { iv: [3987164397, 1019325001, 3008679212, 1738237059, 3727591270], transform: "identity", pad: { marker: [], fill: 175 }, wrapperFinalizeJs: ["u32(s0 - 0x4fe33ed6)", "s1", "((((u32(s2 ^ 0x6fbf3768) >>> 0) < (0xcef760be >>> 0))) ? (s2) : ((((((!(((u32(s2 ^ 0x6fbf3768) >>> 0) < (0xcef760be >>> 0))))) && (((u32(s2 ^ 0x37185a64) >>> 0) < (0x48ddf70a >>> 0))))) ? (s2) : ((((u32(u32(s2 + 0x8dddc3d) ^ 0x37185a64) >>> 0) > (0x48ddf709 >>> 0)) ? u32(s2 + 0x11bbb87a) : u32(s2 + 0x8dddc3d))))))", "s3", "s4"], outEndian: "le" } },
  "5": { ok: true, wrapperFuncidx: 643, coreFuncidx: 36, coreConfig: { funcidx: 36, rounds: 85, schedule: { taps: [16, 14, 8, 3], rotl: 1 }, bigEndianLoad: true, rotlA: 5, rotlB: 30, bands: [{ upTo: 19, K: 2644540819, f: "CH" }, { upTo: 39, K: 338927734, f: "PARITY" }, { upTo: 59, K: 2328281945, f: "MAJ" }, { upTo: 79, K: 22668860, f: "PARITY" }, { upTo: 84, K: 4169149442, f: "PARITY" }], finalize: [null, { tweak: { kind: "xor", val: 3230845277 } }, null, { tweak: { kind: "xor", val: 3185199171 } }, { tweak: { kind: "xor", val: 187938338 } }], coreFinalizeJs: ["u32(u32(a + h0) - 0x452d947)", "u32(u32(b ^ 0xc092c95d) + h1)", "u32((((u32(c - 0x703edf77) >>> 0) < (0xd54d175 >>> 0)) ? u32(c - 0x66c984a4) : c) + h2)", "u32((((u32(d ^ 0xbdda4843) >>> 0) < (0xc6fb2749 >>> 0)) ? u32(d - 0x311604b5) : d) + h3)", "u32((((e >>> 0) < (0x8c16b749 >>> 0)) ? (((u32(e ^ 0xb33b622) >>> 0) < (0x8c16b749 >>> 0)) ? e : u32(e ^ 0xb33b622)) : e) + h4)"] }, wrapper: { iv: [233247978, 1119932196, 1479388225, 1838844254, 2198300283], transform: [100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99], pad: { marker: [133, 59, 24, 1], fill: 131 }, finalize: [null, { kind: "expr", js: "(!(((v >>> 0) < (0x2977abfb >>> 0)) || ((u32(v ^ 0xd399a521) >>> 0) < (0xba6df89b >>> 0)))) ? (u32(v + 0x1c3eca12)) : (v)" }, { kind: "expr", js: "u32(v - 0x53fcc8e4)" }, { kind: "expr", js: "u32(v - 0x111a03d6)" }, { kind: "expr", js: "u32(v + 0x2686e0f3)" }], outEndian: "le" } },
  "6": { ok: true, wrapperFuncidx: 615, coreFuncidx: 60, coreConfig: { funcidx: 60, rounds: 96, schedule: { taps: [16, 14, 8, 3], rotl: 1 }, bigEndianLoad: true, rotlA: 5, rotlB: 30, bands: [{ upTo: 19, K: 3825132990, f: "CH" }, { upTo: 39, K: 4184589019, f: "PARITY" }, { upTo: 59, K: 3508874116, f: "MAJ" }, { upTo: 79, K: 3868330145, f: "PARITY" }, { upTo: 95, K: 3125116181, f: "PARITY" }], finalize: [null, null, null, { tweak: { kind: "xor", val: 2677842 } }, { tweak: { kind: "xor", val: 3578733080 } }], coreFinalizeJs: ["u32(a + h0)", "u32(((((u32(b ^ 0xd54f2218) >>> 0) < (0x1aaf877c >>> 0)) || ((b >>> 0) > (0x53d96693 >>> 0)) || ((u32(b ^ 0x15690e2e) >>> 0) > (0x9952c6e5 >>> 0))) ? (b) : ((((b >>> 0) > (0x4552e008 >>> 0)) ? (((u32(b ^ 0x58291a10) >>> 0) > (0x34ef3bdb >>> 0)) ? u32(b ^ 0x3727d438) : b) : b))) + h1)", "u32(c + h2)", "u32(((((u32(d ^ 0x28dc52) >>> 0) >= (0x7d5cd42 >>> 0))) ? ((((d >>> 0) < (0x66b320ce >>> 0)) ? (((u32(d ^ 0xea8f53e0) >>> 0) > (0xc42c811f >>> 0)) ? u32(d + 0x1f5d0b1) : d) : d)) : (d)) + h3)", "u32(e + h4)"] }, wrapper: { iv: [4001767479, 230182503, 2219536714, 4208890925, 1903277840], transform: "identity", pad: { marker: [], fill: 103 }, wrapperFinalizeJs: ["s0", "(((s1 >>> 0) === (0x43d7d6eb >>> 0)) ? 0x68707c4 : s1)", "s2", "s3", "s4"], outEndian: "le" } },
  "7": { ok: true, wrapperFuncidx: 586, coreFuncidx: 35, coreConfig: { funcidx: 35, rounds: 103, schedule: { taps: [16, 14, 8, 3], rotl: 1 }, bigEndianLoad: true, rotlA: 5, rotlB: 30, bands: [{ upTo: 19, K: 2703957945, f: "CH" }, { upTo: 39, K: 398344860, f: "PARITY" }, { upTo: 59, K: 3422870003, f: "MAJ" }, { upTo: 79, K: 1117256918, f: "PARITY" }, { upTo: 99, K: 4228566568, f: "PARITY" }, { upTo: 102, K: 293055301, f: "PARITY" }], finalize: [null, null, { tweak: { kind: "condSub", gt: 2585018648, sub: 285154304 } }, null, null], coreFinalizeJs: ["u32(a + h0)", "u32(b + h1)", "u32((((c >>> 0) > (0x9a144118 >>> 0)) ? u32(c - 0x10ff1c00) : c) + h2)", "u32(d + h3)", "u32(e + h4)"] }, wrapper: { iv: [1482119604, 1333632890, 1693088919, 1017374016, 1376830045], transform: "identity", pad: { marker: [5, 179, 1, 47], fill: 215 }, finalize: [null, null, { kind: "expr", js: "(!(((v >>> 0) < (0x40efd8d6 >>> 0)) || ((u32(v ^ 0xdaad5831) >>> 0) < (0x3a345cf5 >>> 0)))) ? ((((u32(v ^ 0x7dc47dc2) >>> 0) > (0x40efd8d5 >>> 0)) ? v : u32(v ^ 0x7dc47dc2))) : (v)" }, null, null], outEndian: "le" } },
  "8": { ok: true, wrapperFuncidx: 559, coreFuncidx: 59, coreConfig: { funcidx: 59, rounds: 114, schedule: { taps: [16, 14, 8, 3], rotl: 1 }, bigEndianLoad: true, rotlA: 5, rotlB: 30, bands: [{ upTo: 19, K: 3113132276, f: "CH" }, { upTo: 39, K: 3472588305, f: "PARITY" }, { upTo: 59, K: 3832044334, f: "MAJ" }, { upTo: 79, K: 4191500363, f: "PARITY" }, { upTo: 99, K: 34206467, f: "PARITY" }, { upTo: 113, K: 2023560678, f: "PARITY" }], finalize: [null, null, null, { tweak: { kind: "condSub", gt: 2509517184, sub: 731264233 } }, null], coreFinalizeJs: ["u32(a + h0)", "u32(b + h1)", "const t0=(c^0x4b48a02);const t1=(u32(t0));const t2=(t1>>>0);const t3=(0x95943181>>>0);const t4=(t2<t3);const t5=(!t4);const t6=(c-0x2b9634e9);const t7=(u32(t6));const t8=(t7^0x4b48a02);const t9=(u32(t8));const t10=(t9>>>0);const t11=(t10<t3);const t12=(t5&&t11);const t13=(!t11);const t14=(t5&&t13);const t15=(c-0x572c69d2);const t16=(u32(t15));const t17=(t16^0x4b48a02);const t18=(u32(t17));const t19=(t18>>>0);const t20=(t19<t3);const t21=(t14&&t20);const t22=(!t20);const t23=(t14&&t22);const t24=(c+0x7d3d6145);const t25=(u32(t24));const t26=(t25^0x4b48a02);const t27=(u32(t26));const t28=(t27>>>0);const t29=(t28<t3);const t30=(t23&&t29);const t31=(!t29);const t32=(t23&&t31);const t33=(c+0x51a72c5c);const t34=(u32(t33));const t35=(t34^0x4b48a02);const t36=(u32(t35));const t37=(t36>>>0);const t38=(t37<t3);const t39=(t32&&t38);const t40=(!t38);const t41=(t32&&t40);const t42=(c+0x2610f773);const t43=(u32(t42));const t44=(t43^0x4b48a02);const t45=(u32(t44));const t46=(t45>>>0);const t47=(t46<t3);const t48=(t41&&t47);const t49=(!t47);const t50=(t41&&t49);const t51=(c-0x5853d76);const t52=(u32(t51));const t53=(t52^0x4b48a02);const t54=(u32(t53));const t55=(t54>>>0);const t56=(t55<t3);const t57=(t50&&t56);const t58=(c-0x311b725f);const t59=(u32(t58));const t60=(t59^0x4b48a02);const t61=(u32(t60));const t62=(t61>>>0);const t63=(0x95943180>>>0);const t64=(t62>t63);const t65=(c-0x5cb1a748);const t66=(u32(t65));const t67=(t64?t66:t59);const t68=(t57?t52:t67);const t69=(t48?t43:t68);const t70=(t39?t34:t69);const t71=(t30?t25:t70);const t72=(t21?t16:t71);const t73=(t12?t7:t72);const t74=(t4?c:t73);const t75=(t74+h2);const t76=(u32(t75));return (t76)>>>0;", "u32((((d >>> 0) === (0xe6cc29d0 >>> 0)) ? (((u32(d ^ 0xa4a46d7b) >>> 0) < (0x4c1683f1 >>> 0)) ? 0xeb3f7471 : d) : d) + h3)", "u32((((e >>> 0) > (0x421b9054 >>> 0)) ? (((u32(e + 0x1a51934) >>> 0) > (0x421b9054 >>> 0)) ? u32(e + 0x34a3268) : u32(e + 0x1a51934)) : e) + h4)"] }, wrapper: { iv: [107112185, 3813149085, 1507536000, 237093847, 2226448058], transform: [194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193], pad: { marker: [], fill: 25 }, wrapperFinalizeJs: ["s0", "const t0=(s1>>>0);const t1=(0xd21c7f16>>>0);const t2=(t0<t1);const t3=(!t2);const t4=(0xde588240>>>0);const t5=(t0<t4);const t6=(s1+0x24436cce);const t7=(u32(t6));const t8=(t5?t7:s1);const t9=(t8>>>0);const t10=(t9<t4);const t11=(t7^0x390709c3);const t12=(u32(t11));const t13=(s1^0x390709c3);const t14=(u32(t13));const t15=(t5?t12:t14);const t16=(t15>>>0);const t17=(0xab0cf708>>>0);const t18=(t16>t17);const t19=(t10&t18);const t20=(u32(t19));const t21=(t5|t20);const t22=(u32(t21));const t23=(!t22);const t24=(t22||t23);const t25=(t3&&t24);const t26=(t8+0x24436cce);const t27=(u32(t26));const t28=(t20?t27:t8);const t29=(t22?t28:s1);const t30=(t29>>>0);const t31=(t30<t4);const t32=(t28^0x390709c3);const t33=(u32(t32));const t34=(t22?t33:t14);const t35=(t34>>>0);const t36=(t35>t17);const t37=(t31&t36);const t38=(u32(t37));const t39=(t28+0x24436cce);const t40=(u32(t39));const t41=(t22?t40:t7);const t42=(t38?t41:t29);const t43=(t42>>>0);const t44=(t43<t4);const t45=(t40^0x390709c3);const t46=(u32(t45));const t47=(t22?t46:t12);const t48=(t38?t47:t34);const t49=(t48>>>0);const t50=(t49>t17);const t51=(t44&t50);const t52=(u32(t51));const t53=(t38|t52);const t54=(u32(t53));const t55=(t54>>>0);const t56=(t55===0);const t57=(t25&&t56);const t58=(t42+0x24436cce);const t59=(u32(t58));const t60=(t52?t59:t42);const t61=(t57?t29:t60);const t62=(t2?s1:t61);return (t62)>>>0;", "(((s2 >>> 0) === (0x857690d2 >>> 0)) ? (((u32(s2 ^ 0x48afa1c0) >>> 0) < (0x6b41fcc0 >>> 0)) ? 0x872f4cfe : s2) : s2)", "s3", "u32(s4 + 0x39edf621)"], outEndian: "le" } },
  "9": { ok: true, wrapperFuncidx: 531, coreFuncidx: 34, coreConfig: { funcidx: 34, rounds: 137, schedule: { taps: [16, 14, 8, 3], rotl: 1 }, bigEndianLoad: true, rotlA: 5, rotlB: 30, bands: [{ upTo: 19, K: 1606248311, f: "CH" }, { upTo: 39, K: 3595602522, f: "PARITY" }, { upTo: 59, K: 1289989437, f: "MAJ" }, { upTo: 79, K: 3279343648, f: "PARITY" }, { upTo: 99, K: 906231502, f: "PARITY" }, { upTo: 119, K: 1265687531, f: "PARITY" }, { upTo: 136, K: 589972628, f: "PARITY" }], finalize: [null, null, null, { tweak: { kind: "condSub", gt: 224751944, sub: 1865336269 } }, { tweak: { kind: "condSub", gt: 224751944, sub: 1865336269 } }], coreFinalizeJs: ["((((u32(u32(((a >>> 0) > (0xd657148 >>> 0)) & ((u32(a ^ 0x2e8ab4a0) >>> 0) > (0x6122085f >>> 0))) | u32((((u32(((a >>> 0) > (0xd657148 >>> 0)) & ((u32(a ^ 0x2e8ab4a0) >>> 0) > (0x6122085f >>> 0))) ? u32(a - 0x6f2ec5cd) : a) >>> 0) > (0xd657148 >>> 0)) & (((u32(((a >>> 0) > (0xd657148 >>> 0)) & ((u32(a ^ 0x2e8ab4a0) >>> 0) > (0x6122085f >>> 0))) ? u32(u32(a - 0x6f2ec5cd) ^ 0x2e8ab4a0) : u32(a ^ 0x2e8ab4a0)) >>> 0) > (0x6122085f >>> 0))))) || ((!(u32(u32(((a >>> 0) > (0xd657148 >>> 0)) & ((u32(a ^ 0x2e8ab4a0) >>> 0) > (0x6122085f >>> 0))) | u32((((u32(((a >>> 0) > (0xd657148 >>> 0)) & ((u32(a ^ 0x2e8ab4a0) >>> 0) > (0x6122085f >>> 0))) ? u32(a - 0x6f2ec5cd) : a) >>> 0) > (0xd657148 >>> 0)) & (((u32(((a >>> 0) > (0xd657148 >>> 0)) & ((u32(a ^ 0x2e8ab4a0) >>> 0) > (0x6122085f >>> 0))) ? u32(u32(a - 0x6f2ec5cd) ^ 0x2e8ab4a0) : u32(a ^ 0x2e8ab4a0)) >>> 0) > (0x6122085f >>> 0))))))))) ? (u32(a + h0)) : (h0))", "((((u32(u32(((a >>> 0) > (0xd657148 >>> 0)) & ((u32(a ^ 0x2e8ab4a0) >>> 0) > (0x6122085f >>> 0))) | u32((((u32(((a >>> 0) > (0xd657148 >>> 0)) & ((u32(a ^ 0x2e8ab4a0) >>> 0) > (0x6122085f >>> 0))) ? u32(a - 0x6f2ec5cd) : a) >>> 0) > (0xd657148 >>> 0)) & (((u32(((a >>> 0) > (0xd657148 >>> 0)) & ((u32(a ^ 0x2e8ab4a0) >>> 0) > (0x6122085f >>> 0))) ? u32(u32(a - 0x6f2ec5cd) ^ 0x2e8ab4a0) : u32(a ^ 0x2e8ab4a0)) >>> 0) > (0x6122085f >>> 0))))) || ((!(u32(u32(((a >>> 0) > (0xd657148 >>> 0)) & ((u32(a ^ 0x2e8ab4a0) >>> 0) > (0x6122085f >>> 0))) | u32((((u32(((a >>> 0) > (0xd657148 >>> 0)) & ((u32(a ^ 0x2e8ab4a0) >>> 0) > (0x6122085f >>> 0))) ? u32(a - 0x6f2ec5cd) : a) >>> 0) > (0xd657148 >>> 0)) & (((u32(((a >>> 0) > (0xd657148 >>> 0)) & ((u32(a ^ 0x2e8ab4a0) >>> 0) > (0x6122085f >>> 0))) ? u32(u32(a - 0x6f2ec5cd) ^ 0x2e8ab4a0) : u32(a ^ 0x2e8ab4a0)) >>> 0) > (0x6122085f >>> 0))))))))) ? (u32(b + h1)) : (h1))", "((((u32(u32(((a >>> 0) > (0xd657148 >>> 0)) & ((u32(a ^ 0x2e8ab4a0) >>> 0) > (0x6122085f >>> 0))) | u32((((u32(((a >>> 0) > (0xd657148 >>> 0)) & ((u32(a ^ 0x2e8ab4a0) >>> 0) > (0x6122085f >>> 0))) ? u32(a - 0x6f2ec5cd) : a) >>> 0) > (0xd657148 >>> 0)) & (((u32(((a >>> 0) > (0xd657148 >>> 0)) & ((u32(a ^ 0x2e8ab4a0) >>> 0) > (0x6122085f >>> 0))) ? u32(u32(a - 0x6f2ec5cd) ^ 0x2e8ab4a0) : u32(a ^ 0x2e8ab4a0)) >>> 0) > (0x6122085f >>> 0))))) || ((!(u32(u32(((a >>> 0) > (0xd657148 >>> 0)) & ((u32(a ^ 0x2e8ab4a0) >>> 0) > (0x6122085f >>> 0))) | u32((((u32(((a >>> 0) > (0xd657148 >>> 0)) & ((u32(a ^ 0x2e8ab4a0) >>> 0) > (0x6122085f >>> 0))) ? u32(a - 0x6f2ec5cd) : a) >>> 0) > (0xd657148 >>> 0)) & (((u32(((a >>> 0) > (0xd657148 >>> 0)) & ((u32(a ^ 0x2e8ab4a0) >>> 0) > (0x6122085f >>> 0))) ? u32(u32(a - 0x6f2ec5cd) ^ 0x2e8ab4a0) : u32(a ^ 0x2e8ab4a0)) >>> 0) > (0x6122085f >>> 0))))))))) ? (u32(c + h2)) : (h2))", "const t0=(d>>>0);const t1=(0xd657148>>>0);const t2=(t0>t1);const t3=(d^0x2e8ab4a0);const t4=(u32(t3));const t5=(t4>>>0);const t6=(0x6122085f>>>0);const t7=(t5>t6);const t8=(t2&t7);const t9=(u32(t8));const t10=(d-0x6f2ec5cd);const t11=(u32(t10));const t12=(t9?t11:d);const t13=(t12>>>0);const t14=(t13>t1);const t15=(t11^0x2e8ab4a0);const t16=(u32(t15));const t17=(t9?t16:t4);const t18=(t17>>>0);const t19=(t18>t6);const t20=(t14&t19);const t21=(u32(t20));const t22=(t9|t21);const t23=(u32(t22));const t24=(!t23);const t25=(t23||t24);const t26=(t12-0x6f2ec5cd);const t27=(u32(t26));const t28=(t21?t27:t12);const t29=(t23?t28:d);const t30=(t29>>>0);const t31=(t30>t1);const t32=(t28^0x2e8ab4a0);const t33=(u32(t32));const t34=(t23?t33:t4);const t35=(t34>>>0);const t36=(t35>t6);const t37=(t31&t36);const t38=(u32(t37));const t39=(t28-0x6f2ec5cd);const t40=(u32(t39));const t41=(t23?t40:t11);const t42=(t38?t41:t29);const t43=(t42>>>0);const t44=(t43>t1);const t45=(t40^0x2e8ab4a0);const t46=(u32(t45));const t47=(t23?t46:t16);const t48=(t38?t47:t34);const t49=(t48>>>0);const t50=(t49>t6);const t51=(t42-0x6f2ec5cd);const t52=(u32(t51));const t53=(t50?t52:t42);const t54=(t44?t53:t42);const t55=(t54+h3);const t56=(u32(t55));const t57=(t25?t56:h3);return (t57)>>>0;", "((((u32(u32(((a >>> 0) > (0xd657148 >>> 0)) & ((u32(a ^ 0x2e8ab4a0) >>> 0) > (0x6122085f >>> 0))) | u32((((u32(((a >>> 0) > (0xd657148 >>> 0)) & ((u32(a ^ 0x2e8ab4a0) >>> 0) > (0x6122085f >>> 0))) ? u32(a - 0x6f2ec5cd) : a) >>> 0) > (0xd657148 >>> 0)) & (((u32(((a >>> 0) > (0xd657148 >>> 0)) & ((u32(a ^ 0x2e8ab4a0) >>> 0) > (0x6122085f >>> 0))) ? u32(u32(a - 0x6f2ec5cd) ^ 0x2e8ab4a0) : u32(a ^ 0x2e8ab4a0)) >>> 0) > (0x6122085f >>> 0))))) || ((!(u32(u32(((a >>> 0) > (0xd657148 >>> 0)) & ((u32(a ^ 0x2e8ab4a0) >>> 0) > (0x6122085f >>> 0))) | u32((((u32(((a >>> 0) > (0xd657148 >>> 0)) & ((u32(a ^ 0x2e8ab4a0) >>> 0) > (0x6122085f >>> 0))) ? u32(a - 0x6f2ec5cd) : a) >>> 0) > (0xd657148 >>> 0)) & (((u32(((a >>> 0) > (0xd657148 >>> 0)) & ((u32(a ^ 0x2e8ab4a0) >>> 0) > (0x6122085f >>> 0))) ? u32(u32(a - 0x6f2ec5cd) ^ 0x2e8ab4a0) : u32(a ^ 0x2e8ab4a0)) >>> 0) > (0x6122085f >>> 0))))))))) ? (u32(e + h4)) : (h4))"] }, wrapper: { iv: [1496722686, 313065040, 672521069, 1031977098, 1391433127], transform: [116, 117, 118, 119, 112, 113, 114, 115, 124, 125, 126, 127, 120, 121, 122, 123, 100, 101, 102, 103, 96, 97, 98, 99, 108, 109, 110, 111, 104, 105, 106, 107, 84, 85, 86, 87, 80, 81, 82, 83, 92, 93, 94, 95, 88, 89, 90, 91, 68, 69, 70, 71, 64, 65, 66, 67, 76, 77, 78, 79, 72, 73, 74, 75, 52, 53, 54, 55, 48, 49, 50, 51, 60, 61, 62, 63, 56, 57, 58, 59, 36, 37, 38, 39, 32, 33, 34, 35, 44, 45, 46, 47, 40, 41, 42, 43, 20, 21, 22, 23, 16, 17, 18, 19, 28, 29, 30, 31, 24, 25, 26, 27, 4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11, 244, 245, 246, 247, 240, 241, 242, 243, 252, 253, 254, 255, 248, 249, 250, 251, 228, 229, 230, 231, 224, 225, 226, 227, 236, 237, 238, 239, 232, 233, 234, 235, 212, 213, 214, 215, 208, 209, 210, 211, 220, 221, 222, 223, 216, 217, 218, 219, 196, 197, 198, 199, 192, 193, 194, 195, 204, 205, 206, 207, 200, 201, 202, 203, 180, 181, 182, 183, 176, 177, 178, 179, 188, 189, 190, 191, 184, 185, 186, 187, 164, 165, 166, 167, 160, 161, 162, 163, 172, 173, 174, 175, 168, 169, 170, 171, 148, 149, 150, 151, 144, 145, 146, 147, 156, 157, 158, 159, 152, 153, 154, 155, 132, 133, 134, 135, 128, 129, 130, 131, 140, 141, 142, 143, 136, 137, 138, 139], pad: { marker: [132, 209, 135, 49], fill: 147 }, finalize: [{ kind: "expr", js: "u32(v - 0x119cf2c6)" }, { kind: "expr", js: "(!(((v >>> 0) > (0x7f7b8204 >>> 0)) || ((u32(v - 0x1efa22e2) >>> 0) > (0x7f7b8204 >>> 0)))) ? (u32(v - 0x3df445c4)) : ((!(((v >>> 0) > (0x7f7b8204 >>> 0)))) ? (u32(v - 0x1efa22e2)) : (v))" }, { kind: "expr", js: "(!(((v >>> 0) > (0x6a0ea4e8 >>> 0)) || ((v >>> 0) > (0x203ac7cc >>> 0)))) ? (u32(v - 0x6c5845c8)) : ((!(((v >>> 0) > (0x6a0ea4e8 >>> 0)))) ? (u32(v + 0x49d3dd1c)) : (v))" }, { kind: "expr", js: "u32(v ^ 0x7e1681ae)" }, { kind: "expr", js: "(((v >>> 0) <= (0xfd049518 >>> 0))) ? (u32(v + 0x58c3c14b)) : (v)" }], outEndian: "le" } },
  "10": { ok: true, wrapperFuncidx: 504, coreFuncidx: 58, coreConfig: { funcidx: 58, rounds: 88, schedule: { taps: [16, 14, 8, 3], rotl: 1 }, bigEndianLoad: true, rotlA: 5, rotlB: 30, bands: [{ upTo: 19, K: 2401131562, f: "CH" }, { upTo: 39, K: 2760587591, f: "PARITY" }, { upTo: 59, K: 2084872688, f: "MAJ" }, { upTo: 79, K: 2444328717, f: "PARITY" }, { upTo: 87, K: 3771456617, f: "PARITY" }], finalize: [null, null, null, null, null], coreFinalizeJs: ["u32(a + h0)", "u32(b + h1)", "u32(c + h2)", "u32(d + h3)", "u32(e + h4)"] }, wrapper: { iv: [584565971, 876522939, 2865877150, 560264065, 2549618276], transform: [126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125], pad: { marker: [], fill: 157 }, wrapperFinalizeJs: ["s0", "s1", "(((u32(s2 ^ 0x711b0f98) >>> 0) > (0x52a5eaa7 >>> 0)) ? u32(s2 - 0x3decc170) : s2)", "u32(s3 - 0x6f0c1fc4)", "(((s4 >>> 0) > (0xadae327e >>> 0)) ? u32(s4 + 0x76eea4c0) : s4)"], outEndian: "le" } },
  "11": { ok: true, wrapperFuncidx: 475, coreFuncidx: 33, coreConfig: { funcidx: 33, rounds: 95, schedule: { taps: [16, 14, 8, 3], rotl: 1 }, bigEndianLoad: true, rotlA: 5, rotlB: 30, bands: [{ upTo: 19, K: 894247597, f: "CH" }, { upTo: 39, K: 2883601808, f: "PARITY" }, { upTo: 59, K: 1613159655, f: "MAJ" }, { upTo: 79, K: 3602513866, f: "PARITY" }, { upTo: 94, K: 194230788, f: "PARITY" }], finalize: [{ tweak: { kind: "xor", val: 2633350954 } }, null, null, null, null], coreFinalizeJs: ["u32((((u32(a ^ 0x602ed050) >>> 0) > (0xa7d617ee >>> 0)) ? (((u32(a ^ 0x9cf5bf2a) >>> 0) < (0xb5307c5 >>> 0)) ? u32(a + 0x7892c7b8) : a) : a) + h0)", "u32(u32(b + h1) + 0x26abc6d7)", "u32(c + h2)", "u32(d + h3)", "u32(e + h4)"] }, wrapper: { iv: [3813092984, 1439980838, 1799436867, 1123721964, 1483177993], transform: "identity", pad: { marker: [171, 36, 136, 196], fill: 175 }, finalize: [{ kind: "expr", js: "(((v >>> 0) === (0x6d85a62d >>> 0))) ? (0x6391fa9) : (v)" }, { kind: "expr", js: "(!(((v >>> 0) < (0x7be244c4 >>> 0)) || ((v >>> 0) > (0xb8a9339d >>> 0)) || ((u32(v ^ 0x5106ad00) >>> 0) < (0x2bc6d030 >>> 0)))) ? (u32(v ^ 0xd9784e37)) : (v)" }, null, { kind: "expr", js: "(((v >>> 0) <= (0x9f88e20c >>> 0))) ? ((((u32(v ^ 0xcce52b54) >>> 0) < (0x9f88e20d >>> 0)) ? v : u32(v ^ 0xcce52b54))) : (v)" }, null], outEndian: "le" } },
  "12": { ok: true, wrapperFuncidx: 448, coreFuncidx: 56, coreConfig: { funcidx: 56, rounds: 82, schedule: { taps: [16, 14, 8, 3], rotl: 1 }, bigEndianLoad: true, rotlA: 5, rotlB: 30, bands: [{ upTo: 19, K: 1997697984, f: "CH" }, { upTo: 39, K: 2357154013, f: "PARITY" }, { upTo: 59, K: 2716610042, f: "MAJ" }, { upTo: 79, K: 3076066071, f: "PARITY" }, { upTo: 81, K: 2982314119, f: "PARITY" }], finalize: [{ tweak: { kind: "xor", val: 3818299735 } }, null, null, null, { tweak: { kind: "xor", val: 1442945934 } }], coreFinalizeJs: ["u32((((a >>> 0) < (0xfc4832e6 >>> 0)) ? u32(a ^ 0xe396a157) : a) + h0)", "u32(b + h1)", "u32((((a >>> 0) === (0xf143408d >>> 0)) ? 0x79b2a6eb : c) + h2)", "u32(d + h3)", "u32((((u32(e ^ 0x56019b8e) >>> 0) < (0x2c9d773e >>> 0)) ? u32(e - 0x57374050) : e) + h4)"] }, wrapper: { iv: [3286645189, 473089361, 2462443572, 1192001419, 3181355630], transform: "identity", pad: { marker: [], fill: 191 }, wrapperFinalizeJs: ["s0", "u32(s1 ^ 0x4462a941)", "s2", "u32(s3 ^ 0xca1c11ea)", "(((s4 >>> 0) === (0xf21ed1f >>> 0)) ? 0xdf9d0a02 : s4)"], outEndian: "le" } },
  "13": { ok: true, wrapperFuncidx: 423, coreFuncidx: 32, coreConfig: { funcidx: 32, rounds: 89, schedule: { taps: [16, 14, 8, 3], rotl: 1 }, bigEndianLoad: true, rotlA: 5, rotlB: 30, bands: [{ upTo: 19, K: 2561155883, f: "CH" }, { upTo: 39, K: 255542798, f: "PARITY" }, { upTo: 59, K: 2244897009, f: "MAJ" }, { upTo: 79, K: 4234251220, f: "PARITY" }, { upTo: 88, K: 4085764506, f: "PARITY" }], finalize: [{ tweak: { kind: "xor", val: 2915495277 } }, null, null, null, null], coreFinalizeJs: ["u32(u32(a ^ 0xadc6ed6d) + h0)", "u32(b + h1)", "u32(c + h2)", "u32(d + h3)", "u32(e + h4)"] }, wrapper: { iv: [4290546770, 882263692, 1241719721, 1601175750, 1960631779], transform: [0, 1, 2, 3, 4, 5, 1, 2, 3, 4, 5, 1, 2, 3, 4, 5, 1, 2, 3, 4, 5, 1, 2, 3, 4, 5, 1, 2, 3, 4, 5, 1, 2, 3, 4, 5, 1, 2, 3, 4, 5, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255], pad: { marker: [5, 1, 1, 90], fill: 71 }, finalize: [null, { kind: "expr", js: "(((v >>> 0) === (0x9a06420a >>> 0))) ? (0x81880d39) : (v)" }, { kind: "expr", js: "(((u32(v ^ 0xaf731f24) >>> 0) <= (0x9edf1fd3 >>> 0))) ? (u32(v + 0x2deb11ee)) : (v)" }, { kind: "expr", js: "(((v >>> 0) === (0xc1cc6c5d >>> 0))) ? (0xa3935ac2) : (v)" }, { kind: "expr", js: "u32(v ^ 0xc0a0a7a7)" }], outEndian: "le" } },
  "14": { ok: true, wrapperFuncidx: 398, coreFuncidx: 55, coreConfig: { funcidx: 55, rounds: 100, schedule: { taps: [16, 14, 8, 3], rotl: 1 }, bigEndianLoad: true, rotlA: 5, rotlB: 30, bands: [{ upTo: 19, K: 2198912374, f: "CH" }, { upTo: 39, K: 2558368403, f: "PARITY" }, { upTo: 59, K: 1882653500, f: "MAJ" }, { upTo: 79, K: 2242109529, f: "PARITY" }, { upTo: 99, K: 1653179133, f: "PARITY" }], finalize: [null, null, null, null, { tweak: { kind: "xor", val: 2620318821 } }], coreFinalizeJs: ["u32(u32(a + h0) + (((a >>> 0) < (0x7d324682 >>> 0)) ? (((a >>> 0) < (0x731a9390 >>> 0)) ? 0x142f65e4 : 0xa17b2f2) : 0x0))", "u32(u32(b + h1) + (((b >>> 0) < (0x8c6474b3 >>> 0)) ? (((b >>> 0) < (0x4ec8b331 >>> 0)) ? 0x7b378304 : 0x3d9bc182) : 0x0))", "u32((((u32(c - 0x205c6f0a) >>> 0) < (0x8174e2c5 >>> 0)) ? u32(c + 0x8bb2cb8) : c) + h2)", "u32(d + h3)", "u32((((e >>> 0) > (0x8ef79795 >>> 0)) ? (((u32(e ^ 0x33362942) >>> 0) < (0x318a58a2 >>> 0)) ? u32(e ^ 0x9c2ee465) : e) : e) + h4)"] }, wrapper: { iv: [3764098975, 2898929183, 593316098, 2582670309, 277057224], transform: "identity", pad: { marker: [], fill: 231 }, wrapperFinalizeJs: ["u32(s0 ^ 0xd2157ab1)", "u32(s1 + 0x65a5fde8)", "(((s2 >>> 0) > (0x48f58620 >>> 0)) ? u32(s2 - 0x43c023ef) : s2)", "u32(s3 + 0x7262063d)", "(((u32(s4 ^ 0xceaeeeca) >>> 0) > (0xb743c14a >>> 0)) ? u32(s4 + 0x71f944ba) : s4)"], outEndian: "le" } },
  "15": { ok: true, wrapperFuncidx: 371, coreFuncidx: 31, coreConfig: { funcidx: 31, rounds: 119, schedule: { taps: [16, 14, 8, 3], rotl: 1 }, bigEndianLoad: true, rotlA: 5, rotlB: 30, bands: [{ upTo: 19, K: 923453761, f: "CH" }, { upTo: 39, K: 2912807972, f: "PARITY" }, { upTo: 59, K: 1642365819, f: "MAJ" }, { upTo: 79, K: 3631720030, f: "PARITY" }, { upTo: 99, K: 2448062384, f: "PARITY" }, { upTo: 118, K: 2807518413, f: "PARITY" }], finalize: [null, { tweak: { kind: "xor", val: 1275118291 } }, { tweak: { kind: "xor", val: 915662262 } }, { tweak: { kind: "xor", val: 958859417 } }, null], coreFinalizeJs: ["u32(h0 + (((a >>> 0) === (0x7b5f2575 >>> 0)) ? 0x36aa131b : a))", "u32(h1 + ((((u32(b ^ 0x4c00c2d3) >>> 0) < (0x824c62e5 >>> 0)) || ((u32(b ^ 0x3c55e79f) >>> 0) < (0xe05b34fd >>> 0))) ? (b) : ((((u32(u32(b + 0x10f3a045) ^ 0x3c55e79f) >>> 0) > (0xe05b34fc >>> 0)) ? u32(b + 0x21e7408a) : u32(b + 0x10f3a045)))))", "u32(h2 + (((a >>> 0) === (0x9ba42a08 >>> 0)) ? (((u32(c ^ 0x3693e5b6) >>> 0) < (0xf8df85c9 >>> 0)) ? 0x8c888d20 : c) : c))", "u32(h3 + (((u32(d ^ 0x39270899) >>> 0) < (0x6b6cb477 >>> 0)) ? u32(d + 0x64a9926d) : d))", "u32(h4 + e)"] }, wrapper: { iv: [3842299148, 3693812434, 4053268463, 3377553560, 3737009589], transform: "identity", pad: { marker: [163, 55, 56, 105], fill: 119 }, finalize: [{ kind: "expr", js: "u32(v - 0x1b93692e)" }, { kind: "expr", js: "(((v >>> 0) === (0x64886a13 >>> 0))) ? (0xf2b1f9fd) : (v)" }, { kind: "expr", js: "(!(((v >>> 0) < (0x772cfccf >>> 0)) || ((v >>> 0) !== (0xcc974083 >>> 0)) || ((u32(v ^ 0x6256104) >>> 0) > (0x20d252ee >>> 0)))) ? (0x766b00cb) : (v)" }, { kind: "expr", js: "(((v >>> 0) === (0xae74a012 >>> 0))) ? (0xeded31e) : (v)" }, null], outEndian: "le" } },
  "16": { ok: true, wrapperFuncidx: 343, coreFuncidx: 54, coreConfig: { funcidx: 54, rounds: 118, schedule: { taps: [16, 14, 8, 3], rotl: 1 }, bigEndianLoad: true, rotlA: 5, rotlB: 30, bands: [{ upTo: 19, K: 2258329500, f: "CH" }, { upTo: 39, K: 2617785529, f: "PARITY" }, { upTo: 59, K: 2977241558, f: "MAJ" }, { upTo: 79, K: 3336697587, f: "PARITY" }, { upTo: 99, K: 3628654555, f: "PARITY" }, { upTo: 117, K: 1323041470, f: "PARITY" }], finalize: [null, null, null, null, { tweak: { kind: "xor", val: 181042404 } }], coreFinalizeJs: ["u32((((a >>> 0) === (0xf69e3e2 >>> 0)) ? (((u32(a ^ 0x76093d9e) >>> 0) > (0x94975b5d >>> 0)) ? 0x81a30b21 : a) : a) + h0)", "u32(u32(b + h1) + 0x15b99b12)", "u32(c + h2)", "u32(u32(d + h3) + 0x3fb7441b)", "u32(((((e >>> 0) > (0xa4d23132 >>> 0))) ? (e) : ((((((!(((e >>> 0) > (0xa4d23132 >>> 0))))) && ((((((!(((e >>> 0) < (0x3792dd69 >>> 0))))) && ((!(((u32(e ^ 0x1cfcc399) >>> 0) < (0x60fbd899 >>> 0))))))) && (((u32(e ^ 0x4c7e8165) >>> 0) > (0xa4d23132 >>> 0))))))) ? (u32(e ^ 0x4c7e8165)) : ((((((((e >>> 0) < (0x3792dd69 >>> 0))) ? (e) : ((((((!(((e >>> 0) < (0x3792dd69 >>> 0))))) && (((u32(e ^ 0x1cfcc399) >>> 0) < (0x60fbd899 >>> 0))))) ? (e) : (u32(e ^ 0x4c7e8165))))) >>> 0) > (0x3792dd68 >>> 0)) ? (((((((e >>> 0) < (0x3792dd69 >>> 0))) ? (u32(e ^ 0x1cfcc399)) : ((((((!(((e >>> 0) < (0x3792dd69 >>> 0))))) && (((u32(e ^ 0x1cfcc399) >>> 0) < (0x60fbd899 >>> 0))))) ? (u32(e ^ 0x1cfcc399)) : (u32(e ^ 0x508242fc))))) >>> 0) > (0x60fbd898 >>> 0)) ? u32(((((e >>> 0) < (0x3792dd69 >>> 0))) ? (e) : ((((((!(((e >>> 0) < (0x3792dd69 >>> 0))))) && (((u32(e ^ 0x1cfcc399) >>> 0) < (0x60fbd899 >>> 0))))) ? (e) : (u32(e ^ 0x4c7e8165))))) ^ 0x4c7e8165) : ((((e >>> 0) < (0x3792dd69 >>> 0))) ? (e) : ((((((!(((e >>> 0) < (0x3792dd69 >>> 0))))) && (((u32(e ^ 0x1cfcc399) >>> 0) < (0x60fbd899 >>> 0))))) ? (e) : (u32(e ^ 0x4c7e8165)))))) : ((((e >>> 0) < (0x3792dd69 >>> 0))) ? (e) : ((((((!(((e >>> 0) < (0x3792dd69 >>> 0))))) && (((u32(e ^ 0x1cfcc399) >>> 0) < (0x60fbd899 >>> 0))))) ? (e) : (u32(e ^ 0x4c7e8165)))))))))) + h4)"] }, wrapper: { iv: [3701560273, 2958346309, 652733224, 3677258367, 1371645282], transform: [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 234, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255], pad: { marker: [], fill: 87 }, wrapperFinalizeJs: ["s0", "u32(s1 ^ 0x4c4472c9)", "u32(s2 - 0x5bb4c470)", "u32(s3 ^ 0xd1fddb72)", "(((u32(s4 ^ 0xf7f0c2ac) >>> 0) < (0x6a714ef6 >>> 0)) ? u32(s4 + 0x24c004dc) : s4)"], outEndian: "le" } },
  "17": { ok: true, wrapperFuncidx: 315, coreFuncidx: 30, coreConfig: { funcidx: 30, rounds: 105, schedule: { taps: [16, 14, 8, 3], rotl: 1 }, bigEndianLoad: true, rotlA: 5, rotlB: 30, bands: [{ upTo: 19, K: 1214296239, f: "CH" }, { upTo: 39, K: 3203650450, f: "PARITY" }, { upTo: 59, K: 898037365, f: "MAJ" }, { upTo: 79, K: 2887391576, f: "PARITY" }, { upTo: 99, K: 514279430, f: "PARITY" }, { upTo: 104, K: 873735459, f: "PARITY" }], finalize: [{ kind: "gated", xorM: 1575716802, cmp: "lt", thr: 1613303478, op: { kind: "add", val: 1141583122 } }, null, null, null, null] }, wrapper: { iv: [641919910, 3753229560, 4112685589, 177174322, 536630351], transform: [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 90, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255], pad: { marker: [252, 254, 130, 179], fill: 39 }, wrapperFinalizeJs: ["u32(s0 ^ 0x95e13637)", "s1", "const t0=(s2^0x83084588);const t1=(u32(t0));const t2=(t1>>>0);const t3=(0x16780ad4>>>0);const t4=(t2>t3);const t5=(s2^0xb8761166);const t6=(u32(t5));const t7=(!t4);const t8=(t6>>>0);const t9=(0x129bd7af>>>0);const t10=(t8<t9);const t11=(t7&&t10);const t12=(s2^0xe2d51355);const t13=(u32(t12));const t14=(t11?t6:t13);const t15=(t4?t6:t14);const t16=(t15>>>0);const t17=(t16<t9);const t18=(!t10);const t19=(t7&&t18);const t20=(s2^0x5aa30233);const t21=(u32(t20));const t22=(t19?t21:s2);const t23=(t11?s2:t22);const t24=(t4?s2:t23);const t25=(!t17);const t26=(s2^0xd9ab47bb);const t27=(u32(t26));const t28=(t11?t1:t27);const t29=(t4?t1:t28);const t30=(t29>>>0);const t31=(t30>t3);const t32=(t25&&t31);const t33=(!t31);const t34=(t25&&t33);const t35=(t11?s2:t21);const t36=(t4?s2:t35);const t37=(t36^0x5aa30233);const t38=(u32(t37));const t39=(t34?t38:t24);const t40=(t32?t24:t39);const t41=(t17?t24:t40);return (t41)>>>0;", "s3", "s4"], outEndian: "le" } },
  "18": { ok: true, wrapperFuncidx: 288, coreFuncidx: 53, coreConfig: { funcidx: 53, rounds: 92, schedule: { taps: [16, 14, 8, 3], rotl: 1 }, bigEndianLoad: true, rotlA: 5, rotlB: 30, bands: [{ upTo: 19, K: 2317746626, f: "CH" }, { upTo: 39, K: 2677202655, f: "PARITY" }, { upTo: 59, K: 2001487752, f: "MAJ" }, { upTo: 79, K: 2360943781, f: "PARITY" }, { upTo: 91, K: 3842355249, f: "PARITY" }], finalize: [{ kind: "gated", xorM: 0, cmp: "lt", thr: 438625353, op: { kind: "add", val: 3023116200 } }, { kind: "add", val: 1770428412 }, { kind: "gated", xorM: 1548130508, cmp: "lt", thr: 997674360, op: { kind: "add", val: 1938298826 } }, null, null] }, wrapper: { iv: [346897467, 793138003, 2782492214, 476879129, 2466233340], transform: [222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221], pad: { marker: [], fill: 13 }, wrapperFinalizeJs: ["u32(s0 - 0x69d917bd)", "s1", "s2", "s3", "u32(s4 - 0x32625230)"], outEndian: "le" } },
  "19": { ok: true, wrapperFuncidx: 259, coreFuncidx: 29, coreConfig: { funcidx: 29, rounds: 123, schedule: { taps: [16, 14, 8, 3], rotl: 1 }, bigEndianLoad: true, rotlA: 5, rotlB: 30, bands: [{ upTo: 19, K: 1273713365, f: "CH" }, { upTo: 39, K: 3263067576, f: "PARITY" }, { upTo: 59, K: 1992625423, f: "MAJ" }, { upTo: 79, K: 3981979634, f: "PARITY" }, { upTo: 99, K: 573696556, f: "PARITY" }, { upTo: 119, K: 933152585, f: "PARITY" }, { upTo: 122, K: 1292608614, f: "PARITY" }], finalize: [null, null, null, null, { tweak: { kind: "xor", val: 1559344101 } }], coreFinalizeJs: ["u32(a + h0)", "u32(b + h1)", "u32(c + h2)", "u32(d + h3)", "u32((((u32(e ^ 0x5cf1b3e5) >>> 0) < (0x47b15749 >>> 0)) ? u32(e + 0xc49beb9) : e) + h4)"] }, wrapper: { iv: [51875024, 1973730174, 2333186203, 1657471300, 2016927329], transform: "identity", pad: { marker: [253, 47, 250, 42], fill: 223 }, finalize: [{ kind: "expr", js: "(!(((u32(v ^ 0x9d8acafd) >>> 0) > (0x3124bfc >>> 0)) || ((u32(v ^ 0xec04a7f3) >>> 0) > (0x1c7c97aa >>> 0)))) ? (u32(v - 0x74e7bddb)) : (v)" }, { kind: "expr", js: "(u32(u32(((v >>> 0) < (0xa0b15bc2 >>> 0)) & ((u32(v ^ 0xc3be109c) >>> 0) > (0x515651e4 >>> 0))) | u32((((u32(((v >>> 0) < (0xa0b15bc2 >>> 0)) & ((u32(v ^ 0xc3be109c) >>> 0) > (0x515651e4 >>> 0))) ? u32(v - 0x2c1d3e10) : v) >>> 0) < (0xa0b15bc2 >>> 0)) & (((u32(((v >>> 0) < (0xa0b15bc2 >>> 0)) & ((u32(v ^ 0xc3be109c) >>> 0) > (0x515651e4 >>> 0))) ? u32(u32(v - 0x2c1d3e10) ^ 0xc3be109c) : u32(v ^ 0xc3be109c)) >>> 0) > (0x515651e4 >>> 0))))) ? ((u32((((u32(((v >>> 0) < (0xa0b15bc2 >>> 0)) & ((u32(v ^ 0xc3be109c) >>> 0) > (0x515651e4 >>> 0))) ? u32(v - 0x2c1d3e10) : v) >>> 0) < (0xa0b15bc2 >>> 0)) & (((u32(((v >>> 0) < (0xa0b15bc2 >>> 0)) & ((u32(v ^ 0xc3be109c) >>> 0) > (0x515651e4 >>> 0))) ? u32(u32(v - 0x2c1d3e10) ^ 0xc3be109c) : u32(v ^ 0xc3be109c)) >>> 0) > (0x515651e4 >>> 0))) ? u32((u32(((v >>> 0) < (0xa0b15bc2 >>> 0)) & ((u32(v ^ 0xc3be109c) >>> 0) > (0x515651e4 >>> 0))) ? u32(v - 0x2c1d3e10) : v) - 0x2c1d3e10) : (u32(((v >>> 0) < (0xa0b15bc2 >>> 0)) & ((u32(v ^ 0xc3be109c) >>> 0) > (0x515651e4 >>> 0))) ? u32(v - 0x2c1d3e10) : v))) : (v)" }, { kind: "expr", js: "(((v >>> 0) === (0xd92aedb9 >>> 0))) ? (0xda6e718f) : (v)" }, null, null], outEndian: "le" } },
  "20": { ok: true, wrapperFuncidx: 231, coreFuncidx: 52, coreConfig: { funcidx: 52, rounds: 110, schedule: { taps: [16, 14, 8, 3], rotl: 1 }, bigEndianLoad: true, rotlA: 5, rotlB: 30, bands: [{ upTo: 19, K: 2377163752, f: "CH" }, { upTo: 39, K: 2736619781, f: "PARITY" }, { upTo: 59, K: 3096075810, f: "MAJ" }, { upTo: 79, K: 3455531839, f: "PARITY" }, { upTo: 99, K: 1973227775, f: "PARITY" }, { upTo: 109, K: 3962581986, f: "PARITY" }], finalize: [null, { tweak: { kind: "condSub", gt: 2830422564, sub: 883640008 } }, { tweak: { kind: "condSub", gt: 1958323859, sub: 2119376388 } }, { tweak: { kind: "xor", val: 3324035200 } }, null], coreFinalizeJs: ["u32(a + h0)", "u32((((b >>> 0) > (0xa8b4d224 >>> 0)) ? u32(b - 0x34ab46c8) : b) + h1)", "u32((((u32(c ^ 0x1f47f508) >>> 0) < (0xff697a36 >>> 0)) ? (((u32(c - 0x74b9a694) >>> 0) < (0x597c45b6 >>> 0)) ? (((u32(c + 0x40d670fe) >>> 0) > (0x74b9a693 >>> 0)) ? u32(c - 0x7e531e04) : u32(c + 0x40d670fe)) : c) : c) + h2)", "u32((((d >>> 0) === (0xf43bf41b >>> 0)) ? (((u32(d ^ 0xc620c080) >>> 0) < (0x86f50b1c >>> 0)) ? 0xce6ae363 : d) : d) + h3)", "u32(u32(e + h4) + 0x3e13909)"] }, wrapper: { iv: [3820394525, 852555129, 2841909340, 1571467187, 3560821398], transform: [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 19, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255], pad: { marker: [], fill: 239 }, wrapperFinalizeJs: ["(((s0 >>> 0) < (0x1696f980 >>> 0)) ? (((u32(s0 ^ 0x72bac658) >>> 0) > (0xf2dc4b87 >>> 0)) ? u32(s0 - 0x39d5bb9b) : s0) : s0)", "s1", "(((u32(s2 ^ 0x47e10c20) >>> 0) > (0xc802914d >>> 0)) ? (((u32(s2 ^ 0x2970b3b8) >>> 0) > (0x48ef16e7 >>> 0)) ? u32(s2 - 0x26fc0161) : s2) : s2)", "s3", "s4"], outEndian: "le" } },
  "21": { ok: true, wrapperFuncidx: 204, coreFuncidx: 28, coreConfig: { funcidx: 28, rounds: 129, schedule: { taps: [16, 14, 8, 3], rotl: 1 }, bigEndianLoad: true, rotlA: 5, rotlB: 30, bands: [{ upTo: 19, K: 1243502403, f: "CH" }, { upTo: 39, K: 3232856614, f: "PARITY" }, { upTo: 59, K: 927243529, f: "MAJ" }, { upTo: 79, K: 2916597740, f: "PARITY" }, { upTo: 99, K: 2768111026, f: "PARITY" }, { upTo: 119, K: 3127567055, f: "PARITY" }, { upTo: 128, K: 2451852152, f: "PARITY" }], finalize: [null, null, null, null, null], coreFinalizeJs: ["u32(u32(a + h0) - 0x5ef8f27f)", "u32(b + h1)", "u32(c + h2)", "u32(d + h3)", "u32((((e >>> 0) === (0x8b267d66 >>> 0)) ? 0xc8d9aecc : e) + h4)"] }, wrapper: { iv: [3435743994, 27460916, 386916945, 746372974, 1105829003], transform: [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 217, 198, 199, 196, 197, 194, 195, 192, 193, 206, 207, 204, 205, 202, 203, 200, 201, 246, 247, 244, 245, 242, 243, 240, 241, 254, 255, 252, 253, 250, 251, 248, 249, 230, 231, 228, 229, 226, 227, 224, 225, 238, 239, 236, 237, 234, 235, 232, 233, 22, 23, 20, 21, 18, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255], pad: { marker: [62, 159, 239, 205], fill: 63 }, finalize: [{ kind: "expr", js: "u32(v + 0x34404e0c)" }, { kind: "expr", js: "u32(v - 0x96693d2)" }, { kind: "expr", js: "u32(v ^ 0x353f89d6)" }, { kind: "expr", js: "(((v >>> 0) === (0xfd99fdbe >>> 0))) ? (0xfa2f0e8a) : (v)" }, null], outEndian: "le" } },
  "23": { ok: true, wrapperFuncidx: 149, coreFuncidx: 27, coreConfig: { funcidx: 27, rounds: 135, schedule: { taps: [16, 14, 8, 3], rotl: 1 }, bigEndianLoad: true, rotlA: 5, rotlB: 30, bands: [{ upTo: 19, K: 685785257, f: "CH" }, { upTo: 39, K: 2675139468, f: "PARITY" }, { upTo: 59, K: 1404697315, f: "MAJ" }, { upTo: 79, K: 3394051526, f: "PARITY" }, { upTo: 99, K: 2210393880, f: "PARITY" }, { upTo: 119, K: 2569849909, f: "PARITY" }, { upTo: 134, K: 2929305938, f: "PARITY" }], finalize: [null, null, null, null, null], coreFinalizeJs: ["u32(a + h0)", "u32(b + h1)", "u32(c + h2)", "u32(u32(d + h3) - 0x7da4efd6)", "u32(e + h4)"] }, wrapper: { iv: [3758914212, 3610427498, 3969883527, 3294168624, 3653624653], transform: "identity", pad: { marker: [212, 211, 108, 165], fill: 183 }, wrapperFinalizeJs: ["s0", "u32(s1 - 0x7117c128)", "s2", "s3", "const t0=(s4^0x71bd2411);const t1=(u32(t0));const t2=(t1>>>0);const t3=(0x3e1426cf>>>0);const t4=(t2<t3);const t5=(!t4);const t6=(s4^0xce80cd8c);const t7=(u32(t6));const t8=(t7>>>0);const t9=(0x6792d34c>>>0);const t10=(t8<t9);const t11=(t5&&t10);const t12=(!t10);const t13=(t5&&t12);const t14=(s4>>>0);const t15=(0xe1f8321d>>>0);const t16=(t14>t15);const t17=(!t16);const t18=(s4^0x3024fd80);const t19=(u32(t18));const t20=(t19>>>0);const t21=(0x9ce0527f>>>0);const t22=(t20>t21);const t23=(!t22);const t24=(t17&&t23);const t25=(s4-0x540c8a5d);const t26=(u32(t25));const t27=(t26>>>0);const t28=(t27>t15);const t29=(t24&&t28);const t30=(t13&&t29);const t31=(!t28);const t32=(t24&&t31);const t33=(s4+0x57e6eb46);const t34=(u32(t33));const t35=(t34>>>0);const t36=(t35>t15);const t37=(t32&&t36);const t38=(t13&&t37);const t39=(!t36);const t40=(t32&&t39);const t41=(0xde1dd134>>>0);const t42=(t14>t41);const t43=(t40&&t42);const t44=(t13&&t43);const t45=(s4+0x3da60e9);const t46=(u32(t45));const t47=(t29||t37);const t48=(t47||t43);const t49=(!t48);const t50=(t13&&t49);const t51=(t17&&t22);const t52=(s4-0x50322974);const t53=(u32(t52));const t54=(t53^0x3024fd80);const t55=(u32(t54));const t56=(t51?t19:t55);const t57=(t16?t19:t56);const t58=(t57>>>0);const t59=(t58>t21);const t60=(t50&&t59);const t61=(t51?s4:t53);const t62=(t16?s4:t61);const t63=(!t59);const t64=(t50&&t63);const t65=(t62>>>0);const t66=(t65>t15);const t67=(t64&&t66);const t68=(!t66);const t69=(t64&&t68);const t70=(t62-0x540c8a5d);const t71=(u32(t70));const t72=(t71>>>0);const t73=(t72>t15);const t74=(t69&&t73);const t75=(!t73);const t76=(t69&&t75);const t77=(t62+0x57e6eb46);const t78=(u32(t77));const t79=(t78>>>0);const t80=(t79>t15);const t81=(t76&&t80);const t82=(!t80);const t83=(t76&&t82);const t84=(t65>t41);const t85=(t83&&t84);const t86=(t62+0x3da60e9);const t87=(u32(t86));const t88=(t62-0x50322974);const t89=(u32(t88));const t90=(t85?t87:t89);const t91=(t81?t78:t90);const t92=(t74?t71:t91);const t93=(t67?t62:t92);const t94=(t60?t62:t93);const t95=(t44?t46:t94);const t96=(t38?t34:t95);const t97=(t30?t26:t96);const t98=(t11?s4:t97);const t99=(t4?s4:t98);const t100=(t99^0x71bd2411);const t101=(u32(t100));const t102=(t101>>>0);const t103=(t102<t3);const t104=(t24?t26:s4);const t105=(t32?t34:t104);const t106=(t40?t46:t105);const t107=(!t42);const t108=(t40&&t107);const t109=(t108?t53:t106);const t110=(t51?s4:t109);const t111=(t16?s4:t110);const t112=(t69?t71:t111);const t113=(t76?t78:t112);const t114=(t83?t87:t113);const t115=(!t84);const t116=(t83&&t115);const t117=(t116?t89:t114);const t118=(t85?t114:t117);const t119=(t81?t113:t118);const t120=(t74?t112:t119);const t121=(t67?t111:t120);const t122=(t60?t111:t121);const t123=(t44?t106:t122);const t124=(t38?t105:t123);const t125=(t30?t104:t124);const t126=(t11?s4:t125);const t127=(t4?s4:t126);const t128=(!t103);const t129=(t99^0xce80cd8c);const t130=(u32(t129));const t131=(t130>>>0);const t132=(t131<t9);const t133=(t128&&t132);const t134=(!t132);const t135=(t128&&t134);const t136=(t99>>>0);const t137=(t136>t15);const t138=(!t137);const t139=(t99^0x3024fd80);const t140=(u32(t139));const t141=(t140>>>0);const t142=(t141>t21);const t143=(!t142);const t144=(t138&&t143);const t145=(t99-0x540c8a5d);const t146=(u32(t145));const t147=(t146>>>0);const t148=(t147>t15);const t149=(t144&&t148);const t150=(t135&&t149);const t151=(t144?t146:t127);const t152=(!t148);const t153=(t144&&t152);const t154=(t99+0x57e6eb46);const t155=(u32(t154));const t156=(t155>>>0);const t157=(t156>t15);const t158=(t153&&t157);const t159=(t135&&t158);const t160=(t153?t155:t151);const t161=(!t157);const t162=(t153&&t161);const t163=(t136>t41);const t164=(t162&&t163);const t165=(t135&&t164);const t166=(t99+0x3da60e9);const t167=(u32(t166));const t168=(t162?t167:t160);const t169=(t149||t158);const t170=(t169||t164);const t171=(!t170);const t172=(t135&&t171);const t173=(t138&&t142);const t174=(t99-0x50322974);const t175=(u32(t174));const t176=(t175^0x3024fd80);const t177=(u32(t176));const t178=(t173?t140:t177);const t179=(t137?t140:t178);const t180=(t179>>>0);const t181=(t180>t21);const t182=(t172&&t181);const t183=(!t163);const t184=(t162&&t183);const t185=(t184?t175:t168);const t186=(t173?t127:t185);const t187=(t137?t127:t186);const t188=(!t181);const t189=(t172&&t188);const t190=(t173?t99:t175);const t191=(t137?t99:t190);const t192=(t191>>>0);const t193=(t192>t15);const t194=(t189&&t193);const t195=(!t193);const t196=(t189&&t195);const t197=(t191-0x540c8a5d);const t198=(u32(t197));const t199=(t198>>>0);const t200=(t199>t15);const t201=(t196&&t200);const t202=(t196?t198:t187);const t203=(!t200);const t204=(t196&&t203);const t205=(t191+0x57e6eb46);const t206=(u32(t205));const t207=(t206>>>0);const t208=(t207>t15);const t209=(t204&&t208);const t210=(t204?t206:t202);const t211=(!t208);const t212=(t204&&t211);const t213=(t192>t41);const t214=(t212&&t213);const t215=(t191+0x3da60e9);const t216=(u32(t215));const t217=(t212?t216:t210);const t218=(!t213);const t219=(t212&&t218);const t220=(t191-0x50322974);const t221=(u32(t220));const t222=(t219?t221:t217);const t223=(t214?t217:t222);const t224=(t209?t210:t223);const t225=(t201?t202:t224);const t226=(t194?t187:t225);const t227=(t182?t187:t226);const t228=(t165?t168:t227);const t229=(t159?t160:t228);const t230=(t150?t151:t229);const t231=(t133?t127:t230);const t232=(t103?t127:t231);return (t232)>>>0;"], outEndian: "le" } },
  "24": { ok: true, wrapperFuncidx: 121, coreFuncidx: 50, coreConfig: { funcidx: 50, rounds: 86, schedule: { taps: [16, 14, 8, 3], rotl: 1 }, bigEndianLoad: true, rotlA: 5, rotlB: 30, bands: [{ upTo: 19, K: 2637795268, f: "CH" }, { upTo: 39, K: 2997251297, f: "PARITY" }, { upTo: 59, K: 3356707326, f: "MAJ" }, { upTo: 79, K: 3716163355, f: "PARITY" }, { upTo: 85, K: 4162403891, f: "PARITY" }], finalize: [{ tweak: { kind: "condSub", gt: 3469585436, sub: 1373339620 } }, null, { tweak: { kind: "xor", val: 1088350097 } }, null, null], coreFinalizeJs: ["u32((((a >>> 0) > (0xcecdac1c >>> 0)) ? u32(a - 0x51db7fe4) : a) + h0)", "u32((((b >>> 0) > (0x4fb34ebf >>> 0)) ? u32(b + 0x2b720a74) : b) + h1)", "u32((((u32(c ^ 0xd9202bdc) >>> 0) < (0x19359b4c >>> 0)) ? u32(c ^ 0x40dee791) : c) + h2)", "u32(d + h3)", "u32((((e >>> 0) === (0x5a20706 >>> 0)) ? 0x561aa6cd : e) + h4)"] }, wrapper: { iv: [3926742473, 3337812077, 1032198992, 4056724135, 1751111050], transform: "identity", pad: { marker: [], fill: 247 }, wrapperFinalizeJs: ["(((s0 >>> 0) === (0xf03903f5 >>> 0)) ? (((u32(s0 ^ 0x2360cefe) >>> 0) > (0xc5c2c9f9 >>> 0)) ? 0xd2dfff0e : s0) : s0)", "u32(((((u32(s1 - 0x6467b6dc) >>> 0) <= (0x9285495b >>> 0))) ? (u32(s1 + (((u32(s1 + 0x62d2c4d0) >>> 0) < (0x9285495c >>> 0)) ? 0x8e74f758 : 0xc73a7bac))) : (s1)) + (((((((u32(s1 - 0x6467b6dc) >>> 0) <= (0x9285495b >>> 0))) ? (u32(u32(s1 + (((u32(s1 + 0x62d2c4d0) >>> 0) < (0x9285495c >>> 0)) ? 0x8e74f758 : 0xc73a7bac)) - 0x6467b6dc)) : (u32(s1 - 0x6467b6dc))) >>> 0) < (0x9285495c >>> 0)) ? (((u32(((((u32(s1 - 0x6467b6dc) >>> 0) <= (0x9285495b >>> 0))) ? (u32(s1 + (((u32(s1 + 0x62d2c4d0) >>> 0) < (0x9285495c >>> 0)) ? 0x8e74f758 : 0xc73a7bac))) : (s1)) + 0x62d2c4d0) >>> 0) < (0x9285495c >>> 0)) ? 0x8e74f758 : 0xc73a7bac) : 0x0))", "(((u32(s2 ^ 0xf88714c4) >>> 0) > (0xd89c8433 >>> 0)) ? (((u32(s2 ^ 0x312be2f) >>> 0) > (0x770cdc98 >>> 0)) ? u32(s2 - 0xa7f4aad) : s2) : s2)", "(((s3 >>> 0) > (0x88fad9be >>> 0)) ? (((u32(s3 + 0x4ea49900) >>> 0) > (0x88fad9be >>> 0)) ? u32(s3 - 0x62b6ce00) : u32(s3 + 0x4ea49900)) : s3)", "s4"], outEndian: "le" } }
};

// src/versions/v8/registry.ts
var KEYS = keys_default;
var DIGEST_CONFIGS = digest_configs_default;
var SUPPORTED = Object.keys(KEYS).map((k) => Number(k)).sort((a, b) => a - b);

// src/versions/v8/index.ts
var ENTER_WORLD2_PAYLOAD_LEN = 16;
function enterWorld2PayloadHex(combinedField) {
  return toHex(combinedField.subarray(0, ENTER_WORLD2_PAYLOAD_LEN));
}
function toBytes(x) {
  return typeof x === "string" ? fromHex(x) : x;
}
var XOR_SUFFIX_SELECTORS = new Set([1, 14, 18]);
function le32(n) {
  return Uint8Array.of(n & 255, n >>> 8 & 255, n >>> 16 & 255, n >>> 24 & 255);
}
function maskSuffix(selector, key, counter) {
  if (counter == null)
    return fromHex(key.maskSuffix);
  if (key.maskDerivable)
    return le32(counter);
  const base = fromHex(key.maskSuffix);
  const baseWord = (base[0] | base[1] << 8 | base[2] << 16 | base[3] << 24) >>> 0;
  const v = XOR_SUFFIX_SELECTORS.has(selector) ? (baseWord ^ counter) >>> 0 : baseWord + counter >>> 0;
  return le32(v);
}
function solveIdx1(challenge2, serverIp, uid, gateBits, maxIter, counter) {
  const blend = challenge2.subarray(4, 68);
  const d1 = func327digest20(reversed(blend));
  const combinedField = combine(challenge2, func327digest20);
  const KEY = [combinedField[11], combinedField[12], combinedField[13], combinedField[14]];
  const suffix = maskSuffix(1, KEYS["1"], counter);
  const mask = func327digest20(concatBytes(d1, suffix)).subarray(0, 20);
  const prefix = concatBytes(utf8(serverIp), combinedField);
  const gate = makeIdx1Gate(prefix, gateBits);
  const mt = new Mt19937(KEYS["1"].seed);
  for (let n = 0;n < 5; n++)
    mt.uniformInt(10, 32);
  const S = makeBlendField(BigInt(KEYS["1"].SUB));
  const work = new Uint8Array(64);
  for (let it = 0;it < maxIter; it++) {
    const i = mt.uniformInt(0, 134217727), j = mt.uniformInt(0, 134217727), k = mt.uniformInt(0, 134217727), p = mt.uniformInt(0, 63);
    const a = S.get(i), b = S.get(j);
    S.set(i, b);
    S.set(j, a);
    work[p] = S.get(k);
    diffuseWork(work, 0, KEY);
    if (gate(work)) {
      const response = new Uint8Array(64);
      for (let n = 0;n < 64; n++)
        response[n] = work[n] ^ mask[n % 20];
      return {
        selector: 1,
        winningIteration: it,
        responseHex: toHex(response),
        combinedFieldHex: toHex(combinedField),
        payloadHex: enterWorld2PayloadHex(combinedField)
      };
    }
  }
  return {
    selector: 1,
    winningIteration: -1,
    responseHex: null,
    combinedFieldHex: toHex(combinedField),
    payloadHex: enterWorld2PayloadHex(combinedField)
  };
}
function solve(challenge2, opts) {
  const ch = toBytes(challenge2);
  if (ch.length !== 132)
    throw new Error("challenge must be 132 bytes");
  const selector = ch[4] % 25;
  const key = KEYS[String(selector)];
  if (!key)
    throw new Error("selector " + selector + " not supported");
  const serverIp = opts.serverIp;
  if (!serverIp)
    throw new Error("opts.serverIp required (the IP is part of the hashed PoW message)");
  const uid = (opts.uid || 0) >>> 0;
  const maxIter = opts.maxIter || 24000000;
  const gateBits = opts.gateBits ?? 17;
  if (selector === 1) {
    const dd = decodeIdx1Difficulty(ch);
    return solveIdx1(ch, serverIp, uid, dd ?? gateBits, opts.maxIter ?? 50000000, opts.counter);
  }
  const digest = key.digest === "func176" ? func176 : makeDigest(DIGEST_CONFIGS[String(selector)]);
  const combinedField = combine(ch, digest);
  const blend = ch.subarray(4, 68);
  const KEY = [combinedField[11], combinedField[12], combinedField[13], combinedField[14]];
  const SUB = BigInt(key.SUB);
  const suffix = maskSuffix(selector, key, opts.counter);
  const d1 = digest(reversed(blend));
  const mask = digest(concatBytes(d1, suffix));
  const ip = utf8(serverIp);
  const msg = new Uint8Array(ip.length + 128);
  msg.set(ip, 0);
  msg.set(combinedField, ip.length);
  const WORK_OFF = ip.length + 64;
  const mt = new Mt19937(key.seed);
  for (let i = 0;i < 5; i++)
    mt.uniformInt(10, 32);
  const S = makeBlendField(SUB);
  const work = new Uint8Array(64);
  for (let it = 0;it < maxIter; it++) {
    const i = mt.uniformInt(0, 134217727), j = mt.uniformInt(0, 134217727), k = mt.uniformInt(0, 134217727), p = mt.uniformInt(0, 63);
    const a = S.get(i), b = S.get(j);
    S.set(i, b);
    S.set(j, a);
    work[p] = S.get(k);
    diffuseWork(work, uid, KEY);
    msg.set(work, WORK_OFF);
    if (leadingZeroBitsBE(digest(msg)) >= gateBits) {
      const response = new Uint8Array(64);
      for (let n = 0;n < 64; n++)
        response[n] = work[n] ^ mask[n % mask.length];
      return {
        selector,
        winningIteration: it,
        responseHex: toHex(response),
        combinedFieldHex: toHex(combinedField),
        payloadHex: enterWorld2PayloadHex(combinedField)
      };
    }
  }
  return {
    selector,
    winningIteration: -1,
    responseHex: null,
    combinedFieldHex: toHex(combinedField),
    payloadHex: enterWorld2PayloadHex(combinedField)
  };
}
// src/versions/v8/engine.ts
var MUL_LO = 1332534557;
var MUL_HI = 625341585;
function mul32hi(a, b) {
  a >>>= 0;
  b >>>= 0;
  const a00 = a & 65535, a16 = a >>> 16;
  const b00 = b & 65535, b16 = b >>> 16;
  const c00 = Math.imul(a00, b00);
  let c16 = (c00 >>> 16) + Math.imul(a16, b00);
  const c32 = c16 >>> 16;
  c16 = (c16 & 65535) + Math.imul(a00, b16);
  return c32 + (c16 >>> 16) + Math.imul(a16, b16) >>> 0;
}
function mul64(lo, hi) {
  const l = Math.imul(lo, MUL_LO) >>> 0;
  const h = mul32hi(lo, MUL_LO) + Math.imul(lo, MUL_HI) + Math.imul(hi, MUL_LO) >>> 0;
  return [l, h];
}
function splitmixByte(idx, subLo, subHi) {
  const bo = (idx & ~7) >>> 0;
  const lane = idx & 7;
  const borrow = bo < subLo ? 1 : 0;
  let lo = bo - subLo >>> 0;
  let hi = 0 - subHi - borrow >>> 0;
  let a = (lo >>> 12 | hi << 20) >>> 0, b = hi >>> 12;
  lo = (lo ^ a) >>> 0;
  hi = (hi ^ b) >>> 0;
  a = lo << 25 >>> 0;
  b = (hi << 25 | lo >>> 7) >>> 0;
  lo = (lo ^ a) >>> 0;
  hi = (hi ^ b) >>> 0;
  a = (lo >>> 27 | hi << 5) >>> 0;
  b = hi >>> 27;
  lo = (lo ^ a) >>> 0;
  hi = (hi ^ b) >>> 0;
  const [rLo, rHi] = mul64(lo, hi);
  return lane < 4 ? rLo >>> 8 * lane & 255 : rHi >>> 8 * (lane - 4) & 255;
}
function roundFnSource(name, b, c, d) {
  if (name === "CH")
    return `((${b}&${c})|(~${b}&${d}))>>>0`;
  if (name === "MAJ")
    return `((${b}&${c})|(${b}&${d})|(${c}&${d}))>>>0`;
  return `(${b}^${c}^${d})>>>0`;
}
function rotlVar(v, n) {
  return n === 0 ? `(${v}>>>0)` : `(((${v}<<${n})|(${v}>>>${32 - n}))>>>0)`;
}
var factoryCache = new WeakMap;
function buildCompressFactory(cfg) {
  const cached = factoryCache.get(cfg);
  if (cached)
    return cached;
  const cc = cfg.coreConfig;
  const load = cc.bigEndianLoad ? "((B[p]<<24)|(B[p+1]<<16)|(B[p+2]<<8)|B[p+3])>>>0" : "(B[p]|(B[p+1]<<8)|(B[p+2]<<16)|(B[p+3]<<24))>>>0";
  const tapsExpr = cc.schedule.taps.map((t) => `W[i-${t}]`).join("^");
  const srot = cc.schedule.rotl;
  const schedule = srot === 0 ? `for(let i=16;i<${cc.rounds};i++)W[i]=(${tapsExpr})>>>0;` : `for(let i=16;i<${cc.rounds};i++){const x=(${tapsExpr})>>>0;W[i]=((x<<${srot})|(x>>>${32 - srot}))>>>0;}`;
  let bands = "";
  let start = 0;
  for (const bd of cc.bands) {
    bands += `for(let i=${start};i<=${bd.upTo};i++){const z=(${rotlVar("a", cc.rotlA)}+(${roundFnSource(bd.f, "b", "c", "d")})+e+${bd.K >>> 0}+W[i])>>>0;e=d;d=c;c=${rotlVar("b", cc.rotlB)};b=a;a=z;}`;
    start = bd.upTo + 1;
  }
  let fin;
  if (cc.coreFinalizeJs) {
    const fz = cc.coreFinalizeJs;
    let s = `for(let k=0,p=off;k<16;k++,p+=4)BW[k]=(B[p]|(B[p+1]<<8)|(B[p+2]<<16)|(B[p+3]<<24))>>>0;` + `const h0=state[0],h1=state[1],h2=state[2],h3=state[3],h4=state[4];`;
    for (let w = 0;w < 5; w++) {
      s += /;/.test(fz[w]) ? `state[${w}]=CF[${w}](a,b,c,d,e,h0,h1,h2,h3,h4,BW,u32);` : `state[${w}]=(${fz[w]})>>>0;`;
    }
    fin = s;
  } else {
    fin = `state[0]=(AT(CT[0],a)+state[0])>>>0;state[1]=(AT(CT[1],b)+state[1])>>>0;` + `state[2]=(AT(CT[2],c)+state[2])>>>0;state[3]=(AT(CT[3],d)+state[3])>>>0;state[4]=(AT(CT[4],e)+state[4])>>>0;`;
  }
  const factoryBody = `const u32=u32fn;` + `return function compress(off){` + `for(let i=0,p=off;i<16;i++,p+=4)W[i]=${load};` + schedule + `let a=state[0],b=state[1],c=state[2],d=state[3],e=state[4];` + bands + fin + `};`;
  const factory = new Function("B", "W", "state", "BW", "CF", "CT", "AT", "u32fn", factoryBody);
  factoryCache.set(cfg, factory);
  return factory;
}
var BLEND_FIELD_BYTES = 134217728;
var DENSE_PROMOTE_ENTRIES = 1e6;

class BlendOverrideStore {
  base;
  sparse = new Map;
  sparseCount = 0;
  denseValues = null;
  denseUsed = null;
  constructor(base) {
    this.base = base;
  }
  get(idx) {
    idx >>>= 0;
    const values = this.denseValues;
    if (values) {
      const used = this.denseUsed;
      const bit = 1 << (idx & 7);
      return (used[idx >>> 3] & bit) !== 0 ? values[idx] : this.base(idx);
    }
    const stored = this.sparse.get(idx);
    return stored !== undefined ? stored : this.base(idx);
  }
  set(idx, v) {
    idx >>>= 0;
    v &= 255;
    const values = this.denseValues;
    if (values) {
      values[idx] = v;
      this.denseUsed[idx >>> 3] |= 1 << (idx & 7);
      return;
    }
    if (this.sparse.get(idx) === undefined)
      this.sparseCount++;
    this.sparse.set(idx, v);
    if (this.sparseCount > DENSE_PROMOTE_ENTRIES)
      this.promoteToDense();
  }
  promoteToDense() {
    if (this.denseValues)
      return;
    const values = new Uint8Array(BLEND_FIELD_BYTES);
    const used = new Uint8Array(BLEND_FIELD_BYTES >>> 3);
    for (const [idx, v] of this.sparse) {
      values[idx] = v;
      used[idx >>> 3] |= 1 << (idx & 7);
    }
    this.sparse.clear();
    this.sparseCount = 0;
    this.denseValues = values;
    this.denseUsed = used;
  }
}
function makeFastBlendField(SUB) {
  const subLo = Number(SUB & 0xffffffffn) >>> 0;
  const subHi = Number(SUB >> 32n & 0xffffffffn) >>> 0;
  const store = new BlendOverrideStore((idx) => splitmixByte(idx, subLo, subHi));
  return {
    get(idx) {
      return store.get(idx);
    },
    set(idx, v) {
      store.set(idx, v);
    }
  };
}
function makeGate17(cfg, prefix, workOff) {
  const core = cfg.coreConfig;
  const rounds = core.rounds;
  const factory = buildCompressFactory(cfg);
  const coreFinJs = compileCoreFinalize(core.coreFinalizeJs);
  const coreTweaks = [0, 1, 2, 3, 4].map((w) => tweakOf(core.finalize ? core.finalize[w] : null));
  const wrap = cfg.wrapper;
  const iv = Uint32Array.from(wrap.iv.map(u32));
  const tbl = wrap.transform === "identity" || wrap.transform == null ? null : Uint8Array.from(wrap.transform);
  const marker = Uint8Array.from(wrap.pad.marker);
  const fill = wrap.pad.fill;
  const outBe = (wrap.outEndian ?? "le") === "be";
  const wrapFinJs = compileWrapperFinalize(wrap.wrapperFinalizeJs);
  const wrapTweak0 = tweakOf(wrap.finalize ? wrap.finalize[0] : null);
  const gateMask = outBe ? 4294934528 : 8454143;
  const msgLen = workOff + 64;
  const baseLen = msgLen + marker.length;
  const padLen = Math.ceil(baseLen / 64) * 64;
  const blocks = padLen / 64;
  const mutBlock = Math.floor(workOff / 64);
  const padded = new Uint8Array(padLen).fill(fill);
  for (let x = 0;x < workOff; x++)
    padded[x] = tbl ? tbl[prefix[x]] : prefix[x];
  padded.set(marker, msgLen);
  const dv = new DataView(padded.buffer);
  const W = new Uint32Array(rounds);
  const state = new Uint32Array(5);
  const BW = new Array(16);
  const compress = factory(padded, W, state, BW, coreFinJs, coreTweaks, applyTweak, u32);
  state.set(iv);
  for (let blk = 0;blk < mutBlock; blk++)
    compress(blk * 64);
  const pre = Uint32Array.from(state);
  return function pass(work) {
    for (let x = 0;x < 64; x++)
      padded[workOff + x] = tbl ? tbl[work[x]] : work[x];
    state.set(pre);
    let lastOff = mutBlock * 64;
    for (let blk = mutBlock;blk < blocks; blk++) {
      lastOff = blk * 64;
      compress(lastOff);
    }
    let w0;
    if (wrapFinJs) {
      for (let k = 0;k < 16; k++)
        BW[k] = dv.getUint32(lastOff + k * 4, true);
      w0 = wrapFinJs[0](state[0], state[1], state[2], state[3], state[4], BW, u32) >>> 0;
    } else {
      w0 = applyTweak(wrapTweak0, state[0]) >>> 0;
    }
    return (w0 & gateMask) === 0;
  };
}

// src/session/yielder.ts
var nowMs = () => typeof performance !== "undefined" ? performance.now() : Date.now();
function makeYielder() {
  const mc = typeof MessageChannel !== "undefined" ? new MessageChannel : null;
  if (mc) {
    let pending = null;
    mc.port1.onmessage = () => {
      const r = pending;
      pending = null;
      if (r)
        r();
    };
    return () => new Promise((res) => {
      pending = res;
      mc.port2.postMessage(0);
    });
  }
  return () => new Promise((res) => setTimeout(res, 0));
}

// src/versions/v8/session.ts
var XOR_SUFFIX_SELECTORS2 = new Set([1, 14, 18]);
function le322(n) {
  return Uint8Array.of(n & 255, n >>> 8 & 255, n >>> 16 & 255, n >>> 24 & 255);
}
function maskSuffix2(selector, key, counter) {
  if (key.maskDerivable)
    return le322(counter);
  const base = fromHex(key.maskSuffix);
  const baseWord = (base[0] | base[1] << 8 | base[2] << 16 | base[3] << 24) >>> 0;
  const v = XOR_SUFFIX_SELECTORS2.has(selector) ? (baseWord ^ counter) >>> 0 : baseWord + counter >>> 0;
  return le322(v);
}
function toBytes2(x) {
  return typeof x === "string" ? fromHex(x) : x;
}
var defaultYielder = makeYielder();
var SLICE_MS = 6;

class V8Session {
  opts;
  mts = new Map;
  blend = null;
  blendSub = null;
  regenBlend = true;
  counter = 0;
  constructor(opts) {
    this.opts = opts;
    if (!opts.serverIp)
      throw new Error("opts.serverIp required (the IP is part of the hashed PoW message)");
  }
  prep() {
    this.regenBlend = true;
  }
  get solveCount() {
    return this.counter;
  }
  mtFor(selector, seed) {
    let mt = this.mts.get(selector);
    if (!mt) {
      mt = new Mt19937(seed);
      this.mts.set(selector, mt);
    }
    return mt;
  }
  blendFor(sub) {
    if (this.regenBlend || !this.blend || this.blendSub !== sub) {
      this.blend = makeFastBlendField(sub);
      this.blendSub = sub;
      this.regenBlend = false;
    }
    return this.blend;
  }
  prepareSolve(ch, optsOverride) {
    const selector = ch[4] % 25;
    const key = KEYS[String(selector)];
    if (!key)
      throw new Error("selector " + selector + " not supported");
    const serverIp = optsOverride?.serverIp ?? this.opts.serverIp;
    if (selector === 1) {
      const maxIter2 = optsOverride?.maxIter ?? this.opts.maxIter ?? 50000000;
      const gateBits2 = decodeIdx1Difficulty(ch) ?? optsOverride?.gateBits ?? this.opts.gateBits ?? 17;
      const blend = ch.subarray(4, 68);
      const d12 = func327digest20(reversed(blend));
      const combinedField2 = combine(ch, func327digest20);
      const KEY2 = [combinedField2[11], combinedField2[12], combinedField2[13], combinedField2[14]];
      const mask2 = func327digest20(concatBytes(d12, maskSuffix2(1, KEYS["1"], this.counter))).subarray(0, 20);
      const prefix2 = concatBytes(utf8(serverIp), combinedField2);
      const gate2 = makeIdx1Gate(prefix2, gateBits2);
      const mt2 = this.mtFor(1, KEYS["1"].seed);
      const S2 = this.blendFor(BigInt(KEYS["1"].SUB));
      return { selector, combinedField: combinedField2, mt: mt2, S: S2, gate: gate2, mask: mask2, KEY: KEY2, uid: 0, maxIter: maxIter2 };
    }
    const uid = ((optsOverride?.uid ?? this.opts.uid) || 0) >>> 0;
    const gateBits = optsOverride?.gateBits ?? this.opts.gateBits ?? 17;
    const maxIter = optsOverride?.maxIter ?? this.opts.maxIter ?? 24000000;
    const digest = key.digest === "func176" ? func176 : makeDigest(DIGEST_CONFIGS[String(selector)]);
    const combinedField = combine(ch, digest);
    const blendRegion = ch.subarray(4, 68);
    const KEY = [combinedField[11], combinedField[12], combinedField[13], combinedField[14]];
    const d1 = digest(reversed(blendRegion));
    const mask = digest(concatBytes(d1, maskSuffix2(selector, key, this.counter)));
    const ip = utf8(serverIp);
    const prefix = concatBytes(ip, combinedField);
    let gate;
    if (key.digest === "func176") {
      gate = makeFunc176Gate(prefix, gateBits);
    } else if (gateBits === 17) {
      gate = makeGate17(DIGEST_CONFIGS[String(selector)], prefix, ip.length + 64);
    } else {
      const m = new Uint8Array(ip.length + 128);
      m.set(ip, 0);
      m.set(combinedField, ip.length);
      const WORK_OFF = ip.length + 64;
      gate = (work) => {
        m.set(work, WORK_OFF);
        return leadingZeroBitsBE(digest(m)) >= gateBits;
      };
    }
    const mt = this.mtFor(selector, key.seed);
    const S = this.blendFor(BigInt(key.SUB));
    return { selector, combinedField, mt, S, gate, mask, KEY, uid, maxIter };
  }
  win(ctx, it, work) {
    const response = new Uint8Array(64);
    for (let n = 0;n < 64; n++)
      response[n] = work[n] ^ ctx.mask[n % ctx.mask.length];
    return {
      selector: ctx.selector,
      winningIteration: it,
      responseHex: toHex(response),
      combinedFieldHex: toHex(ctx.combinedField),
      payloadHex: enterWorld2PayloadHex(ctx.combinedField)
    };
  }
  miss(ctx) {
    return {
      selector: ctx.selector,
      winningIteration: -1,
      responseHex: null,
      combinedFieldHex: toHex(ctx.combinedField),
      payloadHex: enterWorld2PayloadHex(ctx.combinedField)
    };
  }
  runSearchSync(ctx) {
    const { mt, S, gate, KEY, uid, maxIter } = ctx;
    for (let n = 0;n < 5; n++)
      mt.uniformInt(10, 32);
    const work = new Uint8Array(64);
    for (let it = 0;it < maxIter; it++) {
      const i = mt.uniformInt(0, 134217727), j = mt.uniformInt(0, 134217727), k = mt.uniformInt(0, 134217727), p = mt.uniformInt(0, 63);
      const a = S.get(i), b = S.get(j);
      S.set(i, b);
      S.set(j, a);
      work[p] = S.get(k);
      diffuseWork(work, uid, KEY);
      if (gate(work)) {
        mt.uniformInt(10, 32);
        return this.win(ctx, it, work);
      }
    }
    return this.miss(ctx);
  }
  async runSearchAsync(ctx, yielder) {
    const { mt, S, gate, KEY, uid, maxIter } = ctx;
    for (let n = 0;n < 5; n++)
      mt.uniformInt(10, 32);
    const work = new Uint8Array(64);
    let last = nowMs();
    for (let it = 0;it < maxIter; it++) {
      const i = mt.uniformInt(0, 134217727), j = mt.uniformInt(0, 134217727), k = mt.uniformInt(0, 134217727), p = mt.uniformInt(0, 63);
      const a = S.get(i), b = S.get(j);
      S.set(i, b);
      S.set(j, a);
      work[p] = S.get(k);
      diffuseWork(work, uid, KEY);
      if (gate(work)) {
        mt.uniformInt(10, 32);
        return this.win(ctx, it, work);
      }
      if ((it & 511) === 0 && nowMs() - last > SLICE_MS) {
        await yielder();
        last = nowMs();
      }
    }
    return this.miss(ctx);
  }
  solve(challenge2, optsOverride) {
    const ch = toBytes2(challenge2);
    if (ch.length !== 132)
      throw new Error("challenge must be 132 bytes");
    const ctx = this.prepareSolve(ch, optsOverride);
    const result = this.runSearchSync(ctx);
    this.counter++;
    return result;
  }
  async solveAsync(challenge2, optsOverride, yielder = defaultYielder) {
    const ch = toBytes2(challenge2);
    if (ch.length !== 132)
      throw new Error("challenge must be 132 bytes");
    const ctx = this.prepareSolve(ch, optsOverride);
    const result = await this.runSearchAsync(ctx, yielder);
    this.counter++;
    return result;
  }
}
// src/versions/makeblendfield.ts
var Command = {
  PREP: 255,
  RESET: 24,
  WRITE_CHALLENGE: 228,
  SOLVE: 172,
  READ_RESPONSE: 4,
  READ_PAYLOAD: 187
};
var CHALLENGE_OFFSET = 0;
var RESPONSE_OFFSET = 160;
var CHALLENGE_LEN = 132;
var RESPONSE_LEN = 64;
var PAYLOAD_OFFSET = RESPONSE_OFFSET + RESPONSE_LEN;
var PAYLOAD_LEN = 16;

class MakeBlendField {
  opts;
  memory = new Uint8Array(PAYLOAD_OFFSET + PAYLOAD_LEN);
  response = null;
  payload = null;
  lastSelector = -1;
  lastIteration = -1;
  session;
  constructor(opts) {
    this.opts = opts;
    this.session = new V8Session(opts);
  }
  dispatch(cmd, _val = 0) {
    switch (cmd) {
      case Command.PREP:
        this.session.prep();
        this.response = null;
        this.payload = null;
        return 0;
      case Command.RESET:
        this.response = null;
        this.payload = null;
        return 0;
      case Command.WRITE_CHALLENGE:
        return CHALLENGE_OFFSET;
      case Command.SOLVE: {
        const challenge2 = this.memory.subarray(CHALLENGE_OFFSET, CHALLENGE_OFFSET + CHALLENGE_LEN);
        const r = this.session.solve(Uint8Array.from(challenge2), { uid: this.opts.uid });
        this.applyResult(r);
        return 0;
      }
      case Command.READ_RESPONSE:
        if (!this.response)
          throw new Error("read-response issued before solve");
        this.memory.set(this.response, RESPONSE_OFFSET);
        return RESPONSE_OFFSET;
      case Command.READ_PAYLOAD:
        if (!this.payload)
          throw new Error("read-payload issued before solve");
        this.memory.set(this.payload, PAYLOAD_OFFSET);
        return PAYLOAD_OFFSET;
      default:
        throw new Error(`unknown MakeBlendField command ${cmd}`);
    }
  }
  applyResult(r) {
    this.lastSelector = r.selector;
    this.lastIteration = r.winningIteration;
    this.response = r.responseHex == null ? new Uint8Array(RESPONSE_LEN) : fromHex(r.responseHex);
    this.payload = fromHex(r.payloadHex);
  }
  get selector() {
    return this.lastSelector;
  }
  get winningIteration() {
    return this.lastIteration;
  }
}
function solveChallenge(challenge2, opts) {
  const bytes = typeof challenge2 === "string" ? fromHex(challenge2) : challenge2;
  if (bytes.length !== CHALLENGE_LEN)
    throw new Error("challenge must be 132 bytes");
  const mbf = new MakeBlendField(opts);
  mbf.dispatch(Command.PREP, 140);
  mbf.dispatch(Command.RESET, 132);
  const writeOffset = mbf.dispatch(Command.WRITE_CHALLENGE, 132);
  mbf.memory.set(bytes, writeOffset);
  mbf.dispatch(Command.SOLVE, 36);
  const readOffset = mbf.dispatch(Command.READ_RESPONSE, 152);
  const response = mbf.memory.slice(readOffset, readOffset + RESPONSE_LEN);
  const payloadOffset = mbf.dispatch(Command.READ_PAYLOAD, 22);
  const payload = mbf.memory.slice(payloadOffset, payloadOffset + PAYLOAD_LEN);
  return {
    selector: mbf.selector,
    winningIteration: mbf.winningIteration,
    response,
    responseHex: toHex(response),
    payload,
    payloadHex: toHex(payload)
  };
}
export {
  v9ShouldEmit,
  utf8,
  u32,
  toHex,
  solve as solveV8,
  solveV5,
  solveV4,
  solveV3,
  solveV2,
  solveV1,
  solveChallenge,
  sha1WithIvLeWords,
  sha1WithIv,
  searchCore,
  rotl32,
  reversed,
  reverseRange,
  parseChallenge,
  leadingZeroBitsLE32,
  leadingZeroBitsBE,
  leWords,
  fromHex,
  difficultyV5,
  difficultyV4,
  difficultyV3,
  difficultyV2,
  difficultyV1,
  concatBytes,
  combineV5,
  combineV4,
  combineV3,
  combineV2,
  combineV1,
  bswap32,
  V8Session,
  SUPPORTED,
  STOCK_SHA1_IV,
  SEED_TABLE,
  Opcode,
  OPCODE_INFO,
  Mt19937,
  MakeBlendField,
  MT_PREBURN,
  KEYS,
  FIELD_REGION_START,
  FIELD_REGION_END,
  F,
  DEFAULT_VALIDATOR_COUNT,
  Command,
  CHALLENGE_LENGTH,
  BLEND_REGION_START,
  BLEND_REGION_END
};
