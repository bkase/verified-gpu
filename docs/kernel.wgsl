/* Certified WGSL (auto-generated):
struct Buf { data: array<i32>, };
@group(0) @binding(0) var<storage, read_write> st: Buf;
var<workgroup> buf: array<i32, 256u>;

@compute @workgroup_size(256)
fn main(@builtin(local_invocation_id) lid: vec3<u32>) {
let _in = st.data[lid.x];
buf[lid.x] = _in;
workgroupBarrier();
if (((lid.x % 2u) == 0u)) {
  let _lhs = buf[u32(((i32(lid.x) * 1) + 0))];
  let _rhs = buf[u32(((i32(lid.x) * 1) + 1))];
  buf[u32(((i32(lid.x) * 1) + 1))] = (_lhs + _rhs);
}
workgroupBarrier();
if (((lid.x % 4u) == 0u)) {
  let _lhs = buf[u32(((i32(lid.x) * 1) + 1))];
  let _rhs = buf[u32(((i32(lid.x) * 1) + 3))];
  buf[u32(((i32(lid.x) * 1) + 3))] = (_lhs + _rhs);
}
workgroupBarrier();
if (((lid.x % 8u) == 0u)) {
  let _lhs = buf[u32(((i32(lid.x) * 1) + 3))];
  let _rhs = buf[u32(((i32(lid.x) * 1) + 7))];
  buf[u32(((i32(lid.x) * 1) + 7))] = (_lhs + _rhs);
}
workgroupBarrier();
if (((lid.x % 16u) == 0u)) {
  let _lhs = buf[u32(((i32(lid.x) * 1) + 7))];
  let _rhs = buf[u32(((i32(lid.x) * 1) + 15))];
  buf[u32(((i32(lid.x) * 1) + 15))] = (_lhs + _rhs);
}
workgroupBarrier();
if (((lid.x % 32u) == 0u)) {
  let _lhs = buf[u32(((i32(lid.x) * 1) + 15))];
  let _rhs = buf[u32(((i32(lid.x) * 1) + 31))];
  buf[u32(((i32(lid.x) * 1) + 31))] = (_lhs + _rhs);
}
workgroupBarrier();
if (((lid.x % 64u) == 0u)) {
  let _lhs = buf[u32(((i32(lid.x) * 1) + 31))];
  let _rhs = buf[u32(((i32(lid.x) * 1) + 63))];
  buf[u32(((i32(lid.x) * 1) + 63))] = (_lhs + _rhs);
}
workgroupBarrier();
if (((lid.x % 128u) == 0u)) {
  let _lhs = buf[u32(((i32(lid.x) * 1) + 63))];
  let _rhs = buf[u32(((i32(lid.x) * 1) + 127))];
  buf[u32(((i32(lid.x) * 1) + 127))] = (_lhs + _rhs);
}
workgroupBarrier();
if (((lid.x % 256u) == 0u)) {
  let _lhs = buf[u32(((i32(lid.x) * 1) + 127))];
  let _rhs = buf[u32(((i32(lid.x) * 1) + 255))];
  buf[u32(((i32(lid.x) * 1) + 255))] = (_lhs + _rhs);
}
workgroupBarrier();
if ((lid.x == 0u)) {
  buf[255u] = 0;
}
workgroupBarrier();
if (((lid.x % 256u) == 0u)) {
  let _a = buf[u32(((i32(lid.x) * 1) + 255))];
  let _t = buf[u32(((i32(lid.x) * 1) + 127))];
  let _b = (_a + _t);
  buf[u32(((i32(lid.x) * 1) + 127))] = _a;
  buf[u32(((i32(lid.x) * 1) + 255))] = _b;
}
workgroupBarrier();
if (((lid.x % 128u) == 0u)) {
  let _a = buf[u32(((i32(lid.x) * 1) + 127))];
  let _t = buf[u32(((i32(lid.x) * 1) + 63))];
  let _b = (_a + _t);
  buf[u32(((i32(lid.x) * 1) + 63))] = _a;
  buf[u32(((i32(lid.x) * 1) + 127))] = _b;
}
workgroupBarrier();
if (((lid.x % 64u) == 0u)) {
  let _a = buf[u32(((i32(lid.x) * 1) + 63))];
  let _t = buf[u32(((i32(lid.x) * 1) + 31))];
  let _b = (_a + _t);
  buf[u32(((i32(lid.x) * 1) + 31))] = _a;
  buf[u32(((i32(lid.x) * 1) + 63))] = _b;
}
workgroupBarrier();
if (((lid.x % 32u) == 0u)) {
  let _a = buf[u32(((i32(lid.x) * 1) + 31))];
  let _t = buf[u32(((i32(lid.x) * 1) + 15))];
  let _b = (_a + _t);
  buf[u32(((i32(lid.x) * 1) + 15))] = _a;
  buf[u32(((i32(lid.x) * 1) + 31))] = _b;
}
workgroupBarrier();
if (((lid.x % 16u) == 0u)) {
  let _a = buf[u32(((i32(lid.x) * 1) + 15))];
  let _t = buf[u32(((i32(lid.x) * 1) + 7))];
  let _b = (_a + _t);
  buf[u32(((i32(lid.x) * 1) + 7))] = _a;
  buf[u32(((i32(lid.x) * 1) + 15))] = _b;
}
workgroupBarrier();
if (((lid.x % 8u) == 0u)) {
  let _a = buf[u32(((i32(lid.x) * 1) + 7))];
  let _t = buf[u32(((i32(lid.x) * 1) + 3))];
  let _b = (_a + _t);
  buf[u32(((i32(lid.x) * 1) + 3))] = _a;
  buf[u32(((i32(lid.x) * 1) + 7))] = _b;
}
workgroupBarrier();
if (((lid.x % 4u) == 0u)) {
  let _a = buf[u32(((i32(lid.x) * 1) + 3))];
  let _t = buf[u32(((i32(lid.x) * 1) + 1))];
  let _b = (_a + _t);
  buf[u32(((i32(lid.x) * 1) + 1))] = _a;
  buf[u32(((i32(lid.x) * 1) + 3))] = _b;
}
workgroupBarrier();
if (((lid.x % 2u) == 0u)) {
  let _a = buf[u32(((i32(lid.x) * 1) + 1))];
  let _t = buf[u32(((i32(lid.x) * 1) + 0))];
  let _b = (_a + _t);
  buf[u32(((i32(lid.x) * 1) + 0))] = _a;
  buf[u32(((i32(lid.x) * 1) + 1))] = _b;
}
workgroupBarrier();
workgroupBarrier();
let _out = buf[lid.x];
st.data[lid.x] = _out;
}

*/

struct Buf { data: array<i32>, };
@group(0) @binding(0) var<storage, read_write> st: Buf;
var<workgroup> buf: array<i32, 256u>;

@compute @workgroup_size(256)
fn main(@builtin(local_invocation_id) lid: vec3<u32>) {
let _in = st.data[lid.x];
buf[lid.x] = _in;
workgroupBarrier();
if (((lid.x % 2u) == 0u)) {
  let _lhs = buf[u32(((i32(lid.x) * 1) + 0))];
  let _rhs = buf[u32(((i32(lid.x) * 1) + 1))];
  buf[u32(((i32(lid.x) * 1) + 1))] = (_lhs + _rhs);
}
workgroupBarrier();
if (((lid.x % 4u) == 0u)) {
  let _lhs = buf[u32(((i32(lid.x) * 1) + 1))];
  let _rhs = buf[u32(((i32(lid.x) * 1) + 3))];
  buf[u32(((i32(lid.x) * 1) + 3))] = (_lhs + _rhs);
}
workgroupBarrier();
if (((lid.x % 8u) == 0u)) {
  let _lhs = buf[u32(((i32(lid.x) * 1) + 3))];
  let _rhs = buf[u32(((i32(lid.x) * 1) + 7))];
  buf[u32(((i32(lid.x) * 1) + 7))] = (_lhs + _rhs);
}
workgroupBarrier();
if (((lid.x % 16u) == 0u)) {
  let _lhs = buf[u32(((i32(lid.x) * 1) + 7))];
  let _rhs = buf[u32(((i32(lid.x) * 1) + 15))];
  buf[u32(((i32(lid.x) * 1) + 15))] = (_lhs + _rhs);
}
workgroupBarrier();
if (((lid.x % 32u) == 0u)) {
  let _lhs = buf[u32(((i32(lid.x) * 1) + 15))];
  let _rhs = buf[u32(((i32(lid.x) * 1) + 31))];
  buf[u32(((i32(lid.x) * 1) + 31))] = (_lhs + _rhs);
}
workgroupBarrier();
if (((lid.x % 64u) == 0u)) {
  let _lhs = buf[u32(((i32(lid.x) * 1) + 31))];
  let _rhs = buf[u32(((i32(lid.x) * 1) + 63))];
  buf[u32(((i32(lid.x) * 1) + 63))] = (_lhs + _rhs);
}
workgroupBarrier();
if (((lid.x % 128u) == 0u)) {
  let _lhs = buf[u32(((i32(lid.x) * 1) + 63))];
  let _rhs = buf[u32(((i32(lid.x) * 1) + 127))];
  buf[u32(((i32(lid.x) * 1) + 127))] = (_lhs + _rhs);
}
workgroupBarrier();
if (((lid.x % 256u) == 0u)) {
  let _lhs = buf[u32(((i32(lid.x) * 1) + 127))];
  let _rhs = buf[u32(((i32(lid.x) * 1) + 255))];
  buf[u32(((i32(lid.x) * 1) + 255))] = (_lhs + _rhs);
}
workgroupBarrier();
if ((lid.x == 0u)) {
  buf[255u] = 0;
}
workgroupBarrier();
if (((lid.x % 256u) == 0u)) {
  let _a = buf[u32(((i32(lid.x) * 1) + 255))];
  let _t = buf[u32(((i32(lid.x) * 1) + 127))];
  let _b = (_a + _t);
  buf[u32(((i32(lid.x) * 1) + 127))] = _a;
  buf[u32(((i32(lid.x) * 1) + 255))] = _b;
}
workgroupBarrier();
if (((lid.x % 128u) == 0u)) {
  let _a = buf[u32(((i32(lid.x) * 1) + 127))];
  let _t = buf[u32(((i32(lid.x) * 1) + 63))];
  let _b = (_a + _t);
  buf[u32(((i32(lid.x) * 1) + 63))] = _a;
  buf[u32(((i32(lid.x) * 1) + 127))] = _b;
}
workgroupBarrier();
if (((lid.x % 64u) == 0u)) {
  let _a = buf[u32(((i32(lid.x) * 1) + 63))];
  let _t = buf[u32(((i32(lid.x) * 1) + 31))];
  let _b = (_a + _t);
  buf[u32(((i32(lid.x) * 1) + 31))] = _a;
  buf[u32(((i32(lid.x) * 1) + 63))] = _b;
}
workgroupBarrier();
if (((lid.x % 32u) == 0u)) {
  let _a = buf[u32(((i32(lid.x) * 1) + 31))];
  let _t = buf[u32(((i32(lid.x) * 1) + 15))];
  let _b = (_a + _t);
  buf[u32(((i32(lid.x) * 1) + 15))] = _a;
  buf[u32(((i32(lid.x) * 1) + 31))] = _b;
}
workgroupBarrier();
if (((lid.x % 16u) == 0u)) {
  let _a = buf[u32(((i32(lid.x) * 1) + 15))];
  let _t = buf[u32(((i32(lid.x) * 1) + 7))];
  let _b = (_a + _t);
  buf[u32(((i32(lid.x) * 1) + 7))] = _a;
  buf[u32(((i32(lid.x) * 1) + 15))] = _b;
}
workgroupBarrier();
if (((lid.x % 8u) == 0u)) {
  let _a = buf[u32(((i32(lid.x) * 1) + 7))];
  let _t = buf[u32(((i32(lid.x) * 1) + 3))];
  let _b = (_a + _t);
  buf[u32(((i32(lid.x) * 1) + 3))] = _a;
  buf[u32(((i32(lid.x) * 1) + 7))] = _b;
}
workgroupBarrier();
if (((lid.x % 4u) == 0u)) {
  let _a = buf[u32(((i32(lid.x) * 1) + 3))];
  let _t = buf[u32(((i32(lid.x) * 1) + 1))];
  let _b = (_a + _t);
  buf[u32(((i32(lid.x) * 1) + 1))] = _a;
  buf[u32(((i32(lid.x) * 1) + 3))] = _b;
}
workgroupBarrier();
if (((lid.x % 2u) == 0u)) {
  let _a = buf[u32(((i32(lid.x) * 1) + 1))];
  let _t = buf[u32(((i32(lid.x) * 1) + 0))];
  let _b = (_a + _t);
  buf[u32(((i32(lid.x) * 1) + 0))] = _a;
  buf[u32(((i32(lid.x) * 1) + 1))] = _b;
}
workgroupBarrier();
workgroupBarrier();
let _out = buf[lid.x];
st.data[lid.x] = _out;
}
