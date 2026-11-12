/* The worked example of the C record-layout slice (docs/projects/c-record-layout.md). */
struct Point { short x; short y; };

struct Header {
  char tag;
  int length;
  double stamp;
  struct Point corners[2];
  long long id;
  void *next;
};

union Value { char bytes[12]; int i; double d; long double ld; };

struct Message { struct Header header; union Value value; unsigned char flags; };
