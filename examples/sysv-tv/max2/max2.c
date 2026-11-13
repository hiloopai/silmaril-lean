/* The worked example of the System V translation-validation shapes
   (docs/projects/sysv-tv.md): one C function, compiled at -O0 and -O2. */
int max2(int a, int b)
{
  if (a > b)
    return a;
  return b;
}
