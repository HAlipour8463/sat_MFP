#include <sys/time.h>
#include <sys/resource.h>

float timer ()
{
  struct rusage r;

  getrusage(0, &r);
  return (double)(r.ru_utime.tv_sec+r.ru_utime.tv_usec/(double)1000000);
}
