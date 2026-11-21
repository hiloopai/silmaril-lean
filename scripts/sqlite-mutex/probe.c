#include "sqlite3.h"
#include <assert.h>
#include <stdio.h>
#include <string.h>

static void (*original_leave)(sqlite3_mutex *);
static sqlite3_mutex *last_leave;
static int leave_calls;

static void counted_leave(sqlite3_mutex *mutex) {
  ++leave_calls;
  last_leave = mutex;
  original_leave(mutex);
}

int main(void) {
  sqlite3_mutex_methods methods;
  assert(strcmp(sqlite3_libversion(), "3.54.1") == 0);
  assert(sqlite3_threadsafe() == 1);
  assert(sqlite3_initialize() == SQLITE_OK);
  assert(sqlite3_shutdown() == SQLITE_OK);
  assert(sqlite3_config(SQLITE_CONFIG_GETMUTEX, &methods) == SQLITE_OK);
  original_leave = methods.xMutexLeave;
  assert(original_leave != NULL);
  methods.xMutexLeave = counted_leave;
  assert(sqlite3_config(SQLITE_CONFIG_MUTEX, &methods) == SQLITE_OK);
  assert(sqlite3_initialize() == SQLITE_OK);

  sqlite3_mutex *mutex = sqlite3_mutex_alloc(SQLITE_MUTEX_FAST);
  assert(mutex != NULL);
  leave_calls = 0;
  sqlite3_mutex_leave(NULL);
  assert(leave_calls == 0);
  puts("null: no callback");

  sqlite3_mutex_enter(mutex);
  sqlite3_mutex_leave(mutex);
  assert(leave_calls == 1 && last_leave == mutex);
  assert(sqlite3_mutex_try(mutex) == SQLITE_OK);
  sqlite3_mutex_leave(mutex);
  assert(leave_calls == 2 && last_leave == mutex);
  puts("owned: one callback for the original pointer; reacquisition succeeds");

  sqlite3_mutex_free(mutex);
  assert(sqlite3_shutdown() == SQLITE_OK);
  return 0;
}
