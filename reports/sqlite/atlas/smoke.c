#include "sqlite3.h"
#include <stdio.h>
#include <string.h>

static int check(const char *what, int passed) {
    if (!passed) fprintf(stderr, "profile smoke failed: %s\n", what);
    return passed;
}

int main(void) {
    sqlite3 *db = NULL;
    sqlite3_stmt *stmt = NULL;
    int ok = 1;

    ok &= check("source ID", strcmp(sqlite3_sourceid(), SQLITE_SOURCE_ID) == 0);
    ok &= check("THREADSAFE=1", sqlite3_threadsafe() == 1
                && sqlite3_compileoption_used("THREADSAFE=1"));
    ok &= check("OMIT_LOAD_EXTENSION", sqlite3_compileoption_used("OMIT_LOAD_EXTENSION"));
    ok &= check("MAX_MMAP_SIZE=0", sqlite3_compileoption_used("MAX_MMAP_SIZE=0"));
    if (!check("open database file", sqlite3_open("smoke.db", &db) == SQLITE_OK)) return 1;

    ok &= check("create and write", sqlite3_exec(db,
        "CREATE TABLE atlas(x); INSERT INTO atlas VALUES ('sqlite');",
        NULL, NULL, NULL) == SQLITE_OK);
    if (check("prepare SELECT", sqlite3_prepare_v2(db, "SELECT length(x) FROM atlas",
              -1, &stmt, NULL) == SQLITE_OK)) {
        ok &= check("read result", sqlite3_step(stmt) == SQLITE_ROW
                    && sqlite3_column_int(stmt, 0) == 6);
        ok &= check("finalize SELECT", sqlite3_finalize(stmt) == SQLITE_OK);
    } else {
        ok = 0;
    }
    if (check("prepare mmap PRAGMA", sqlite3_prepare_v2(db, "PRAGMA mmap_size=4096",
              -1, &stmt, NULL) == SQLITE_OK)) {
        int rc = sqlite3_step(stmt);
        ok &= check("mmap disabled for a file database", rc == SQLITE_DONE
                    || (rc == SQLITE_ROW && sqlite3_column_int64(stmt, 0) == 0));
        ok &= check("finalize mmap PRAGMA", sqlite3_finalize(stmt) == SQLITE_OK);
    } else {
        ok = 0;
    }
    ok &= check("close database", sqlite3_close(db) == SQLITE_OK);
    return ok ? 0 : 1;
}
