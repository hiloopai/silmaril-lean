#include <sqlite3.h>
#include <stdio.h>
#include <string.h>

int main(int argc, char **argv)
{
    sqlite3 *db = NULL;
    sqlite3_stmt *stmt = NULL;
    int rc = SQLITE_OK;
    int value = 0;

    if (argc != 2) return 2;
    if (strcmp(argv[1], "--baseline") == 0) return 0;
    if (strcmp(argv[1], "--initialize") == 0) {
        rc = sqlite3_initialize();
        if (rc == SQLITE_OK) rc = sqlite3_shutdown();
        return rc != SQLITE_OK;
    }

    const int memory = strcmp(argv[1], ":memory:") == 0;
    const int flags = (memory ? SQLITE_OPEN_READWRITE | SQLITE_OPEN_CREATE
                              : SQLITE_OPEN_READONLY)
                    | SQLITE_OPEN_FULLMUTEX | SQLITE_OPEN_PRIVATECACHE;
    rc = sqlite3_open_v2(argv[1], &db, flags, NULL);
    if (rc != SQLITE_OK) goto done;
    if (memory) {
        rc = sqlite3_exec(db,
            "CREATE TABLE sample(id INTEGER PRIMARY KEY,amount INTEGER NOT NULL) STRICT;"
            "INSERT INTO sample VALUES(1,40),(2,42);", NULL, NULL, NULL);
        if (rc != SQLITE_OK) goto done;
    }
    rc = sqlite3_prepare_v2(db, "SELECT amount FROM sample WHERE id=?1",
                            -1, &stmt, NULL);
    if (rc != SQLITE_OK) goto done;
    rc = sqlite3_bind_int(stmt, 1, 2);
    if (rc != SQLITE_OK) goto done;
    rc = sqlite3_step(stmt);
    if (rc != SQLITE_ROW) goto done;
    if (sqlite3_column_type(stmt, 0) != SQLITE_INTEGER) {
        rc = SQLITE_MISMATCH;
        goto done;
    }
    value = sqlite3_column_int(stmt, 0);
    rc = sqlite3_step(stmt);
    if (rc == SQLITE_DONE) rc = SQLITE_OK;

done:
    if (stmt != NULL) {
        const int cleanup = sqlite3_finalize(stmt);
        if (rc == SQLITE_OK) rc = cleanup;
    }
    if (db != NULL) {
        if (rc != SQLITE_OK) fprintf(stderr, "%d: %s\n", rc, sqlite3_errmsg(db));
        const int cleanup = sqlite3_close(db);
        if (rc == SQLITE_OK) rc = cleanup;
    }
    if (rc != SQLITE_OK) return 1;
    return printf("%d\n", value) < 0 || fflush(stdout) == EOF;
}
