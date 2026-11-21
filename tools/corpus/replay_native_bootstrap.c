/* Optional measurement bootstrap: full initialization runs before IO main.
 * Compile with -DREPLAY_INITIALIZE=initialize_<exact root module>.
 * The unchanged generated driver provides run_main and its compiled IO body.
 * This substitutes only the native startup sequence, retaining runtime work.
 */
#include <lean/lean.h>
#ifndef REPLAY_INITIALIZE
#error "Exact generated root initialization symbol required"
#endif
extern char **lean_setup_args(int argc, char **argv);
extern lean_object *REPLAY_INITIALIZE(uint8_t builtin);
extern lean_object *run_main(int argc, char **argv);

int __wrap_main(int argc, char **argv) {
    argv = lean_setup_args(argc, argv);
    lean_object *result = REPLAY_INITIALIZE(1);
    lean_io_mark_end_initialization();
    if (lean_io_result_is_ok(result)) {
        lean_dec_ref(result);
        lean_init_task_manager();
        result = lean_run_main(&run_main, argc, argv);
    }
    lean_finalize_task_manager();
    if (lean_io_result_is_ok(result)) {
        lean_dec_ref(result);
        return 0;
    }
    lean_io_result_show_error(result);
    lean_dec_ref(result);
    return 1;
}
