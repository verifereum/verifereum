open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0304";
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip7702_set_code_tx/test_call_pointer_to_created_from_create_after_oog_call_again.json";
val defs = mapi (define_test "0304") tests;
val () = export_theory_no_docs ();
