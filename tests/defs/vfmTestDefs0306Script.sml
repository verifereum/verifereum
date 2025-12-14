open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0306";
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip7702_set_code_tx/test_call_to_precompile_in_pointer_context.json";
val defs = mapi (define_test "0306") tests;
val () = export_theory_no_docs ();
