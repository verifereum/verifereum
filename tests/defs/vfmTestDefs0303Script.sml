open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0303";
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip7702_set_code_tx/test_call_into_self_delegating_set_code.json";
val defs = mapi (define_test "0303") tests;
val () = export_theory_no_docs ();
