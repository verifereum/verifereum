open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0331";
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip7702_set_code_tx/test_nonce_overflow_after_first_authorization.json";
val defs = mapi (define_test "0331") tests;
val () = export_theory_no_docs ();
