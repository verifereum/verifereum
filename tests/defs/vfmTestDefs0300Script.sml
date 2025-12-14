open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0300";
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip7702_set_code_tx/test_address_from_set_code.json";
val defs = mapi (define_test "0300") tests;
val () = export_theory_no_docs ();
