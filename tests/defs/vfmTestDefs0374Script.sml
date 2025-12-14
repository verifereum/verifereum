open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0374";
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip7702_set_code_tx/test_set_code_using_chain_specific_id.json";
val defs = mapi (define_test "0374") tests;
val () = export_theory_no_docs ();
