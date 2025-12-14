open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0359";
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip7702_set_code_tx/test_set_code_to_contract_creator.json";
val defs = mapi (define_test "0359") tests;
val () = export_theory_no_docs ();
