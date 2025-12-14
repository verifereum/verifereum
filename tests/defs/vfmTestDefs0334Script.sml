open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0334";
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip7702_set_code_tx/test_pointer_contract_pointer_loop.json";
val defs = mapi (define_test "0334") tests;
val () = export_theory_no_docs ();
