open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0322";
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip7702_set_code_tx/test_ext_code_on_chain_delegating_set_code.json";
val defs = mapi (define_test "0322") tests;
val () = export_theory_no_docs ();
