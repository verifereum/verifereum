open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0376";
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip7702_set_code_tx/test_signature_s_out_of_range.json";
val defs = mapi (define_test "0376") tests;
val () = export_theory_no_docs ();
