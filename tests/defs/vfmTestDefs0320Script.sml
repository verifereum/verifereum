open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0320";
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip7702_set_code_tx/test_eoa_init_as_pointer.json";
val defs = mapi (define_test "0320") tests;
val () = export_theory_no_docs ();
