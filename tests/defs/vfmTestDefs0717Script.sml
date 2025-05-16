open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0717";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCreate2/CreateMessageRevertedOOGInInit2.json";
val defs = mapi (define_test "0717") tests;
val () = export_theory_no_docs ();
