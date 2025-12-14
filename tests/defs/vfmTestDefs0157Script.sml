open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0157";
val tests = json_path_to_tests "../fixtures/blockchain_tests/istanbul/eip1344_chainid/test_chainid.json";
val defs = mapi (define_test "0157") tests;
val () = export_theory_no_docs ();
