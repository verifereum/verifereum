open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2005";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRevertTest/RevertDepthCreateAddressCollision.json";
val defs = mapi (define_test "2005") tests;
val () = export_theory_no_docs ();
