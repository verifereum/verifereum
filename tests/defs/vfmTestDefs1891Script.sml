open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1891";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRevertTest/RevertDepthCreateAddressCollision.json";
val defs = mapi (define_test "1891") tests;
val () = export_theory_no_docs ();
