open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2006";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRevertTest/RevertDepthCreateOOG.json";
val defs = mapi (define_test "2006") tests;
val () = export_theory_no_docs ();
