open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1906";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRevertTest/RevertOpcodeReturn.json";
val defs = mapi (define_test "1906") tests;
val () = export_theory_no_docs ();
