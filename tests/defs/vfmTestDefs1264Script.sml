open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1264";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stPreCompiledContracts2/ecrecoverShortBuff.json";
val defs = mapi (define_test "1264") tests;
val () = export_theory_no_docs ();
