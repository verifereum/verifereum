open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0657";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallCreateCallCodeTest/callOutput3partial.json";
val defs = mapi (define_test "0657") tests;
val () = export_theory_no_docs ();
