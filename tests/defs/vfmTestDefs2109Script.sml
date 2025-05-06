open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2109";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stShift/shr10.json";
val defs = mapi (define_test "2109") tests;
val () = export_theory_no_docs ();
