open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2031";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stSpecialTest/gasPrice0.json";
val defs = mapi (define_test "2031") tests;
val () = export_theory_no_docs ();
