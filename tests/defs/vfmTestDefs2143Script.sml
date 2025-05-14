open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2143";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stSpecialTest/OverflowGasMakeMoney.json";
val defs = mapi (define_test "2143") tests;
val () = export_theory_no_docs ();
