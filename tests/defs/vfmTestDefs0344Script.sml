open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0344";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/VMTests/vmArithmeticTest/expPower256Of256.json";
val defs = mapi (define_test "0344") tests;
val () = export_theory_no_docs ();
