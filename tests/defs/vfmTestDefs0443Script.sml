open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0443";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/VMTests/vmArithmeticTest/twoOps.json";
val defs = mapi (define_test "0443") tests;
val () = export_theory_no_docs ();
