open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0338";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/VMTests/vmArithmeticTest/arith.json";
val defs = mapi (define_test "0338") tests;
val () = export_theory_no_docs ();
