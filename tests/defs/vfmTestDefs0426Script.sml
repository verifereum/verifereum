open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0426";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/VMTests/vmArithmeticTest/addmod.json";
val defs = mapi (define_test "0426") tests;
val () = export_theory_no_docs ();
