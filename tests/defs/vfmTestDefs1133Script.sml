open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1133";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stMemoryTest/stackLimitGas_1024.json";
val defs = mapi (define_test "1133") tests;
val () = export_theory_no_docs ();
