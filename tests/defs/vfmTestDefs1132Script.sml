open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1132";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stMemoryTest/stackLimitGas_1023.json";
val defs = mapi (define_test "1132") tests;
val () = export_theory_no_docs ();
