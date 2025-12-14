open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0148";
val tests = json_path_to_tests "../fixtures/blockchain_tests/frontier/scenarios/test_scenarios.json";
val defs = mapi (define_test "0148") tests;
val () = export_theory_no_docs ();
