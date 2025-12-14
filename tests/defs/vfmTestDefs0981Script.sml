open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0981";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stEIP2930/storageCosts.json";
val defs = mapi (define_test "0981") tests;
val () = export_theory_no_docs ();
