open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0316";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/Cancun/stEIP1153_transientStorage/21_tstoreCannotBeDosdOOO.json";
val defs = mapi (define_test "0316") tests;
val () = export_theory_no_docs ();
