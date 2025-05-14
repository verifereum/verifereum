open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0314";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/Cancun/stEIP1153_transientStorage/17_tstoreGas.json";
val defs = mapi (define_test "0314") tests;
val () = export_theory_no_docs ();
