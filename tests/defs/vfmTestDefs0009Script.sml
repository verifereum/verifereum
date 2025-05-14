open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0009";
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip1153_tstore/tload_calls/tload_calls.json";
val defs = mapi (define_test "0009") tests;
val () = export_theory_no_docs ();
