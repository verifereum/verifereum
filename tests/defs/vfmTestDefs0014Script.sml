open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0014";
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip1153_tstore/tstorage/tload_after_tstore.json";
val defs = mapi (define_test "0014") tests;
val () = export_theory_no_docs ();
