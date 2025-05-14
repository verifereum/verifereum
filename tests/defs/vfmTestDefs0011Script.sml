open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0011";
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip1153_tstore/tstorage/gas_usage.json";
val defs = mapi (define_test "0011") tests;
val () = export_theory_no_docs ();
