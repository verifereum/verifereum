open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0015";
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip1153_tstore/tstorage/transient_storage_unset_values.json";
val defs = mapi (define_test "0015") tests;
val () = export_theory_no_docs ();
