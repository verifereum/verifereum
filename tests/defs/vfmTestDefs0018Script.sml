open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0018";
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip1153_tstore/tstorage_create_contexts/contract_creation.json";
val defs = mapi (define_test "0018") tests;
val () = export_theory_no_docs ();
