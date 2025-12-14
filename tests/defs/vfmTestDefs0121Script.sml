open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0121";
val tests = json_path_to_tests "../fixtures/blockchain_tests/frontier/create/test_create_suicide_store.json";
val defs = mapi (define_test "0121") tests;
val () = export_theory_no_docs ();
