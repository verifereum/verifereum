open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0389";
val tests = json_path_to_tests "../fixtures/blockchain_tests/shanghai/eip3860_initcode/test_legacy_create_edge_code_size.json";
val defs = mapi (define_test "0389") tests;
val () = export_theory_no_docs ();
