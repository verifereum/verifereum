open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0295";
val tests = json_path_to_tests "../fixtures/blockchain_tests/shanghai/eip3860_initcode/with_eof/legacy_create_edge_code_size.json";
val defs = mapi (define_test "0295") tests;
val () = export_theory_no_docs ();
