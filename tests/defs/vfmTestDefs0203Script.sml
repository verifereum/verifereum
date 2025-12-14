open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0203";
val tests = json_path_to_tests "../fixtures/blockchain_tests/osaka/eip7934_block_rlp_limit/test_block_at_rlp_size_limit_boundary.json";
val defs = mapi (define_test "0203") tests;
val () = export_theory_no_docs ();
