open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0205";
val tests = json_path_to_tests "../fixtures/blockchain_tests/osaka/eip7934_block_rlp_limit/test_fork_transition_block_rlp_limit.json";
val defs = mapi (define_test "0205") tests;
val () = export_theory_no_docs ();
