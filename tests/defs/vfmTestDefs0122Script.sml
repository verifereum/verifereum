open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0122";
val tests = json_path_to_tests "../fixtures/blockchain_tests/frontier/examples/test_block_intermediate_state.json";
val defs = mapi (define_test "0122") tests;
val () = export_theory_no_docs ();
