open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0110";
val tests = json_path_to_tests "../fixtures/blockchain_tests/frontier/examples/block_intermediate_state/block_intermidiate_state.json";
val defs = mapi (define_test "0110") tests;
val () = export_theory_no_docs ();
