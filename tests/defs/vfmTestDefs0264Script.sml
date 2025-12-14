open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0264";
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip2935_historical_block_hashes_from_state/test_eip_2935.json";
val defs = mapi (define_test "0264") tests;
val () = export_theory_no_docs ();
