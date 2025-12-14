open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0261";
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip2935_historical_block_hashes_from_state/test_block_hashes_call_opcodes.json";
val defs = mapi (define_test "0261") tests;
val () = export_theory_no_docs ();
