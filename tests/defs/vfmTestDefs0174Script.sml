open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0174";
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip2935_historical_block_hashes_from_state/block_hashes/block_hashes_call_opcodes.json";
val defs = mapi (define_test "0174") tests;
val () = export_theory_no_docs ();
