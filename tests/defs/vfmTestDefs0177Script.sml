open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0177";
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip2935_historical_block_hashes_from_state/block_hashes/invalid_history_contract_calls.json";
val defs = mapi (define_test "0177") tests;
val () = export_theory_no_docs ();
