open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0183";
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip2935_historical_block_hashes_from_state/contract_deployment/system_contract_deployment.json";
val defs = mapi (define_test "0183") tests;
val () = export_theory_no_docs ();
