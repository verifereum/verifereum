open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0289";
val tests = json_path_to_tests "../fixtures/blockchain_tests/shanghai/eip3651_warm_coinbase/warm_coinbase/warm_coinbase_gas_usage.json";
val defs = mapi (define_test "0289") tests;
val () = export_theory_no_docs ();
