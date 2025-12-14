open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0383";
val tests = json_path_to_tests "../fixtures/blockchain_tests/shanghai/eip3651_warm_coinbase/test_warm_coinbase_gas_usage.json";
val defs = mapi (define_test "0383") tests;
val () = export_theory_no_docs ();
