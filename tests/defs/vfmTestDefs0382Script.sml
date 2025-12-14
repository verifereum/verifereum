open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0382";
val tests = json_path_to_tests "../fixtures/blockchain_tests/shanghai/eip3651_warm_coinbase/test_warm_coinbase_call_out_of_gas.json";
val defs = mapi (define_test "0382") tests;
val () = export_theory_no_docs ();
