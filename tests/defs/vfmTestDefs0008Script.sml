open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0008";
val tests = json_path_to_tests "../fixtures/blockchain_tests/byzantium/eip197_ec_pairing/test_gas_costs.json";
val defs = mapi (define_test "0008") tests;
val () = export_theory_no_docs ();
