open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0145";
val tests = json_path_to_tests "../fixtures/blockchain_tests/frontier/opcodes/test_value_transfer_gas_calculation_homestead.json";
val defs = mapi (define_test "0145") tests;
val () = export_theory_no_docs ();
