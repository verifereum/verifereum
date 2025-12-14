open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0143";
val tests = json_path_to_tests "../fixtures/blockchain_tests/frontier/opcodes/test_value_transfer_gas_calculation.json";
val defs = mapi (define_test "0143") tests;
val () = export_theory_no_docs ();
