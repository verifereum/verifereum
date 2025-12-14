open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0150";
val tests = json_path_to_tests "../fixtures/blockchain_tests/frontier/validation/test_gas_limit_below_minimum.json";
val defs = mapi (define_test "0150") tests;
val () = export_theory_no_docs ();
