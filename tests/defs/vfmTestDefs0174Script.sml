open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0174";
val tests = json_path_to_tests "../fixtures/blockchain_tests/osaka/eip7825_transaction_gas_limit_cap/test_transaction_gas_limit_cap_at_transition.json";
val defs = mapi (define_test "0174") tests;
val () = export_theory_no_docs ();
