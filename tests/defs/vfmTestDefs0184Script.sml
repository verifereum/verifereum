open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0184";
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip6110_deposits/modified_contract/invalid_log_length.json";
val defs = mapi (define_test "0184") tests;
val () = export_theory_no_docs ();
