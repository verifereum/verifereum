open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0182";
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip6110_deposits/modified_contract/extra_logs.json";
val defs = mapi (define_test "0182") tests;
val () = export_theory_no_docs ();
