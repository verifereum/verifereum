open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0132";
val tests = json_path_to_tests "../fixtures/blockchain_tests/paris/security/selfdestruct_balance_bug/tx_selfdestruct_balance_bug.json";
val defs = mapi (define_test "0132") tests;
val () = export_theory_no_docs ();
