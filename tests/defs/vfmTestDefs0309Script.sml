open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0309";
val tests = json_path_to_tests "../fixtures/blockchain_tests/shanghai/eip4895_withdrawals/withdrawals/withdrawing_to_precompiles.json";
val defs = mapi (define_test "0309") tests;
val () = export_theory_no_docs ();
