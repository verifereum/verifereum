open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0822";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stEIP150Specific/CallAndCallcodeConsumeMoreGasThenTransactionHas.json";
val defs = mapi (define_test "0822") tests;
val () = export_theory_no_docs ();
