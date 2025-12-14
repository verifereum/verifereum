open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0229";
val tests = json_path_to_tests "../fixtures/blockchain_tests/osaka/eip7951_p256verify_precompiles/test_precompile_will_return_success_with_tx_value.json";
val defs = mapi (define_test "0229") tests;
val () = export_theory_no_docs ();
