open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0911";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stEIP150Specific/NewGasPriceForCodes.json";
val defs = mapi (define_test "0911") tests;
val () = export_theory_no_docs ();
