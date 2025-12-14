open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0417";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/Shanghai/stEIP3651_warmcoinbase/coinbaseWarmAccountCallGas.json";
val defs = mapi (define_test "0417") tests;
val () = export_theory_no_docs ();
