open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0424";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/Shanghai/stEIP3860_limitmeterinitcode/creationTxInitCodeSizeLimit.json";
val defs = mapi (define_test "0424") tests;
val () = export_theory_no_docs ();
