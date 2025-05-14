open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0334";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/Shanghai/stEIP3860_limitmeterinitcode/createInitCodeSizeLimit.json";
val defs = mapi (define_test "0334") tests;
val () = export_theory_no_docs ();
