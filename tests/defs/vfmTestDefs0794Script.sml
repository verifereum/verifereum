open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0794";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCreate2/Create2OOGafterInitCode.json";
val defs = mapi (define_test "0794") tests;
val () = export_theory_no_docs ();
