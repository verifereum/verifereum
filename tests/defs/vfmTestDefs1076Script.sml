open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1076";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stHomesteadSpecific/createContractViaContractOOGInitCode.json";
val defs = mapi (define_test "1076") tests;
val () = export_theory_no_docs ();
