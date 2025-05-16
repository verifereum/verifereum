open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2064";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_Call1024BalanceTooLow.json";
val defs = mapi (define_test "2064") tests;
val () = export_theory_no_docs ();
