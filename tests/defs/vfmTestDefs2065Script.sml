open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2065";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_Call1024BalanceTooLow2.json";
val defs = mapi (define_test "2065") tests;
val () = export_theory_no_docs ();
