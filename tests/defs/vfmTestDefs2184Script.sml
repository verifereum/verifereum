open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2184";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_Call1MB1024Calldepth.json";
val defs = mapi (define_test "2184") tests;
val () = export_theory_no_docs ();
