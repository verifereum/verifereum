open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2367";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_callcallcodecallcode_011_SuicideEnd.json";
val defs = mapi (define_test "2367") tests;
val () = export_theory_no_docs ();
