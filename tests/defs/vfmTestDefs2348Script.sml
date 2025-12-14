open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2348";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_callcodecallcodecallcode_111_SuicideEnd.json";
val defs = mapi (define_test "2348") tests;
val () = export_theory_no_docs ();
