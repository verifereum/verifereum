open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0626";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallDelegateCodesCallCodeHomestead/callcodecallcodecallcode_111_SuicideEnd.json";
val defs = mapi (define_test "0626") tests;
val () = export_theory_no_docs ();
