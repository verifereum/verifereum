open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0612";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallCodes/callcodecall_10_OOGE.json";
val defs = mapi (define_test "0612") tests;
val () = export_theory_no_docs ();
