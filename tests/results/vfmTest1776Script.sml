open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs1776Theory;
val () = new_theory "vfmTest1776";
val thyn = "vfmTestDefs1776";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
