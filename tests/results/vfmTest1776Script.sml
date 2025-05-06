open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1776Theory;
val () = new_theory "vfmTest1776";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1776") $ get_result_defs "vfmTestDefs1776";
val () = export_theory_no_docs ();
