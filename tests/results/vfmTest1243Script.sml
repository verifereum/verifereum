open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1243Theory;
val () = new_theory "vfmTest1243";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1243") $ get_result_defs "vfmTestDefs1243";
val () = export_theory_no_docs ();
