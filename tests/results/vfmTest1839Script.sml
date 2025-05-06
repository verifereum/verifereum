open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1839Theory;
val () = new_theory "vfmTest1839";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1839") $ get_result_defs "vfmTestDefs1839";
val () = export_theory_no_docs ();
