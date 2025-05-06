open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1661Theory;
val () = new_theory "vfmTest1661";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1661") $ get_result_defs "vfmTestDefs1661";
val () = export_theory_no_docs ();
