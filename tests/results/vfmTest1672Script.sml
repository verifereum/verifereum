open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1672Theory;
val () = new_theory "vfmTest1672";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1672") $ get_result_defs "vfmTestDefs1672";
val () = export_theory_no_docs ();
