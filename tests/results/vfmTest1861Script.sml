open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1861Theory;
val () = new_theory "vfmTest1861";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1861") $ get_result_defs "vfmTestDefs1861";
val () = export_theory_no_docs ();
