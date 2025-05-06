open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1935Theory;
val () = new_theory "vfmTest1935";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1935") $ get_result_defs "vfmTestDefs1935";
val () = export_theory_no_docs ();
