open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1778Theory;
val () = new_theory "vfmTest1778";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1778") $ get_result_defs "vfmTestDefs1778";
val () = export_theory_no_docs ();
