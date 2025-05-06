open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1603Theory;
val () = new_theory "vfmTest1603";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1603") $ get_result_defs "vfmTestDefs1603";
val () = export_theory_no_docs ();
