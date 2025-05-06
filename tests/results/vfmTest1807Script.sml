open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1807Theory;
val () = new_theory "vfmTest1807";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1807") $ get_result_defs "vfmTestDefs1807";
val () = export_theory_no_docs ();
