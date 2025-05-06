open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1106Theory;
val () = new_theory "vfmTest1106";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1106") $ get_result_defs "vfmTestDefs1106";
val () = export_theory_no_docs ();
