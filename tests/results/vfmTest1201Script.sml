open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1201Theory;
val () = new_theory "vfmTest1201";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1201") $ get_result_defs "vfmTestDefs1201";
val () = export_theory_no_docs ();
