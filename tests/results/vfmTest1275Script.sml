open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1275Theory;
val () = new_theory "vfmTest1275";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1275") $ get_result_defs "vfmTestDefs1275";
val () = export_theory_no_docs ();
