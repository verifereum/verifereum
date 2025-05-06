open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1269Theory;
val () = new_theory "vfmTest1269";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1269") $ get_result_defs "vfmTestDefs1269";
val () = export_theory_no_docs ();
