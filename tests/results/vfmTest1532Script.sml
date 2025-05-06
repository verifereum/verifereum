open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1532Theory;
val () = new_theory "vfmTest1532";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1532") $ get_result_defs "vfmTestDefs1532";
val () = export_theory_no_docs ();
