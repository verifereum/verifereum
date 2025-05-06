open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1445Theory;
val () = new_theory "vfmTest1445";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1445") $ get_result_defs "vfmTestDefs1445";
val () = export_theory_no_docs ();
