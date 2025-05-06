open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1454Theory;
val () = new_theory "vfmTest1454";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1454") $ get_result_defs "vfmTestDefs1454";
val () = export_theory_no_docs ();
