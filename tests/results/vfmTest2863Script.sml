open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2863Theory;
val () = new_theory "vfmTest2863";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2863") $ get_result_defs "vfmTestDefs2863";
val () = export_theory_no_docs ();
