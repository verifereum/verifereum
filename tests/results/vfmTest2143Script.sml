open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2143Theory;
val () = new_theory "vfmTest2143";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2143") $ get_result_defs "vfmTestDefs2143";
val () = export_theory_no_docs ();
