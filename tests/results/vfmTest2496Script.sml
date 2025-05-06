open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2496Theory;
val () = new_theory "vfmTest2496";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2496") $ get_result_defs "vfmTestDefs2496";
val () = export_theory_no_docs ();
