open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2693Theory;
val () = new_theory "vfmTest2693";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2693") $ get_result_defs "vfmTestDefs2693";
val () = export_theory_no_docs ();
