open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0027Theory;
val () = new_theory "vfmTest0027";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0027") $ get_result_defs "vfmTestDefs0027";
val () = export_theory_no_docs ();
