open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0912Theory;
val () = new_theory "vfmTest0912";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0912") $ get_result_defs "vfmTestDefs0912";
val () = export_theory_no_docs ();
