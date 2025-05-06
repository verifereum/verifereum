open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0700Theory;
val () = new_theory "vfmTest0700";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0700") $ get_result_defs "vfmTestDefs0700";
val () = export_theory_no_docs ();
