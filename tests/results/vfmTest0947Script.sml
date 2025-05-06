open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0947Theory;
val () = new_theory "vfmTest0947";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0947") $ get_result_defs "vfmTestDefs0947";
val () = export_theory_no_docs ();
