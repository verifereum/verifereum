open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0141Theory;
val () = new_theory "vfmTest0141";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0141") $ get_result_defs "vfmTestDefs0141";
val () = export_theory_no_docs ();
