open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0021Theory;
val () = new_theory "vfmTest0021";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0021") $ get_result_defs "vfmTestDefs0021";
val () = export_theory_no_docs ();
