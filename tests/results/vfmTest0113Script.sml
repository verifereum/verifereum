open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0113Theory;
val () = new_theory "vfmTest0113";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0113") $ get_result_defs "vfmTestDefs0113";
val () = export_theory_no_docs ();
