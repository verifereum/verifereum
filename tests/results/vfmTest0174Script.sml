open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0174Theory;
val () = new_theory "vfmTest0174";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0174") $ get_result_defs "vfmTestDefs0174";
val () = export_theory_no_docs ();
