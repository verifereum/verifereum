open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0720Theory;
val () = new_theory "vfmTest0720";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0720") $ get_result_defs "vfmTestDefs0720";
val () = export_theory_no_docs ();
