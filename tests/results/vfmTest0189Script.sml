open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0189Theory;
val () = new_theory "vfmTest0189";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0189") $ get_result_defs "vfmTestDefs0189";
val () = export_theory_no_docs ();
