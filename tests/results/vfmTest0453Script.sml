open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0453Theory;
val () = new_theory "vfmTest0453";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0453") $ get_result_defs "vfmTestDefs0453";
val () = export_theory_no_docs ();
