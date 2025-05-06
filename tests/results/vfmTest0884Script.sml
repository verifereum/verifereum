open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0884Theory;
val () = new_theory "vfmTest0884";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0884") $ get_result_defs "vfmTestDefs0884";
val () = export_theory_no_docs ();
