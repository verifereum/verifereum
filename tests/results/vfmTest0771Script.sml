open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0771Theory;
val () = new_theory "vfmTest0771";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0771") $ get_result_defs "vfmTestDefs0771";
val () = export_theory_no_docs ();
