open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0260Theory;
val () = new_theory "vfmTest0260";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0260") $ get_result_defs "vfmTestDefs0260";
val () = export_theory_no_docs ();
