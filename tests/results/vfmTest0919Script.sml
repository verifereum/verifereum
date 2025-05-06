open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0919Theory;
val () = new_theory "vfmTest0919";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0919") $ get_result_defs "vfmTestDefs0919";
val () = export_theory_no_docs ();
