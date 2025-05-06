open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0392Theory;
val () = new_theory "vfmTest0392";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0392") $ get_result_defs "vfmTestDefs0392";
val () = export_theory_no_docs ();
