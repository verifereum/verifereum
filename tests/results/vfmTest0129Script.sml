open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0129Theory;
val () = new_theory "vfmTest0129";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0129") $ get_result_defs "vfmTestDefs0129";
val () = export_theory_no_docs ();
