open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0945Theory;
val () = new_theory "vfmTest0945";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0945") $ get_result_defs "vfmTestDefs0945";
val () = export_theory_no_docs ();
