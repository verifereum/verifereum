open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0960Theory;
val () = new_theory "vfmTest0960";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0960") $ get_result_defs "vfmTestDefs0960";
val () = export_theory_no_docs ();
