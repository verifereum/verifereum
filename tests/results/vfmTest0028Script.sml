open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0028Theory;
val () = new_theory "vfmTest0028";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0028") $ get_result_defs "vfmTestDefs0028";
val () = export_theory_no_docs ();
