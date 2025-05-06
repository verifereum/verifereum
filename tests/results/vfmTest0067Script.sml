open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0067Theory;
val () = new_theory "vfmTest0067";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0067") $ get_result_defs "vfmTestDefs0067";
val () = export_theory_no_docs ();
