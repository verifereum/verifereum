open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0269Theory;
val () = new_theory "vfmTest0269";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0269") $ get_result_defs "vfmTestDefs0269";
val () = export_theory_no_docs ();
