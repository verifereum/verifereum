open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0207Theory;
val () = new_theory "vfmTest0207";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0207") $ get_result_defs "vfmTestDefs0207";
val () = export_theory_no_docs ();
