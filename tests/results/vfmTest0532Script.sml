open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0532Theory;
val () = new_theory "vfmTest0532";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0532") $ get_result_defs "vfmTestDefs0532";
val () = export_theory_no_docs ();
