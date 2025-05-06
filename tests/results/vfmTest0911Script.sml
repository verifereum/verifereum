open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0911Theory;
val () = new_theory "vfmTest0911";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0911") $ get_result_defs "vfmTestDefs0911";
val () = export_theory_no_docs ();
