Theory vfmTest0493[no_sig_docs]
Ancestors vfmTestDefs0493
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0493_0.nsv", "result0493_1.nsv"];
val thyn = "vfmTestDefs0493";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
