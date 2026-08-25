Theory vfmTest0666[no_sig_docs]
Ancestors vfmTestDefs0666
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0666_0.nsv"];
val thyn = "vfmTestDefs0666";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
