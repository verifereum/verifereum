Theory vfmTest0411[no_sig_docs]
Ancestors vfmTestDefs0411
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0411_0.nsv"];
val thyn = "vfmTestDefs0411";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
