Theory vfmTest0401[no_sig_docs]
Ancestors vfmTestDefs0401
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0401_0.nsv"];
val thyn = "vfmTestDefs0401";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
