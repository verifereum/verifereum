Theory vfmTest0343[no_sig_docs]
Ancestors vfmTestDefs0343
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0343_0.nsv", "result0343_1.nsv"];
val thyn = "vfmTestDefs0343";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
