Theory vfmTest2783[no_sig_docs]
Ancestors vfmTestDefs2783
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2783_0.nsv", "result2783_1.nsv", "result2783_2.nsv", "result2783_3.nsv"];
val thyn = "vfmTestDefs2783";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
