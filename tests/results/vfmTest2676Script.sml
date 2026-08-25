Theory vfmTest2676[no_sig_docs]
Ancestors vfmTestDefs2676
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2676_0.nsv", "result2676_1.nsv", "result2676_2.nsv", "result2676_3.nsv"];
val thyn = "vfmTestDefs2676";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
