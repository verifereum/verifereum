Theory vfmTest2628[no_sig_docs]
Ancestors vfmTestDefs2628
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2628_0.nsv", "result2628_1.nsv", "result2628_2.nsv", "result2628_3.nsv"];
val thyn = "vfmTestDefs2628";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
