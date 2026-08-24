Theory vfmTest2808[no_sig_docs]
Ancestors vfmTestDefs2808
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2808_0.nsv", "result2808_1.nsv", "result2808_2.nsv", "result2808_3.nsv"];
val thyn = "vfmTestDefs2808";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
