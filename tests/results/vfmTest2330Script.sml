Theory vfmTest2330[no_sig_docs]
Ancestors vfmTestDefs2330
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2330_0.nsv", "result2330_1.nsv", "result2330_2.nsv", "result2330_3.nsv"];
val thyn = "vfmTestDefs2330";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
